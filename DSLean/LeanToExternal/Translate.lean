import Lean
import Std.Internal.Parsec
import Std.Internal.Parsec.Basic
import Std.Internal.Parsec.String
import Qq.Macro
import Lean.Elab.Command
import DSLean.Utils.Pattern
import Lean.Parser.Command
import Lean.Parser.Syntax
import Lean.Parser.Term
import Lean.Elab.Syntax


import DSLean.Utils.Syntax
import DSLean.Utils.Datatypes
import DSLean.ExternalToLean.Main

open Lean Meta Tactic Elab Meta Term Tactic Expr Command
open Qq


/-- Given the name of a binder occurring in `pattern`, finds the corresponding name in `target` given that they have the same structure. -/
partial def findTargetBinderName (pattern : Expr) (target : Expr) (binderName : Name) : TermElabM Name := do
  match (pattern, target) with
  | (Expr.forallE n ty body _, Expr.forallE n' ty' body' _) =>
    if n == binderName then return n'
    else
      findTargetBinderName ty ty' binderName <|>
      findTargetBinderName body body' binderName
  | (Expr.lam n ty body _, Expr.lam n' ty' body' _) =>
    if n == binderName then return n'
    else
      findTargetBinderName ty ty' binderName <|>
      findTargetBinderName body body' binderName
  | (Expr.letE n ty val body _, Expr.letE n' ty' val' body' _) =>
    if n == binderName then return n'
    else
      findTargetBinderName ty ty' binderName <|>
      findTargetBinderName val val' binderName <|>
      findTargetBinderName body body' binderName
  | (Expr.app f a, Expr.app f' a') =>
    findTargetBinderName f f' binderName <|>
    findTargetBinderName a a' binderName
  | (Expr.mdata _ e, Expr.mdata _ e') =>
    findTargetBinderName e e' binderName
  | (Expr.proj _ _ struct, Expr.proj _ _ struct') =>
    findTargetBinderName struct struct' binderName
  | _ => throwError "Binder name not found in pattern"


partial def Lean.Expr.printdbg (e : Expr) : String :=
  match e with
  | Expr.bvar idx => s!"bvar({idx})"
  | Expr.fvar id => s!"fvar({id.name})"
  | Expr.mvar id => s!"mvar({id.name})"
  | Expr.sort l => s!"sort({l})"
  | Expr.const id ls => s!"const({id}, {ls})"
  | Expr.app f a => s!"app({f.printdbg}, {a.printdbg})"
  | Expr.lam n ty body _ => s!"lam({n}, {ty.printdbg}, {body.printdbg})"
  | Expr.forallE n ty body _ => s!"forallE({n}, {ty.printdbg}, {body.printdbg})"
  | Expr.letE n ty val body _ => s!"letE({n}, {ty.printdbg}, {val.printdbg}, {body.printdbg})"
  | Expr.lit l => s!"lit()"
  | Expr.proj n idx struct => s!"proj({n}, {idx}, {struct})"
  | Expr.mdata md e => s!"mdata({md}, {e.printdbg})"



def Lean.Expr.traverseAllStateful {m} [Monad m] {α : Type} (e : Expr) (init : α) (fn : Expr → α → m ((Option Expr) × α)) : m (Expr × α) := do
  match (← fn e init) with
  | (some e', a) => return (e', a)
  | (none, a) =>
    match e with
    | .app f arg =>
      let (f', a') ← traverseAllStateful f a fn
      let (arg', a'') ← traverseAllStateful arg a' fn
      return (.app f' arg', a'')
    | .lam n ty body info =>
      let (ty', a') ← traverseAllStateful ty a fn
      let (body', a'') ← traverseAllStateful body a' fn
      return (.lam n ty' body' info, a'')
    | .forallE n ty body info =>
      let (ty', a') ← traverseAllStateful ty a fn
      let (body', a'') ← traverseAllStateful body a' fn
      return (.forallE n ty' body' info, a'')
    | .letE n ty val body info =>
      let (ty', a') ← traverseAllStateful ty a fn
      let (val', a'') ← traverseAllStateful val a' fn
      let (body', a''') ← traverseAllStateful body a'' fn
      return (.letE n ty' val' body' info, a''')
    | .mdata md e' =>
      let (e'', a') ← traverseAllStateful e' a fn
      return (.mdata md e'', a')
    | .proj n idx struct =>
      let (struct', a') ← traverseAllStateful struct a fn
      return (.proj n idx struct', a')
    | _ => return (e, a)


def Lean.Expr.traverseAll {m} [Monad m] (e : Expr) (fn : Expr → m (Option Expr)) : m Expr :=
  (Lean.Expr.traverseAllStateful e () (fun e => fun _ => do
    let res ← fn e
    match res with
    | some e' => return (some e', ())
    | none => return (none, ()))
  ) >>= (fun x => pure (Prod.fst x))


/-- A specific sub-expression within an `Expr` identified by a path of indices. -/
structure ExprLocation where
  e : Expr
  path : List Nat
deriving Repr

instance : ToMessageData ExprLocation where
  toMessageData loc :=
    m!"ExprLocation(path={loc.path}, e={loc.e.printdbg})"

/-- Given a sub-expression, find it and run `fn`. Also telescopes all the surrounding binders so the sub-expression doesn't have hanging bvars. -/
partial def ExprLocation.telescopeAll (loc : ExprLocation) (fn : Expr → β → TermElabM α) (input : β) : TermElabM α := do
  match loc.path with
  | [] => fn loc.e input
  | idx :: rest =>
    match loc.e with
    | .lam n ty _ _ =>
      if idx == 0 then
        (⟨ty, rest⟩ : ExprLocation).telescopeAll fn input
      else
        lambdaBoundedTelescope loc.e 1 fun fvar body' => do
          withLCtx' ((← getLCtx).setUserName fvar[0]!.fvarId! n) do -- Set the name of the bound variable in the local context
            (⟨body', rest⟩ : ExprLocation).telescopeAll fn input
    | .forallE _ ty _ _ =>
      if idx == 0 then
        (⟨ty, rest⟩ : ExprLocation).telescopeAll fn input
      else
        forallBoundedTelescope loc.e (some 1) fun _ body =>
          (⟨body, rest⟩ : ExprLocation).telescopeAll fn input
    | .letE _ ty val _ _ =>
      if idx == 0 then
        (⟨ty, rest⟩ : ExprLocation).telescopeAll fn input
      else if idx == 1 then
        (⟨val, rest⟩ : ExprLocation).telescopeAll fn input
      else
        letBoundedTelescope loc.e (some 1) fun _ body =>
          (⟨body, rest⟩ : ExprLocation).telescopeAll fn input
    | .app f a =>
      if idx == 0 then
        (⟨f, rest⟩ : ExprLocation).telescopeAll fn input
      else
        (⟨a, rest⟩ : ExprLocation).telescopeAll fn input
    | .mdata _ e' =>
      (⟨e', rest⟩ : ExprLocation).telescopeAll fn input
    | .proj _ _ struct =>
      (⟨struct, rest⟩ : ExprLocation).telescopeAll fn input
    | _ => throwError "ExprLocation.telescopeAll: invalid path"


/-- Given an expression `e` containing metavariables, we make these metavariables dependent on binders that surround them: for example, normally `fun x => ?m` may not be able to be unified with `fun x => x+1`; however, this function returns an expression of the same structure that can be unified. Not sure why `isDefEq` can't handle this nicely. Returns modified expressions, plus a map from old mvars to the new areas corresponding to them. -/
partial def makeMVarsDependentGetLocations (e : Expr) (blankMap : Std.HashMap MVarId Name) : TermElabM (Expr × Std.HashMap MVarId (Name × ExprLocation)) := do
  let ⟨e', _, updatedMVars⟩ ← go e blankMap {} [] []
  return (e', updatedMVars.map (fun _ (name, path) => (name, ⟨e', path⟩)))
where go : Expr → Std.HashMap MVarId Name → Std.HashMap MVarId (Name × List Nat) → List Expr → List Nat → TermElabM (Expr × Std.HashMap MVarId Name × Std.HashMap MVarId (Name × List Nat)) := fun e mvarIdsRemaining newMVarIds binderTypes locationPath =>
do
  match e with
  | .mvar id =>
    if mvarIdsRemaining.contains id then
      let rec mkMVarType (binderTypes : List Expr) : TermElabM Expr := do
        match binderTypes with
        | ty :: rest =>
          let inner ← mkMVarType rest
          mkArrow ty inner
        | _ => inferType e
      let rec addBVars (mvar : Expr) (depth : Nat) : Expr :=
        match depth with
        | 0 => mvar
        | _ => addBVars (Expr.app mvar (Expr.bvar (depth - 1))) (depth - 1)

      let new := addBVars (← mkFreshExprMVar (some (← mkMVarType binderTypes))) binderTypes.length
      return (new, mvarIdsRemaining.filter (fun id' _ => id' != id), newMVarIds.insert id (mvarIdsRemaining.get! id, locationPath))
    else
      return (e, mvarIdsRemaining, newMVarIds)
  | .lam n ty body info =>
    let (ty', mvarIdsRemaining', newMVarIds') ← go ty mvarIdsRemaining newMVarIds binderTypes (locationPath ++ [0])
    let (body', mvarIdsRemaining'', newMVarIds'') ← go body mvarIdsRemaining' newMVarIds' (ty' :: binderTypes) (locationPath ++ [1])
    return (.lam n ty' body' info, mvarIdsRemaining'', newMVarIds'')
  | .forallE n ty body info =>
    let (ty', mvarIdsRemaining', newMVarIds') ← go ty mvarIdsRemaining newMVarIds binderTypes (locationPath ++ [0])
    let (body', mvarIdsRemaining'', newMVarIds'') ← go body mvarIdsRemaining' newMVarIds' (ty' :: binderTypes) (locationPath ++ [1])
    return (.forallE n ty' body' info, mvarIdsRemaining'', newMVarIds'')
  | .letE n ty val body info =>
    let (ty', mvarIds', newMVarIds') ← go ty mvarIdsRemaining newMVarIds binderTypes (locationPath ++ [0])
    let (val', mvarIds'', newMVarIds'') ← go val mvarIds' newMVarIds' binderTypes (locationPath ++ [1])
    let (body', mvarIds''', newMVarIds''') ← go body mvarIds'' newMVarIds'' (ty' :: binderTypes) (locationPath ++ [2])
    return (.letE n ty' val' body' info, mvarIds''', newMVarIds''')
  | .app f a =>
    let (f', mvarIds', newMVarIds') ← go f mvarIdsRemaining newMVarIds binderTypes (locationPath ++ [0])
    let (a', mvarIds'', newMVarIds'') ← go a mvarIds' newMVarIds' binderTypes (locationPath ++ [1])
    return (.app f' a', mvarIds'', newMVarIds'')
  | .mdata md e' =>
    let (e'', mvarIds', newMVarIds') ← go e' mvarIdsRemaining newMVarIds binderTypes (locationPath ++ [0])
    return (.mdata md e'', mvarIds', newMVarIds')
  | .proj n idx struct =>
    let (struct', mvarIds', newMVarIds') ← go struct mvarIdsRemaining newMVarIds binderTypes (locationPath ++ [0])
    return (.proj n idx struct', mvarIds', newMVarIds')
  | _ => return (e, mvarIdsRemaining, newMVarIds)


/-- Given an expression `e` containing metavariables, we make these metavariables dependent on binders that surround them: for example, normally `fun x => ?m` may not be able to be unified with `fun x => x+1`; however, this function returns an expression of the same structure that can be unified. Not sure why `isDefEq` can't handle this nicely. Returns modified expressions, plus a map from old mvars to the new areas corresponding to them. -/
partial def makeMVarsDependent (e : Expr) (mvarIds : List MVarId) : TermElabM (Expr × Std.HashMap MVarId Expr) := do
  let ⟨e', _, updatedMVars⟩ ← go e mvarIds {} []
  return (e', updatedMVars)
where go : Expr → List MVarId → Std.HashMap MVarId Expr → List Expr → TermElabM (Expr × List MVarId × Std.HashMap MVarId Expr) := fun e mvarIdsRemaining newMVarIds binderTypes =>
do
  match e with
  | .mvar id =>
    if mvarIds.contains id then
      let rec mkMVarType (binderTypes : List Expr) : TermElabM Expr := do
        match binderTypes with
        | ty :: rest =>
          let inner ← mkMVarType rest
          mkArrow ty inner
        | _ => inferType e
      let rec addBVars (mvar : Expr) (depth : Nat) : Expr :=
        match depth with
        | 0 => mvar
        | _ => addBVars (Expr.app mvar (Expr.bvar (depth - 1))) (depth - 1)

      let new := addBVars (← mkFreshExprMVar (some (← mkMVarType binderTypes))) binderTypes.length
      return (new, mvarIdsRemaining.filter (fun mid => mid != id), newMVarIds.insert id new)
    else
      return (e, mvarIdsRemaining, newMVarIds)
  | .lam n ty body info =>
    let (ty', mvarIdsRemaining', newMVarIds') ← go ty mvarIdsRemaining newMVarIds binderTypes
    let (body', mvarIdsRemaining'', newMVarIds'') ← go body mvarIdsRemaining' newMVarIds' (ty' :: binderTypes)
    return (.lam n ty' body' info, mvarIdsRemaining'', newMVarIds'')
  | .forallE n ty body info =>
    let (ty', mvarIdsRemaining', newMVarIds') ← go ty mvarIds newMVarIds binderTypes
    let (body', mvarIdsRemaining'', newMVarIds'') ← go body mvarIdsRemaining' newMVarIds' (ty' :: binderTypes)
    return (.forallE n ty' body' info, mvarIdsRemaining'', newMVarIds'')
  | .letE n ty val body info =>
    let (ty', mvarIds', newMVarIds') ← go ty mvarIds newMVarIds binderTypes
    let (val', mvarIds'', newMVarIds'') ← go val mvarIds' newMVarIds' binderTypes
    let (body', mvarIds''', newMVarIds''') ← go body mvarIds'' newMVarIds'' (ty' :: binderTypes)
    return (.letE n ty' val' body' info, mvarIds''', newMVarIds''')
  | .app f a =>
    let (f', mvarIds', newMVarIds') ← go f mvarIds newMVarIds binderTypes
    let (a', mvarIds'', newMVarIds'') ← go a mvarIds' newMVarIds' binderTypes
    return (.app f' a', mvarIds'', newMVarIds'')
  | .mdata md e' =>
    let (e'', mvarIds', newMVarIds') ← go e' mvarIds newMVarIds binderTypes
    return (.mdata md e'', mvarIds', newMVarIds')
  | .proj n idx struct =>
    let (struct', mvarIds', newMVarIds') ← go struct mvarIds newMVarIds binderTypes
    return (.proj n idx struct', mvarIds', newMVarIds')
  | _ => return (e, mvarIdsRemaining, newMVarIds)


-- TODO: is there a less jank way to handle `binderRenames`? Does this always work if variables are shadowed later?

/-- Given an expression, translate it into an external representation using the rules defined in the externalSyntax `cat`, recursively filling in "blanks". -/
partial def translateExpr (cat : Name) (patterns : Array ExternalEquivalence) (e : Expr) (binderRenames : Std.HashMap Name String := {}) (depth := 0) : TermElabM String := do
  if depth > 1000 then
    throwError m!"Exceeded maximum recursion depth when translating expression {e}. There's probably an infinite loop in the DSL somewhere."

  let pattern_contents ← patterns.filterMapM (fun pat => do
    match pat.exprPattern with
    | .postponed _ => pure none
    | .eager p =>
      let (_, _, patExpr, blankMap) ← p.unpackExpr
      pure <| some (pat, patExpr, blankMap)
    )
  let pattern_contents := pattern_contents.qsort (fun (_, e, _) _ => -- TODO: put "no-op" patterns at the end too?
    if e.isLambda || e.isForall || e.isLet then false else true
  ) -- Try simpler patterns first; `isDefEq` can change any expression to match `lambda`s etc via reductions and whatnot

  let mut firstErr : Option Exception := none

  for (pat, pat_expr_old, blankMap) in pattern_contents do
      let (pat_expr, newBlankMap) ← makeMVarsDependentGetLocations pat_expr_old blankMap -- When reloading metavariables from their abstracted form, they may not be able to depend on binders around them, so we make each one maximally dependent manually


      if pat.stxNodeKind == (externalIdentKind (mkIdent cat)) then -- Special case: identifiers
        if e.isFVar then
          match binderRenames.get? (← e.fvarId!.getUserName) with
          | some renamed => return renamed
          | none => return (← e.fvarId!.getUserName).toString
        else
          continue

      if pat.stxNodeKind == (externalNumKind (mkIdent cat)) then
        if e.nat?.isSome || e.isRawNatLit then
          return (← PrettyPrinter.ppExpr e).pretty -- Special case: external number literals
        else
          continue

      if pat.stxNodeKind == (externalScientificKind (mkIdent cat)) then
        if Simp.isOfScientificLit e then
          return (← PrettyPrinter.ppExpr e).pretty -- Special case: external scientific literals
        else
          continue

      else
      -- logInfo m!"Trying pattern {pat_expr} for expression {e}"

      try
        let out ← withoutModifyingMCtx do

          if (← isDefEqGuarded pat_expr e) then
            -- logInfo m!"Matched! Pattern is now {← instantiateMVars pat_expr}"

            let processBlank := fun e br => do translateExpr cat patterns (← Core.betaReduce (← instantiateMVars e)) br (depth + 1)

            let filledMap := Std.HashMap.ofList <| newBlankMap.values.map (fun (n, loc) =>  (n, loc.telescopeAll processBlank))


            let mut result := ""
            let mut binderRenames' := binderRenames

            for chunk in pat.rawSyntaxPatterns do
              match chunk with
              | .node _ k args =>
                match k with
                | `Lean.Parser.Syntax.atom =>
                  match args.toList with
                  | .node _ _ atomArgs :: _ =>
                    match atomArgs.toList with
                    | (.atom _ raw ) :: _ => -- If this part of the pattern is just a literal, put it in the output directly
                      result := result ++ " " ++ (raw.take (raw.length - 1) |>.takeRight (raw.length - 2)) -- Strip away the quotes
                    | _ => throwError m!"Unable to turn atom pattern into string: {atomArgs.map (fun x => x.printdbg)}"
                  | _ => throwError m!"Unable to turn atom pattern into string: {args.map (fun x => x.printdbg)}"
                | `Lean.Parser.Syntax.cat =>
                  match args.toList with
                  | (.ident _ raw _ _ ) :: _ => -- If this part of the pattern is a blank, look up what we filled it with
                    match filledMap.get? raw.toName with
                    | some blank => do
                      let blankStr ← blank binderRenames' -- TODO: make this lazy but still cache everything
                      result := result ++ " " ++ blankStr

                    | none => throwError m!"Internal error: no filled string for blank {raw.toName}"
                  | _ => throwError m!"Unable to turn pattern into string: {args}"
                | `stx.pseudo.antiquot =>
                  match args.toList with
                  | _ :: _ :: (.ident _ raw _ _ ) :: _ => -- If this part of the pattern is an identifier variable, find the corresponding identifier's name
                    let binderName ← findTargetBinderName pat_expr e raw.toName
                    binderRenames' := binderRenames'.insert raw.toName (if binderName.isAnonymous then "x" else binderName.toString)
                    result := result ++ " " ++ (if binderName.isAnonymous then "x" else binderName.toString)
                  | _ => throwError m!"Unsupported antiquot args: {args}"
                | _ => throwError m!"Unsupported syntax node kind: {k}"
              | x => throwError m!"Unsupported syntax part: {x.printdbg}"
            return some result.trim
          else
            return none

        match out with
        | some s =>
          let postprocessed := s.replace "\\\\" "\\" -- Doesn't handle escaping right when passing through meta level for some reason
          return postprocessed
        | none => continue


      catch ex => -- If there was some problem when matching the pattern, continue but remember the error to report it later
        firstErr := some ex
        continue

  match firstErr with
  | some e => throw e
  | none => throwError m!"No matching pattern found for expression {e}"


/-- Translate a Lean expression `e` into external syntax according to the external syntax category `cat`. -/
def toExternal (cat : Name) (e : Expr) : TermElabM String := do
  let patterns ← liftCommandElabM <| getExternalEquivalencesForCategory cat
  let p1 :: _ := patterns.toList | throwError m!"No external equivalences found for category '{cat}'"
  unless p1.isInjective do
    throwError m!"Translation to external syntax failed: external equivalence for category '{cat}' is not injective, cannot translate from Lean expression to external syntax"

  translateExpr cat patterns e
