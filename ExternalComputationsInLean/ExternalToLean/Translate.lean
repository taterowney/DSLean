import Lean
import Std.Internal.Parsec
import Std.Internal.Parsec.Basic
import Std.Internal.Parsec.String
import Qq.Macro
import Lean.Elab.Command
import ExternalComputationsInLean.Utils.Pattern
import Lean.Parser.Command
import Lean.Parser.Syntax
import Lean.Parser.Term
import Lean.Elab.Syntax


import ExternalComputationsInLean.Utils.Syntax
import ExternalComputationsInLean.Utils.Datatypes
import ExternalComputationsInLean.LeanToExternal.Main

open Lean Meta Tactic Elab Meta Term Tactic Expr Command
open Qq



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
      -- logInfo m!"Type of new mvar: {(← mkMVarType binderTypes)}"
      let rec addBVars (mvar : Expr) (depth : Nat) : Expr :=
        match depth with
        | 0 => mvar
        | _ => addBVars (Expr.app mvar (Expr.bvar (depth - 1))) (depth - 1)
      -- logInfo m!"New expression: {addBVars (← mkFreshExprMVar (some (← mkMVarType binderTypes))) binderTypes.length}"

      let new := addBVars (← mkFreshExprMVar (some (← mkMVarType binderTypes))) binderTypes.length

      return (new, mvarIdsRemaining.filter (fun mid => mid != id), newMVarIds.insert id new)
    else
      return (e, mvarIdsRemaining, newMVarIds)
  | .lam n ty body info =>
    let (ty', mvarIdsRemaining', newMVarIds') ← go ty mvarIdsRemaining newMVarIds binderTypes
    let (body', mvarIdsRemaining'', newMVarIds'') ← go body mvarIdsRemaining' newMVarIds' (ty' :: binderTypes)
    -- logInfo m!"Body is {body'}"
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



partial def translateExpr (cat : Name) (patterns : Array ExternalEquivalence) (e : Expr) (depth := 0) : TermElabM String := do
  if depth > 1000 then
    throwError m!"Exceeded maximum recursion depth when translating expression {e}. There's probably an infinite loop in the DSL somewhere."

  for pat in patterns do
    match pat.exprPattern with
    | .postponed _ => continue
    | .eager p =>
      let (mvars, _, pat_expr, blankMap) ← p.unpackExpr
      let (pat_expr, new_mvars) ← makeMVarsDependent pat_expr (mvars.toList.map (fun mv => mv.mvarId!)) -- When reloading metavariables from their abstracted form, they may not be able to depend on binders around them, so we make each one maximally dependent manually
      let blankMap := Std.HashMap.ofList <| ← blankMap.toList.mapM (m := TermElabM) (fun (id, n) => do (match new_mvars.get? id with | some newId => pure (newId, n) | none => throwError "Internal assertion failed: makeMVarsDependent didn't specify what it replaced all the metavariables with")) -- Update the blank map to use the new metavariable IDs

      if pat.stxNodeKind == (externalNumKind (mkIdent cat)) then
        if e.nat?.isSome || e.isRawNatLit then
          return (← PrettyPrinter.ppExpr e).pretty -- Special case: external number literals
        else
          continue

      else
      logInfo m!"Trying pattern {pat_expr} for expression {e}"
      if (← isDefEqGuarded pat_expr e) then
        logInfo m!"Matched! Pattern is now {← instantiateMVars pat_expr}"
        let filledBlanks ← blankMap.keys.mapM (fun e => do translateExpr cat patterns (← Core.betaReduce (← instantiateMVars e)) (depth + 1)) -- TODO: for now, we betaReduce everything to make dependent mvars with binders applied not appear as new `fun`s. However, there might be a case where the user doesn't want this beta reduction to happen to their own arguments. Maybe a way to only beta-reduce certain arguments?
        let filledMap := Std.HashMap.ofList (blankMap.values.zip filledBlanks)

        let mut result := ""
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
                | some str => result := result ++ " " ++ str
                | none => throwError m!"Internal error: no filled string for blank {raw.toName}"
              | _ => throwError m!"Unable to turn pattern into string: {args}"
            | `stx.pseudo.antiquot =>
              match args.toList with
              | _ :: _ :: (.ident _ raw _ _ ) :: _ => -- If this part of the pattern is an identifier variable, find the corresponding identifier's name
                -- logInfo m!"{pat_expr} {e} {raw.toName}"
                let binderName ← findTargetBinderName pat_expr e raw.toName
                result := result ++ " " ++ (if binderName.isAnonymous then "x" else binderName.toString)
              | _ => throwError m!"Unsupported antiquot args: {args}"
            | _ => throwError m!"Unsupported syntax node kind: {k}"
          | x => throwError m!"Unsupported syntax part: {x.printdbg}"
        return result.trim

  throwError m!"No matching pattern found for expression {e}"

def toExternal (cat : Name) (e : Expr) : TermElabM String := do
  let patterns ← liftCommandElabM <| getExternalEquivalencesForCategory cat
  let p1 :: _ := patterns.toList | throwError m!"No external equivalences found for category '{cat}'"
  unless p1.isInjective do
    throwError m!"Translation to external syntax failed: external equivalence for category '{cat}' is not injective, cannot translate from Lean expression to external syntax"

  translateExpr cat patterns e
