import Lean
import Qq.Macro
import DSLean.Utils.Syntax

open Lean Elab Meta Term Expr
open Qq


structure EagerExprPattern where
  expr : AbstractMVarsResult
  vars : Array Name
  varMap : Std.HashMap MVarId Name
  binderVars : Array Name
deriving Inhabited

inductive ExprPattern where
  | eager (pat : EagerExprPattern)
  | postponed (stx : Syntax)
deriving Inhabited

def ExprPattern.getVars (self : ExprPattern) : Array Name :=
  match self with
  | .eager p => p.vars
  | .postponed _ => #[]
def ExprPattern.getBinderVars (self : ExprPattern) : Array Name :=
  match self with
  | .eager p => p.binderVars
  | .postponed _ => #[]

/-- Determines if a metavariable represents a blank to be filled by other patterns, or just inferred. TODO: distinction between blanks in different ExprPatterns -/
def EagerExprPattern.isBlank (self : EagerExprPattern) (mvars : Array Expr) (e : Expr) : TermElabM (Option Name) := do
  match e with
  | .mvar id =>
    let some idx := mvars.findIdx? (fun mv => mv.mvarId! == id) | throwError "Internal assertion failed in `isBlank`: mvar not found in pattern's mvar list"
    let some oldId := self.expr.mvars[idx]? | throwError "Internal assertion failed in `isBlank`: mvar id not found in abstracted mvar list"
    return self.varMap.get? oldId.mvarId!
  | _ => return none

/-- Determines if a metavariable represents a blank to be filled by other patterns, or just inferred. TODO: distinction between blanks in different ExprPatterns -/
def ExprPattern.isBlank (self : ExprPattern) (mvars : Array Expr) (e : Expr) : TermElabM (Option Name) := do
  match self with
    | .eager p => p.isBlank mvars e
    | .postponed _ => return none

/-- Elaborates to a hole that's type-independent of binders around it, with the specified name. -/
syntax (name := blankStx) "_blank" ident : term
@[term_elab blankStx]
def elabBlankStx : TermElab := fun stx expectedType? => do
  withLCtx {} {} do
    let t ← match expectedType? with
    | some typ => pure typ
    | none => mkFreshTypeMVar
    mkFreshExprSyntheticOpaqueMVar t (tag := stx.getArgs[1]!.getId)

def mkBlankId (userName : Name) := mkIdent (`_blankName ++ userName)


def isPostponeException? (ex : Exception) : Bool :=
  match ex with
  | Exception.internal id .. => id == postponeExceptionId
  | _ => false

/-- TODO: just catch exception within toPattern -/
private inductive repeatReplaceIdentsOutput where
  | eager (e : Expr × List Name)
  | postponed (stx : Syntax)


/-- A somewhat suspicious way of finding unbound identifiers, replacing them with holes, and returning their names, while leaving binders and bound variables in place. Expressions that need to be postponed don't go through this process; instead it just gives back their syntax. Adapted from `Lean.Elab.Term.withAutoBoundImplicit`. -/
partial def repeatReplaceIdents (stx : Syntax) (expectedType? : Option Expr) : TermElabM (repeatReplaceIdentsOutput) := do
  let initCtx : AutoBoundImplicitContext := .mk true {}
  withReader (fun ctx => { ctx with autoBoundImplicitContext := .some initCtx }) do
    let rec loop (s : Lean.Elab.Term.SavedState) (stx : Syntax) (expectedType? : Option Expr) : TermElabM (repeatReplaceIdentsOutput) := withIncRecDepth do
      checkSystem "auto-implicit"
      try
        -- let e ← elabTerm stx expectedType?
        let ⟨e, _, _, _⟩ ← classifyMVars stx expectedType? -- I don't understand why, but this has slightly better behavior with regards to natural vs synthetic mvars than the normal `elabTerm`
        return .eager (e, [])
      catch
        | ex => match isAutoBoundImplicitLocalException? ex with
          | some n =>
            -- Restore state, declare `n`, and try again
            s.restore (restoreInfo := true)
            let out : TermElabM (Syntax × List Name) := Syntax.findAndReplaceM (fun stx => do
              match stx with
              | Lean.Syntax.ident _ val name _ =>
                if name == n then
                  let asIdent := mkBlankId val.toName
                  return some (← `( _blank $asIdent ), [val.toName])
                else
                  return none
              | _ => pure none
            ) stx
            let (stx', newNames) ← out

            let userName ←  match newNames with
              | name :: _ => pure name
              | _ => throwError m!"Internal error in `repeatReplaceIdents`: expected at least one name from findAndReplaceM"

            -- let ⟨e, names⟩ ← loop (← saveState) stx' expectedType?
            -- return (e, userName :: names)
            match (← loop (← saveState) stx' expectedType?) with
            | .eager (e, names) => return .eager (e, userName :: names)
            | .postponed stx' => return .postponed stx'

          | none   =>
            match isPostponeException? ex with
            | true => return .postponed stx
            | false => throw ex
    loop (← saveState) stx expectedType?


private partial def getMVar : MVarId → TermElabM (List MVarId) := fun id => do
     return [id] ++ (← match (← id.getType) with
      | Expr.mvar id' => getMVar id'
      | _             => pure [])
def getAllMVarIds (e : Expr) : TermElabM (List MVarId) := do
  (← getMVars e).foldlM (fun acc id => do return acc ++ (← getMVar id)) []

/-- Given an Expr, find all named `syntheticOpaque` `mvar`s (including those in types, etc.), and return a mapping from their `MVarId`s to their names. -/
def pairMVarNames (e : Expr) : TermElabM (Std.HashMap MVarId Name) := do
  let allMVars ← getAllMVarIds e
  let mvars ← allMVars.filterMapM (fun id => do
    match ← id.getKind with
      | .syntheticOpaque =>
        let tag ← id.getTag
        if (`_blankName).isPrefixOf tag then
          pure (some (id, tag.updatePrefix .anonymous))
        else pure none
      | _ => pure none
    )
  return Std.HashMap.ofList mvars

/-- Checks that variables on the left and righthand sides of the patterns match -/
def checkVars (e : Expr) (varNames : Array Name) (pat_varNames : Array Name) (binderVarNames : Array Name) (checkInjective? : Bool := true) (checkSurjective? : Bool := true) : TermElabM Unit := do
  let rec collectBinderNames (e : Expr) : TermElabM (Array Name) :=
    match e with
    | .lam n t b _ => do
      let rest ← collectBinderNames b
      let rest := rest ++ (← collectBinderNames t)
      return rest.push n
    | .forallE n t b _ => do
      let rest ← collectBinderNames b
      let rest := rest ++ (← collectBinderNames t)
      return rest.push n
    | .letE n t v b _ => do
      let rest ← collectBinderNames b
      let rest := rest ++ (← collectBinderNames t)
      let rest := rest ++ (← collectBinderNames v)
      return rest.push n
    | .app f a => do
      let fNames ← collectBinderNames f
      let aNames ← collectBinderNames a
      return fNames ++ aNames
    | .proj _ _ s => collectBinderNames s
    | .mdata _ b => collectBinderNames b
    | _ => return #[]

  let pat_binderVarNames ← collectBinderNames e

  if checkSurjective? then
    for n in pat_varNames do
      unless varNames.contains n do
        throwError m!"Variables don't match. Got {varNames} on lefthand side and {pat_varNames} on righthand side."
    -- Don't need to check surjectivity for binder names, since there can be binders that aren't variables (in which case they just keep their original names)

  if checkInjective? then
    for n in varNames do
      unless pat_varNames.contains n do
        throwError m!"Variables don't match. Got {varNames} on lefthand side and {pat_varNames} on righthand side."
    for n in binderVarNames do
      unless pat_binderVarNames.contains n do
        throwError m!"Binders don't match. Got {binderVarNames} on lefthand side and {pat_binderVarNames} on righthand side."


/-- Converts a `Syntax` into an `ExprPattern`. Names of variable binder names are provided left to right through `binderVars`. -/
def Lean.Syntax.toPattern (stx : Syntax) (expectedType? : Option Expr) (varNames : Array Name) (binderVarNames : Array Name) (checkInjective? : Bool) (checkSurjective? : Bool) : TermElabM ExprPattern := do
  -- withoutModifyingElabMetaStateWithInfo do
  withoutModifyingStateWithInfoAndMessages do
  withTheReader Term.Context (fun ctx => { ctx with ignoreTCFailures := true }) <| do -- TODO: use inPattern? Does this help?

    match ← repeatReplaceIdents stx expectedType? with
    | .eager (e, pat_varNames) =>
      let paired ← pairMVarNames e

      unless pat_varNames.isPerm paired.values do
        throwError m!"Internal assertion failed in `toPattern`: variable names do not match replaced idents"

      checkVars e varNames pat_varNames.toArray binderVarNames checkInjective? checkSurjective?

      synthesizeSyntheticMVarsNoPostponing (ignoreStuckTC := true)
      return ExprPattern.eager <| EagerExprPattern.mk (← abstractMVars e) pat_varNames.toArray paired binderVarNames
    | .postponed stx =>
      try
        checkVars q(()) varNames #[] binderVarNames checkInjective? checkSurjective? -- just check that there are no variables to fill in
      catch e =>
        throwError m!"Couldn't infer contents of pattern (it was postponed), so variables cannot not be used."
      return ExprPattern.postponed stx

/-- Converts a `TSyntax` into an `ExprPattern`. Names of variable binder names are provided left to right through `binderVars`. -/
def Lean.TSyntax.toPattern {ks : Name} (stx : TSyntax ks) (expectedType? : Option Expr) (varNames : Array Name := #[]) (binderVarNames : Array Name := #[]) (checkInjective? : Bool) (checkSurjective? : Bool) : TermElabM ExprPattern := do
  stx.raw.toPattern expectedType? varNames binderVarNames checkInjective? checkSurjective?


def Lean.Expr.toPattern (e : Expr) (varNames : Array Name := #[]) (binderVarNames : Array Name := #[]) : TermElabM ExprPattern := do
  return ExprPattern.eager <| EagerExprPattern.mk (← abstractMVars e) varNames (← pairMVarNames e) binderVarNames


/-- Turn an `ExprPattern` into an `Expr` by filling in the blanks with the provided expressions. -/
partial def ExprPattern.unify (self : ExprPattern) (expectedType? : Option Expr) (blankContinuation : Name → Option Expr → TermElabM Expr) (identBlankContinuation : Name → TermElabM Name) : TermElabM Expr := do
  match self with
  | .eager p =>
    let (mvars, _, e) ← openAbstractMVarsResult p.expr
    let out ← go e mvars
    instantiateMVars out
  | .postponed stx =>
    let e ← elabTerm stx expectedType?
    instantiateMVars e
where
  go : Expr → Array Expr → TermElabM Expr := fun e mvars => do
    match e with
    | .mvar id =>
      match ← self.isBlank mvars e with
      | some name => do
        try
          let ty ← go (← id.getType) mvars
          let target ← blankContinuation name (some ty)

          id.setKind .natural -- isDefEq can't assign `syntheticOpaque`s

          let updatedLCtx ← getLCtx
          setMCtx <| (← getMCtx).modifyExprMVarLCtx id (fun _ => updatedLCtx) -- TODO: This is probably unsafe in some situations; however, I can't figure out a nice way around it without refactoring everything. The mvar in question must be able to depend on the (newly created) fvars for `isDefEq` to work unfortunately. We could fix this by postponing the creation of the abstracted mvars until after the corresponding binder is created.
          let ty := (← id.getDecl).type
          if ty.isMVar then
            setMCtx <| (← getMCtx).modifyExprMVarLCtx ty.mvarId! (fun _ => updatedLCtx) -- TODO: what if ty isn't an mvar but has mvars somewhere else?

          unless ← isDefEq e target do
            throwError m!"Type mismatch when filling in blank '{name}': expected to unify with {e}, got {target}; current vars are {self.getVars}"
        catch e =>
          throwError m!"Type mismatch when filling in blank '{name}': {e.toMessageData}"
      | _ => pure ()
      return e
    | .app f a =>
      let f' ← go f mvars
      let a' ← go a mvars
      return .app f' a'
    | .proj n i s =>
      let s' ← go s mvars
      return .proj n i s'
    | .lam n t b bi =>
      let binderName ← try let x ← identBlankContinuation n; pure x catch _ => pure n
      let binderType ← go t mvars
      let out ← withLocalDecl binderName bi binderType fun binderExpr => do
        instantiateMVars <| ← mkLambdaFVars #[binderExpr] (← go b mvars) (binderInfoForMVars := bi)
      return out
    | .forallE n t b bi => do
      let binderName ← try let x ← identBlankContinuation n; pure x catch _ => pure n
      let binderType ← go t mvars
      withLocalDecl binderName bi binderType fun binderExpr => do
        mkForallFVars #[binderExpr] (← go b mvars) (binderInfoForMVars := bi)
    | .letE n t v b nondep => do
      let binderName ← try let x ← identBlankContinuation n; pure x catch _ => pure n
      let binderType ← go t mvars
      let valueExpr ← go v mvars

      withLetDecl binderName binderType valueExpr fun binderExpr => do
        let body ← go b mvars
        let out ← mkLetFVars #[binderExpr] body nondep
        return out
    | .fvar id =>
      let name ← try let x ← identBlankContinuation id.name; pure x catch _ => pure id.name
      match (← getLCtx).findFromUserName? name with
      | some ldecl => return mkFVar ldecl.fvarId
      | none => throwError m!"Unknown identifier '{name}'"
    | _ => return e



def EagerExprPattern.unpackExpr (self : EagerExprPattern) : TermElabM (Array Expr × Array BinderInfo × Expr × (Std.HashMap MVarId Name)) := do
    let (all_mvars, bis, e) ← openAbstractMVarsResult self.expr
    let mvars ← (← getAllMVarIds e).filterMapM (fun id => do
      match ← self.isBlank all_mvars (Expr.mvar id) with
      | some name => pure (some (id, name))
      | none => pure none)
    return (all_mvars, bis, e, Std.HashMap.ofList mvars)
