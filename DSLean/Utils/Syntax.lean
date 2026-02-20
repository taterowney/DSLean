import Lean


open Lean Meta Elab Term Tactic Expr Lean.Meta.Tactic.TryThis



/-- Loop through a Syntax object and replace unknown identifiers with holes (elaborated to synthetic mvars). Returns a list of the names of the replaced identifiers. -/
partial def collectAndReplaceUnknownIdents (stx : Syntax) : TermElabM (Syntax × List Name) := do
  if stx.isIdent then
    let tryResolve : TermElabM Syntax := do
      let res ← Term.resolveId? stx
      if (!res.isSome) then
        throwError "Unresolved identifier"
      pure stx
    try
      return ⟨(← tryResolve), []⟩
    catch _ =>
      return (Lean.mkHole stx, [stx.getId])
  let mut out := stx
  let mut names : List Name := []
  for (c, i) in List.zipIdx <| stx.getArgs.toList do
    let (c', newNames) ← collectAndReplaceUnknownIdents c
    out := out.setArg i c'
    names := names ++ newNames
  return (out, names)


/-- Elaborate `stx` in the current `MVarContext`. If given, the `expectedType` will be used to help
elaboration and then a `TypeMismatchError` will be thrown if the elaborated type doesn't match.  -/
def TermElabM.elabTermEnsuringType (stx : Syntax) (expectedType? : Option Expr) (mayPostpone := false) : TermElabM Expr := do
  let e ← Lean.Elab.Term.elabTerm stx expectedType? mayPostpone
  -- We do use `Term.ensureExpectedType` because we don't want coercions being inserted here.
  match expectedType? with
  | none => return e
  | some expectedType =>
    let eType ← inferType e
    -- We allow synthetic opaque metavars to be assigned in the following step since the `isDefEq` is not really
    -- part of the elaboration, but part of the tactic. See issue #492
    unless (← withAssignableSyntheticOpaque <| isDefEq eType expectedType) do
      Term.throwTypeMismatchError none expectedType eType e
    return e

/--
Execute `k`, and collect new "holes" in the resulting expression.

* `parentTag` and `tagSuffix` are used to tag untagged goals with `Lean.Elab.Tactic.tagUntaggedGoals`.
* If `allowNaturalHoles` is true, then `_`'s are allowed and create new goals.
-/
def TermElabM.withCollectingNewGoalsFrom (k : TermElabM Expr) (_ : Name) (_ : Name) (allowNaturalHoles := false) : TermElabM (Expr × List MVarId) :=
  /-
  When `allowNaturalHoles = true`, unassigned holes should become new metavariables, including `_`s.
  Thus, we set `holesAsSyntheticOpaque` to true if it is not already set to `true`.
  See issue #1681. We have the tactic
  ```
  `refine' (fun x => _)
  ```
  If we create a natural metavariable `?m` for `_` with type `Nat`, then when we try to abstract `x`,
  a new metavariable `?n` with type `Nat -> Nat` is created, and we assign `?m := ?n x`,
  and the resulting term is `fun x => ?n x`. Then, `getMVarsNoDelayed` would return `?n` as a new goal
  which would be confusing since it has type `Nat -> Nat`.
  -/
  if allowNaturalHoles then
    withTheReader Term.Context (fun ctx => { ctx with holesAsSyntheticOpaque := ctx.holesAsSyntheticOpaque || allowNaturalHoles }) do
      /-
      We also enable the assignment of synthetic metavariables, otherwise we will fail to
      elaborate terms such as `f _ x` where `f : (α : Type) → α → α` and `x : A`.

      IMPORTANT: This is not a perfect solution. For example, `isDefEq` will be able assign metavariables associated with `by ...`.
      This should not be an immediate problem since this feature is only used to implement `refine'`. If it becomes
      an issue in practice, we should add a new kind of opaque metavariable for `refine'`, and mark the holes created using `_`
      with it, and have a flag that allows us to assign this kind of metavariable, but prevents us from assigning metavariables
      created by the `by ...` notation.
      -/
      withAssignableSyntheticOpaque go
  else
    go
where
  go := do
    let mvarCounterSaved := (← getMCtx).mvarCounter
    let val ← k
    let newMVarIds ← getMVarsNoDelayed val
    /- ignore let-rec auxiliary variables, they are synthesized automatically later -/
    let newMVarIds ← newMVarIds.filterM fun mvarId => return !(← Term.isLetRecAuxMVar mvarId)
    /- Filter out all mvars that were created prior to `k`. -/
    let newMVarIds ← filterOldMVars newMVarIds mvarCounterSaved
    /- If `allowNaturalHoles := false`, all natural mvarIds must be assigned.
    Passing this guard ensures that `newMVarIds` does not contain unassigned natural mvars. -/
    unless allowNaturalHoles do
      let _ ← newMVarIds.filterM fun mvarId => return (← mvarId.getKind).isNatural
      -- logUnassignedAndAbort naturalMVarIds
    /-
    We sort the new metavariable ids by index to ensure the new goals are ordered using the order the metavariables have been created.
    See issue #1682.
    Potential problem: if elaboration of subterms is delayed the order the new metavariables are created may not match the order they
    appear in the `.lean` file. We should tell users to prefer tagged goals.
    -/
    let newMVarIds ← sortMVarIdsByIndex newMVarIds
    -- tagUntaggedGoals parentTag tagSuffix newMVarIds
    return (val, newMVarIds.toList)


def elabTermWithHoles (stx : Syntax) (expectedType? : Option Expr) (tagSuffix : Name) (allowNaturalHoles := false) : TermElabM (Expr × List MVarId) := do
  TermElabM.withCollectingNewGoalsFrom (TermElabM.elabTermEnsuringType stx expectedType?) (`anonymous) tagSuffix allowNaturalHoles


/-- Elaborate `stx` and classify metavariables:
* `holes` are the mvars created directly from `_` / `?m` holes
* `synth` are synthetic (typeclass/coercion/tactic/postponed) mvars
* `natural` are remaining “natural” mvars -/
def classifyMVars (stx : Syntax) (expected? : Option Expr := none)
    : TermElabM (Expr × Array MVarId × Array (MVarId × Option Term.SyntheticMVarKind) × Array MVarId) := do
  -- tagSuffix is used to tag unnamed goal mvars; allow natural `_` holes
  let tag := Name.str .anonymous "user_hole"
  let (e, holeMVars) ← elabTermWithHoles stx expected? tag (allowNaturalHoles := true)

  -- collect *all* mvars that still occur in the term
  let all ← Meta.getMVars e

  -- fast set for membership
  let holeSet := holeMVars.foldl (init := ({} : Std.HashSet MVarId)) (·.insert ·)

  -- partition the rest using SyntheticMVarDecl (TC/coercion/tactic/postponed info)
  let mut synth : Array (MVarId × Option Term.SyntheticMVarKind) := #[]
  let mut natural : Array MVarId := #[]
  for m in all do
    if holeSet.contains m then
      continue
    else
      match (← Term.getSyntheticMVarDecl? m) with
      | some d => synth := synth.push (m, some d.kind)
      | none   =>
        -- if it was created as a synthetic-opaque goal (?m / tactic goal) we still mark it "synth"
        match (← m.getKind) with
        | MetavarKind.syntheticOpaque => synth := synth.push (m, none)
        | _                           => natural := natural.push m
  pure (e, holeMVars.toArray, synth, natural)



partial def Lean.Syntax.printdbg (stx : Syntax) : String :=
  match stx with
  | .ident _ name _ _ => s!"(mkIdent `{name})"
  | .atom _ val => s!"(Lean.Syntax.atom default \"{val.replace "\"" "\\\""}\")"
  | .node _ k args =>
    let argsStr := args.map (fun a => printdbg a) |>.toList
    s!"(Lean.Syntax.node default `{k} #{argsStr})"
  | .missing => "Missing"




partial def Syntax.findAndReplaceM {m : Type → Type} [Monad m] (fn : Syntax → m (Option (Syntax × List Name))) : Syntax → m (Syntax × List Name)
  | stx@(Lean.Syntax.node info kind args) => do
    match (← fn stx) with
    | some stx => return stx
    | none     =>
        let (args, names) := (← args.mapM (Syntax.findAndReplaceM fn)).unzip
        return (Lean.Syntax.node info kind args, names.toList.flatten)
  | stx => do
    let o ← fn stx
    return o.getD (stx, [])
def TSyntax.findAndReplaceM {k : Name} {m : Type → Type} [Monad m] (fn : Syntax → m (Option (Syntax × List Name))) (stx : TSyntax k) : m (TSyntax k × List Name) :=
  do
    let (stx, names) ← Syntax.findAndReplaceM fn stx.1
    return (TSyntax.mk stx, names)
