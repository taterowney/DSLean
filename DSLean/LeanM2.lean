/- The `lean_m2` tactic, for proving ideal membership in a wide variety of rings -/
import DSLean.Command
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Congruence.Defs
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Use

open Lean Meta Elab Term Command Tactic

-- M2 string → Lean Expr (surjective, for parsing M2 coefficient output back to Lean)
external M2_in where
  x "+" y   ==> x + y   ; (precedence := 0)
  x "-" y   ==> x - y   ; (precedence := 0)
  x "*" y   ==> x * y   ; (precedence := 1)
  x "/" y   ==> x / y   ; (precedence := 1)
  x "^" y   ==> x ^ y   ; (precedence := 2)
  "-" x     ==> - x
  "(" x ")" ==> x
  "ii"       ==> Complex.I


-- Lean → M2 string (injective, for serializing polynomials to Macaulay2 syntax)
set_option linter.unusedVariables false
external M2_out where
  "(" x "+" y ")" <== x + y
  "(" x "-" y ")" <== x - y
  "(" x "*" y ")" <== x * y
  "(" x "/" y ")" <== x / y
  x "^" y <== x ^ y
  x "!" <== Nat.factorial x
  "-" x <== -(x : Int)
  "-" x <== -(x : ℝ)
  "-" x <== -(x : ℂ)

  -- Complex imaginary unit
  "ii" <== Complex.I

  -- Polynomial support
  "a0" <== Polynomial.X
  "(" x ")" <== Polynomial.C x

  ";" $x "=" y ";" rest <== let x := y; rest
  "ZZ" <== ℤ
  "QQ" <== ℚ
  "RR" <== ℝ
  "CC" <== ℂ
  R "/" x <== R ⧸ Ideal.span ({x} : Set R)

/- Because of Macaulay2's really weird output format, there's some manual parsing that needs to be done to make it look anything like a reasonable grammar -/

/-- Extract the element and ideal set from a goal of the form `elem ∈ Ideal.span S`.
    Returns `(ringType, setExpr, elemExpr)`. -/
def getMem (goal : Expr) : MetaM (Expr × Expr × Expr) := do
  -- Don't whnf the whole goal — that unfolds ∈ through SetLike and loses Membership.mem
  let goal ← instantiateMVars goal
  match goal.getAppFn.constName? with
  | some ``Membership.mem =>
    let args := goal.getAppArgs
    if args.size < 5 then throwError "getMem: unexpected number of arguments to Membership.mem ({args.size})"
    let ringType := args[0]!
    let idealSpan := args[3]!
    let elem := args[4]!
    match idealSpan.getAppFn.constName? with
    | some ``Ideal.span =>
      -- @Ideal.span R inst S
      let setExpr := idealSpan.appArg!
      return (ringType, setExpr, elem)
    | some ``Submodule.span =>
      -- @Submodule.span R _ inst S
      let setExpr := idealSpan.appArg!
      return (ringType, setExpr, elem)
    | _ => throwError m!"getMem: expected Ideal.span or Submodule.span, got {idealSpan}"
  | _ => throwError m!"getMem: expected membership goal (elem ∈ Ideal.span S), got head: {goal.getAppFn}"

/-- Extract generators from a set expression like `insert x (insert y (insert z ∅))`.
    Returns the list of generator expressions. -/
partial def parseExprIdealSpan (setExpr : Expr) : MetaM (List Expr) := do
  -- Don't use whnf — it unfolds set notation into predicates
  let setExpr ← instantiateMVars setExpr
  match setExpr.getAppFn.constName? with
  | some ``Insert.insert =>
    let args := setExpr.getAppArgs
    if args.size < 5 then throwError "parseExprIdealSpan: unexpected Insert.insert args"
    let x := args[3]!
    let rest := args[4]!
    let restGens ← parseExprIdealSpan rest
    return x :: restGens
  | some ``Set.insert =>
    let args := setExpr.getAppArgs
    if args.size < 3 then throwError "parseExprIdealSpan: unexpected Set.insert args"
    let x := args[1]!
    let rest := args[2]!
    let restGens ← parseExprIdealSpan rest
    return x :: restGens
  | some ``Singleton.singleton =>
    let args := setExpr.getAppArgs
    if args.size < 4 then throwError "parseExprIdealSpan: unexpected Singleton.singleton args"
    return [args[3]!]
  | some ``Set.singleton =>
    let args := setExpr.getAppArgs
    if args.size < 2 then throwError "parseExprIdealSpan: unexpected Set.singleton args"
    return [args[1]!]
  | some ``EmptyCollection.emptyCollection => return []
  | some ``Bot.bot => return []
  | _ =>
    throwError m!"parseExprIdealSpan: unsupported set expression (head: {setExpr.getAppFn})"

/-- Collect all unique free variables from a list of expressions,
    returning pairs of (original name, M2 name). -/
def collectAtomNames (exprs : List Expr) : MetaM (List (String × String)) := do
  let mut seen : Std.HashSet FVarId := {}
  let mut pairs : Array (String × String) := #[]
  for e in exprs do
    for fid in (← e.collectFVars.run {}).2.fvarIds do
      unless seen.contains fid do
        seen := seen.insert fid
        pairs := pairs.push ((← fid.getUserName).toString, s!"x{pairs.size}")
  return pairs.toList

/-- Information about a ring type for M2 script generation. -/
structure RingInfo where
  coeffRepr : String                    -- base coefficient ring ("ZZ", "QQ", "RR", "CC", "ZZ/p")
  quotientVars : List String := []      -- extra vars from polynomial indeterminates (e.g., ["a0"])
  quotientIdeal : Option String := none -- quotient ideal (e.g., "ideal(a0^2)")
  isComplex : Bool := false             -- whether to use Complex.I simp lemmas in proof closure
  -- useNatLiterals : Bool := false        -- use M2_in_nat (Nat exponents) instead of M2_in (Int exponents)

/-- Extract a Nat literal from an Expr (handles raw literals and OfNat). -/
private partial def getNatLit? (e : Expr) : Option Nat :=
  match e with
  | .lit (.natVal n) => some n
  | .app (.const ``Nat.succ _) inner => (getNatLit? inner).map (· + 1)
  | _ =>
    -- Handle @OfNat.ofNat Nat n inst
    if e.isAppOf ``OfNat.ofNat then
      let args := e.getAppArgs
      if args.size >= 2 then getNatLit? args[1]! else none
    else none

/-- Map a Lean type expression to its Macaulay2 ring information.
    Checks structure before whnf to avoid losing type information (e.g., ZMod reducing to Fin). -/
partial def getRingInfo (ringType : Expr) : Lean.Elab.Term.TermElabM RingInfo := do
  let rt ← instantiateMVars ringType
  -- Check structure before whnf
  match rt.getAppFn.constName? with
  | some ``ZMod =>
    let args := rt.getAppArgs
    if args.size < 1 then throwError "getRingInfo: ZMod missing argument"
    match getNatLit? args[0]! with
    | some p => return { coeffRepr := s!"ZZ/{p}" }
    | none => throwError m!"getRingInfo: ZMod argument is not a Nat literal: {args[0]!}"
  | some ``Complex => return { coeffRepr := "CC", isComplex := true }
  | some ``Polynomial =>
    let args := rt.getAppArgs
    if args.size < 1 then throwError "getRingInfo: Polynomial missing argument"
    let baseInfo ← getRingInfo args[0]!
    return { coeffRepr := baseInfo.coeffRepr, isComplex := baseInfo.isComplex}
  | some ``HasQuotient.Quotient =>
    -- R ⧸ I desugars to @HasQuotient.Quotient R (Ideal R) inst I
    let args := rt.getAppArgs
    if args.size < 4 then throwError m!"getRingInfo: HasQuotient.Quotient has {args.size} args, expected ≥ 4"
    let baseRingType := args[0]!
    let idealExpr := args[3]!
    let baseInfo ← getRingInfo baseRingType
    let generators ← parseExprIdealSpan (idealExpr.appArg!)
    let genStrs ← generators.mapM (toExternal' `M2_out)
    let genList := ", ".intercalate genStrs
    let isPoly := (← instantiateMVars baseRingType).getAppFn.constName? == some ``Polynomial
    return { coeffRepr := baseInfo.coeffRepr, isComplex := baseInfo.isComplex,
             quotientVars := if isPoly then ["a0"] else [],
             quotientIdeal := some s!"ideal({genList})" }
  | _ =>
    -- Fall back to whnf for simple types
    let rtw ← whnf rt
    let name? := rtw.constName? <|> rtw.getAppFn.constName?
    match name? with
    | some ``Int => return { coeffRepr := "ZZ" }
    | some ``Rat => return { coeffRepr := "QQ" }
    | some ``Real => return { coeffRepr := "RR" }
    | some ``Complex => return { coeffRepr := "CC", isComplex := true }
    | _ => throwError m!"getRingInfo: unsupported ring type {ringType} (whnf: {rtw})"

/-- Replace fvar user-names with M2 variable names in a translated string. -/
def replaceVarsInM2String (s : String) (atomMap : List (String × String)) : String :=
  atomMap.foldl (fun acc (origName, m2Name) => acc.replace origName m2Name) s

/-- Replace M2 variable names back with fvar user-names. Replaces longer names first. -/
def replaceVarsBackFromM2 (s : String) (atomNamePairs : List (String × String)) : String :=
  let sorted := atomNamePairs.toArray.qsort (fun (_, m2a) (_, m2b) => m2a.length > m2b.length)
  sorted.foldl (fun acc (origName, m2Name) => acc.replace m2Name origName) s

/-- Build the M2 script string for ideal membership checking. -/
def buildM2Script (info : RingInfo) (atomNames : List String) (elemStr : String) (genStrs : List String) : String :=
  let allVars := info.quotientVars ++ atomNames
  let varList := String.intercalate ", " allVars
  let genList := String.intercalate ", " genStrs
  let lb := "{"  -- M2 brace
  let rb := "}"
  -- Ring declaration with optional quotient ideal
  let ringDecl := s!"R = {info.coeffRepr}[{varList}]"
  let ringDecl := match info.quotientIdeal with
    | some qi => ringDecl ++ " / " ++ qi
    | none => ringDecl
  -- Strategy: compute GB with change matrix, then express f in terms of original generators
  -- CM satisfies: gens I * CM = gens GB, so coeffs_orig = CM * (f // gens GB)
  let lines := [
    ringDecl,
    "I = ideal(" ++ genList ++ ")",
    "Gfull = gb(I, ChangeMatrix=>true)",
    "fMat = matrix" ++ lb ++ lb ++ elemStr ++ rb ++ rb,
    "print(toString((fMat % gens Gfull)_(0,0)))",
    "coeffVec = (getChangeMatrix Gfull) * (fMat // gens Gfull)",
    "scan(numrows coeffVec, i -> print(toString(coeffVec_(i,0))))"
  ]
  String.intercalate "\n" lines ++ "\n"

/-- Parse M2 stdout from `--script` mode with `print(toString(...))` statements.
    First line: remainder (should be "0")
    Remaining lines: one coefficient per line (plain expressions with explicit `*`). -/
def parseM2Output (stdout : String) (numGens : Nat) : MetaM (Bool × List String) := do
  let lines := stdout.splitOn "\n"
    |>.map (fun s => s.trimAscii.toString)
    |>.filter (· ≠ "")
    |>.filter (fun s => !(s.startsWith "--"))
  match lines with
  | [] => throwError "lean_m2: no output from Macaulay2"
  | remLine :: coeffLines =>
    unless remLine == "0" do
      throwError m!"lean_m2: Macaulay2 reports nonzero remainder ({remLine}) — element is not in the ideal"
    if coeffLines.length != numGens then
      throwError m!"lean_m2: expected {numGens} coefficients from M2, got {coeffLines.length}. Raw output:\n{stdout}"
    return (true, coeffLines)

/-- Call Macaulay2 with the given script and return stdout. -/
def callM2 (script : String) : MetaM String := do
  let m2Path := (← IO.getEnv "DSLEAN_M2_PATH").getD "M2"-- "M2"
  IO.FS.withTempFile fun _handle path => do
    IO.FS.writeFile path script
    let result ← IO.Process.output {
      cmd := m2Path, args := #["--script", path.toString]
    }
    if result.exitCode != 0 then
      throwError m!"lean_m2: Macaulay2 exited with code {result.exitCode}.\nstderr: {result.stderr}\nstdout: {result.stdout}"
    return result.stdout

/-- The `lean_m2` tactic: proves ideal membership goals by calling Macaulay2 for
    Gröbner basis computation and constructing a kernel-verified proof via `ring`. -/
elab "lean_m2" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← getMainGoal
    let goalType ← instantiateMVars (← goal.getType)

    -- Step 1: Extract goal structure
    let (ringType, setExpr, elem) ← getMem goalType
    let generators ← parseExprIdealSpan setExpr

    if generators.isEmpty then
      throwError "lean_m2: no generators found in ideal"

    -- Step 2: Collect atoms (fvars) and build name map
    let atomNamePairs ← collectAtomNames (elem :: generators)
    let atomM2Names := atomNamePairs.map (·.2)

    -- Step 3: Detect ring type
    let ringInfo ← getRingInfo ringType

    -- Step 4: Translate elem and generators to M2 strings
    let elemStr ← toExternal' `M2_out elem
    let elemM2 := replaceVarsInM2String elemStr atomNamePairs

    let genM2Strs ← generators.mapM fun gen => do
      return replaceVarsInM2String (← toExternal' `M2_out gen) atomNamePairs

    -- Step 5: Build M2 script
    let script := buildM2Script ringInfo atomM2Names elemM2 genM2Strs

    -- Step 6: Call M2
    let stdout ← callM2 script

    -- Step 7: Parse M2 output
    let (_, coeffStrs) ← parseM2Output stdout generators.length
    -- Step 8: Parse coefficient strings back to Lean expressions via M2_in
    let coeffTerms ← coeffStrs.toArray.mapM fun coeffStr => do
      let coeffWithNames := replaceVarsBackFromM2 coeffStr atomNamePairs
      let coeffExpr ← fromExternal' `M2_in coeffWithNames
      synthesizeSyntheticMVarsNoPostponing
      PrettyPrinter.delab (← instantiateMVars coeffExpr)

    -- Step 9: Construct proof
    -- Simplify the goal using ideal membership lemmas
    let spanInsert := mkIdent ``Ideal.mem_span_insert'
    let spanSingleton := mkIdent ``Ideal.mem_span_singleton'
    evalTactic (← `(tactic|
      simp only [$spanInsert:ident, $spanSingleton:ident]))

    -- Use each coefficient. mem_span_insert' gives ∃ a, x + a*y ∈ span s,
    -- so the insert coefficients need to be negated (a = -c).
    -- The last coefficient (for mem_span_singleton': ∃ a, a*y = x) is used directly.
    for i in List.range coeffTerms.size do
      let coeffTerm := coeffTerms[i]!
      let term ← if i < coeffTerms.size - 1 then `(- $coeffTerm) else pure coeffTerm
      Mathlib.Tactic.runUse false (← Mathlib.Tactic.mkUseDischarger none) [term]

    evalTactic (← `(tactic| ring))
    let gs ← getGoals
    if !gs.isEmpty then
      evalTactic (← `(tactic| aesop))
