import DSLean.Command
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.RingTheory.Congruence.Defs
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Use

-- Lean → M2 string (injective, for serializing polynomials to Macaulay2 syntax)
external M2_out where
  "(" x "+" y ")" <== x + y
  "(" x "-" y ")" <== x - y
  "(" x "*" y ")" <== x * y
  "(" x "/" y ")" <== x / y
  x "^" y <== x ^ y
  x "!" <== Nat.factorial x
  "-" x <== -(x : Int)

  ";" $x "=" y ";" rest <== let x := y; rest
  "ZZ" <== ℤ
  "QQ" <== ℚ
  R "/" x <== R ⧸ Ideal.span ({x} : Set R)

-- M2 string → Lean Expr (surjective, for parsing M2 coefficient output back to Lean)
external M2_in (numberCast := Int.ofNat) where
  x "+" y   ==> x + y   ; (precedence := 0)
  x "-" y   ==> x - y   ; (precedence := 0)
  x "*" y   ==> x * y   ; (precedence := 1)
  x "/" y   ==> x / y   ; (precedence := 1)
  x "^" y   ==> x ^ y   ; (precedence := 2)
  "-" x     ==> - x
  "(" x ")" ==> x

open Lean Meta Elab Term Command Tactic Qq in
#eval do
  logInfo m!"{← toExternal `M2_out (q(ℚ ⧸ Ideal.span (Set.singleton 5 : Set ℚ)))}"

open Lean Meta Elab Term Command Tactic

private def strContains (s : String) (sub : String) : Bool :=
  (s.splitOn sub).length > 1

/-- Extract the element and ideal set from a goal of the form `elem ∈ Ideal.span S`.
    Returns `(ringType, setExpr, elemExpr)`. -/
def getMem (goal : Expr) : MetaM (Expr × Expr × Expr) := do
  -- Don't whnf the whole goal — that unfolds ∈ through SetLike and loses Membership.mem
  let goal ← instantiateMVars goal
  match goal.getAppFn.constName? with
  | some ``Membership.mem =>
    -- @Membership.mem R (Ideal R) inst (Ideal.span S) elem
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

/-- Collect all unique free variables from a list of expressions. -/
def collectAtoms (exprs : List Expr) : MetaM (Array FVarId × Std.HashMap FVarId Nat) := do
  let mut seen : Std.HashMap FVarId Nat := {}
  let mut fvars : Array FVarId := #[]
  for e in exprs do
    let state := (← e.collectFVars.run {}).2
    for fid in state.fvarIds do
      unless seen.contains fid do
        seen := seen.insert fid fvars.size
        fvars := fvars.push fid
  return (fvars, seen)

/-- Map a Lean type expression to its Macaulay2 ring representation string. -/
def getRingRepr (ringType : Expr) : MetaM String := do
  let ringType ← whnf ringType
  match ringType.constName? with
  | some ``Int => return "ZZ"
  | some ``Rat => return "QQ"
  | _ =>
    match ringType.getAppFn.constName? with
    | some ``Int => return "ZZ"
    | some ``Rat => return "QQ"
    | _ => throwError m!"getRingRepr: unsupported ring type {ringType}"

/-- Replace fvar user-names with M2 variable names in a translated string. -/
def replaceVarsInM2String (s : String) (atomMap : List (String × String)) : String :=
  atomMap.foldl (fun acc (origName, m2Name) => acc.replace origName m2Name) s

/-- Insert explicit `*` between adjacent M2 variable names (e.g., "x0x1" → "x0*x1"),
    between a number and a variable (e.g., "3x0" → "3*x0"),
    and between a variable and a number. -/
def insertExplicitMul (s : String) (atomNames : List String) : String := Id.run do
  -- Sort by length descending to replace longer names first
  let sorted := atomNames.toArray.qsort (fun a b => a.length > b.length)
  -- First pass: replace each atom name with a tagged version
  let mut result := s
  for name in sorted do
    result := result.replace name s!"«{name}»"
  -- Now insert * between adjacent tagged names, or number«name» patterns
  -- Pattern: »« means two adjacent variables, digit« means number*var
  result := result.replace "»«" "»*«"
  -- Handle number followed by variable: e.g., "3«x0»" → "3*«x0»"
  let mut chars := result.toList
  let mut output : List Char := []
  for i in List.range chars.length do
    let c := chars[i]!
    if c == '«' && i > 0 then
      let prev := chars[i-1]!
      if prev.isDigit then
        output := output ++ ['*']
    output := output ++ [c]
  result := String.mk output
  -- Remove tags
  result := result.replace "«" "" |>.replace "»" ""
  result

/-- Replace M2 variable names back with fvar user-names. Replaces longer names first.
    Also inserts explicit `*` for M2's implicit multiplication. -/
def replaceVarsBackFromM2 (s : String) (atomNamePairs : List (String × String)) (atomM2Names : List String) : String :=
  -- First insert explicit multiplication between adjacent M2 var names
  let withMul := insertExplicitMul s atomM2Names
  -- Then replace M2 names with original names (longer first)
  let sorted := atomNamePairs.toArray.qsort (fun (_, m2a) (_, m2b) => m2a.length > m2b.length)
  sorted.foldl (fun acc (origName, m2Name) => acc.replace m2Name origName) withMul

/-- Build the M2 script string for ideal membership checking. -/
def buildM2Script (ringRepr : String) (atomNames : List String) (elemStr : String) (genStrs : List String) : String :=
  let varList := String.intercalate ", " atomNames
  let genList := String.intercalate ", " genStrs
  let lb := "{"  -- M2 brace
  let rb := "}"
  -- Strategy: compute GB with change matrix, then express f in terms of original generators
  -- CM satisfies: gens I * CM = gens GB, so coeffs_orig = CM * (f // gens GB)
  let lines := [
    "R = " ++ ringRepr ++ "[" ++ varList ++ "]",
    "I = ideal(" ++ genList ++ ")",
    "Gfull = gb(I, ChangeMatrix=>true)",
    "fMat = matrix" ++ lb ++ lb ++ elemStr ++ rb ++ rb,
    "print(fMat % gens Gfull)",
    "print((getChangeMatrix Gfull) * (fMat // gens Gfull))"
  ]
  String.intercalate "\n" lines ++ "\n"

/-- Parse M2 stdout from `--script` mode with `print` statements.
    First print: remainder (should be "0")
    Second print: column vector of coefficients, one per line as `{deg} | coeff |` -/
def parseM2Output (stdout : String) (numGens : Nat) : MetaM (Bool × List String) := do
  let lines := stdout.splitOn "\n"
    |>.map (fun s => s.trimAscii.toString)
    |>.filter (· ≠ "")

  -- First non-empty line should be the remainder
  match lines with
  | [] => throwError "lean_m2: no output from Macaulay2"
  | remLine :: coeffLines =>
    let remainderIsZero := remLine.trimAscii.toString == "0"
    unless remainderIsZero do
      throwError m!"lean_m2: Macaulay2 reports nonzero remainder ({remLine}) — element is not in the ideal"

    -- Parse coefficient lines: each looks like "{1} | coeff_expr |"
    -- or for a 1×1 matrix: "| coeff_expr |"
    let mut coeffs : List String := []
    for line in coeffLines do
      if strContains line "|" then
        -- Extract content between | delimiters
        let parts := line.splitOn "|" |>.map (fun s => s.trimAscii.toString) |>.filter (· ≠ "")
        -- The last non-empty part between |s is the coefficient
        -- For "{1} | coeff |", parts = ["{1}", "coeff"] or just ["coeff"]
        match parts.reverse with
        | coeff :: _ => coeffs := coeffs ++ [coeff]
        | [] => pure ()

    if coeffs.length != numGens then
      throwError m!"lean_m2: expected {numGens} coefficients from M2, got {coeffs.length}. Raw output:\n{stdout}"

    return (remainderIsZero, coeffs)

/-- Call Macaulay2 with the given script and return stdout. -/
def callM2 (script : String) : MetaM String := do
  let m2Path := (← IO.getEnv "DSLEAN_M2_PATH").getD "/Applications/Macaulay2-1.21/bin/M2"-- "M2"
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

    logInfo m!"lean_m2: ring type = {ringType}"
    logInfo m!"lean_m2: element = {elem}"
    logInfo m!"lean_m2: {generators.length} generators"

    -- Step 2: Collect atoms (fvars) and build name map
    let allExprs := elem :: generators
    let (atomFvars, atomIndexMap) ← collectAtoms allExprs

    let mut atomNamePairs : List (String × String) := []
    for fid in atomFvars do
      let userName := (← fid.getUserName).toString
      let idx := atomIndexMap.get! fid
      atomNamePairs := atomNamePairs ++ [(userName, s!"x{idx}")]

    let atomM2Names := atomFvars.zipIdx.toList.map (fun (_, i) => s!"x{i}")

    -- Step 3: Detect ring type
    let ringRepr ← getRingRepr ringType

    -- Step 4: Translate elem and generators to M2 strings
    let elemStr ← toExternal `M2_out elem
    let elemM2 := replaceVarsInM2String elemStr atomNamePairs

    let mut genM2Strs : List String := []
    for gen in generators do
      let genStr ← toExternal `M2_out gen
      let genM2 := replaceVarsInM2String genStr atomNamePairs
      genM2Strs := genM2Strs ++ [genM2]

    logInfo m!"lean_m2: M2 element = {elemM2}"
    logInfo m!"lean_m2: M2 generators = {genM2Strs}"

    -- Step 5: Build M2 script
    let script := buildM2Script ringRepr atomM2Names elemM2 genM2Strs

    logInfo m!"lean_m2: M2 script:\n{script}"

    -- Step 6: Call M2
    let stdout ← callM2 script

    logInfo m!"lean_m2: M2 output:\n{stdout}"

    -- Step 7: Parse M2 output
    let (_, coeffStrs) ← parseM2Output stdout generators.length

    logInfo m!"lean_m2: coefficients = {coeffStrs}"

    -- Step 8: Parse coefficient strings back to Lean expressions via M2_in
    let mut coeffTerms : Array (TSyntax `term) := #[]
    for coeffStr in coeffStrs do
      let coeffWithNames := replaceVarsBackFromM2 coeffStr atomNamePairs atomM2Names
      logInfo m!"lean_m2: parsing coefficient: {coeffWithNames}"
      let coeffExpr ← fromExternal' `M2_in coeffWithNames
      let coeffTerm ← PrettyPrinter.delab coeffExpr
      coeffTerms := coeffTerms.push coeffTerm

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
      if i < coeffTerms.size - 1 then
        -- For mem_span_insert': negate the coefficient
        let negTerm ← `(- $coeffTerm)
        logInfo m!"lean_m2: using coefficient (negated for insert): {negTerm}"
        Mathlib.Tactic.runUse false (← Mathlib.Tactic.mkUseDischarger none) [negTerm]
      else
        -- For mem_span_singleton': use directly
        logInfo m!"lean_m2: using coefficient (singleton): {coeffTerm}"
        Mathlib.Tactic.runUse false (← Mathlib.Tactic.mkUseDischarger none) [coeffTerm]

    -- Close with ring (simp normalizes Int.ofNat zpow exponents from M2_in parsing)
    evalTactic (← `(tactic| simp only [Int.ofNat_eq_natCast, zpow_natCast]; ring))
