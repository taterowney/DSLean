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
  let goal ← whnf goal
  match goal.getAppFn.constName? with
  | some ``Membership.mem =>
    let args := goal.getAppArgs
    if args.size < 5 then throwError "getMem: unexpected number of arguments to Membership.mem"
    let ringType := args[0]!
    let elem := args[3]!
    let idealSpan := args[4]!
    let idealSpan ← whnf idealSpan
    match idealSpan.getAppFn.constName? with
    | some ``Ideal.span =>
      let spanArgs := idealSpan.getAppArgs
      if spanArgs.size < 2 then throwError "getMem: unexpected number of arguments to Ideal.span"
      let setExpr := spanArgs[1]!
      return (ringType, setExpr, elem)
    | some ``Submodule.span =>
      let spanArgs := idealSpan.getAppArgs
      if spanArgs.size < 3 then throwError "getMem: unexpected number of arguments to Submodule.span"
      let setExpr := spanArgs[2]!
      return (ringType, setExpr, elem)
    | _ => throwError m!"getMem: expected Ideal.span or Submodule.span, got {idealSpan}"
  | _ => throwError "getMem: expected membership goal of the form (elem ∈ Ideal.span S)"

/-- Extract generators from a set expression like `insert x (insert y (insert z ∅))`.
    Returns the list of generator expressions. -/
partial def parseExprIdealSpan (setExpr : Expr) : MetaM (List Expr) := do
  let setExpr ← whnf setExpr
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

/-- Replace M2 variable names back with fvar user-names. Replaces longer names first. -/
def replaceVarsBackFromM2 (s : String) (atomMap : List (String × String)) : String :=
  let sorted := atomMap.toArray.qsort (fun (_, m2a) (_, m2b) => m2a.length > m2b.length)
  sorted.foldl (fun acc (origName, m2Name) => acc.replace m2Name origName) s

/-- Build the M2 script string for ideal membership checking. -/
def buildM2Script (ringRepr : String) (atomNames : List String) (elemStr : String) (genStrs : List String) : String :=
  let varList := String.intercalate ", " atomNames
  let genList := String.intercalate ", " genStrs
  let lines := [
    s!"R = {ringRepr}[{varList}]",
    s!"f = {elemStr}",
    s!"I = ideal({genList})",
    s!"G = gb(I, ChangeMatrix=>true)",
    s!"f % G",
    s!"(getChangeMatrix G) * (transpose gens gb I) * (f // gens gb I)"
  ]
  String.intercalate "\n" lines ++ "\n"

/-- Parse M2 stdout to extract the remainder and coefficient expressions. -/
def parseM2Output (stdout : String) (numGens : Nat) : MetaM (Bool × List String) := do
  let lines := stdout.splitOn "\n"
    |>.map (fun s => s.trimAscii.toString)
    |>.filter (· ≠ "")

  let mut remainderIsZero := false
  let mut coeffLine := ""
  let mut foundCoeffs := false

  for line in lines do
    if strContains line "= 0" && !foundCoeffs then
      if line.startsWith "o" then
        remainderIsZero := true
    if strContains line "|" && !foundCoeffs then
      coeffLine := line
      foundCoeffs := true
    else if foundCoeffs && strContains line "|" then
      coeffLine := coeffLine ++ " " ++ line

  unless remainderIsZero do
    throwError "lean_m2: Macaulay2 reports nonzero remainder — element is not in the ideal"

  let coeffPart := if strContains coeffLine "=" then
    (coeffLine.splitOn "=").getLast!.trimAscii.toString
  else
    coeffLine.trimAscii.toString

  let inner := (coeffPart.replace "|" "").trimAscii.toString

  let coeffs := if inner.isEmpty then []
    else inner.splitOn " " |>.filter (· ≠ "")

  if coeffs.length != numGens then
    let allParts := coeffPart.splitOn "|"
      |>.map (fun s => s.trimAscii.toString)
      |>.filter (· ≠ "")
    if allParts.length == numGens then
      return (remainderIsZero, allParts)
    else
      throwError m!"lean_m2: expected {numGens} coefficients from M2, got {coeffs.length}. Raw: {coeffLine}"

  return (remainderIsZero, coeffs)

/-- Call Macaulay2 with the given script and return stdout. -/
def callM2 (script : String) : MetaM String := do
  let m2Path := (← IO.getEnv "DSLEAN_M2_PATH").getD "M2"
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
      let coeffWithNames := replaceVarsBackFromM2 coeffStr atomNamePairs
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

    -- Use each coefficient
    for coeffTerm in coeffTerms do
      logInfo m!"lean_m2: using coefficient: {coeffTerm}"
      Mathlib.Tactic.runUse false (← Mathlib.Tactic.mkUseDischarger none) [coeffTerm]

    -- Close with ring
    evalTactic (← `(tactic| ring))
