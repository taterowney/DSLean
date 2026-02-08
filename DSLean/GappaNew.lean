import DSLean.Command
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
set_option linter.unusedVariables false set_option linter.unusedTactic false set_option linter.unreachableTactic false

open Lean Meta Elab Term Command Tactic in
/-- Automatically unfolds all local let/have declarations -/
elab "unfold_local" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let localDecls ← (← getLCtx).getFVarIds.filterMapM (fun id => do
      if ← id.isLetVar then
        let name := (mkIdent (← id.getUserName))
        return some (← `(Lean.Parser.Tactic.simpLemma| $name:term))
      else return none )
    Lean.Elab.Tactic.evalTactic <| ← `(tactic| dsimp [$localDecls,*] at *)



injective external Gappa_input where
  "(" x "+" y ")" <== x + y
  "(" x "-" y ")" <== x - y
  "(" x "*" y ")" <== x * y
  "(" x "/" y ")" <== x / y
  "sqrt(" x ")" <== Real.sqrt x
  "-" x <== - (x:Real)

  "(" x "->" y ")" <== x → y
  "(" x "/\\" y ")" <== x ∧ y
  "(" x "\\/" y ")" <== x ∨ y
  "not" x <== ¬ x

  "[" x "," y "]" <== Set.Icc x y
  x "in" y <== x ∈ y
  x "=" y <== x = y

macro "gappa_auto" : tactic => `(tactic|
  first
    | aesop
    | (unfold_local <;> simp_all <;> try norm_num at * <;> try ring_nf at * <;> try linarith <;> try nlinarith <;> try aesop)
    | (constructor <;> (first | aesop | assumption | simp_all | norm_num at * | linarith | nlinarith))
    | assumption
    | simp_all
    | norm_num at *
    | linarith
    | nlinarith)

macro "constantBound" : tactic => `(tactic| unfold_local <;> norm_num <;> constructor <;> simp_all)
macro "sqrtG" : tactic => `(tactic| unfold_local <;> norm_num <;>
  constructor <;> apply (sq_le_sq₀ (by norm_num) (by norm_num)).mp
    <;> rw [Real.sq_sqrt (x := 2) (by norm_num)]
    <;> norm_num)
macro "mul_pp" : tactic => `(tactic| unfold_local <;> norm_num at * <;>
  constructor <;> apply (sq_le_sq₀ (by norm_num) (by norm_num)).mp
  <;> simp only [mul_pow, Real.sq_sqrt (x := 2) (by norm_num)]
  <;> norm_num)

open Lean Elab Tactic in
elab "treeSimplify" : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| try unfold_local))
  Lean.Elab.Tactic.evalTactic (← `(tactic| try simp_all))
  Lean.Elab.Tactic.evalTactic (← `(tactic| try (norm_num at *)))
  Lean.Elab.Tactic.evalTactic (← `(tactic| try exact (h1 h2)))
  Lean.Elab.Tactic.evalTactic (← `(tactic| try exact (h1 (by constructor <;> nlinarith [h2.1, h2.2]))))
  Lean.Elab.Tactic.evalTactic (← `(tactic| try exact (h1 (by constructor <;> linarith [h2.1, h2.2]))))
  Lean.Elab.Tactic.evalTactic (← `(tactic|
    try (
      have hf13 : f1 ≤ f3 := by norm_num [f1, f3]
      have hf42 : f4 ≤ f2 := by norm_num [f4, f2]
      exact h1 (by
        constructor
        · linarith [hf13, h2.1]
        · linarith [hf42, h2.2]))))
  Lean.Elab.Tactic.evalTactic (← `(tactic| try contradiction))
  Lean.Elab.Tactic.evalTactic (← `(tactic| try aesop))
  Lean.Elab.Tactic.evalTactic (← `(tactic| try linarith))
  Lean.Elab.Tactic.evalTactic (← `(tactic| try nlinarith))

surjective external Gappa_output (numberCast := Int.ofNat) where
  x "->" y   ==> x → y; +rightAssociative
  x "/\\" y  ==> x ∧ y
  x "\\/" y  ==> x ∨ y
  "not" x    ==> ¬ x
  "true"     ==> true
  "false"    ==> false
  "True"     ==> True
  "False"    ==> False
  "(" inside ")"                      ==> inside
  "let" $n ":=" val "in" rest         ==> let n := val; rest
  "let" $n ":" ty ":=" val "in" rest  ==> let n:ty := val; rest
  "let" $n "(" $arg ":" argTy ")" ":=" val "in" rest
                                      ==> let n := (fun arg:argTy => val); rest
  "let" $n "(" $arg ":" argTy ")" ":" retTy ":=" val "in" rest
                                      ==> let n : argTy → retTy := (fun arg:argTy => val); rest
  "let" $n "(" $arg1 ":" argTy1 ")" "(" $arg2 ":" argTy2 ")" ":" retTy ":=" val "in" rest
                                      ==> let n : argTy1 → argTy2 → retTy := (fun arg1:argTy1 => fun arg2:argTy2 => val); rest
  "fun" $n "=>" rest                  ==> fun n => rest
  "fun" "(" $n ":" ty ")" "=>" body   ==> fun n:ty => body
  "-" x  ==> - x
  "_"    ==> _
  x y ==> (id ∘ x) y; +rightAssociative

  "Reals.Rdefinitions.R"                    ==> ℝ
  "Gappa.Gappa_pred_bnd.Float1" x           ==> (IntCast.intCast x : Real)
  "Gappa.Gappa_definitions.Float2" x y      ==> (IntCast.intCast x : Real) * ((2:Real) ^ (y:Int))
  "Gappa.Gappa_definitions.makepairF" x y   ==> Set.Icc x y
  "Gappa.Gappa_definitions.BND" x y         ==> x ∈ y
  "Gappa.Gappa_definitions.ABS" x y         ==> (abs x) ∈ y
  "Reals.Rdefinitions.Rle" x y              ==> x ≤ y
  "Reals.Rdefinitions.Rplus" x y            ==> x + y
  "Reals.Rdefinitions.Rminus" x y           ==> x - y
  "Reals.Rdefinitions.Rmult" x y            ==> x * y
  "Reals.Rdefinitions.Rdiv" x y             ==> x / y
  "Reals.Rdefinitions.Ropp" x               ==> - (x:Real)
  "Reals.R_sqrt.sqrt" x                     ==> Real.sqrt x

  "Gappa.Gappa_pred_bnd.constant1" a b c            ==> by constantBound
  "Gappa.Gappa_tree.simplify" a                     ==> by treeSimplify
  "Gappa.Gappa_tree.simplify" a b c d e f g         ==> by treeSimplify
  "Gappa.Gappa_pred_bnd.sqrtG" a b c d e            ==> by sqrtG
  "Gappa.Gappa_pred_bnd.neg" a b c d e              ==> by constantBound
  "Gappa.Gappa_pred_bnd.add" a b c d e f g h        ==> by constantBound
  "Gappa.Gappa_pred_bnd.sub" a b c d e f g h        ==> by constantBound
  "Gappa.Gappa_pred_bnd.mul_pp" a b c d e f g h     ==> by mul_pp
  "Gappa.Gappa_pred_bnd.div_pp" a b c d e f g h     ==> by gappa_auto
  "Gappa.Gappa_pred_abs.abs_of_bnd_p" a b c d e     ==> by gappa_auto
  "Gappa.Gappa_pred_bnd.square" a b c d e           ==> by gappa_auto
  "Gappa.Gappa_pred_bnd.subset" a b c d e           ==> by gappa_auto
  "Gappa.Gappa_rewriting.add_xilu" a b c d          ==> by gappa_auto
  "Gappa.Gappa_pred_bnd.intersect_hb" a b c d e f g ==> by gappa_auto
  "Gappa.Gappa_pred_bnd.intersect_bh" a b c d e f g ==> by gappa_auto
  "Gappa.Gappa_pred_bnd.union" a b c d              ==> by gappa_auto

  "proj1" x  ==> And.left x
  "proj2" x  ==> And.right x

private def normalizeSimplifyLine (line : String) : String :=
  let key := "Gappa.Gappa_tree.simplify"
  if !(line.contains key) then
    line
  else
    (let pre := (line.splitOn key)[0]!;
    pre ++ key ++ " _ in")

partial def preprocess (s : String) : IO String := do
  let noComments := s.replace "(*" "/-" |>.replace "*)" "-/"
  let noNat := noComments.replace "%nat" ""
  let normalized := String.intercalate "\n" <| (noNat.splitOn "\n").map normalizeSimplifyLine
  return normalized

private def getEnvOrDefault (name defaultValue : String) : IO String := do
  match (← IO.getEnv name) with
  | some value =>
      if value.isEmpty then
        pure defaultValue
      else
        pure value
  | none => pure defaultValue

private def getGappaInputPath : IO System.FilePath := do
  let tmpDir ← getEnvOrDefault "DSLEAN_TMP_DIR" "/tmp/dslean"
  let tmpDirPath : System.FilePath := tmpDir
  IO.FS.createDirAll tmpDirPath
  pure <| tmpDirPath / "lean_test.g"

private def getGappaDebug : IO Bool := do
  let debug ← getEnvOrDefault "DSLEAN_GAPPA_DEBUG" "0"
  pure <| debug = "1" || debug = "true" || debug = "TRUE"

open Lean Meta Elab Term Command Tactic in
elab "gappa" : tactic => do
  let goal ← getMainGoal
  let typ ← instantiateMVars (← goal.getType)
  let formatted ← toExternal `Gappa_input typ
  let inputPath ← getGappaInputPath
  IO.FS.writeFile inputPath s!"\{{formatted}}"
  let gappaBin ← getEnvOrDefault "DSLEAN_GAPPA_BIN" "/usr/bin/gappa"
  let res ←
    try
      IO.Process.run {
        cmd := gappaBin,
        args := #["-Bcoq-lambda", inputPath.toString],
        stdin := .piped, stdout := .piped, stderr := .piped
      }
    catch _ =>
      throwError m!"gappa invocation failed (cmd: {gappaBin}, input: {inputPath}). Set DSLEAN_GAPPA_BIN and DSLEAN_TMP_DIR."
  if (← getGappaDebug) then
    logInfo m!"Raw Gappa output:\n{res}"
  let input ← preprocess res
  if (← getGappaDebug) then
    logInfo m!"Processed Gappa output:\n{input}"
  let proof ← processExternal `Gappa_output input
  let proof ← Meta.whnf proof

  let newhyp : Hypothesis := {
    userName := `h_gappa,
    type := ← Core.betaReduce (← Meta.whnf (← inferType proof)),
    value := proof
  }
  let ⟨ids, new⟩ ← goal.assertHypotheses #[newhyp]
  replaceMainGoal [new]

  Lean.Elab.Tactic.evalTactic (← `(tactic| norm_num at * ))
  Lean.Elab.Tactic.evalTactic (← `(tactic| try grind ))
