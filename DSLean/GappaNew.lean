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

macro "tac" : tactic => `(tactic| sorry)

macro "constantBound" : tactic => `(tactic| unfold_local <;> norm_num <;> constructor <;> simp_all)
macro "sqrtG" : tactic => `(tactic| unfold_local <;> norm_num <;>
  constructor <;> apply (sq_le_sq₀ (by norm_num) (by norm_num)).mp
    <;> rw [Real.sq_sqrt (x := 2) (by norm_num)]
    <;> norm_num)
macro "mul_pp" : tactic => `(tactic| unfold_local <;> norm_num at * <;>
  constructor <;> apply (sq_le_sq₀ (by norm_num) (by norm_num)).mp
  <;> simp only [mul_pow, Real.sq_sqrt (x := 2) (by norm_num)]
  <;> norm_num)

surjective external Gappa_output (numberCast := Int.ofNat) where
  x "->" y   ==> x → y; +rightAssociative
  x "/\\" y  ==> x ∧ y
  x "\\/" y  ==> x ∨ y
  "not" x    ==> ¬ x
  "True"     ==> True
  "False"    ==> False
  "(" inside ")"                      ==> inside
  "let" $n ":=" val "in" rest         ==> let n := val; rest
  "let" $n ":" ty ":=" val "in" rest  ==> let n:ty := val; rest
  "fun" $n "=>" rest                  ==> fun n => rest
  "fun" "(" $n ":" ty ")" "=>" body   ==> fun n:ty => body
  "-" x  ==> - x
  "_"    ==> _
  x y ==> (id ∘ x) y

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

  "Gappa.Gappa_pred_bnd.constant1" a b c          ==> by constantBound <;> sorry
  "Gappa.Gappa_tree.simplify" a                   ==> by tac
  "Gappa.Gappa_pred_bnd.sqrtG" a b c d e          ==> by tac
  "Gappa.Gappa_pred_bnd.neg" a b c d e            ==> by constantBound <;> sorry
  "Gappa.Gappa_pred_bnd.add" a b c d e f g h      ==> by constantBound <;> sorry
  "Gappa.Gappa_pred_bnd.sub" a b c d e f g h      ==> by constantBound <;> sorry
  "Gappa.Gappa_pred_bnd.mul_pp" a b c d e f g h   ==> by tac
  "Gappa.Gappa_pred_bnd.div_pp" a b c d e f g h   ==> by tac
  "Gappa.Gappa_pred_abs.abs_of_bnd_p" a b c d e   ==> by tac
  "Gappa.Gappa_pred_bnd.square" a b c d e         ==> by tac
  "Gappa.Gappa_pred_bnd.subset" a b c d e         ==> by tac
  "Gappa.Gappa_rewriting.add_xilu" a b c d          ==> by tac
  "Gappa.Gappa_pred_bnd.intersect_hb" a b c d e f g ==> by tac
  "Gappa.Gappa_pred_bnd.intersect_bh" a b c d e f g ==> by tac
  "Gappa.Gappa_pred_bnd.union" a b c d              ==> by tac

  "proj1" x  ==> And.left x
  "proj2" x  ==> And.right x

-- TODO: this doesn't work at all anymore :(
partial def preprocess (s : String) : IO String :=
  let escaped_comments := s.replace "(*" "/-" |>.replace "*)" "-/"
  let rec loop (input : String) (acc : String := "") : String :=
    if input = "" then acc else
    if input.dropWhile (· == ' ') |>.startsWith "Gappa.Gappa_tree.simplify" then
      loop (input.dropWhile '\n' |>.toString.drop 1).toString (acc ++ "Gappa.Gappa_tree.simplify _ in ")
    else
      let line := input.takeWhile (· != '\n')
      loop (input.dropWhile '\n' |>.toString.drop 1).toString (acc ++ line ++ "\n")
  let escaped := loop escaped_comments
  return escaped

open Lean Meta Elab Term Command Tactic in
elab "gappa" : tactic => do
  let goal ← getMainGoal
  let typ ← instantiateMVars (← goal.getType)
  let formatted ← toExternal `Gappa_input typ
  IO.FS.writeFile "/Users/trowney/Desktop/Code/gappa/gappa/lean_test.g" s!"\{{formatted}}"
  let res ← IO.Process.run {
    cmd := "/Users/trowney/Desktop/Code/gappa/gappa/src/gappa",
    args := #[s!"-Bcoq-lambda", "/Users/trowney/Desktop/Code/gappa/gappa/lean_test.g"],
    stdin := .piped, stdout := .piped, stderr := .piped
  }
  let input ← preprocess res
  logInfo m!"Gappa output: {input}"
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
