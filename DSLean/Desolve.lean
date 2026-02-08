import DSLean.Command
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic


open Qq Lean Elab Term Command Tactic Meta


external Sage_ODE_out where
  "(" body ")" <== fun (x : Real) => body
  "(" body ")" <== fun (y : Real → Real) => body
  "Integer(" x ")" <== (x : Int)
  x "+" y "*0" <== (x : Real → Real) y
  "(" lhs ")" "-" "(" rhs ")" <== lhs = rhs -- Expects everything to total to 0

  x "+" y <== x+y
  x "-" y <== x-y
  x "*" y <== x*y
  x "/" y <== x/y
  x "^" y <== x^y
  "diff(" fn "," var ")" <== deriv fn var
  "-" x <== -(x:Real)
  "e^" x <== Real.exp x
  "log(" x ")" <== Real.log x
  "sqrt(" x ")" <== Real.sqrt x
  "sin(" x ")" <== Real.sin x
  "cos(" x ")" <== Real.cos x
  "tan(" x ")" <== Real.tan x

external Sage_ODE_in where
  "{" inside "}" ==> fun (_C _K1 _K2 x : Real) => inside
  x "+" y ==> x + y   ; (precedence := 0)
  x "-" y ==> x - y   ; (precedence := 0)
  x "*" y ==> x * y   ; (precedence := 1)
  x "/" y ==> x / y   ; (precedence := 1)
  x "^" y ==> x ^ y   ; (precedence := 2)
  "-" x ==> -(x:Real)
  "e^" x ==> Real.exp x
  "log(" x ")" ==> Real.log x
  "sqrt(" x ")" ==> Real.sqrt x
  "sin(" x ")" ==> Real.sin x
  "cos(" x ")" ==> Real.cos x
  "tan(" x ")" ==> Real.tan x
  "(" x ")" ==> x


-- def python_sage_path : String :=
--   "/usr/local/bin/sage"

private axiom sage_sound :
  ∀ (ode : Real → (Real → Real) → Prop)
    (sage_out : Real → Real → Real → Real → Real)
    (soln : Real → Real → Real → Real → Real),
    sage_out = soln →
    ∀ (y : Real → Real), (∀ x, ode x y) → ∃ C K1 K2, ∀ x, y x = soln C K1 K2 x

def isODEsolution (ode : Real → (Real → Real) → Prop) (soln : Real → Real → Real → Real → Real) : Prop :=
  ∀ (y : Real → Real), (∀ x, ode x y) → ∃ C K1 K2, ∀ x, y x = soln C K1 K2 x

elab "desolve" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let target ← instantiateMVars (← (← getMainGoal).getType)
    if !target.isAppOfArity ``isODEsolution 2 then
      throwError "desolve tactic requires goals involving `isODEsolution`."
    let ode := target.appFn!.appArg!
    let soln := target.appArg!

    let formatted := "x = var('x'); y = function('y')(x); print(desolve(" ++ (← toExternal `Sage_ODE_out ode) ++ ",y).simplify_full())"
    let res ← IO.Process.run {
      cmd := (← IO.getEnv "DSLEAN_SAGE_PATH").getD "sage",
      args := #["-c", formatted],
      stdin := .piped, stdout := .piped, stderr := .piped
    }

    let out ← fromExternal' `Sage_ODE_in ("{" ++ res ++ "}")
    logInfo m!"Sage output: {res}, {out}"

    let eq ← mkFreshExprMVar <| mkAppN (mkConst ``Eq [1]) #[q(Real → Real→ Real→ Real→ Real), soln, out]
    let term := mkAppN q(sage_sound) #[ode, out, soln, eq]

    let new ← (← getMainGoal).apply term
    replaceMainGoal new

    evalTactic (← `(tactic| try rfl; try congr <;> rfl ))
