import ExternalComputationsInLean.Command
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Basic

open Qq


injective external Sage_ODE where
  ";x=var('" $x "\\');" rest <== ∀ (x : Real), rest
  ";y=function('" $y "\\');" rest <== ∀ (y : Real → Real), rest
  "Integer(" x ")" <== (x : Int)
  "desolve(" eq ",y)==" fn <== eq → fn
  "(" lhs ")" "-" "(" rhs ")" <== lhs = rhs -- Expects everything to total to 0
  x "(" y ")" <== (x : Real → Real) y

  x "+" y <== x+y
  x "-" y <== x-y
  x "*" y <== x*y
  x "/" y <== x/y
  x "^" y <== x^y
  "diff(" fn "," var ")" <== deriv fn var


-- #eval toExternal `Sage_ODE q(∀ (x : Real), x=x)
-- #eval toExternal `Sage_ODE q(∀ (x : Real), ∀ (y : Real → Real), deriv y x + y x = 1 → y x = x + 1)
