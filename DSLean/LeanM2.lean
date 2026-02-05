import DSLean.Command
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.RingTheory.Congruence.Defs
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span


injective external M2_out where
  x "+" y <== x + y
  x "-" y <== x - y
  x "*" y <== x * y
  x "/" y <== x / y
  x "^" y <== x ^ y
  x "!" <== Nat.factorial x

  ";" $x "=" y ";" rest <== let x := y; rest
  "ZZ" <== ℤ
  "QQ" <== ℚ
  R "/" x <== R ⧸ Ideal.span ({x} : Set R)




open Lean Meta Elab Term Command Tactic Qq in
#eval do
  logInfo m!"{← toExternal `M2_out (q(ℚ ⧸ Ideal.span (Set.singleton 5 : Set ℚ)))}"
