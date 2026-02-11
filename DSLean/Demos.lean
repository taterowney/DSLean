import DSLean.Gappa
import DSLean.Desolve
import DSLean.LeanM2
set_option warn.sorry false
open Lean Meta Qq







external test_lang where
  "true" <==> «True»
  "false" <==> «False»
  "not" x <==> ¬ x
  x "and" y <==> x ∧ y
  x "or" y <==> x ∨ y
  x "implies" y <==> x → y

#eval do logInfo m!"{← fromExternal' `test_lang "not true and false implies true"}"

#eval toExternal `test_lang (q(«True» ∧ «False» → «True»))










/- `gappa` tactic: interval arithmetic -/


-- theorem test_thm : √2 ∈ Set.Icc 1.414 1.4151 := by
--   gappa
-- #print test_thm
-- example (y : ℝ) : y ∈ Set.Icc 0 1 → y * y * y ∈ Set.Icc 0 1 := by
--   gappa
-- example (y : ℝ) : y ∈ Set.Icc 0 1 → y * (1-y) ∈ Set.Icc 0 0.5 := by
--   gappa






-- example (a b c : Real) : c ∈ Set.Icc (-0.3 : Real) (-0.1 : Real) ∧ (2 * a ∈ Set.Icc 3 4 -> b + c ∈ Set.Icc 1 2) ∧
--   a - c ∈ Set.Icc 1.9 2.05 → b + 1 ∈ Set.Icc 2 3.5 := by
--   gappa



/- `desolve`: ordinary differential equations -/


#print isODEsolution


-- example : isODEsolution
--   (fun x => fun y => deriv y x = 1)
--   (fun C K1 K2 x => C + x) := by
--   desolve

-- example : isODEsolution
--   (fun x => fun y => deriv y x + y x = 1)
--   (fun C K1 K2 x => (C + Real.exp x) * (Real.exp (-x))) := by
--   desolve

-- example : isODEsolution
--   (fun x => fun y => deriv (deriv y) x + 2 * deriv y x + y x = 0)
--   (fun C K1 K2 x => (K2 * x + K1 ) * Real.exp (-x)) := by
--   desolve



/- `lean_m2`: ideal membership via Macaulay2 -/

-- example (x y : ℤ) : 2 * x + 3 * y ∈ Ideal.span {x, y} := by lean_m2
example (x y : ℚ) : x^2 * y + y^3 ∈ Ideal.span {x, y} := by
  simp only [Ideal.mem_span_insert', Ideal.mem_span_singleton']
  use 0
  use (x^2 + y^2)
  ring
  /- No goals left! -/


example (x y : ℚ) : x^2 * y + y^3 ∈ Ideal.span {x, y} := by
  simp only [Ideal.mem_span_insert', Ideal.mem_span_singleton']
  use -↑(Int.ofNat 0)
  use (x^(Int.ofNat 2) + y^(Int.ofNat 2))
  ring
  /-
  x y : ℚ
⊢ x ^ 2 * y + y ^ 2 * y = y * x ^ 2 + y ^ 3
  -/


example (x y : ℚ) : x^2 * y + y^3 ∈ Ideal.span {x, y} := by  lean_m2

example (x y : ℚ) : x^3 + y^3 ∈ Ideal.span {x + y} := by lean_m2
example (x y : ℚ) : x^3 - y^3 ∈ Ideal.span {x - y} := by lean_m2

/- Finite fields -/
example (x y : ZMod 11) : x^2 + y^2 ∈ Ideal.span {x, y} := by lean_m2
example (x y z : ZMod 3) : x^2 * y + z^3 ∈ Ideal.span {x, y, z} := by lean_m2
example (x y : ZMod 5) : x^3 + y^3 ∈ Ideal.span {x + y} := by lean_m2

/- Reals (polynomial expressions) -/
example (x y z : ℝ) : x^2 * y + z^3 ∈ Ideal.span {x, y, z} := by lean_m2

/- Complex -/
example (z w : ℂ) : z + Complex.I * w ∈ Ideal.span {z, w} := by lean_m2
example (x y : ℂ) : x^2 + y^2 ∈ Ideal.span {x - Complex.I * y} := by lean_m2


/- Polynomial rings -/
example (x y : Polynomial ℚ) : x^2 * y + y^3 ∈ Ideal.span {x, y} := by lean_m2
example (p q : Polynomial ℤ) : p^2 * q + p * q^2 ∈ Ideal.span {p * q} := by lean_m2

/- Quotient rings -/
open Polynomial in
example (x y : ℚ[X] ⧸ (Ideal.span {(X:ℚ[X])^2})) : x + y ∈ Ideal.span {x, y} := by lean_m2
open Polynomial in
example (x y : ℚ[X] ⧸ (Ideal.span {(X:ℚ[X])^2})) : x * y ∈ Ideal.span {x^3, y} := by lean_m2
