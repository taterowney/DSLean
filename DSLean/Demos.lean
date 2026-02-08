import DSLean.Gappa
import DSLean.Desolve
set_option warn.sorry false
open Lean Meta Qq







external test_lang where
  "true" <==> «True»
  "false" <==> «False»
  "not" x <==> ¬ x
  x "and" y <==> x ∧ y
  x "or" y <==> x ∨ y
  x "implies" y <==> x → y

#eval do logInfo m!"{← fromExternal `test_lang "not true and false implies true"}"

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
