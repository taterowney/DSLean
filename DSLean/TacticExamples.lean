import DSLean.Gappa
import DSLean.Desolve
open Lean Meta Qq



/- `gappa` tactic: interval arithmetic -/



-- example (y : ℝ) :
--   y ∈ Set.Icc 0 1 →
--   y * (1-y) ∈ Set.Icc 0 0.5 := by
--     gappa
--     · Gappa_reduce_arrows
--       nlinarith
--     · Gappa_reduce_arrows
--       nlinarith
--     Gappa_reduce_arrows
--     nlinarith


-- example (a b c : Real) :
--   c ∈ Set.Icc (-0.3 : Real) (-0.1 : Real) ∧
--   (2 * a ∈ Set.Icc 3 4 → b + c ∈ Set.Icc 1 2) ∧
--   a - c ∈ Set.Icc 1.9 2.05 →
--   b + 1 ∈ Set.Icc 2 3.5 := by
--     gappa


-- example (y : ℝ) :
--   y ∈ Set.Icc 0 1 →
--   y * y * y ∈ Set.Icc 0 1 := by
--     gappa
--     · Gappa_simplify

/- `desolve`: ordinary differential equations -/


#print isODEsolution


-- example : isODEsolution
--   (fun x => fun y => deriv y x = 1)
--   (fun C _ _ x => C + x) := by
--   desolve

-- example : isODEsolution
--   (fun x => fun y => deriv y x + y x = 1)
--   (fun C _ _ x => (C + Real.exp x) * (Real.exp (-x))) := by
--   desolve

-- example : isODEsolution
--   (fun x => fun y => deriv (deriv y) x + 2 * deriv y x + y x = 0)
--   (fun _ K1 K2 x => Real.exp (-x) * (K2 * x + K1)) := by
--   desolve
--     /- Goals remaining: ⊢ (fun _ K1 K2 x => (K1 + K2 * x)) * Real.exp (-x)) =
--                            fun _ K1 K2 x => Real.exp (-x) * (K2 * x + K1) -/
--   funext
--   rw [mul_comm]
