import ExternalComputationsInLean.IntervalArith
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.GoldenRatio



-- set_option warn.sorry false



-- Bounds on square roots
example : √2 * 1000 ≤ 1415 := by
  gappa

example : √3 * 1024 ≤ 1774 := by
  gappa

-- Bounding the golden ratio
open goldenRatio in
example : 16 ≤ φ * 10 ∧ φ * 10 ≤ 17 := by
  unfold goldenRatio
  constructor
  · suffices (1 + √5) / 2 * 10 ≥ 16 by exact this
    gappa
  gappa




-- variable (y : ℝ)

-- Bounds on a quadratic expression
-- Doesn't work yet because of some weird bug in the parser around anonymous functions. The translation and solving stage work just fine though...
-- example : y >= 0 ∧ y <= 1 → y * (1-y) * 3 <= 1 := by
--   gappa
