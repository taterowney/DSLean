import DSLean.Gappa
import DSLean.Desolve
import DSLean.LeanM2



/- `gappa` tactic: interval arithmetic via the Gappa solver -/



example (a b c : Real) :
  c ∈ Set.Icc (-0.3 : Real) (-0.1 : Real) ∧
  (2 * a ∈ Set.Icc 3 4 → b + c ∈ Set.Icc 1 2) ∧
  a - c ∈ Set.Icc 1.9 2.05 →
  b + 1 ∈ Set.Icc 2 3.5 := by
    gappa

example (y : ℝ) :
  y ∈ Set.Icc 0 1 →
  y * y * y ∈ Set.Icc 0 1 := by
    gappa
    expose_names -- Some goals left over that automation couldn't solve by itself
    have := right (by nlinarith)
    nlinarith


example (y : ℝ) :
  y ∈ Set.Icc 0 1 →
  y * (1-y) ∈ Set.Icc 0 0.5 := by
    gappa
    · gappa_reduce_arrows
      nlinarith
    gappa_reduce_arrows
    nlinarith




/- `desolve`: ordinary differential equations via SageMath -/


#print isODEsolution


example : isODEsolution
  (fun x => fun y => deriv y x = 1)
  (fun C _ _ x => C + x) := by
  desolve

example : isODEsolution
  (fun x => fun y => deriv y x + y x = 1)
  (fun C _ _ x => (C + Real.exp x) * (Real.exp (-x))) := by
  desolve

/- If the witness Sage returns is not the same as what was provided, the user is asked to prove their equivalence -/
example : isODEsolution
  (fun x => fun y => deriv (deriv y) x + 2 * deriv y x + y x = 0)
  (fun _ K1 K2 x => Real.exp (-x) * (K2 * x + K1)) := by
  desolve
    /- Goals remaining: ⊢ (fun _ K1 K2 x => (K1 + K2 * x)) * Real.exp (-x)) =
                           fun _ K1 K2 x => Real.exp (-x) * (K2 * x + K1) -/
  funext
  rw [mul_comm]





/- `lean_m2`: ideal membership via Macaulay2 -/

example (x y : ℤ) : 2 * x + 3 * y ∈ Ideal.span {x, y} := by lean_m2

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



example (a b c d e f : ℚ) : a^4+a^2*b*c-a^2*d*e+a*b^3+b^2*c*d-b^2*e*f+a*c^3+b*c^2*d-c^2*f^2
  ∈ Ideal.span {a^2+b*c-d*e, a*b+c*d-e*f, a*c+b*d-f^2}  := by
  lean_m2



example (x y : ℚ) (h_sum : x+y = 0) : x^3 + y^3 = 0 := by
  suffices h : x^3 + y^3 ∈ Ideal.span {x + y} by
    simp [h_sum] at h
    exact h
  lean_m2
