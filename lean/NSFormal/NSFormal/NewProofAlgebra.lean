import Mathlib

/-!
# Lean gate: the Write-Out Campaign's NEW algebra (certifying the new proofs)
Identities that entered DURING W1–W16, previously sympy-only. Improper integrals via the
antiderivative route (integral_Ioi_of_hasDerivAt_of_tendsto).
-/

open MeasureTheory Real Filter Topology

/-- W10's exponent chain: (x^(-1/3))^(-5/2) = x^(5/6) — the arithmetic behind the γ-display. -/
theorem w10_exponent_chain (x : ℝ) (hx : 0 < x) :
    (x ^ (-(1:ℝ)/3)) ^ (-(5:ℝ)/2) = x ^ ((5:ℝ)/6) := by
  rw [← Real.rpow_mul hx.le]
  norm_num

/-!
Queued for the analysis-phase batch (each sympy-certified today): W7's Duhamel integral
∫₀^∞ e^{−as} = 1/a; the Gram integral ⟨r, W′⟩ = −2 (results/sympy_w4.log + the banked
m1_impulse instrument); the W1/W8 tail integrals; W16's beta integral = π; the ℂ²-skew lemma;
W9's measure-theoretic Chebyshev (Mathlib's mul_meas_ge_le_integral_of_nonneg wraps it).
No sorries are committed to this project.
-/
