import Mathlib

/-!
# Lean gate, target 2: Lemma 18's identity and the ruler mathematics
Lemma 18 (NS_Proof): with cᵢ = ξ·eᵢ in the strain eigenframe and Aᵢ = cᵢ² − 1/3, the
stretching rate is exactly the anisotropy–eigenvalue pairing, with the Cauchy–Schwarz and
organization bounds. Plus the δ²-ruler calibration factor's closed form ½ − (ln 2)/3
(integral evaluation sympy-certified: results/sympy_rulers.log).
-/

/-- Lemma 18, the exact pairing: if ξ is unit in the eigenframe (c₀²+c₁²+c₂² = 1) and S is
trace-free (λ₀+λ₁+λ₂ = 0), then α = Σλᵢcᵢ² = ΣᵢAᵢλᵢ with Aᵢ = cᵢ² − 1/3. -/
theorem lemma18_pairing (c0 c1 c2 l0 l1 l2 : ℝ)
    (hc : c0^2 + c1^2 + c2^2 = 1) (hl : l0 + l1 + l2 = 0) :
    l0*c0^2 + l1*c1^2 + l2*c2^2
      = (c0^2 - 1/3)*l0 + (c1^2 - 1/3)*l1 + (c2^2 - 1/3)*l2 := by
  have h : (1/3 : ℝ)*(l0 + l1 + l2) = 0 := by rw [hl]; ring
  linarith [h]

/-- The Cauchy–Schwarz step of Lemma 18's bound (Lagrange identity form). -/
theorem lemma18_cauchy_schwarz (a0 a1 a2 l0 l1 l2 : ℝ) :
    (a0*l0 + a1*l1 + a2*l2)^2 ≤ (a0^2 + a1^2 + a2^2)*(l0^2 + l1^2 + l2^2) := by
  nlinarith [sq_nonneg (a0*l1 - a1*l0), sq_nonneg (a0*l2 - a2*l0), sq_nonneg (a1*l2 - a2*l1)]

/-- The organization bound: the anisotropy vector's norm² is at most 2/3 —
Org_∞ = sup‖A‖ ≤ √(2/3), attained at perfect alignment. -/
theorem lemma18_org_bound (c0 c1 c2 : ℝ) (hc : c0^2 + c1^2 + c2^2 = 1) :
    (c0^2 - 1/3)^2 + (c1^2 - 1/3)^2 + (c2^2 - 1/3)^2 ≤ 2/3 := by
  nlinarith [sq_nonneg (c0*c1), sq_nonneg (c0*c2), sq_nonneg (c1*c2), sq_nonneg c0,
             sq_nonneg c1, sq_nonneg c2]

/-- The δ²-ruler calibration factor: the exact closed form of the truncated-Gaussian
ω²-weighted moment ratio (integrals (3/16 − ln2/8) and 3/8, sympy-certified):
their ratio is exactly ½ − (ln 2)/3 ≈ 0.268951 — the "0.269" of MEASUREMENTS.md. -/
theorem calibration_factor_closed_form :
    (3/16 - Real.log 2 / 8) / (3/8 : ℝ) = 1/2 - Real.log 2 / 3 := by
  ring

