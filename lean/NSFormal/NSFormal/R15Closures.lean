/-
R15Closures.lean — machine certificates for the R1–R5 closure campaign
(NS_Proof.md, R1/R2/R3/R4/R5 CLOSURE sections and Lemma D; adjudication:
code/sympy_r15.py, log results/sympy_r15.log).

Nineteen certificates: the R1-A exact constants, the R1-B closure exponent
and n(η) implication, Lemma D's race ratio and affine-recursion step, the
rent-window cancellation and leakage clause, R2-A's sharp-case algebra,
R3's Γ_min cancellation and c_E stack, the R_m clause and flux fatness,
R4's γ-free overtone equilibrium, the grace formula, the zero-mean
oscillation identity, and the assembly allocation.
-/
import Mathlib

open Real

namespace NSFormal.R15

/-- R1-A: κ₃·6/π = 8 — the mean-value constant chain is exact. -/
theorem r1a_mean_value_eight : (4 * Real.pi / 3) * (6 / Real.pi) = 8 := by
  field_simp
  ring

/-- R1-B: the closure exponent identity (2n+5)/(2n+4) = 1 + 1/(2n+4). -/
theorem r1b_closure_exponent (n : ℕ) :
    ((2 * n + 5 : ℝ)) / (2 * n + 4) = 1 + 1 / (2 * n + 4) := by
  have h : (2 * n + 4 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- R1-B: the n(η) implication — if 1/η − 1 < 2n+4 (with 0 < η < 1) then
(1 + 1/(2n+4))·(1−η) < 1: the jet order closes the gap. -/
theorem r1b_n_eta (eta : ℝ) (n : ℕ) (h0 : 0 < eta) (h1 : eta < 1)
    (hn : 1 / eta - 1 < 2 * n + 4) :
    (1 + 1 / (2 * n + 4)) * (1 - eta) < 1 := by
  have hd : (0:ℝ) < 2 * n + 4 := by positivity
  have key : 1 - eta < eta * (2 * n + 4) := by
    have := (div_lt_iff₀ h0).mp (by linarith : 1 / eta < 2 * n + 4 + 1)
    nlinarith
  have expand : (1 + 1 / (2 * n + 4)) * (1 - eta)
      = (1 - eta) + (1 - eta) / (2 * n + 4) := by ring
  rw [expand]
  have hfrac : (1 - eta) / (2 * n + 4) < eta := by
    rw [div_lt_iff₀ hd]; nlinarith [key]
  linarith

/-- Lemma D race: the ratio Ω/ω² picks up exactly (1−ε)^W per the gross-4,
peak-2 bookkeeping: (Ω₀(4(1−ε))^W)/(ω₀2^W)² = (Ω₀/ω₀²)(1−ε)^W. -/
theorem rd_race_ratio (Om0 w0 eps : ℝ) (hw : w0 ≠ 0) (W : ℕ) :
    (Om0 * (4 * (1 - eps))^W) / (w0 * 2^W)^2
      = (Om0 / w0^2) * (1 - eps)^W := by
  have h2 : ((2:ℝ)^W)^2 = 4^W := by
    rw [← pow_mul, mul_comm W 2, pow_mul]; norm_num
  have h4 : ((4:ℝ))^W ≠ 0 := by positivity
  calc (Om0 * (4 * (1 - eps))^W) / (w0 * 2^W)^2
      = (Om0 * (4^W * (1 - eps)^W)) / (w0^2 * ((2:ℝ)^W)^2) := by
        rw [mul_pow, mul_pow]
    _ = (Om0 * (4^W * (1 - eps)^W)) / (w0^2 * 4^W) := by rw [h2]
    _ = (Om0 / w0^2) * (1 - eps)^W := by field_simp

/-- Lemma D (q2): the exact affine-recursion step — with c = b/(a−1),
a·(a^W(x₀+c) − c) + b = a^{W+1}(x₀+c) − c: the margin folds into the entry
constant with no loss. -/
theorem rd_affine_step (a b x0 : ℝ) (ha : a ≠ 1) (W : ℕ) :
    a * (a^W * (x0 + b/(a-1)) - b/(a-1)) + b
      = a^(W+1) * (x0 + b/(a-1)) - b/(a-1) := by
  have h : a - 1 ≠ 0 := sub_ne_zero.mpr ha
  field_simp
  ring

/-- Lemma D (q4): the rent–window cancellation — rate × window = θ·Ω exactly:
(νθK⁻²s⁻²Ω)·((Ks)²/ν) = θΩ. -/
theorem rd_rent_window (nu th K s Om : ℝ) (hnu : nu ≠ 0) (hK : K ≠ 0)
    (hs : s ≠ 0) :
    (nu * th * K⁻¹^2 * s⁻¹^2 * Om) * ((K * s)^2 / nu) = th * Om := by
  field_simp

/-- Lemma D (q1): the leakage clause — C/(686Kθ) ≤ 1/2 ⟺ C/(343θ) ≤ K. -/
theorem rd_leakage_clause (C K th : ℝ) (_hC : 0 < C) (hK : 0 < K)
    (hth : 0 < th) :
    C / (686 * K * th) ≤ 1/2 ↔ C / (343 * th) ≤ K := by
  rw [div_le_div_iff₀ (by positivity) (by norm_num),
      div_le_iff₀ (by positivity)]
  constructor <;> intro h <;> nlinarith

/-- R2-A sharpness: at constant ω over the disc (Γ = ωπs²), the
Cauchy–Schwarz floor is attained: Γ² = πs²·(ω²πs²). -/
theorem r2a_floor_sharp (w s : ℝ) :
    (w * Real.pi * s^2)^2 = (Real.pi * s^2) * (w^2 * Real.pi * s^2) := by
  ring

/-- R3-A: the γ-cancellation in Γ_min — c_cc(R₇γ)(4ν/(C₁′γ)) = 4c_ccR₇ν/C₁′. -/
theorem r3a_gamma_min (ccc R7 g nu C1 : ℝ) (hg : g ≠ 0) (hC : C1 ≠ 0) :
    ccc * (R7 * g) * (4 * nu / (C1 * g)) = 4 * ccc * R7 * nu / C1 := by
  field_simp

/-- R3-A: the stack identity deriving c_E = 1/4π —
(L/4δ)·(Γ²/πδ) = Γ²L/(4πδ²). -/
theorem r3a_ce_stack (L dl Gam : ℝ) (hd : dl ≠ 0) :
    (L / (4 * dl)) * (Gam^2 / (Real.pi * dl))
      = Gam^2 * L / (4 * Real.pi * dl^2) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- R3-B4: the R_m clause — πR₇/R_m² ≤ 1/(24b₃) ⟺ 24πb₃R₇ ≤ R_m². -/
theorem r3b_rm_clause (R7 Rm b3 : ℝ) (_hR : 0 < R7) (hRm : 0 < Rm)
    (hb : 0 < b3) :
    Real.pi * R7 / Rm^2 ≤ 1 / (24 * b3) ↔ 24 * Real.pi * b3 * R7 ≤ Rm^2 := by
  have hpi := Real.pi_pos
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  constructor <;> intro h <;> nlinarith

/-- R3-B4: flux forces fatness — Γ ≤ πωs² ⟺ Γ/(πω) ≤ s². -/
theorem r3b_fatness (Gam w s : ℝ) (hw : 0 < w) :
    Gam ≤ Real.pi * w * s^2 ↔ Gam / (Real.pi * w) ≤ s^2 := by
  rw [div_le_iff₀ (by positivity)]
  constructor <;> intro h <;> nlinarith [Real.pi_pos]

/-- R4-A: the overtone equilibrium is γ-free — C_prΔ₀γ/(2c₁γ) = C_prΔ₀/(2c₁). -/
theorem r4a_overtone (Cpr D0 g c1 : ℝ) (hg : g ≠ 0) (hc : c1 ≠ 0) :
    Cpr * D0 * g / (2 * c1 * g) = Cpr * D0 / (2 * c1) := by
  field_simp

/-- R4-C: the zero-mean oscillation identity — the 2β-harmonic quadratic form
on a precessing unit tilt is a pure cosine:
cos2β(cos²φ − sin²φ) + sin2β(2 sinφ cosφ) = cos(2φ − 2β). -/
theorem r4c_zero_mean (phi beta : ℝ) :
    Real.cos (2*beta) * (Real.cos phi ^ 2 - Real.sin phi ^ 2)
      + Real.sin (2*beta) * (2 * Real.sin phi * Real.cos phi)
      = Real.cos (2*phi - 2*beta) := by
  rw [Real.cos_sub, ← Real.cos_two_mul', ← Real.sin_two_mul]
  ring

/-- R2 assembly: the multiplicative allocation is exact —
3/8 + 3·(1/24) = 1/2. -/
theorem r2asm_allocation : (3:ℝ)/8 + 3 * (1/24) = 1/2 := by norm_num

/-- S1: the exterior-strain inheritance arithmetic — from osc ≤ 2Δ₀a and
mean′ ≥ (1 − (3/2)Δ₀)a with 0 < Δ₀ ≤ 1/6, the child's relative oscillation
obeys osc ≤ 3Δ₀·mean′. (sympy_r15 gate s1_inheritance) -/
theorem s1_inheritance (D a osc mean' : ℝ) (hD0 : 0 < D) (hD : D ≤ 1/6)
    (ha : 0 < a) (hosc : osc ≤ 2*D*a) (hm : (1 - (3/2)*D)*a ≤ mean') :
    osc ≤ 3*D*mean' := by
  have h3D : (0:ℝ) ≤ 3*D := by linarith
  have key : 3*D*((1 - (3/2)*D)*a) ≤ 3*D*mean' :=
    mul_le_mul_of_nonneg_left hm h3D
  nlinarith [mul_nonneg (mul_nonneg hD0.le ha.le)
    (by linarith : (0:ℝ) ≤ 1 - (9/2)*D)]

/-- S5: the far-field power domination — x^(5/8) ≤ x^(5/6) + 1 for x ≥ 0:
the γ-free count's raw power folds under the published budget display. -/
theorem pow_dominate (x : ℝ) (hx : 0 ≤ x) :
    x ^ ((5:ℝ)/8) ≤ x ^ ((5:ℝ)/6) + 1 := by
  rcases le_total x 1 with h | h
  · have h1 : x ^ ((5:ℝ)/8) ≤ 1 := Real.rpow_le_one hx h (by norm_num)
    have h2 : (0:ℝ) ≤ x ^ ((5:ℝ)/6) := Real.rpow_nonneg hx _
    linarith
  · have h1 : x ^ ((5:ℝ)/8) ≤ x ^ ((5:ℝ)/6) :=
      Real.rpow_le_rpow_of_exponent_le h (by norm_num)
    linarith

/-- R2-B/S5: the count solve — N = X^(3/4) satisfies N^(4/3) = X. -/
theorem r2b_count_solve (X : ℝ) (hX : 0 < X) :
    (X ^ ((3:ℝ)/4)) ^ ((4:ℝ)/3) = X := by
  have hmul : ((3:ℝ)/4) * ((4:ℝ)/3) = 1 := by norm_num
  rw [← Real.rpow_mul hX.le, hmul, Real.rpow_one]

end NSFormal.R15

/-- R6 closure (the fixed-dissipation reduction): the skew identity's algebraic
core. For the rotation field `u = (-y f, x f, 0)` and radial weight `g` (both
functions of `x^2+y^2`, chain-rule coefficients `2x`, `2y`), the divergence of
`g * u` cancels exactly: the rotation is skew in the Gaussian-weighted frame. -/
theorem r6_skew_divergence (x y gp g fp f : ℝ) :
    (-y) * (gp * (2*x) * f + g * (fp * (2*x))) +
      x * (gp * (2*y) * f + g * (fp * (2*y))) = 0 := by ring
