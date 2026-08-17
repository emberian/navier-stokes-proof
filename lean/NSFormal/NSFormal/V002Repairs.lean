/-
V002Repairs.lean — machine certificates for the v002 repair campaign
(the envelope chain and the any-point funnel; NS_Proof.md, "V002 REPAIR
CAMPAIGN" section; adjudication: code/sympy_v002.py, log results/sympy_v002.log).

Sixteen certificates: the exact and algebraic cores of the corrected kinematic
identity's one-sided form, the windowed-Duhamel arithmetic (kernel time
integral, rescaled-enstrophy power, the M₈ threshold, quiet growth), the
tangled fold, the K₄ constant, the interval-drift exponent assembly, the ε₈
squeeze arithmetic, the ν^{3/2} persistence-floor arithmetic, the
capped-debris pricing (per-event integral; γ-cancelling episode count), and
the P6 sweep's calibrated absorption split (the ε-log bound, the 3/8
coefficient pin with 8/3 < e, and the closure to the published budget
display; adjudication: code/sympy_p6.py, log results/sympy_p6.log).
-/
import Mathlib

open Real

namespace NSFormal.V002

/-- The one-sided viscous sign at a spatial maximizer: with `d = Δ|ω| ≤ 0`,
`m = |ω| ≥ 0`, `g = |∇ξ|² ≥ 0`, the viscous contribution `d − m·g` is
nonpositive. (sympy gate 1) -/
theorem l1_subsolution_sign (d m g : ℝ) (hd : d ≤ 0) (hm : 0 ≤ m) (hg : 0 ≤ g) :
    d - m * g ≤ 0 := by
  nlinarith [mul_nonneg hm hg]

/-- The Duhamel kernel time integral: `∫₀¹ σ^(−3/4) dσ = 4` — the 3/4 < 1
integrability saving that lets the kernel-weighted strain be summed without a
pointwise strain bound. (sympy gate 2) -/
theorem kernel_time_integral :
    ∫ σ in (0:ℝ)..1, σ ^ (-(3:ℝ)/4) = 4 := by
  rw [integral_rpow (Or.inl (by norm_num))]
  rw [show -(3:ℝ)/4 + 1 = 1/4 by norm_num]
  rw [Real.one_rpow, Real.zero_rpow (by norm_num : (1/4:ℝ) ≠ 0)]
  norm_num

/-- The rescaled-enstrophy exponent arithmetic: `r⁴ · r⁻³ = r` — the reason the
local enstrophy of the window rescaling carries one positive power of `r`,
hence vanishes at high intensity. (sympy gate 3) -/
theorem rescaled_enstrophy_power (r : ℝ) (hr : 0 < r) :
    r ^ (4:ℕ) * (r ^ (3:ℕ))⁻¹ = r := by
  field_simp

/-- Root extraction for the M₈ threshold: a nonnegative quantity whose fourth
power is at most `(1/2)⁴` is at most `1/2`. (sympy gate 4, part b) -/
theorem quarter_root_bound (x : ℝ) (hx : 0 ≤ x) (h : x ^ (4:ℕ) ≤ (1/2:ℝ) ^ (4:ℕ)) :
    x ≤ 1/2 := by
  by_contra hcon
  have hx2 : 1/2 < x := by linarith [not_le.mp hcon]
  have h1 : (0:ℝ) < x - 1/2 := by linarith
  have h2 : (0:ℝ) < x + 1/2 := by linarith
  have h3 : (0:ℝ) < x^2 - 1/4 := by nlinarith [mul_pos h1 h2]
  have h4 : (0:ℝ) < x^2 + 1/4 := by positivity
  nlinarith [mul_pos h3 h4]

/-- The M₈ threshold arithmetic: if `M ≥ 16 C⁴ Ω² / ν³` then
`C⁴ Ω² / (ν³ M) ≤ (1/2)⁴` — the fourth power of the Duhamel production bound
`P₁ = C √Ω ν^{−3/4} M^{−1/4}` lands at or below `(1/2)⁴`, so `P₁ ≤ 1/2` by
`quarter_root_bound`: every window is quiet above `M₈`. (sympy gate 4) -/
theorem m8_threshold_arithmetic (C Om nu M : ℝ) (hC : 0 < C) (hOm : 0 < Om)
    (hnu : 0 < nu) (hM8 : 16 * C ^ 4 * Om ^ 2 / nu ^ 3 ≤ M) :
    C ^ 4 * Om ^ 2 / (nu ^ 3 * M) ≤ (1/2:ℝ) ^ (4:ℕ) := by
  have hM : 0 < M := lt_of_lt_of_le (by positivity) hM8
  rw [div_le_iff₀ (by positivity)]
  have h16 : 16 * C ^ 4 * Om ^ 2 ≤ M * nu ^ 3 := by
    rw [div_le_iff₀ (by positivity)] at hM8
    linarith
  nlinarith [h16]

/-- The quiet-window growth bound: from the Duhamel split `1 ≤ 1/G + P` with
`0 ≤ P ≤ 1/2` and `G > 0`, the per-window growth obeys `G ≤ 1/(1−P)`, and
`1/(1−P) ≤ 1 + 2P`. (sympy gate 5) -/
theorem quiet_growth_bound (G P : ℝ) (hG : 0 < G) (hP : 0 ≤ P) (hP2 : P ≤ 1/2)
    (h : 1 ≤ 1/G + P) : G ≤ 1/(1-P) ∧ 1/(1-P) ≤ 1 + 2*P := by
  have h1P : (0:ℝ) < 1 - P := by linarith
  constructor
  · rw [le_div_iff₀ h1P]
    have hg' : (1 - P) ≤ 1/G := by linarith
    have : (1 - P) * G ≤ (1/G) * G :=
      mul_le_mul_of_nonneg_right hg' hG.le
    have hGG : (1/G) * G = 1 := by field_simp
    nlinarith [this]
  · rw [div_le_iff₀ h1P]
    nlinarith

/-- The tangled fold: `(1+x)^N ≤ exp(N·x)` for `x ≥ 0` — compounding the quiet
per-window growth over at most `N*` windows gives `F_tan ≤ e^{N*}`.
(sympy gate 6) -/
theorem ftan_fold (x : ℝ) (N : ℕ) (hx : 0 ≤ x) :
    (1 + x) ^ N ≤ Real.exp (N * x) := by
  calc (1 + x) ^ N ≤ (Real.exp x) ^ N := by
        apply pow_le_pow_left₀ (by linarith)
        linarith [Real.add_one_le_exp x]
    _ = Real.exp (N * x) := (Real.exp_nat_mul x N).symm

/-- The K₄ constant algebra:
`√(2/(2π)³) · √(E₀/(2ν)) = √(E₀/((2π)³ ν))`. (sympy gate 7) -/
theorem k4_omega_star_integral (E0 nu : ℝ) (hE : 0 ≤ E0) (hnu : 0 < nu) :
    Real.sqrt (2 / (2*Real.pi)^3) * Real.sqrt (E0 / (2*nu))
      = Real.sqrt (E0 / ((2*Real.pi)^3 * nu)) := by
  rw [← Real.sqrt_mul (by positivity)]
  congr 1
  field_simp

/-- The interval-drift exponent assembly is a ring identity:
`2(C₁'+c_λ)I + 2mT + C_ev(1 + (e_d/c)I)
 = (2(C₁'+c_λ) + C_ev e_d/c)I + 2mT + C_ev`. (sympy gate 8) -/
theorem drift_interval_bound (C1 cl mm T Cev ed c I : ℝ) (hc : c ≠ 0) :
    2*(C1 + cl)*I + 2*mm*T + Cev*(1 + (ed/c)*I)
      = (2*(C1 + cl) + Cev*ed/c)*I + 2*mm*T + Cev := by
  field_simp
  ring

/-- The ε₈ squeeze arithmetic: for `ε < (c/C)⁴` (all positive), the squeeze
output `C · ε^{1/4}` lands strictly below the floor `c` — the any-point
contradiction. (sympy gate 9; mirrors `sc7_small_eps_choice`.) -/
theorem eps8_squeeze_arithmetic (C c eps : ℝ) (hC : 0 < C) (hc : 0 < c)
    (heps : 0 < eps) (h : eps < (c / C) ^ ((4:ℝ))) :
    C * eps ^ ((1:ℝ)/4) < c := by
  have hbase : (0:ℝ) < c / C := div_pos hc hC
  have hlt : eps ^ ((1:ℝ)/4) < ((c / C) ^ ((4:ℝ))) ^ ((1:ℝ)/4) :=
    Real.rpow_lt_rpow heps.le h (by norm_num)
  have hmul : (4:ℝ) * ((1:ℝ)/4) = 1 := by norm_num
  rw [← Real.rpow_mul hbase.le, hmul, Real.rpow_one] at hlt
  calc C * eps ^ ((1:ℝ)/4) < C * (c / C) := mul_lt_mul_of_pos_left hlt hC
    _ = c := by field_simp

/-- The persistence-floor arithmetic: if `1/2 ≤ K·m/s` with `K, s > 0`, then
`m ≥ s/(2K)` — instantiated with `s = (νσ)^{3/2}` this is the local L¹
vorticity mass floor of the quiet window. (sympy gate 10) -/
theorem nu32_floor_arithmetic (K s mass : ℝ) (hK : 0 < K) (hs : 0 < s)
    (h : 1/2 ≤ K * mass / s) : s / (2*K) ≤ mass := by
  rw [le_div_iff₀ hs] at h
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- The capped-debris per-event integral is uniform in distance:
`(Γ/max(d,δ)²)·(δ²/ν) ≤ Γ/ν`, because `δ ≤ max(d,δ)`. (sympy gate 11) -/
theorem cd_event_integral (Gam d delta nu : ℝ) (hG : 0 ≤ Gam) (hd : 0 < d)
    (hdel : 0 < delta) (hnu : 0 < nu) :
    Gam / (max d delta) ^ 2 * (delta ^ 2 / nu) ≤ Gam / nu := by
  have hmax : 0 < max d delta := lt_max_of_lt_right hdel
  have h2 : delta ^ 2 ≤ (max d delta) ^ 2 :=
    pow_le_pow_left₀ hdel.le (le_max_right d delta) 2
  rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) hnu]
  nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hG) hnu.le,
    sq_nonneg (max d delta)]

/-- The capped-debris episode count cancels γ exactly:
`(4νΩ/(c₁ γ c_E Γ² L)) · (γ/c) = 4νΩ/(c₁ c_E Γ² L c)`. (sympy gate 12) -/
theorem cd_event_count (nu Om c1 gam cE Gam L c : ℝ) (hg : gam ≠ 0)
    (hc1 : c1 ≠ 0) (hcE : cE ≠ 0) (hG : Gam ≠ 0) (hL : L ≠ 0) (hc : c ≠ 0) :
    (4*nu*Om / (c1 * gam * cE * Gam^2 * L)) * (gam / c)
      = 4*nu*Om / (c1 * cE * Gam^2 * L * c) := by
  field_simp

/-- P6: the calibrated logarithm split — for `0 < ε ≤ 1` and `t ≥ 0`,
`log(1+t) ≤ εt + log(1/ε)`; at `ε = 1` this is the plain split `log(1+t) ≤ t`.
Proof: `ε(1+t) ≤ 1+εt ≤ exp(εt)`. (sympy_p6 gate 1) -/
theorem bg_calibrated_log (t eps : ℝ) (ht : 0 ≤ t) (h0 : 0 < eps) (h1 : eps ≤ 1) :
    Real.log (1 + t) ≤ eps * t + Real.log (1 / eps) := by
  have hpos : (0:ℝ) < 1 + t := by linarith
  have key : eps * (1 + t) ≤ Real.exp (eps * t) := by
    have h2 : eps * (1 + t) ≤ 1 + eps * t := by nlinarith
    have h3 : eps * t + 1 ≤ Real.exp (eps * t) := Real.add_one_le_exp (eps * t)
    linarith
  have hlog : Real.log (eps * (1 + t)) ≤ eps * t :=
    (Real.log_le_iff_le_exp (by positivity)).mpr key
  rw [Real.log_mul (ne_of_gt h0) (ne_of_gt hpos)] at hlog
  rw [one_div, Real.log_inv]
  linarith

/-- P6: the split coefficient and its cost — at `ε = 3(A+B)/(8B)` the γ-coefficient
`Bε/(A+B)` is exactly `3/8`, and the calibration cost `log(8B/(3(A+B)))` is at
most `1` because `8B/(3(A+B)) < 8/3 < e`. (sympy_p6 gates 2–3) -/
theorem bg_split_coefficient (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    B * (3 * (A + B) / (8 * B)) / (A + B) = 3 / 8 ∧
    Real.log (8 * B / (3 * (A + B))) ≤ 1 := by
  have hAB : (0:ℝ) < A + B := by linarith
  refine ⟨by field_simp, ?_⟩
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have harg : (0:ℝ) < 8 * B / (3 * (A + B)) := by positivity
  have h1 : 8 * B / (3 * (A + B)) < Real.exp 1 := by
    rw [div_lt_iff₀ (by positivity)]
    have hcomp : (2.7182818283:ℝ) * (3 * (A + B)) < Real.exp 1 * (3 * (A + B)) :=
      mul_lt_mul_of_pos_right he (by linarith)
    nlinarith [hcomp]
  have h2 : Real.log (8 * B / (3 * (A + B))) < 1 := by
    calc Real.log (8 * B / (3 * (A + B))) < Real.log (Real.exp 1) :=
          Real.log_lt_log harg h1
      _ = 1 := Real.log_exp 1
  exact le_of_lt h2

/-- P6: the joint closure — from
`γ ≤ A + B·logL + B·cal + (3/8)γ + (1/8)γ` with `cal ≤ 1`, the total absorbable
coefficient is `1/2` and `γ ≤ 2A + 2B(1 + logL)`: the published budget display,
unconditional. (sympy_p6 gate 4) -/
theorem bg_split_closure (g A B lg cal : ℝ) (hB : 0 ≤ B)
    (hcal : cal ≤ 1)
    (h : g ≤ A + B * lg + B * cal + 3/8 * g + 1/8 * g) :
    g ≤ 2 * A + 2 * B * (1 + lg) := by
  nlinarith [mul_le_mul_of_nonneg_left hcal hB]

end NSFormal.V002
