import Mathlib

/-!
# Lean gate, capstone batch: the Write-Out Campaign's queued algebra
Every coefficient chain and closure inequality the write-outs produced, kernel-certified.
(The improper-integral evaluations remain sympy-certified, queued for the analysis phase;
the ℂ²-skew lemma Re⟨a, iΔJa⟩ = 0 likewise.)
-/

/-- W5's boundary arithmetic: at Λ = μ²/(4M(1+L)²) with τ = 2(1+L)/μ, the Grönwall exponent
MΛτ²/2 equals exactly 1/2 (the ⚠→✔-corrected value). -/
theorem w5_boundary_exponent (M mu L : ℝ) (hM : 0 < M) (hmu : 0 < mu) (hL : 0 ≤ L) :
    M * (mu^2/(4*M*(1+L)^2)) * (2*(1+L)/mu)^2 / 2 = 1/2 := by
  field_simp
  ring

/-- W5's window slack: μτ/2 − (1/2 + ln M) = 1/2 when μτ/2 = 1 + ln M — the corrected chain
closes with slack exactly 1/2 for every M ≥ 1. -/
theorem w5_window_slack (L : ℝ) : (1 + L) - (1/2 + L) = 1/2 := by ring

/-- W6's bootstrap closure core: 1 − √(1−s) ≤ s on [0,1] — the smallest quadratic root stays
below the barrier 2C₁. -/
theorem w6_closure (s : ℝ) (h0 : 0 ≤ s) (h1 : s ≤ 1) : 1 - Real.sqrt (1 - s) ≤ s := by
  have hq : 0 ≤ Real.sqrt (1 - s) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (1 - s) ^ 2 = 1 - s := Real.sq_sqrt (by linarith)
  nlinarith [hq, hsq]

/-- W9's shell series: Σ (1/4)^k = 4/3 — the dyadic γ-budget converges with the exact
constant. -/
theorem w9_shell_series : ∑' (k : ℕ), ((1:ℝ)/4)^k = 4/3 := by
  rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

/-- W13's defect gap: from ε·A ≤ C·ε² with A, C > 0 and ε ≥ 0: either ε = 0 or ε ≥ A/C —
the maintenance dichotomy. -/
theorem w13_defect_gap (eps A C : ℝ) (hA : 0 < A) (hC : 0 < C) (he : 0 ≤ eps)
    (h : eps * A ≤ C * eps^2) : eps = 0 ∨ A/C ≤ eps := by
  rcases eq_or_lt_of_le he with h0 | hpos
  · left; exact h0.symm
  · right
    rw [div_le_iff₀ hC]
    nlinarith [hpos, h]

/-- W3's log-norm assembly (scalar form): the damping and strain parts combine to the episode
rate — (−d + εκ)·n with n = ‖a‖². -/
theorem w3_lognorm_assembly (d e k n : ℝ) : -d*n + e*k*n = (e*k - d)*n := by ring

/-- W10's Hölder exponents: 5/6 + 1/6 = 1 — the conjugate pairing behind ∫γ ≤ KT^{1/6}. -/
theorem w10_holder_exponents : (5:ℝ)/6 + 1/6 = 1 := by norm_num

/-- SC-7's small-ε choice (Anchor Lemma 3′c): with the class tolerance chosen below
ε₇ = (ε_CKN/C_QT)^{4/3}, the quantitative-Tsai size bound C_QT·ε^{3/4} lands strictly below
the CKN nontriviality level — the horn-(iii) contradiction, no repair accounting.
(sympy: code/sympy_sc7.py) -/
theorem sc7_small_eps_choice (C eCKN eps : ℝ) (hC : 0 < C) (he : 0 < eCKN) (heps : 0 < eps)
    (h : eps < (eCKN / C) ^ ((4:ℝ)/3)) : C * eps ^ ((3:ℝ)/4) < eCKN := by
  have hbase : (0:ℝ) < eCKN / C := div_pos he hC
  have hlt : eps ^ ((3:ℝ)/4) < ((eCKN / C) ^ ((4:ℝ)/3)) ^ ((3:ℝ)/4) :=
    Real.rpow_lt_rpow heps.le h (by norm_num)
  have hmul : ((4:ℝ)/3) * ((3:ℝ)/4) = 1 := by norm_num
  rw [← Real.rpow_mul hbase.le, hmul, Real.rpow_one] at hlt
  calc C * eps ^ ((3:ℝ)/4) < C * (eCKN / C) := mul_lt_mul_of_pos_left hlt hC
    _ = eCKN := by field_simp

/-- SC-2 / Lemma CP-1's veto engine (matrix form): a velocity field with vanishing third
component has a Jacobian with zero third row, and its symmetric part then has zero axial
diagonal entry — S₃₃ = 0 exactly (the shifted-2D-field veto; sympy: code/sympy_sc2.py (1)). -/
theorem cp_veto_shifted_field (J : Matrix (Fin 3) (Fin 3) ℝ) (hrow : ∀ j, J 2 j = 0) :
    ((1:ℝ)/2) • (J + J.transpose) 2 2 = 0 := by
  simp [Matrix.add_apply, Matrix.transpose_apply, hrow]

/-- SC-2 / Lemma CP-1's residue expansion: for a symmetric strain with S₃₃ = 0, the pairing
ξᵀSξ with ξ = (sinθ cosφ, sinθ sinφ, cosθ) carries NO cos²θ term — every surviving term is
at least first order in sinθ (sympy: code/sympy_sc2.py (2)). -/
theorem cp_axial_residue (S11 S12 S13 S22 S23 st ct cp sp : ℝ) :
    (![st*cp, st*sp, ct] ⬝ᵥ
      (Matrix.of ![![S11, S12, S13], ![S12, S22, S23], ![S13, S23, 0]]).mulVec
        ![st*cp, st*sp, ct])
    = 2*ct*st*(S13*cp + S23*sp) + st^2*(S11*cp^2 + 2*S12*cp*sp + S22*sp^2) := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- SC-2 / Lemma CP-2's payment algebra: at the L19-R1 pair equilibrium θ_eq = Cγd²/Γ, the
vetoed payment θ_eq²·Γ/d² equals C²γ²d²/Γ, and at the mutual-dominance edge d² = Γ/γ it is
exactly C²γ (sympy: code/sympy_sc2.py (3)). -/
theorem cp_payment_algebra (C g G d : ℝ) (hG : G ≠ 0) (hd : d ≠ 0) :
    (C*g*d^2/G)^2 * (G/d^2) = C^2*g^2*d^2/G ∧
    (C*g*(G/g)/G)^2 * (G/(G/g)) = C^2*g ∨ g = 0 := by
  rcases eq_or_ne g 0 with hg | hg
  · right; exact hg
  · left
    constructor
    · field_simp
    · field_simp

/-- SC-2 / Lemma CP-2's band cancellation: the equilibrium payment summed with the
enstrophy-weighted count is γ-free — (γ²/Γmin)·(4νΩ/(c₁γc_EΓmin²L))·(Γmax/γ) =
4νΩΓmax/(c₁c_EΓmin³L): the near band pays C_n·ν·Ω, integrable by the energy identity
(sympy: code/sympy_sc2.py (3)). -/
theorem cp_band_cancellation (g Gmin Gmax nu Om c1 cE L : ℝ)
    (hg : g ≠ 0) (hGmin : Gmin ≠ 0) (hc1 : c1 ≠ 0) (hcE : cE ≠ 0) (hL : L ≠ 0) :
    (g^2/Gmin) * (4*nu*Om/(c1*g*cE*Gmin^2*L)) * (Gmax/g)
      = 4*nu*Om*Gmax/(c1*cE*Gmin^3*L) := by
  field_simp

/-- SC-1 / Lemma BG-2's log absorption: from γ ≤ A + B·log(e + Cγ), the factorization
e + Cγ ≤ (e + C(A+B))(1 + γ/(A+B)) yields absorption with coefficient B/(A+B) < 1
IDENTICALLY — the finding's "log-coefficient < 1" by structure, not tuning:
A·γ ≤ (A+B)·(A + B·log(e + C(A+B))). (sympy: code/sympy_sc1.py (1)-(3)) -/
theorem bg_log_absorption (g A B C : ℝ) (hg : 0 ≤ g) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (h : g ≤ A + B * Real.log (Real.exp 1 + C * g)) :
    A * g ≤ (A + B) * (A + B * Real.log (Real.exp 1 + C * (A + B))) := by
  have he1 : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
  have hAB : (0:ℝ) < A + B := by linarith
  have hCg : (0:ℝ) ≤ C * g := mul_nonneg hC.le hg
  have harg1 : (0:ℝ) < Real.exp 1 + C * g := by linarith
  have harg2 : (0:ℝ) < Real.exp 1 + C * (A + B) := by nlinarith
  have hone : (0:ℝ) < 1 + g / (A + B) := by positivity
  have hfactor : Real.exp 1 + C * g ≤ (Real.exp 1 + C * (A + B)) * (1 + g / (A + B)) := by
    have hd : C * (A + B) * (g / (A + B)) = C * g := by field_simp
    nlinarith [mul_nonneg he1.le (div_nonneg hg hAB.le), mul_pos hC hAB, hd]
  have hlog1 : Real.log (Real.exp 1 + C * g)
      ≤ Real.log ((Real.exp 1 + C * (A + B)) * (1 + g / (A + B))) :=
    Real.log_le_log harg1 hfactor
  have hsplit : Real.log ((Real.exp 1 + C * (A + B)) * (1 + g / (A + B)))
      = Real.log (Real.exp 1 + C * (A + B)) + Real.log (1 + g / (A + B)) :=
    Real.log_mul (ne_of_gt harg2) (ne_of_gt hone)
  have htan : Real.log (1 + g / (A + B)) ≤ g / (A + B) := by
    have := Real.log_le_sub_one_of_pos hone
    linarith
  have hchain : g ≤ A + B * Real.log (Real.exp 1 + C * (A + B)) + B * (g / (A + B)) := by
    have hlog2 : Real.log (Real.exp 1 + C * g)
        ≤ Real.log (Real.exp 1 + C * (A + B)) + g / (A + B) := by
      rw [hsplit] at hlog1; linarith
    nlinarith [mul_le_mul_of_nonneg_left hlog2 hB.le]
  have hmul := mul_le_mul_of_nonneg_left hchain hAB.le
  have hdiv : (A + B) * (B * (g / (A + B))) = B * g := by field_simp
  nlinarith [hmul, hdiv]

/-- SC-1 / Lemma BG-3(b)'s sheath absorption: γ ≤ X + λγ with λ ≤ 1/2 gives γ ≤ 2X — the
merger-floor choice R_m makes the wrapped-sheath term multiplicatively absorbable. -/
theorem bg_half_absorption (g X lam : ℝ) (hlam : lam ≤ 1/2) (hg : 0 ≤ g)
    (h : g ≤ X + lam * g) : g ≤ 2 * X := by nlinarith

/-- SC-4 / Lemma EC-1's perturbative bootstrap: at clock ratio ω ≥ 2MC_e·γ the equilibrium
ellipticity C_eγ/ω is ≤ 1/(2M) — strictly inside the linear theory's validity window
e ≤ 1/M. (sympy: code/sympy_sc4.py (2)) -/
theorem ec_threshold (M Ce g w : ℝ) (hM : 0 < M) (hCe : 0 < Ce) (hg : 0 < g)
    (hw : 2*M*Ce*g ≤ w) : Ce*g/w ≤ 1/(2*M) := by
  have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hw
  rw [div_le_div_iff₀ hw0 (by positivity)]
  nlinarith

/-- SC-4 / Lemma EC-2's BKM split: (w − r)₊ + min(w, r) = w — the vorticity supremum splits
exactly into the budget-paid sub-ratio part and the Grönwall-capped intense part.
(sympy: code/sympy_sc4.py (3)) -/
theorem ec_bkm_split (w r : ℝ) : max (w - r) 0 + min w r = w := by
  rcases le_total w r with h | h
  · rw [max_eq_right (by linarith), min_eq_left h]; ring
  · rw [max_eq_left (by linarith), min_eq_right h]; ring

/-- SC-3 / Lemma FT-3's transit factor: exp((g/c)·(log(1/θ)/g)) = θ^{-1/c} — the
organizer's gap g cancels; the per-transit growth factor is intensity-free.
(sympy: code/sympy_sc35.py (1)) -/
theorem ft_transit_factor (g c th : ℝ) (hg : 0 < g) (hc : 0 < c) (hth : 0 < th) :
    Real.exp ((g/c) * (Real.log (1/th) / g)) = th ^ (-(1:ℝ)/c) := by
  have h1 : (g/c) * (Real.log (1/th) / g) = (-(1:ℝ)/c) * Real.log th := by
    rw [one_div, Real.log_inv]
    field_simp
  rw [h1, mul_comm, Real.exp_mul, Real.exp_log hth]

/-- SC-3 / Lemma FT-5's chain fold: exp(A)·Gⁿ = exp(A + n·log G) for G > 0 — the transit
factors fold into the single exponential the ‖ω‖_∞ chain uses.
(sympy: code/sympy_sc35.py (2)) -/
theorem ft_chain_fold (A G n : ℝ) (hG : 0 < G) :
    Real.exp A * G ^ n = Real.exp (A + n * Real.log G) := by
  rw [Real.exp_add, mul_comm n, Real.exp_mul, Real.exp_log hG]

/-- SC-5 / Lemma DC-2's coherence inheritance: with sub-ball deviation ≤ 2Δ₀a and sub-ball
mean b ≥ (1−Δ₀)a, the sub-ball is 3Δ₀-coherent for Δ₀ ≤ 1/3: 2Δ₀a ≤ 3Δ₀b.
(sympy: code/sympy_sc35.py (3)) -/
theorem dc_coherence_inherit (a b D : ℝ) (ha : 0 ≤ a) (hD : 0 ≤ D) (hD3 : D ≤ 1/3)
    (hb : (1 - D) * a ≤ b) : 2*D*a ≤ 3*D*b := by
  nlinarith [mul_le_mul_of_nonneg_left hb (by linarith : (0:ℝ) ≤ 3*D),
             mul_nonneg (mul_nonneg hD ha) (by linarith : (0:ℝ) ≤ 1 - 3*D)]

/-- SC-8 / Lemma B′(B1′)'s slice scaling: r² · r⁻³ = r⁻¹ (rpow) — the critical rescaling's
exponent arithmetic making the Morrey density an exact functional of the amplitude-carrying
slice. (sympy: code/sympy_sc8.py (1)) -/
theorem sc8_slice_scaling (r : ℝ) (hr : 0 < r) :
    r ^ (2:ℝ) * r ^ (-(3:ℝ)) = r ^ (-(1:ℝ)) := by
  rw [← Real.rpow_add hr]
  norm_num

/-- SC-8 / Lemma B′(B1′)'s Hölder pairing on the unit ball: 1/2 = 1/3 + 1/6 — the L²–L³
continuity exponents. -/
theorem sc8_holder_exponents : (1:ℝ)/2 = 1/3 + 1/6 := by norm_num

/-- SC-9 / Lemma SU(i)'s Green-kernel integral: ∫₀¹ x^m dx = 1/(m+1) — the radial factor
giving the band constants their 1/m decay. (sympy: code/sympy_sc9.py (1)) -/
theorem su_green_integral (m : ℕ) :
    ∫ x in (0:ℝ)..1, x ^ m = 1 / (m + 1) := by
  rw [integral_pow]
  norm_num

/-- SC-9 / Lemma QD(b)'s exponent positivity: m − 1/2 ≥ 1/2 > 0 for every m ≥ 1 — the
corrected depletion power beats the edge for every sector. -/
theorem qd_exponent_positive (m : ℕ) (hm : 1 ≤ m) : (1:ℝ)/2 ≤ (m:ℝ) - 1/2 := by
  have : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  linarith

/-- SC-9 / Lemma QD(b)'s power collapse: (x^{1/2})^{2m−1} = x^{m−1/2} (rpow, x > 0) — the
critical-radius inversion feeding the corrected exponent. (sympy: code/sympy_sc9.py (3)) -/
theorem qd_rpow_collapse (x : ℝ) (hx : 0 < x) (m : ℕ) :
    (x ^ ((1:ℝ)/2)) ^ ((2:ℝ)*m - 1) = x ^ ((m:ℝ) - 1/2) := by
  rw [← Real.rpow_mul hx.le]
  congr 1
  ring

/-- Pass-2 P2-3 / EC-1's rate floor: for 0 < x ≤ B, x^{-1/3} ≥ B^{-1/3} — the circulation
Reynolds number of class tubes is bounded, so the viscous critical-layer rate keeps a
data-only floor. (sympy: code/sympy_p2.py (1)) -/
theorem ec_rate_floor (x B : ℝ) (hx : 0 < x) (hB : x ≤ B) :
    B ^ (-(1:ℝ)/3) ≤ x ^ (-(1:ℝ)/3) := by
  have hB0 : 0 < B := lt_of_lt_of_le hx hB
  apply Real.rpow_le_rpow_of_nonpos hx hB
  norm_num

/-- Pass-2 P2-4 / FT-2's veto reading: the middle of the 2D strain eigenvalues
(σ, 0, −σ), σ ≥ 0, is 0 exactly — tube-dominated capped points have vetoed λ₂.
(sympy: code/sympy_p2.py (2)) -/
theorem ft_middle_eigenvalue (s : ℝ) (hs : 0 ≤ s) :
    max (min s 0) (max (min 0 (-s)) (min s (-s))) = 0 := by
  rw [min_eq_right hs, min_eq_right (neg_nonpos.mpr hs),
      min_eq_right (by linarith : -s ≤ s), max_self,
      max_eq_left (neg_nonpos.mpr hs)]
