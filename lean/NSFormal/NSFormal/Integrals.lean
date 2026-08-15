import Mathlib

/-!
# Lean gate: the integral certificates (the six-item queue, attacked properly)
Each was sympy-certified; here they are kernel-certified via the antiderivative route
(integral_Ioi_of_hasDerivAt_of_tendsto') and Mathlib's own Chebyshev.
-/

open MeasureTheory Real Filter Topology

/-- W7's Duhamel integral: ∫₀^∞ e^{−a s} ds = 1/a. -/
theorem w7_duhamel_integral (a : ℝ) (ha : 0 < a) :
    ∫ s in Set.Ioi (0:ℝ), Real.exp (-a * s) = 1 / a := by
  have hderiv : ∀ s ∈ Set.Ici (0:ℝ),
      HasDerivAt (fun t => -(1/a) * Real.exp (-a * t)) (Real.exp (-a * s)) s := by
    intro s _
    have h1 : HasDerivAt (fun t : ℝ => -a * t) (-a) s := by
      simpa using (hasDerivAt_id s).const_mul (-a)
    have h2 := h1.exp.const_mul (-(1/a))
    have harith : -(1/a) * (Real.exp (-a * s) * -a) = Real.exp (-a * s) := by
      field_simp
    exact harith ▸ h2
  have hint : IntegrableOn (fun s => Real.exp (-a * s)) (Set.Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 ha
  have hlim : Tendsto (fun t => -(1/a) * Real.exp (-a * t)) atTop (nhds 0) := by
    have h3 : Tendsto (fun t : ℝ => a * t) atTop atTop :=
      Tendsto.const_mul_atTop ha tendsto_id
    have h4 : Tendsto (fun t : ℝ => Real.exp (-(a * t))) atTop (nhds 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp h3
    have h5 : Tendsto (fun t : ℝ => Real.exp (-a * t)) atTop (nhds 0) := by
      simpa [neg_mul] using h4
    simpa using h5.const_mul (-(1/a))
  have key := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  rw [key]
  simp

/-- W1's tail integral (1D core): for r > 0, ∫_r^∞ s^{−4} ds = r^{−3}/3 (rpow form). -/
theorem w1_tail_integral (r : ℝ) (hr : 0 < r) :
    ∫ s in Set.Ioi r, s ^ (-(4:ℝ)) = r ^ (-(3:ℝ)) / 3 := by
  have hderiv : ∀ s ∈ Set.Ici r,
      HasDerivAt (fun t : ℝ => -(3:ℝ)⁻¹ * t ^ (-(3:ℝ))) (s ^ (-(4:ℝ))) s := by
    intro s hs
    have hs0 : s ≠ 0 := by
      have : (0:ℝ) < s := lt_of_lt_of_le hr hs
      exact ne_of_gt this
    have h1 := (Real.hasDerivAt_rpow_const (p := (-(3:ℝ))) (Or.inl hs0)).const_mul (-(3:ℝ)⁻¹)
    have harith : -(3:ℝ)⁻¹ * ((-(3:ℝ)) * s ^ ((-(3:ℝ)) - 1)) = s ^ (-(4:ℝ)) := by
      rw [show (-(3:ℝ)) - 1 = -(4:ℝ) by norm_num]
      ring
    exact harith ▸ h1
  have hint : IntegrableOn (fun s : ℝ => s ^ (-(4:ℝ))) (Set.Ioi r) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hr
  have hlim : Tendsto (fun t : ℝ => -(3:ℝ)⁻¹ * t ^ (-(3:ℝ))) atTop (nhds 0) := by
    have := tendsto_rpow_neg_atTop (y := (3:ℝ)) (by norm_num)
    simpa using this.const_mul (-(3:ℝ)⁻¹)
  have key := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  rw [key]
  simp
  ring

/-- The ℂ-skew core: if z is self-conjugate (real), then Re(iz) = 0 — the reason the detuning
generator iΔJ contributes nothing to the episode's energy rate (W3's skew step). -/
theorem skew_core (z : ℂ) (h : (starRingEnd ℂ) z = z) : (Complex.I * z).re = 0 := by
  have him : z.im = 0 := by
    have h2 := congrArg Complex.im h
    simp at h2
    linarith
  simp [Complex.mul_re, him]

/-- The Hermitian quadratic form is self-conjugate: the 2×2 content behind skew_core's
application (d₁, d₂ real diagonal, off-diagonal c and c̄). -/
theorem hermitian_quadratic_real (d1 d2 : ℝ) (c a1 a2 : ℂ) :
    (starRingEnd ℂ) ((d1:ℂ) * a1 * (starRingEnd ℂ) a1 + (d2:ℂ) * a2 * (starRingEnd ℂ) a2
      + c * (starRingEnd ℂ) a1 * a2 + (starRingEnd ℂ) c * a1 * (starRingEnd ℂ) a2)
    = (d1:ℂ) * a1 * (starRingEnd ℂ) a1 + (d2:ℂ) * a2 * (starRingEnd ℂ) a2
      + c * (starRingEnd ℂ) a1 * a2 + (starRingEnd ℂ) c * a1 * (starRingEnd ℂ) a2 := by
  simp [map_add, map_mul, Complex.conj_ofReal]
  ring

/-- W8's tail integral (1D core): for r > 0, ∫_r^∞ s^{−6} ds = r^{−5}/5 (rpow form). -/
theorem w8_tail_integral (r : ℝ) (hr : 0 < r) :
    ∫ s in Set.Ioi r, s ^ (-(6:ℝ)) = r ^ (-(5:ℝ)) / 5 := by
  have hderiv : ∀ s ∈ Set.Ici r,
      HasDerivAt (fun t : ℝ => -(5:ℝ)⁻¹ * t ^ (-(5:ℝ))) (s ^ (-(6:ℝ))) s := by
    intro s hs
    have hs0 : s ≠ 0 := ne_of_gt (lt_of_lt_of_le hr hs)
    have h1 := (Real.hasDerivAt_rpow_const (p := (-(5:ℝ))) (Or.inl hs0)).const_mul (-(5:ℝ)⁻¹)
    have harith : -(5:ℝ)⁻¹ * ((-(5:ℝ)) * s ^ ((-(5:ℝ)) - 1)) = s ^ (-(6:ℝ)) := by
      rw [show (-(5:ℝ)) - 1 = -(6:ℝ) by norm_num]
      ring
    exact harith ▸ h1
  have hint : IntegrableOn (fun s : ℝ => s ^ (-(6:ℝ))) (Set.Ioi r) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hr
  have hlim : Tendsto (fun t : ℝ => -(5:ℝ)⁻¹ * t ^ (-(5:ℝ))) atTop (nhds 0) := by
    have := tendsto_rpow_neg_atTop (y := (5:ℝ)) (by norm_num)
    simpa using this.const_mul (-(5:ℝ)⁻¹)
  have key := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  rw [key]
  simp
  ring

/-- W4's Gram integral: ∫₀^∞ r²·(2e^{−r²})′ dr = −2 — the ⟨r, W′⟩ = −2 pairing. -/
theorem gram_integral :
    ∫ r in Set.Ioi (0:ℝ), r^2 * (-4 * r * Real.exp (-r^2)) = -2 := by
  have hderiv : ∀ r ∈ Set.Ici (0:ℝ),
      HasDerivAt (fun t : ℝ => (2*t^2 + 2) * Real.exp (-t^2))
        (r^2 * (-4 * r * Real.exp (-r^2))) r := by
    intro r _
    have h1 : HasDerivAt (fun t : ℝ => 2*t^2 + 2) (4*r) r := by
      have h1' := ((hasDerivAt_pow 2 r).const_mul (2:ℝ)).add_const 2
      have e1 : (2:ℝ) * (((2:ℕ):ℝ) * r ^ ((2:ℕ) - 1)) = 4 * r := by push_cast; ring
      exact e1 ▸ h1'
    have h2 : HasDerivAt (fun t : ℝ => Real.exp (-t^2)) (Real.exp (-r^2) * (-(2*r))) r := by
      have := ((hasDerivAt_pow 2 r).neg).exp
      simpa [pow_one] using this
    have h3 := h1.mul h2
    have harith : 4*r * Real.exp (-r^2) + (2*r^2 + 2) * (Real.exp (-r^2) * (-(2*r)))
        = r^2 * (-4 * r * Real.exp (-r^2)) := by ring
    exact harith ▸ h3
  have hint : IntegrableOn (fun r : ℝ => r^2 * (-4 * r * Real.exp (-r^2))) (Set.Ioi 0) := by
    have h := (integrableOn_rpow_mul_exp_neg_mul_sq (b := 1) one_pos
      (s := (3:ℝ)) (by norm_num)).const_mul (-4)
    apply h.congr
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
    have hcast : x ^ ((3:ℝ)) = x ^ (3:ℕ) := by
      rw [show ((3:ℝ)) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    simp [hcast]
    ring
  have hlim : Tendsto (fun t : ℝ => (2*t^2 + 2) * Real.exp (-t^2)) atTop (nhds 0) := by
    have hsq : Tendsto (fun t : ℝ => t^2) atTop atTop := tendsto_pow_atTop (by norm_num)
    have h1 : Tendsto (fun t : ℝ => t^2 * Real.exp (-t^2)) atTop (nhds 0) := by
      have := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hsq
      apply this.congr
      intro x
      simp
    have h2 : Tendsto (fun t : ℝ => Real.exp (-t^2)) atTop (nhds 0) := by
      have := Real.tendsto_exp_neg_atTop_nhds_zero.comp hsq
      apply this.congr
      intro x
      simp
    have hsum := (h1.const_mul 2).add (h2.const_mul 2)
    have hcong : ∀ t : ℝ, 2*(t^2 * Real.exp (-t^2)) + 2*(Real.exp (-t^2))
        = (2*t^2 + 2) * Real.exp (-t^2) := by intro t; ring
    simpa [hcong] using hsum
  have key := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  rw [key]
  simp

/-- W9's Chebyshev, wrapped verbatim from Mathlib: ε·μ{ε ≤ f} ≤ ∫f for nonneg integrable f —
the volume bound Vol{|ω| ≥ ω*} ≤ 2Ω/ω*² in its measure-theoretic form. -/
theorem w9_chebyshev {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {f : α → ℝ} (hf_nonneg : 0 ≤ᵐ[μ] f) (hf_int : MeasureTheory.Integrable f μ) (ε : ℝ) :
    ε * μ.real {x | ε ≤ f x} ≤ ∫ x, f x ∂μ :=
  MeasureTheory.mul_meas_ge_le_integral_of_nonneg hf_nonneg hf_int ε

/-- Continuity of the beta antiderivative on the closed interval. -/
theorem beta_cont : ContinuousOn (fun y : ℝ => Real.arcsin (2*y - 1)) (Set.Icc 0 1) :=
  (Real.continuous_arcsin.comp
    (((continuous_const.mul continuous_id).sub continuous_const))).continuousOn

/-- The beta derivative: arcsin(2x−1)′ = x^{−1/2}(1−x)^{−1/2} on (0,1). -/
theorem beta_deriv (x : ℝ) (hx : x ∈ Set.Ioo (0:ℝ) 1) :
    HasDerivAt (fun y : ℝ => Real.arcsin (2*y - 1))
      (x ^ (-(1:ℝ)/2) * (1-x) ^ (-(1:ℝ)/2)) x := by
  obtain ⟨hx0, hx1⟩ := hx
  have h1 : (2*x - 1) ≠ -1 := by intro h; nlinarith
  have h2 : (2*x - 1) ≠ 1 := by intro h; nlinarith
  have hin : HasDerivAt (fun y : ℝ => 2*y - 1) 2 x := by
    simpa using ((hasDerivAt_id x).const_mul (2:ℝ)).sub_const 1
  have ha := (Real.hasDerivAt_arcsin h1 h2).comp x hin
  have harith : 1 / Real.sqrt (1 - (2*x-1)^2) * 2
      = x ^ (-(1:ℝ)/2) * (1-x) ^ (-(1:ℝ)/2) := by
    have h4 : 1 - (2*x-1)^2 = 2^2 * (x*(1-x)) := by ring
    rw [h4, Real.sqrt_mul (by positivity) (x*(1-x)), Real.sqrt_sq (by norm_num),
        Real.sqrt_mul hx0.le (1-x)]
    rw [show (-(1:ℝ)/2) = -(1/2 : ℝ) by norm_num,
        Real.rpow_neg hx0.le, Real.rpow_neg (by linarith : (0:ℝ) ≤ 1 - x),
        ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
    have hs1 : (0:ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
    have hs2 : (0:ℝ) < Real.sqrt (1-x) := Real.sqrt_pos.mpr (by linarith)
    field_simp
  exact harith ▸ ha

/-- Integrability of the beta integrand across [0,1], by halves. -/
theorem beta_integrable :
    IntervalIntegrable (fun x : ℝ => x ^ (-(1:ℝ)/2) * (1-x) ^ (-(1:ℝ)/2)) volume 0 1 := by
  have half1 : IntervalIntegrable (fun x : ℝ => x ^ (-(1:ℝ)/2) * (1-x) ^ (-(1:ℝ)/2))
      volume 0 (1/2) := by
    have base : IntervalIntegrable (fun x : ℝ => x ^ (-(1:ℝ)/2)) volume 0 (1/2) :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    have cont : ContinuousOn (fun x : ℝ => (1-x) ^ (-(1:ℝ)/2)) (Set.uIcc 0 (1/2)) := by
      apply ContinuousOn.rpow_const ((continuous_const.sub continuous_id).continuousOn)
      intro x hx
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/2)] at hx
      left
      intro hzero
      have h1x : (1:ℝ) = x := sub_eq_zero.mp hzero
      have hx2 := hx.2
      linarith
    exact base.mul_continuousOn cont
  have half2 : IntervalIntegrable (fun x : ℝ => x ^ (-(1:ℝ)/2) * (1-x) ^ (-(1:ℝ)/2))
      volume (1/2) 1 := by
    have base : IntervalIntegrable (fun u : ℝ => u ^ (-(1:ℝ)/2)) volume 0 (1/2) :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    have shifted := (base.comp_sub_left 1).symm
    have hb1 : (1:ℝ) - 1/2 = 1/2 := by norm_num
    have hb2 : (1:ℝ) - 0 = 1 := by norm_num
    rw [hb1, hb2] at shifted
    have cont : ContinuousOn (fun x : ℝ => x ^ (-(1:ℝ)/2)) (Set.uIcc (1/2) 1) := by
      apply ContinuousOn.rpow_const continuousOn_id
      intro x hx
      rw [Set.uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 1)] at hx
      left
      have := hx.1
      positivity
    have prod := shifted.mul_continuousOn cont
    have heq : (fun x : ℝ => x ^ (-(1:ℝ)/2) * (1-x) ^ (-(1:ℝ)/2))
        = (fun x : ℝ => (1-x) ^ (-(1:ℝ)/2) * x ^ (-(1:ℝ)/2)) := by
      funext x; ring
    rw [heq]
    exact prod
  exact half1.trans half2

/-- W16's beta integral: ∫₀¹ x^{−1/2}(1−x)^{−1/2} dx = π — the exact value behind
Fujita–Kato's contraction. THE final Lean-queue item, landed. -/
theorem w16_beta_integral :
    ∫ x in (0:ℝ)..1, x ^ (-(1:ℝ)/2) * (1-x) ^ (-(1:ℝ)/2) = π := by
  have key := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le (by norm_num)
    beta_cont (fun x hx => (beta_deriv x hx).hasDerivWithinAt) beta_integrable
  rw [key]
  norm_num [Real.arcsin_one, Real.arcsin_neg_one]
