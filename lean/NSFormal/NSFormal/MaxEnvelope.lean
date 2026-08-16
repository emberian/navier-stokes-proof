import Mathlib

/-!
# Spatial maxima and time envelopes

For a continuous real-valued function on a nonempty compact space, this file
constructs an actual maximizer from the extreme-value theorem.  It then proves that
the maximum-value functional is `1`-Lipschitz in the uniform norm and transfers
uniform right-slope bounds to the maximum envelope.
-/

open Filter Set
open scoped Topology

noncomputable section

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]

/-- A continuous real-valued function on a nonempty compact space attains its
maximum. -/
theorem exists_spatial_maximizer (f : C(X, ℝ)) : ∃ x : X, ∀ y : X, f y ≤ f x := by
  obtain ⟨x, _hx, hmax⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set X)).exists_isMaxOn
      Set.univ_nonempty f.continuous.continuousOn
  exact ⟨x, fun y => hmax (Set.mem_univ y)⟩

/-- A chosen maximizer, justified by `exists_spatial_maximizer`. -/
def spatialMaximizer (f : C(X, ℝ)) : X :=
  Classical.choose (exists_spatial_maximizer f)

theorem le_at_spatialMaximizer (f : C(X, ℝ)) (x : X) :
    f x ≤ f (spatialMaximizer f) :=
  Classical.choose_spec (exists_spatial_maximizer f) x

/-- The maximum value of a continuous function on a nonempty compact space. -/
def spatialMax (f : C(X, ℝ)) : ℝ := f (spatialMaximizer f)

/-- The (nonempty) set on which a continuous field attains its spatial maximum. -/
def maximizerSet (f : C(X, ℝ)) : Set X := {x | f x = spatialMax f}

@[simp]
theorem spatialMax_eq_apply (f : C(X, ℝ)) :
    spatialMax f = f (spatialMaximizer f) := rfl

theorem le_spatialMax (f : C(X, ℝ)) (x : X) : f x ≤ spatialMax f :=
  le_at_spatialMaximizer f x

theorem spatialMaximizer_mem_maximizerSet (f : C(X, ℝ)) :
    spatialMaximizer f ∈ maximizerSet f := by
  simp [maximizerSet]

theorem maximizerSet_nonempty (f : C(X, ℝ)) : (maximizerSet f).Nonempty :=
  ⟨spatialMaximizer f, spatialMaximizer_mem_maximizerSet f⟩

theorem isClosed_maximizerSet (f : C(X, ℝ)) : IsClosed (maximizerSet f) := by
  exact isClosed_singleton.preimage f.continuous

theorem isCompact_maximizerSet (f : C(X, ℝ)) : IsCompact (maximizerSet f) :=
  (isClosed_maximizerSet f).isCompact

/-- A point where `g` is largest among the maximizers of `f`. -/
def derivativeMaximizer (f g : C(X, ℝ)) : X :=
  Classical.choose <|
    (isCompact_maximizerSet f).exists_isMaxOn (maximizerSet_nonempty f)
      g.continuous.continuousOn

theorem derivativeMaximizer_mem (f g : C(X, ℝ)) :
    derivativeMaximizer f g ∈ maximizerSet f :=
  (Classical.choose_spec <|
    (isCompact_maximizerSet f).exists_isMaxOn (maximizerSet_nonempty f)
      g.continuous.continuousOn).1

/-- The largest derivative value among the current spatial maximizers. -/
def maxDerivativeAtMaximizers (f g : C(X, ℝ)) : ℝ :=
  g (derivativeMaximizer f g)

theorem le_maxDerivativeAtMaximizers (f g : C(X, ℝ)) {x : X}
    (hx : x ∈ maximizerSet f) : g x ≤ maxDerivativeAtMaximizers f g := by
  exact (Classical.choose_spec <|
    (isCompact_maximizerSet f).exists_isMaxOn (maximizerSet_nonempty f)
      g.continuous.continuousOn).2 hx

theorem maxDerivativeAtMaximizers_le_iff (f g : C(X, ℝ)) (C : ℝ) :
    maxDerivativeAtMaximizers f g ≤ C ↔ ∀ x ∈ maximizerSet f, g x ≤ C := by
  constructor
  · intro h x hx
    exact (le_maxDerivativeAtMaximizers f g hx).trans h
  · intro h
    exact h _ (derivativeMaximizer_mem f g)

theorem spatialMax_const_smul (f : C(X, ℝ)) {c : ℝ} (hc : 0 ≤ c) :
    spatialMax (c • f) = c * spatialMax f := by
  apply le_antisymm
  · change c * f (spatialMaximizer (c • f)) ≤ c * spatialMax f
    exact mul_le_mul_of_nonneg_left (le_spatialMax f _) hc
  · change c * spatialMax f ≤ spatialMax (c • f)
    simpa using le_spatialMax (c • f) (spatialMaximizer f)

theorem maximizerSet_const_smul (f : C(X, ℝ)) {c : ℝ} (hc : 0 < c) :
    maximizerSet (c • f) = maximizerSet f := by
  ext x
  simp only [maximizerSet, Set.mem_ofPred_eq, ContinuousMap.smul_apply,
    smul_eq_mul, spatialMax_const_smul f hc.le]
  constructor
  · exact mul_left_cancel₀ hc.ne'
  · exact fun h => congrArg (c * ·) h

/-- If fields converge uniformly to `f`, then maximizers of the converging
fields eventually lie in every strict superlevel neighborhood of the maximizer
set selected by a second continuous field `g`. -/
theorem eventually_apply_later_maximizer_lt_maxDerivative
    {ι : Type*} {l : Filter ι} {v : ι → C(X, ℝ)} {f g : C(X, ℝ)} {r : ℝ}
    (hv : Tendsto v l (𝓝 f)) (hr : maxDerivativeAtMaximizers f g < r) :
    ∀ᶠ i in l, g (spatialMaximizer (v i)) < r := by
  let B : Set X := {x | r ≤ g x}
  by_cases hB : B.Nonempty
  · have hBclosed : IsClosed B := isClosed_le continuous_const g.continuous
    have hBcompact : IsCompact B := hBclosed.isCompact
    obtain ⟨y, hyB, hymax⟩ :=
      hBcompact.exists_isMaxOn hB f.continuous.continuousOn
    have hynot : y ∉ maximizerSet f := by
      intro hy
      have hgy := le_maxDerivativeAtMaximizers f g hy
      exact (not_lt_of_ge (hyB.trans hgy)) hr
    have hfy : f y < spatialMax f := by
      have hle := le_spatialMax f y
      exact lt_of_le_of_ne hle (by simpa [maximizerSet] using hynot)
    have hδ : 0 < (spatialMax f - f y) / 3 := by linarith
    filter_upwards [Metric.tendsto_nhds.mp hv _ hδ] with i hi
    let x := spatialMaximizer (v i)
    have hclose : ∀ z : X, |v i z - f z| < (spatialMax f - f y) / 3 := by
      intro z
      calc
        |v i z - f z| = ‖(v i - f) z‖ := by simp
        _ ≤ ‖v i - f‖ := ContinuousMap.norm_coe_le_norm _ z
        _ = dist (v i) f := by rw [dist_eq_norm]
        _ < (spatialMax f - f y) / 3 := hi
    by_contra hxlt
    have hxB : x ∈ B := not_lt.mp hxlt
    have hfx : f x ≤ f y := hymax hxB
    have hmax_now : v i (spatialMaximizer f) ≤ v i x :=
      le_at_spatialMaximizer (v i) (spatialMaximizer f)
    have hxclose := abs_lt.mp (hclose x)
    have hmaxclose := abs_lt.mp (hclose (spatialMaximizer f))
    have hfmax : f (spatialMaximizer f) = spatialMax f := rfl
    linarith
  · filter_upwards [] with i
    exact lt_of_not_ge fun hi => hB ⟨spatialMaximizer (v i), hi⟩

theorem spatialMax_sub_le_norm (f g : C(X, ℝ)) :
    spatialMax f - spatialMax g ≤ ‖f - g‖ := by
  let x := spatialMaximizer f
  have hg : g x ≤ spatialMax g := le_spatialMax g x
  have hfg : f x - g x ≤ ‖f - g‖ := by
    calc
      f x - g x ≤ |f x - g x| := le_abs_self _
      _ = ‖(f - g) x‖ := by simp
      _ ≤ ‖f - g‖ := ContinuousMap.norm_coe_le_norm (f - g) x
  change f x - spatialMax g ≤ ‖f - g‖
  linarith

theorem abs_spatialMax_sub_le_norm (f g : C(X, ℝ)) :
    |spatialMax f - spatialMax g| ≤ ‖f - g‖ := by
  rw [abs_le]
  constructor
  · have h := spatialMax_sub_le_norm g f
    rw [norm_sub_rev g f] at h
    linarith
  · exact spatialMax_sub_le_norm f g

theorem dist_spatialMax_le (f g : C(X, ℝ)) :
    dist (spatialMax f) (spatialMax g) ≤ dist f g := by
  simpa [Real.dist_eq, dist_eq_norm] using abs_spatialMax_sub_le_norm f g

theorem lipschitzWith_one_spatialMax : LipschitzWith 1 (spatialMax : C(X, ℝ) → ℝ) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simpa using dist_spatialMax_le f g

theorem continuous_spatialMax : Continuous (spatialMax : C(X, ℝ) → ℝ) :=
  lipschitzWith_one_spatialMax.continuous

theorem Continuous.spatialMax_comp
    {Y : Type*} [TopologicalSpace Y] {u : Y → C(X, ℝ)} (hu : Continuous u) :
    Continuous (fun y => spatialMax (u y)) :=
  continuous_spatialMax.comp hu

/-- Comparing at a maximizer of the later slice bounds the increment of the
maximum envelope. -/
theorem spatialMax_sub_le_at_later_maximizer (u : ℝ → C(X, ℝ)) (s t : ℝ) :
    spatialMax (u s) - spatialMax (u t) ≤
      u s (spatialMaximizer (u s)) - u t (spatialMaximizer (u s)) := by
  have h := le_spatialMax (u t) (spatialMaximizer (u s))
  change u s (spatialMaximizer (u s)) - spatialMax (u t) ≤
    u s (spatialMaximizer (u s)) - u t (spatialMaximizer (u s))
  linarith

/-- A uniform right-slope bound for every spatial point transfers to the maximum
envelope at the same two times. -/
theorem spatialMax_slope_le_of_forall
    (u : ℝ → C(X, ℝ)) {t s C : ℝ} (hts : t < s)
    (hslope : ∀ x : X, (s - t)⁻¹ * (u s x - u t x) ≤ C) :
    (s - t)⁻¹ * (spatialMax (u s) - spatialMax (u t)) ≤ C := by
  let x := spatialMaximizer (u s)
  calc
    (s - t)⁻¹ * (spatialMax (u s) - spatialMax (u t)) ≤
        (s - t)⁻¹ * (u s x - u t x) :=
      mul_le_mul_of_nonneg_left (spatialMax_sub_le_at_later_maximizer u s t)
        (inv_nonneg.mpr (sub_nonneg.mpr hts.le))
    _ ≤ C := hslope x

/-- The right-limsup slope condition used by Grönwall transfers from a uniform
pointwise estimate to the spatial maximum envelope. -/
theorem spatialMax_frequently_slope_lt_of_eventually_uniform
    (u : ℝ → C(X, ℝ)) {t C : ℝ}
    (hslope : ∀ r, C < r →
      ∀ᶠ s in 𝓝[>] t, ∀ x : X, (s - t)⁻¹ * (u s x - u t x) < r) :
    ∀ r, C < r →
      ∃ᶠ s in 𝓝[>] t,
        (s - t)⁻¹ * (spatialMax (u s) - spatialMax (u t)) < r := by
  intro r hr
  have he := (hslope r hr).and
    (@self_mem_nhdsWithin ℝ _ t (Set.Ioi t))
  exact he.frequently.mono fun s hs => by
    let x := spatialMaximizer (u s)
    calc
      (s - t)⁻¹ * (spatialMax (u s) - spatialMax (u t)) ≤
          (s - t)⁻¹ * (u s x - u t x) :=
        mul_le_mul_of_nonneg_left (spatialMax_sub_le_at_later_maximizer u s t)
          (inv_nonneg.mpr (sub_nonneg.mpr hs.2.le))
      _ < r := hs.1 x

/-- Banach-valued differentiability in the sup norm supplies the uniform
pointwise slope estimate needed by `spatialMax_frequently_slope_lt_of_eventually_uniform`.
Consequently the upper right Dini slope of the maximum envelope is bounded by
the spatial maximum of the derivative field. -/
theorem spatialMax_frequently_slope_lt_of_hasDerivAt
    (u : ℝ → C(X, ℝ)) (u' : C(X, ℝ)) {t : ℝ} (hu : HasDerivAt u u' t) :
    ∀ r, spatialMax u' < r →
      ∃ᶠ s in 𝓝[>] t,
        (s - t)⁻¹ * (spatialMax (u s) - spatialMax (u t)) < r := by
  apply spatialMax_frequently_slope_lt_of_eventually_uniform
    (u := u) (t := t) (C := spatialMax u')
  intro r hr
  have hε : 0 < r - spatialMax u' := sub_pos.mpr hr
  have htend : Tendsto (slope u t) (𝓝[>] t) (𝓝 u') :=
    hu.tendsto_slope.mono_left (nhdsGT_le_nhdsNE t)
  have hnorm : Tendsto (fun s => ‖slope u t s - u'‖) (𝓝[>] t) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp htend
  filter_upwards [(tendsto_order.mp hnorm).2 (r - spatialMax u') hε] with s hs
  intro x
  have hpoint : slope u t s x - u' x < r - spatialMax u' := by
    calc
      slope u t s x - u' x ≤ |slope u t s x - u' x| := le_abs_self _
      _ = ‖(slope u t s - u') x‖ := by simp
      _ ≤ ‖slope u t s - u'‖ := ContinuousMap.norm_coe_le_norm _ x
      _ < r - spatialMax u' := hs
  have hx := le_spatialMax u' x
  simpa [slope_def_module] using (show slope u t s x < r by linarith)

/-- Danskin's upper right-Dini estimate for a compact spatial domain: the
maximum envelope is controlled by the largest time derivative among the
*current maximizers*.  This is the form compatible with a parabolic maximum
principle, since diffusion need only have a favorable sign at those points. -/
theorem spatialMax_eventually_slope_lt_of_hasDerivAt_at_maximizers
    (u : ℝ → C(X, ℝ)) (u' : C(X, ℝ)) {t : ℝ} (hu : HasDerivAt u u' t) :
    ∀ r, maxDerivativeAtMaximizers (u t) u' < r →
      ∀ᶠ s in 𝓝[>] t,
        (s - t)⁻¹ * (spatialMax (u s) - spatialMax (u t)) < r := by
  intro r hr
  let m := (maxDerivativeAtMaximizers (u t) u' + r) / 2
  have hCm : maxDerivativeAtMaximizers (u t) u' < m := by
    dsimp [m]
    linarith
  have hmr : m < r := by
    dsimp [m]
    linarith
  have hlater :
      ∀ᶠ s in 𝓝[>] t, u' (spatialMaximizer (u s)) < m :=
    eventually_apply_later_maximizer_lt_maxDerivative
      (hu.continuousAt.tendsto.mono_left inf_le_left) hCm
  have htend : Tendsto (slope u t) (𝓝[>] t) (𝓝 u') :=
    hu.tendsto_slope.mono_left (nhdsGT_le_nhdsNE t)
  have hnorm : Tendsto (fun s => ‖slope u t s - u'‖) (𝓝[>] t) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp htend
  have herr : ∀ᶠ s in 𝓝[>] t, ‖slope u t s - u'‖ < r - m :=
    (tendsto_order.mp hnorm).2 (r - m) (sub_pos.mpr hmr)
  have he := (hlater.and herr).and
    (@self_mem_nhdsWithin ℝ _ t (Set.Ioi t))
  exact he.mono fun s hs => by
    let x := spatialMaximizer (u s)
    have hpoint : slope u t s x < r := by
      have hdiff : slope u t s x - u' x < r - m := by
        calc
          slope u t s x - u' x ≤ |slope u t s x - u' x| := le_abs_self _
          _ = ‖(slope u t s - u') x‖ := by simp
          _ ≤ ‖slope u t s - u'‖ := ContinuousMap.norm_coe_le_norm _ x
          _ < r - m := hs.1.2
      have hux : u' x < m := hs.1.1
      linarith
    calc
      (s - t)⁻¹ * (spatialMax (u s) - spatialMax (u t)) ≤
          (s - t)⁻¹ * (u s x - u t x) :=
        mul_le_mul_of_nonneg_left (spatialMax_sub_le_at_later_maximizer u s t)
          (inv_nonneg.mpr (sub_nonneg.mpr hs.2.le))
      _ = slope u t s x := by simp [slope_def_module]
      _ < r := hpoint

/-- The frequently-small right-slope formulation consumed by Mathlib's
Grönwall fencing theorem, obtained from the stronger upper-Dini estimate. -/
theorem spatialMax_frequently_slope_lt_of_hasDerivAt_at_maximizers
    (u : ℝ → C(X, ℝ)) (u' : C(X, ℝ)) {t : ℝ} (hu : HasDerivAt u u' t) :
    ∀ r, maxDerivativeAtMaximizers (u t) u' < r →
      ∃ᶠ s in 𝓝[>] t,
        (s - t)⁻¹ * (spatialMax (u s) - spatialMax (u t)) < r := by
  intro r hr
  exact (spatialMax_eventually_slope_lt_of_hasDerivAt_at_maximizers
    u u' hu r hr).frequently

/-- A Grönwall estimate for the spatial maximum of a differentiable curve of
continuous fields.  No differentiability of the maximizing point, or even a
continuous choice of maximizing point, is assumed. -/
theorem spatialMax_le_exp_of_hasDerivAt
    {u u' : ℝ → C(X, ℝ)} {a b K : ℝ}
    (hu_cont : ContinuousOn u (Icc a b))
    (hu_deriv : ∀ t ∈ Ico a b, HasDerivAt u (u' t) t)
    (hproduction : ∀ t ∈ Ico a b, spatialMax (u' t) ≤ K * spatialMax (u t)) :
    ∀ t ∈ Icc a b,
      spatialMax (u t) ≤ spatialMax (u a) * Real.exp (K * (t - a)) := by
  intro t ht
  have h := le_gronwallBound_of_liminf_deriv_right_le
    (δ := spatialMax (u a)) (K := K) (ε := 0) (a := a) (b := b)
    (f := fun s => spatialMax (u s)) (f' := fun s => spatialMax (u' s))
    (continuous_spatialMax.comp_continuousOn hu_cont)
    (fun s hs => spatialMax_frequently_slope_lt_of_hasDerivAt
      (u := u) (u' := u' s) (t := s) (hu_deriv s hs))
    (le_refl (spatialMax (u a))) (by simpa using hproduction) t ht
  simpa [gronwallBound_ε0] using h

/-- The maximum-principle Grönwall estimate.  Its production hypothesis is
required only at points where the current field attains its maximum. -/
theorem spatialMax_le_exp_of_hasDerivAt_at_maximizers
    {u u' : ℝ → C(X, ℝ)} {a b K : ℝ}
    (hu_cont : ContinuousOn u (Icc a b))
    (hu_deriv : ∀ t ∈ Ico a b, HasDerivAt u (u' t) t)
    (hproduction : ∀ t ∈ Ico a b, ∀ x ∈ maximizerSet (u t),
      u' t x ≤ K * spatialMax (u t)) :
    ∀ t ∈ Icc a b,
      spatialMax (u t) ≤ spatialMax (u a) * Real.exp (K * (t - a)) := by
  intro t ht
  have h := le_gronwallBound_of_liminf_deriv_right_le
    (δ := spatialMax (u a)) (K := K) (ε := 0) (a := a) (b := b)
    (f := fun s => spatialMax (u s))
    (f' := fun s => maxDerivativeAtMaximizers (u s) (u' s))
    (continuous_spatialMax.comp_continuousOn hu_cont)
    (fun s hs => spatialMax_frequently_slope_lt_of_hasDerivAt_at_maximizers
      (u := u) (u' := u' s) (t := s) (hu_deriv s hs))
    (le_refl (spatialMax (u a)))
    (fun s hs => by
      rw [maxDerivativeAtMaximizers_le_iff]
      simpa using hproduction s hs) t ht
  simpa [gronwallBound_ε0] using h

/-- Variable-coefficient maximum-principle Grönwall estimate.  If `A' = k`,
then a maximizer-only production bound `u' ≤ k(t) max u` integrates to the
exponential factor `exp (A t - A a)`. -/
theorem spatialMax_le_exp_primitive_of_hasDerivAt_at_maximizers
    {u u' : ℝ → C(X, ℝ)} {k A : ℝ → ℝ} {a b : ℝ}
    (hu_cont : ContinuousOn u (Icc a b))
    (hu_deriv : ∀ t ∈ Ico a b, HasDerivAt u (u' t) t)
    (hA : ∀ t : ℝ, HasDerivAt A (k t) t)
    (hproduction : ∀ t ∈ Ico a b, ∀ x ∈ maximizerSet (u t),
      u' t x ≤ k t * spatialMax (u t)) :
    ∀ t ∈ Icc a b,
      spatialMax (u t) ≤ spatialMax (u a) * Real.exp (A t - A a) := by
  let c : ℝ → ℝ := fun t => Real.exp (-A t)
  let v : ℝ → C(X, ℝ) := fun t => c t • u t
  let v' : ℝ → C(X, ℝ) := fun t =>
    c t • u' t + (-k t * c t) • u t
  have hA_cont : Continuous A := continuous_iff_continuousAt.mpr fun t => (hA t).continuousAt
  have hc_cont : Continuous c := by
    dsimp [c]
    fun_prop
  have hc_deriv : ∀ t : ℝ, HasDerivAt c (-k t * c t) t := by
    intro t
    have h := (hA t).neg.exp
    convert h using 1 <;> dsimp [c]
    ring
  have hv_cont : ContinuousOn v (Icc a b) := by
    exact hc_cont.continuousOn.smul hu_cont
  have hv_deriv : ∀ t ∈ Ico a b, HasDerivAt v (v' t) t := by
    intro t ht
    exact (hc_deriv t).smul (hu_deriv t ht)
  have hv_production : ∀ t ∈ Ico a b, ∀ x ∈ maximizerSet (v t),
      v' t x ≤ (0 : ℝ) * spatialMax (v t) := by
    intro t ht x hx
    have hcpos : 0 < c t := by
      dsimp [c]
      exact Real.exp_pos _
    have hx_u : x ∈ maximizerSet (u t) := by
      change x ∈ maximizerSet (c t • u t) at hx
      rwa [maximizerSet_const_smul (u t) hcpos] at hx
    have hpoint := hproduction t ht x hx_u
    have hx_eq : u t x = spatialMax (u t) := hx_u
    dsimp [v']
    simp only [zero_mul]
    rw [hx_eq]
    nlinarith [mul_nonneg hcpos.le
      (sub_nonneg.mpr (show k t * spatialMax (u t) - u' t x ≥ 0 by linarith))]
  have hv_bound := spatialMax_le_exp_of_hasDerivAt_at_maximizers
    (u := v) (u' := v') (a := a) (b := b) (K := 0)
    hv_cont hv_deriv hv_production
  intro t ht
  have hvt := hv_bound t ht
  rw [spatialMax_const_smul (u t) (Real.exp_pos (-A t)).le,
    spatialMax_const_smul (u a) (Real.exp_pos (-A a)).le] at hvt
  simp only [zero_mul, Real.exp_zero, mul_one] at hvt
  calc
    spatialMax (u t) = Real.exp (A t) *
        (Real.exp (-A t) * spatialMax (u t)) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    _ ≤ Real.exp (A t) * (Real.exp (-A a) * spatialMax (u a)) :=
      mul_le_mul_of_nonneg_left hvt (Real.exp_nonneg _)
    _ = (Real.exp (A t) * Real.exp (-A a)) * spatialMax (u a) := by ring
    _ = Real.exp (A t + -A a) * spatialMax (u a) := by rw [Real.exp_add]
    _ = spatialMax (u a) * Real.exp (A t - A a) := by
      rw [sub_eq_add_neg, mul_comm]

/-- Continuous-rate form with the primitive written as an interval integral. -/
theorem spatialMax_le_exp_intervalIntegral_of_hasDerivAt_at_maximizers
    {u u' : ℝ → C(X, ℝ)} {k : ℝ → ℝ} {a b : ℝ}
    (hu_cont : ContinuousOn u (Icc a b))
    (hu_deriv : ∀ t ∈ Ico a b, HasDerivAt u (u' t) t)
    (hk : Continuous k)
    (hproduction : ∀ t ∈ Ico a b, ∀ x ∈ maximizerSet (u t),
      u' t x ≤ k t * spatialMax (u t)) :
    ∀ t ∈ Icc a b,
      spatialMax (u t) ≤ spatialMax (u a) * Real.exp (∫ s in a..t, k s) := by
  let A : ℝ → ℝ := fun t => ∫ s in a..t, k s
  have hA : ∀ t : ℝ, HasDerivAt A (k t) t := fun t =>
    (hk.integral_hasStrictDerivAt a t).hasDerivAt
  have h := spatialMax_le_exp_primitive_of_hasDerivAt_at_maximizers
    (u := u) (u' := u') (k := k) (A := A) (a := a) (b := b)
    hu_cont hu_deriv hA hproduction
  simpa [A] using h
