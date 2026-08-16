import NSFormal.MaxEnvelope
import NSFormal.Vorticity

/-!
# Squared-vorticity maximum principle

This file assembles the corrected scalar vorticity equation with the compact-space
Danskin theorem.  All spatial differential obligations remain explicit:

* transport vanishes at a current spatial maximum;
* the scalar Laplacian is nonpositive there;
* the squared-gradient dissipation is nonnegative;
* the stretching production has the stated bound.

In particular, none of these facts is silently inferred along a material trajectory.
-/

open Filter Set
open scoped Topology

noncomputable section

variable {X : Type*} [TopologicalSpace X]
variable {E : Type*} [NormedAddCommGroup E]

/-- Half squared magnitude, pointwise, as a continuous scalar field. -/
def vorticityEnergyField (w : C(X, E)) : C(X, ℝ) :=
  ⟨fun x => vorticityEnergy (w x), by
    unfold vorticityEnergy
    fun_prop⟩

@[simp]
theorem vorticityEnergyField_apply (w : C(X, E)) (x : X) :
    vorticityEnergyField w x = vorticityEnergy (w x) := rfl

theorem vorticityEnergyField_nonneg (w : C(X, E)) (x : X) :
    0 ≤ vorticityEnergyField w x :=
  vorticityEnergy_nonneg (w x)

variable [CompactSpace X] [Nonempty X]

variable [InnerProductSpace ℝ E]

/-- The pointwise real inner product as a bilinear map on continuous fields. -/
def pointwiseInnerLinearMap :
    C(X, E) →ₗ[ℝ] C(X, E) →ₗ[ℝ] C(X, ℝ) :=
  LinearMap.mk₂ ℝ
    (fun f g => ⟨fun x => inner ℝ (f x) (g x), by fun_prop⟩)
    (by intro f g h; ext x; simp [inner_add_left])
    (by intro c f g; ext x; simp [real_inner_smul_left])
    (by intro f g h; ext x; simp [inner_add_right])
    (by intro c f g; ext x; simp [real_inner_smul_right])

/-- The pointwise inner product is bounded in the sup norm. -/
def pointwiseInnerCLM : C(X, E) →L[ℝ] C(X, E) →L[ℝ] C(X, ℝ) :=
  LinearMap.mkContinuous₂ pointwiseInnerLinearMap 1 fun f g => by
    rw [one_mul, ContinuousMap.norm_le_of_nonempty]
    intro x
    calc
      ‖pointwiseInnerLinearMap f g x‖ ≤ ‖f x‖ * ‖g x‖ := norm_inner_le_norm _ _
      _ ≤ ‖f‖ * ‖g‖ := mul_le_mul (ContinuousMap.norm_coe_le_norm f x)
        (ContinuousMap.norm_coe_le_norm g x) (norm_nonneg _) (norm_nonneg _)

@[simp]
theorem pointwiseInnerCLM_apply (f g : C(X, E)) (x : X) :
    pointwiseInnerCLM f g x = inner ℝ (f x) (g x) := rfl

/-- The pointwise energy derivative associated to a vorticity field and its
time derivative. -/
def vorticityEnergyDerivativeField (w w' : C(X, E)) : C(X, ℝ) :=
  pointwiseInnerCLM w w'

@[simp]
theorem vorticityEnergyDerivativeField_apply (w w' : C(X, E)) (x : X) :
    vorticityEnergyDerivativeField w w' x = inner ℝ (w x) (w' x) := rfl

/-- Sup-norm differentiability of a vorticity field implies sup-norm
differentiability of its half-squared-magnitude field, including at zeros. -/
theorem HasDerivAt.vorticityEnergyField
    {ω : ℝ → C(X, E)} {ω' : C(X, E)} {t : ℝ} (hω : HasDerivAt ω ω' t) :
    HasDerivAt (fun s => vorticityEnergyField (ω s))
      (vorticityEnergyDerivativeField (ω t) ω') t := by
  have hpair := pointwiseInnerCLM.hasDerivAt_of_bilinear
    (u := ω) (v := ω) (u' := ω') (v' := ω') (fun _ => hω) (fun _ => hω)
  have hscaled := HasDerivAt.const_smul (2 : ℝ)⁻¹ hpair
  have hfun :
      (2 : ℝ)⁻¹ • (fun s => pointwiseInnerCLM (ω s) (ω s)) =
        fun s => _root_.vorticityEnergyField (ω s) := by
    funext s
    ext x
    simp [vorticityEnergy, pointwiseInnerCLM_apply, div_eq_mul_inv]
    ring
  have hderiv :
      (2 : ℝ)⁻¹ •
          (pointwiseInnerCLM (ω t) ω' + pointwiseInnerCLM ω' (ω t)) =
        vorticityEnergyDerivativeField (ω t) ω' := by
    ext x
    simp [vorticityEnergyDerivativeField, pointwiseInnerCLM_apply, real_inner_comm]
    ring
  rw [hfun] at hscaled
  exact hscaled.congr_deriv hderiv

/-- The pointwise half-squared-norm construction is continuous for the sup
norm on a compact spatial domain. -/
theorem continuous_vorticityEnergyField :
    Continuous (_root_.vorticityEnergyField : C(X, E) → C(X, ℝ)) := by
  have hfun :
      (_root_.vorticityEnergyField : C(X, E) → C(X, ℝ)) =
        fun w => (2 : ℝ)⁻¹ • pointwiseInnerCLM w w := by
    funext w
    ext x
    simp [vorticityEnergy, pointwiseInnerCLM_apply, div_eq_mul_inv]
    ring
  rw [hfun]
  fun_prop

omit [InnerProductSpace ℝ E] in
/-- The corrected maximum-principle closure for half squared vorticity.

`lapEnergy` represents `Δ(‖ω‖²/2)`, while `gradVorticitySq` represents
`|∇ω|²`.  Thus `lapEnergy - gradVorticitySq` is exactly the scalar obtained
from pairing `ω` with `Δω`. -/
theorem spatialMax_vorticityEnergy_le_exp
    {ω : ℝ → C(X, E)}
    {energyDeriv stretching lapEnergy gradVorticitySq transportEnergy :
      ℝ → C(X, ℝ)}
    {a b ν K : ℝ}
    (henergy_cont : ContinuousOn (fun t => vorticityEnergyField (ω t)) (Icc a b))
    (henergy_deriv : ∀ t ∈ Ico a b,
      HasDerivAt (fun s => vorticityEnergyField (ω s)) (energyDeriv t) t)
    (hν : 0 ≤ ν)
    (hevolution : ∀ t ∈ Ico a b, ∀ x : X,
      energyDeriv t x = stretching t x +
        ν * (lapEnergy t x - gradVorticitySq t x) - transportEnergy t x)
    (hstretch : ∀ t ∈ Ico a b, ∀ x ∈ maximizerSet (vorticityEnergyField (ω t)),
      stretching t x ≤ K * vorticityEnergyField (ω t) x)
    (hlap : ∀ t ∈ Ico a b, ∀ x ∈ maximizerSet (vorticityEnergyField (ω t)),
      lapEnergy t x ≤ 0)
    (hgrad : ∀ t ∈ Ico a b, ∀ x ∈ maximizerSet (vorticityEnergyField (ω t)),
      0 ≤ gradVorticitySq t x)
    (htransport : ∀ t ∈ Ico a b, ∀ x ∈ maximizerSet (vorticityEnergyField (ω t)),
      transportEnergy t x = 0) :
    ∀ t ∈ Icc a b,
      spatialMax (vorticityEnergyField (ω t)) ≤
        spatialMax (vorticityEnergyField (ω a)) * Real.exp (K * (t - a)) := by
  apply spatialMax_le_exp_of_hasDerivAt_at_maximizers
    (u := fun t => vorticityEnergyField (ω t)) (u' := energyDeriv)
    henergy_cont henergy_deriv
  intro t ht x hx
  have hdiff : ν * (lapEnergy t x - gradVorticitySq t x) ≤ 0 := by
    apply mul_nonpos_of_nonneg_of_nonpos hν
    linarith [hlap t ht x hx, hgrad t ht x hx]
  calc
    energyDeriv t x = stretching t x +
        ν * (lapEnergy t x - gradVorticitySq t x) - transportEnergy t x :=
      hevolution t ht x
    _ ≤ stretching t x := by rw [htransport t ht x hx]; linarith
    _ ≤ K * vorticityEnergyField (ω t) x := hstretch t ht x hx
    _ = K * spatialMax (vorticityEnergyField (ω t)) := by
      rw [show vorticityEnergyField (ω t) x =
        spatialMax (vorticityEnergyField (ω t)) from hx]

/-- Maximum-principle closure stated directly for a differentiable vorticity
curve.  The scalar energy derivative is no longer an independent hypothesis;
it is definitionally paired from `ω` and `ω'`. -/
theorem spatialMax_vorticityEnergy_le_exp_of_vorticity_deriv
    {ω ω' : ℝ → C(X, E)}
    {stretching lapEnergy gradVorticitySq transportEnergy : ℝ → C(X, ℝ)}
    {a b ν K : ℝ}
    (hω_cont : ContinuousOn ω (Icc a b))
    (hω_deriv : ∀ t ∈ Ico a b, HasDerivAt ω (ω' t) t)
    (hν : 0 ≤ ν)
    (hevolution : ∀ t ∈ Ico a b, ∀ x : X,
      vorticityEnergyDerivativeField (ω t) (ω' t) x = stretching t x +
        ν * (lapEnergy t x - gradVorticitySq t x) - transportEnergy t x)
    (hstretch : ∀ t ∈ Ico a b, ∀ x ∈ maximizerSet (vorticityEnergyField (ω t)),
      stretching t x ≤ K * vorticityEnergyField (ω t) x)
    (hlap : ∀ t ∈ Ico a b, ∀ x ∈ maximizerSet (vorticityEnergyField (ω t)),
      lapEnergy t x ≤ 0)
    (hgrad : ∀ t ∈ Ico a b, ∀ x ∈ maximizerSet (vorticityEnergyField (ω t)),
      0 ≤ gradVorticitySq t x)
    (htransport : ∀ t ∈ Ico a b, ∀ x ∈ maximizerSet (vorticityEnergyField (ω t)),
      transportEnergy t x = 0) :
    ∀ t ∈ Icc a b,
      spatialMax (vorticityEnergyField (ω t)) ≤
        spatialMax (vorticityEnergyField (ω a)) * Real.exp (K * (t - a)) := by
  exact spatialMax_vorticityEnergy_le_exp
    (energyDeriv := fun t => vorticityEnergyDerivativeField (ω t) (ω' t))
    (continuous_vorticityEnergyField.comp_continuousOn hω_cont)
    (fun t ht => (hω_deriv t ht).vorticityEnergyField) hν hevolution
    hstretch hlap hgrad htransport

/-- Variable-coefficient form driven by a primitive `A' = k`.  This is the
version suitable for an integrated strain budget. -/
theorem spatialMax_vorticityEnergy_le_exp_primitive_of_vorticity_deriv
    {ω ω' : ℝ → C(X, E)}
    {stretching lapEnergy gradVorticitySq transportEnergy : ℝ → C(X, ℝ)}
    {k A : ℝ → ℝ} {a b ν : ℝ}
    (hω_cont : ContinuousOn ω (Icc a b))
    (hω_deriv : ∀ t ∈ Ico a b, HasDerivAt ω (ω' t) t)
    (hA : ∀ t : ℝ, HasDerivAt A (k t) t)
    (hν : 0 ≤ ν)
    (hevolution : ∀ t ∈ Ico a b, ∀ x : X,
      vorticityEnergyDerivativeField (ω t) (ω' t) x = stretching t x +
        ν * (lapEnergy t x - gradVorticitySq t x) - transportEnergy t x)
    (hstretch : ∀ t ∈ Ico a b, ∀ x ∈ maximizerSet (vorticityEnergyField (ω t)),
      stretching t x ≤ k t * vorticityEnergyField (ω t) x)
    (hlap : ∀ t ∈ Ico a b, ∀ x ∈ maximizerSet (vorticityEnergyField (ω t)),
      lapEnergy t x ≤ 0)
    (hgrad : ∀ t ∈ Ico a b, ∀ x ∈ maximizerSet (vorticityEnergyField (ω t)),
      0 ≤ gradVorticitySq t x)
    (htransport : ∀ t ∈ Ico a b, ∀ x ∈ maximizerSet (vorticityEnergyField (ω t)),
      transportEnergy t x = 0) :
    ∀ t ∈ Icc a b,
      spatialMax (vorticityEnergyField (ω t)) ≤
        spatialMax (vorticityEnergyField (ω a)) * Real.exp (A t - A a) := by
  apply spatialMax_le_exp_primitive_of_hasDerivAt_at_maximizers
    (u := fun t => vorticityEnergyField (ω t))
    (u' := fun t => vorticityEnergyDerivativeField (ω t) (ω' t))
    (k := k) (A := A)
    (continuous_vorticityEnergyField.comp_continuousOn hω_cont)
    (fun t ht => (hω_deriv t ht).vorticityEnergyField) hA
  intro t ht x hx
  have hdiff : ν * (lapEnergy t x - gradVorticitySq t x) ≤ 0 := by
    apply mul_nonpos_of_nonneg_of_nonpos hν
    linarith [hlap t ht x hx, hgrad t ht x hx]
  calc
    vorticityEnergyDerivativeField (ω t) (ω' t) x = stretching t x +
        ν * (lapEnergy t x - gradVorticitySq t x) - transportEnergy t x :=
      hevolution t ht x
    _ ≤ stretching t x := by rw [htransport t ht x hx]; linarith
    _ ≤ k t * vorticityEnergyField (ω t) x := hstretch t ht x hx
    _ = k t * spatialMax (vorticityEnergyField (ω t)) := by
      rw [show vorticityEnergyField (ω t) x =
        spatialMax (vorticityEnergyField (ω t)) from hx]
