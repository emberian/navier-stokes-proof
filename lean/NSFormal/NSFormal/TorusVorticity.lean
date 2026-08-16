import NSFormal.PeriodicCalculus
import NSFormal.Budget

/-!
# Torus vorticity maximum principle

This specializes the abstract compact maximum principle to the concrete period-`2π`
three-torus.  The transport, Laplacian, and gradient signs are derived from the
periodic lift; they are not hypotheses of the final theorem.  What remains explicit
is the scalar vorticity-energy equation and the stretching estimate.
-/

open Set
open scoped RealInnerProductSpace Topology

noncomputable section

theorem ContDiff.torusLift_vorticityEnergyField
    {w : C(Torus3, Vec3)} (hw : ContDiff ℝ 2 (torusLift w)) :
    ContDiff ℝ 2 (torusLift (vorticityEnergyField w)) := by
  have h := ContDiff.const_smul (2 : ℝ)⁻¹ (hw.norm_sq ℝ)
  change ContDiff ℝ 2 (fun y => vorticityEnergy (w (torus3Mk y)))
  simpa [torusLift, vorticityEnergy, div_eq_mul_inv, mul_comm] using h

/-- A corrected maximum-principle estimate on the actual three-torus.  The fields
`lapEnergy`, `gradVorticitySq`, and `transportEnergy` are identified with their
periodic-lift definitions; their required signs then follow as theorems. -/
theorem torus_spatialMax_vorticityEnergy_le_exp
    {ω ω' velocity : ℝ → C(Torus3, Vec3)}
    {stretching lapEnergy gradVorticitySq transportEnergy :
      ℝ → C(Torus3, ℝ)}
    {a b ν K : ℝ}
    (hω_cont : ContinuousOn ω (Icc a b))
    (hω_deriv : ∀ t ∈ Ico a b, HasDerivAt ω (ω' t) t)
    (hω_space : ∀ t ∈ Ico a b, ContDiff ℝ 2 (torusLift (ω t)))
    (hν : 0 ≤ ν)
    (hevolution : ∀ t ∈ Ico a b, ∀ x : Torus3,
      vorticityEnergyDerivativeField (ω t) (ω' t) x = stretching t x +
        ν * (lapEnergy t x - gradVorticitySq t x) - transportEnergy t x)
    (hstretch : ∀ t ∈ Ico a b,
      ∀ x ∈ maximizerSet (vorticityEnergyField (ω t)),
        stretching t x ≤ K * vorticityEnergyField (ω t) x)
    (hlap_def : ∀ t ∈ Ico a b, ∀ x : Torus3,
      lapEnergy t x = torusLiftLaplacian (vorticityEnergyField (ω t))
        (torus3Representative x))
    (hgrad_def : ∀ t ∈ Ico a b, ∀ x : Torus3,
      gradVorticitySq t x = torusLiftGradientSq (ω t) (torus3Representative x))
    (htransport_def : ∀ t ∈ Ico a b, ∀ x : Torus3,
      transportEnergy t x =
        fderiv ℝ (torusLift (vorticityEnergyField (ω t)))
          (torus3Representative x) (torusLift (velocity t) (torus3Representative x))) :
    ∀ t ∈ Icc a b,
      spatialMax (vorticityEnergyField (ω t)) ≤
        spatialMax (vorticityEnergyField (ω a)) * Real.exp (K * (t - a)) := by
  apply spatialMax_vorticityEnergy_le_exp_of_vorticity_deriv
    hω_cont hω_deriv hν hevolution hstretch
  · intro t ht x hx
    rw [hlap_def t ht x]
    exact torusLiftLaplacian_nonpos_at_maximizer
      (vorticityEnergyField (ω t)) hx (hω_space t ht).torusLift_vorticityEnergyField
  · intro t ht x _hx
    rw [hgrad_def t ht x]
    exact torusLiftGradientSq_nonneg (ω t) (torus3Representative x)
  · intro t ht x hx
    rw [htransport_def t ht x]
    exact fderiv_torusLift_apply_eq_zero_at_maximizer
      (vorticityEnergyField (ω t)) hx _

/-- Variable-coefficient torus estimate suitable for a time-integrated strain
budget `A' = k`. -/
theorem torus_spatialMax_vorticityEnergy_le_exp_primitive
    {ω ω' velocity : ℝ → C(Torus3, Vec3)}
    {stretching lapEnergy gradVorticitySq transportEnergy : ℝ → C(Torus3, ℝ)}
    {k A : ℝ → ℝ} {a b ν : ℝ}
    (hω_cont : ContinuousOn ω (Icc a b))
    (hω_deriv : ∀ t ∈ Ico a b, HasDerivAt ω (ω' t) t)
    (hω_space : ∀ t ∈ Ico a b, ContDiff ℝ 2 (torusLift (ω t)))
    (hA : ∀ t : ℝ, HasDerivAt A (k t) t)
    (hν : 0 ≤ ν)
    (hevolution : ∀ t ∈ Ico a b, ∀ x : Torus3,
      vorticityEnergyDerivativeField (ω t) (ω' t) x = stretching t x +
        ν * (lapEnergy t x - gradVorticitySq t x) - transportEnergy t x)
    (hstretch : ∀ t ∈ Ico a b,
      ∀ x ∈ maximizerSet (vorticityEnergyField (ω t)),
        stretching t x ≤ k t * vorticityEnergyField (ω t) x)
    (hlap_def : ∀ t ∈ Ico a b, ∀ x : Torus3,
      lapEnergy t x = torusLiftLaplacian (vorticityEnergyField (ω t))
        (torus3Representative x))
    (hgrad_def : ∀ t ∈ Ico a b, ∀ x : Torus3,
      gradVorticitySq t x = torusLiftGradientSq (ω t) (torus3Representative x))
    (htransport_def : ∀ t ∈ Ico a b, ∀ x : Torus3,
      transportEnergy t x =
        fderiv ℝ (torusLift (vorticityEnergyField (ω t)))
          (torus3Representative x) (torusLift (velocity t) (torus3Representative x))) :
    ∀ t ∈ Icc a b,
      spatialMax (vorticityEnergyField (ω t)) ≤
        spatialMax (vorticityEnergyField (ω a)) * Real.exp (A t - A a) := by
  apply spatialMax_vorticityEnergy_le_exp_primitive_of_vorticity_deriv
    hω_cont hω_deriv hA hν hevolution hstretch
  · intro t ht x hx
    rw [hlap_def t ht x]
    exact torusLiftLaplacian_nonpos_at_maximizer
      (vorticityEnergyField (ω t)) hx (hω_space t ht).torusLift_vorticityEnergyField
  · intro t ht x _hx
    rw [hgrad_def t ht x]
    exact torusLiftGradientSq_nonneg (ω t) (torus3Representative x)
  · intro t ht x hx
    rw [htransport_def t ht x]
    exact fderiv_torusLift_apply_eq_zero_at_maximizer
      (vorticityEnergyField (ω t)) hx _

/-- The same torus estimate starting from the vector vorticity equation.  The
scalar energy equation consumed above is derived here by pairing the vector PDE
with `ω` and applying the checked periodic diffusion identity. -/
theorem torus_spatialMax_vorticityEnergy_le_exp_of_vector_equation
    {ω ω' velocity stretchingVector lapVorticity transportVector :
      ℝ → C(Torus3, Vec3)}
    {stretchingEnergy lapEnergy gradVorticitySq transportEnergy :
      ℝ → C(Torus3, ℝ)}
    {a b ν K : ℝ}
    (hω_cont : ContinuousOn ω (Icc a b))
    (hω_deriv : ∀ t ∈ Ico a b, HasDerivAt ω (ω' t) t)
    (hω_space : ∀ t ∈ Ico a b, ContDiff ℝ 2 (torusLift (ω t)))
    (hν : 0 ≤ ν)
    (hvorticity : ∀ t ∈ Ico a b, ∀ x : Torus3,
      ω' t x = stretchingVector t x + ν • lapVorticity t x - transportVector t x)
    (hstretch_def : ∀ t ∈ Ico a b, ∀ x : Torus3,
      stretchingEnergy t x = inner ℝ (ω t x) (stretchingVector t x))
    (hlapVorticity_def : ∀ t ∈ Ico a b, ∀ x : Torus3,
      lapVorticity t x =
        torusLiftVectorLaplacian (ω t) (torus3Representative x))
    (hlapEnergy_def : ∀ t ∈ Ico a b, ∀ x : Torus3,
      lapEnergy t x = torusLiftLaplacian (vorticityEnergyField (ω t))
        (torus3Representative x))
    (hgrad_def : ∀ t ∈ Ico a b, ∀ x : Torus3,
      gradVorticitySq t x = torusLiftGradientSq (ω t) (torus3Representative x))
    (htransport_pair : ∀ t ∈ Ico a b, ∀ x : Torus3,
      transportEnergy t x = inner ℝ (ω t x) (transportVector t x))
    (htransport_def : ∀ t ∈ Ico a b, ∀ x : Torus3,
      transportEnergy t x =
        fderiv ℝ (torusLift (vorticityEnergyField (ω t)))
          (torus3Representative x) (torusLift (velocity t) (torus3Representative x)))
    (hstretch : ∀ t ∈ Ico a b,
      ∀ x ∈ maximizerSet (vorticityEnergyField (ω t)),
        stretchingEnergy t x ≤ K * vorticityEnergyField (ω t) x) :
    ∀ t ∈ Icc a b,
      spatialMax (vorticityEnergyField (ω t)) ≤
        spatialMax (vorticityEnergyField (ω a)) * Real.exp (K * (t - a)) := by
  apply torus_spatialMax_vorticityEnergy_le_exp
    hω_cont hω_deriv hω_space hν (hstretch := hstretch)
    (hlap_def := hlapEnergy_def) (hgrad_def := hgrad_def)
    (htransport_def := htransport_def)
  intro t ht x
  have hdiff := inner_torusLiftVectorLaplacian_eq
    (ω t) (torus3Representative x) (hω_space t ht)
  rw [vorticityEnergyDerivativeField_apply, hvorticity t ht x,
    inner_sub_right, inner_add_right, real_inner_smul_right,
    ← hstretch_def t ht x, hlapVorticity_def t ht x,
    ← htransport_pair t ht x]
  rw [show ω t x = torusLift (ω t) (torus3Representative x) by simp [torusLift],
    hdiff, ← hlapEnergy_def t ht x,
    ← hgrad_def t ht x]

/-- Variable-coefficient maximum estimate derived directly from the vector
vorticity equation. -/
theorem torus_spatialMax_vorticityEnergy_le_exp_primitive_of_vector_equation
    {ω ω' velocity stretchingVector lapVorticity transportVector :
      ℝ → C(Torus3, Vec3)}
    {stretchingEnergy lapEnergy gradVorticitySq transportEnergy :
      ℝ → C(Torus3, ℝ)}
    {k A : ℝ → ℝ} {a b ν : ℝ}
    (hω_cont : ContinuousOn ω (Icc a b))
    (hω_deriv : ∀ t ∈ Ico a b, HasDerivAt ω (ω' t) t)
    (hω_space : ∀ t ∈ Ico a b, ContDiff ℝ 2 (torusLift (ω t)))
    (hA : ∀ t : ℝ, HasDerivAt A (k t) t)
    (hν : 0 ≤ ν)
    (hvorticity : ∀ t ∈ Ico a b, ∀ x : Torus3,
      ω' t x = stretchingVector t x + ν • lapVorticity t x - transportVector t x)
    (hstretch_def : ∀ t ∈ Ico a b, ∀ x : Torus3,
      stretchingEnergy t x = inner ℝ (ω t x) (stretchingVector t x))
    (hlapVorticity_def : ∀ t ∈ Ico a b, ∀ x : Torus3,
      lapVorticity t x = torusLiftVectorLaplacian (ω t) (torus3Representative x))
    (hlapEnergy_def : ∀ t ∈ Ico a b, ∀ x : Torus3,
      lapEnergy t x = torusLiftLaplacian (vorticityEnergyField (ω t))
        (torus3Representative x))
    (hgrad_def : ∀ t ∈ Ico a b, ∀ x : Torus3,
      gradVorticitySq t x = torusLiftGradientSq (ω t) (torus3Representative x))
    (htransport_pair : ∀ t ∈ Ico a b, ∀ x : Torus3,
      transportEnergy t x = inner ℝ (ω t x) (transportVector t x))
    (htransport_def : ∀ t ∈ Ico a b, ∀ x : Torus3,
      transportEnergy t x =
        fderiv ℝ (torusLift (vorticityEnergyField (ω t)))
          (torus3Representative x) (torusLift (velocity t) (torus3Representative x)))
    (hstretch : ∀ t ∈ Ico a b,
      ∀ x ∈ maximizerSet (vorticityEnergyField (ω t)),
        stretchingEnergy t x ≤ k t * vorticityEnergyField (ω t) x) :
    ∀ t ∈ Icc a b,
      spatialMax (vorticityEnergyField (ω t)) ≤
        spatialMax (vorticityEnergyField (ω a)) * Real.exp (A t - A a) := by
  apply torus_spatialMax_vorticityEnergy_le_exp_primitive
    hω_cont hω_deriv hω_space hA hν (hstretch := hstretch)
    (hlap_def := hlapEnergy_def) (hgrad_def := hgrad_def)
    (htransport_def := htransport_def)
  intro t ht x
  have hdiff := inner_torusLiftVectorLaplacian_eq
    (ω t) (torus3Representative x) (hω_space t ht)
  rw [vorticityEnergyDerivativeField_apply, hvorticity t ht x,
    inner_sub_right, inner_add_right, real_inner_smul_right,
    ← hstretch_def t ht x, hlapVorticity_def t ht x,
    ← htransport_pair t ht x]
  rw [show ω t x = torusLift (ω t) (torus3Representative x) by simp [torusLift],
    hdiff, ← hlapEnergy_def t ht x, ← hgrad_def t ht x]

/-- Continuous-rate version of the torus vector-vorticity estimate, with the
exponent represented by the actual time integral of the stretching rate. -/
theorem torus_spatialMax_vorticityEnergy_le_exp_intervalIntegral_of_vector_equation
    {ω ω' velocity stretchingVector lapVorticity transportVector :
      ℝ → C(Torus3, Vec3)}
    {stretchingEnergy lapEnergy gradVorticitySq transportEnergy :
      ℝ → C(Torus3, ℝ)}
    {k : ℝ → ℝ} {a b ν : ℝ}
    (hω_cont : ContinuousOn ω (Icc a b))
    (hω_deriv : ∀ t ∈ Ico a b, HasDerivAt ω (ω' t) t)
    (hω_space : ∀ t ∈ Ico a b, ContDiff ℝ 2 (torusLift (ω t)))
    (hk : Continuous k)
    (hν : 0 ≤ ν)
    (hvorticity : ∀ t ∈ Ico a b, ∀ x : Torus3,
      ω' t x = stretchingVector t x + ν • lapVorticity t x - transportVector t x)
    (hstretch_def : ∀ t ∈ Ico a b, ∀ x : Torus3,
      stretchingEnergy t x = inner ℝ (ω t x) (stretchingVector t x))
    (hlapVorticity_def : ∀ t ∈ Ico a b, ∀ x : Torus3,
      lapVorticity t x =
        torusLiftVectorLaplacian (ω t) (torus3Representative x))
    (hlapEnergy_def : ∀ t ∈ Ico a b, ∀ x : Torus3,
      lapEnergy t x = torusLiftLaplacian (vorticityEnergyField (ω t))
        (torus3Representative x))
    (hgrad_def : ∀ t ∈ Ico a b, ∀ x : Torus3,
      gradVorticitySq t x = torusLiftGradientSq (ω t) (torus3Representative x))
    (htransport_pair : ∀ t ∈ Ico a b, ∀ x : Torus3,
      transportEnergy t x = inner ℝ (ω t x) (transportVector t x))
    (htransport_def : ∀ t ∈ Ico a b, ∀ x : Torus3,
      transportEnergy t x =
        fderiv ℝ (torusLift (vorticityEnergyField (ω t)))
          (torus3Representative x) (torusLift (velocity t) (torus3Representative x)))
    (hstretch : ∀ t ∈ Ico a b,
      ∀ x ∈ maximizerSet (vorticityEnergyField (ω t)),
        stretchingEnergy t x ≤ k t * vorticityEnergyField (ω t) x) :
    ∀ t ∈ Icc a b,
      spatialMax (vorticityEnergyField (ω t)) ≤
        spatialMax (vorticityEnergyField (ω a)) *
          Real.exp (∫ s in a..t, k s) := by
  let A : ℝ → ℝ := fun t => ∫ s in a..t, k s
  have hA : ∀ t : ℝ, HasDerivAt A (k t) t := fun t =>
    (hk.integral_hasStrictDerivAt a t).hasDerivAt
  have h := torus_spatialMax_vorticityEnergy_le_exp_primitive_of_vector_equation
    hω_cont hω_deriv hω_space hA hν hvorticity hstretch_def
    hlapVorticity_def hlapEnergy_def hgrad_def htransport_pair htransport_def hstretch
  simpa [A] using h

/-- Repaired finite-time closure of the vorticity maximum argument.  An
enstrophy budget and a pointwise rate estimate give an explicit exponential
bound for half the squared vorticity maximum.  Viscous diffusion is retained
throughout the vector vorticity equation. -/
theorem torus_spatialMax_vorticityEnergy_le_exp_strain_budget
    {ω ω' velocity stretchingVector lapVorticity transportVector :
      ℝ → C(Torus3, Vec3)}
    {stretchingEnergy lapEnergy gradVorticitySq transportEnergy :
      ℝ → C(Torus3, ℝ)}
    {Ω γ : ℝ → ℝ} {T B C5 C1 C0 ν : ℝ}
    (hT : 0 ≤ T) (hC5 : 0 ≤ C5) (hC1 : 0 ≤ C1)
    (hΩ_cont : Continuous Ω) (hγ_cont : Continuous γ)
    (hΩ_nonneg : ∀ t, 0 ≤ Ω t)
    (hbudget : (∫ t in Set.Icc 0 T, Ω t) ≤ B)
    (hγ_bound : ∀ t ∈ Set.Icc 0 T,
      γ t ≤ C5 * Ω t ^ ((5 : ℝ) / 6) + C1 * Ω t + C0)
    (hω_cont : ContinuousOn ω (Icc 0 T))
    (hω_deriv : ∀ t ∈ Ico 0 T, HasDerivAt ω (ω' t) t)
    (hω_space : ∀ t ∈ Ico 0 T, ContDiff ℝ 2 (torusLift (ω t)))
    (hν : 0 ≤ ν)
    (hvorticity : ∀ t ∈ Ico 0 T, ∀ x : Torus3,
      ω' t x = stretchingVector t x + ν • lapVorticity t x - transportVector t x)
    (hstretch_def : ∀ t ∈ Ico 0 T, ∀ x : Torus3,
      stretchingEnergy t x = inner ℝ (ω t x) (stretchingVector t x))
    (hlapVorticity_def : ∀ t ∈ Ico 0 T, ∀ x : Torus3,
      lapVorticity t x =
        torusLiftVectorLaplacian (ω t) (torus3Representative x))
    (hlapEnergy_def : ∀ t ∈ Ico 0 T, ∀ x : Torus3,
      lapEnergy t x = torusLiftLaplacian (vorticityEnergyField (ω t))
        (torus3Representative x))
    (hgrad_def : ∀ t ∈ Ico 0 T, ∀ x : Torus3,
      gradVorticitySq t x = torusLiftGradientSq (ω t) (torus3Representative x))
    (htransport_pair : ∀ t ∈ Ico 0 T, ∀ x : Torus3,
      transportEnergy t x = inner ℝ (ω t x) (transportVector t x))
    (htransport_def : ∀ t ∈ Ico 0 T, ∀ x : Torus3,
      transportEnergy t x =
        fderiv ℝ (torusLift (vorticityEnergyField (ω t)))
          (torus3Representative x) (torusLift (velocity t) (torus3Representative x)))
    (hstretch : ∀ t ∈ Ico 0 T,
      ∀ x ∈ maximizerSet (vorticityEnergyField (ω t)),
        stretchingEnergy t x ≤ γ t * vorticityEnergyField (ω t) x) :
    spatialMax (vorticityEnergyField (ω T)) ≤
      spatialMax (vorticityEnergyField (ω 0)) *
        Real.exp (C5 * B ^ ((5 : ℝ) / 6) * T ^ ((1 : ℝ) / 6) +
          C1 * B + C0 * T) := by
  have hmax :=
    torus_spatialMax_vorticityEnergy_le_exp_intervalIntegral_of_vector_equation
      hω_cont hω_deriv hω_space hγ_cont hν hvorticity hstretch_def
      hlapVorticity_def hlapEnergy_def hgrad_def htransport_pair htransport_def hstretch
  have hmaxT := hmax T ⟨hT, le_rfl⟩
  have hintegral := intervalIntegral_strain_budget_le hT hC5 hC1 hΩ_cont hγ_cont
    hΩ_nonneg hbudget hγ_bound
  have hinitial : 0 ≤ spatialMax (vorticityEnergyField (ω 0)) := by
    change 0 ≤ vorticityEnergyField (ω 0)
      (spatialMaximizer (vorticityEnergyField (ω 0)))
    exact vorticityEnergyField_nonneg _ _
  exact hmaxT.trans <| mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr hintegral) hinitial
