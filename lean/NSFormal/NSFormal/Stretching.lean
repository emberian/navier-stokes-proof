import NSFormal.VectorCalculus

/-!
# Honest vortex-stretching bounds

This file isolates the elementary estimate that is actually available from the
velocity gradient.  It does not postulate a geometric-depletion mechanism:
obtaining an integrable bound for this gradient rate remains a separate analytic
obligation.
-/

open Set
open scoped RealInnerProductSpace

noncomputable section

/-- Symmetric part of a Euclidean velocity derivative, i.e. the strain map. -/
def symmetricPart (D : Vec3 →L[ℝ] Vec3) : Vec3 →L[ℝ] Vec3 :=
  (2 : ℝ)⁻¹ • (D + ContinuousLinearMap.adjoint D)

/-- The skew part of the velocity gradient makes no contribution to the
quadratic stretching form. -/
theorem inner_symmetricPart_eq (D : Vec3 →L[ℝ] Vec3) (w : Vec3) :
    inner ℝ w (symmetricPart D w) = inner ℝ w (D w) := by
  have hadj : inner ℝ w ((ContinuousLinearMap.adjoint D) w) = inner ℝ w (D w) := by
    rw [real_inner_comm ((ContinuousLinearMap.adjoint D) w) w]
    exact ContinuousLinearMap.adjoint_inner_left D w w
  simp [symmetricPart, inner_add_right, real_inner_smul_right, hadj]
  ring

/-- The quadratic stretching form is controlled by twice the operator norm of
the velocity derivative times half the squared vorticity magnitude. -/
theorem inner_continuousLinearMap_le_two_opNorm_vorticityEnergy
    (D : Vec3 →L[ℝ] Vec3) (w : Vec3) :
    inner ℝ w (D w) ≤ 2 * ‖D‖ * vorticityEnergy w := by
  calc
    inner ℝ w (D w) ≤ ‖w‖ * ‖D w‖ := real_inner_le_norm w (D w)
    _ ≤ ‖w‖ * (‖D‖ * ‖w‖) :=
      mul_le_mul_of_nonneg_left (D.le_opNorm w) (norm_nonneg w)
    _ = 2 * ‖D‖ * vorticityEnergy w := by
      rw [vorticityEnergy]
      ring

/-- Sharp elementary form using the symmetric strain rather than the full
velocity gradient. -/
theorem inner_continuousLinearMap_le_two_strainNorm_vorticityEnergy
    (D : Vec3 →L[ℝ] Vec3) (w : Vec3) :
    inner ℝ w (D w) ≤ 2 * ‖symmetricPart D‖ * vorticityEnergy w := by
  rw [← inner_symmetricPart_eq D w]
  exact inner_continuousLinearMap_le_two_opNorm_vorticityEnergy
    (symmetricPart D) w

/-- Concrete torus stretching is bounded by the operator norm of the lifted
velocity gradient at the same representative. -/
theorem inner_torusStretching_le_two_gradientNorm_energy
    (velocity ω : C(Torus3, Vec3)) (x : Torus3) :
    inner ℝ (ω x) (torusStretching velocity ω x) ≤
      2 * ‖fderiv ℝ (torusLift velocity) (torus3Representative x)‖ *
        vorticityEnergy (ω x) := by
  have h := inner_continuousLinearMap_le_two_opNorm_vorticityEnergy
    (fderiv ℝ (torusLift velocity) (torus3Representative x)) (ω x)
  simpa [torusStretching, torusDirectionalDerivative, torusLift] using h

/-- Physical strain-norm version of the concrete torus stretching bound. -/
theorem inner_torusStretching_le_two_strainNorm_energy
    (velocity ω : C(Torus3, Vec3)) (x : Torus3) :
    inner ℝ (ω x) (torusStretching velocity ω x) ≤
      2 * ‖symmetricPart
        (fderiv ℝ (torusLift velocity) (torus3Representative x))‖ *
        vorticityEnergy (ω x) := by
  have h := inner_continuousLinearMap_le_two_strainNorm_vorticityEnergy
    (fderiv ℝ (torusLift velocity) (torus3Representative x)) (ω x)
  simpa [torusStretching, torusDirectionalDerivative, torusLift] using h

/-- Any scalar rate dominating twice the local velocity-gradient norm controls
the stretching energy.  This discharges the elementary stretching step in the
maximum principle while leaving the genuinely hard rate estimate explicit. -/
theorem inner_torusStretching_le_rate_energy
    (velocity ω : C(Torus3, Vec3)) (x : Torus3) (k : ℝ)
    (hgradient :
      2 * ‖fderiv ℝ (torusLift velocity) (torus3Representative x)‖ ≤ k) :
    inner ℝ (ω x) (torusStretching velocity ω x) ≤
      k * vorticityEnergy (ω x) := by
  exact (inner_torusStretching_le_two_gradientNorm_energy velocity ω x).trans
    (mul_le_mul_of_nonneg_right hgradient (vorticityEnergy_nonneg (ω x)))

/-- A rate dominating twice the local strain norm controls stretching. -/
theorem inner_torusStretching_le_strainRate_energy
    (velocity ω : C(Torus3, Vec3)) (x : Torus3) (k : ℝ)
    (hstrain :
      2 * ‖symmetricPart
        (fderiv ℝ (torusLift velocity) (torus3Representative x))‖ ≤ k) :
    inner ℝ (ω x) (torusStretching velocity ω x) ≤
      k * vorticityEnergy (ω x) := by
  exact (inner_torusStretching_le_two_strainNorm_energy velocity ω x).trans
    (mul_le_mul_of_nonneg_right hstrain (vorticityEnergy_nonneg (ω x)))

/-- Field-form wrapper used by the variable-rate maximum principle. -/
theorem stretchingEnergy_le_rate_at_maximizers
    {velocity ω stretchingVector : ℝ → C(Torus3, Vec3)}
    {stretchingEnergy : ℝ → C(Torus3, ℝ)} {k : ℝ → ℝ} {a b : ℝ}
    (hstretchingVector : ∀ t ∈ Ico a b, ∀ x : Torus3,
      stretchingVector t x = torusStretching (velocity t) (ω t) x)
    (hstretchingEnergy : ∀ t ∈ Ico a b, ∀ x : Torus3,
      stretchingEnergy t x = inner ℝ (ω t x) (stretchingVector t x))
    (hgradient : ∀ t ∈ Ico a b,
      ∀ x ∈ maximizerSet (vorticityEnergyField (ω t)),
        2 * ‖fderiv ℝ (torusLift (velocity t)) (torus3Representative x)‖ ≤ k t) :
    ∀ t ∈ Ico a b, ∀ x ∈ maximizerSet (vorticityEnergyField (ω t)),
      stretchingEnergy t x ≤ k t * vorticityEnergyField (ω t) x := by
  intro t ht x hx
  rw [hstretchingEnergy t ht x, hstretchingVector t ht x]
  exact inner_torusStretching_le_rate_energy (velocity t) (ω t) x (k t)
    (hgradient t ht x hx)

/-- Maximizer wrapper using the physical symmetric strain norm. -/
theorem stretchingEnergy_le_strainRate_at_maximizers
    {velocity ω stretchingVector : ℝ → C(Torus3, Vec3)}
    {stretchingEnergy : ℝ → C(Torus3, ℝ)} {k : ℝ → ℝ} {a b : ℝ}
    (hstretchingVector : ∀ t ∈ Ico a b, ∀ x : Torus3,
      stretchingVector t x = torusStretching (velocity t) (ω t) x)
    (hstretchingEnergy : ∀ t ∈ Ico a b, ∀ x : Torus3,
      stretchingEnergy t x = inner ℝ (ω t x) (stretchingVector t x))
    (hstrain : ∀ t ∈ Ico a b,
      ∀ x ∈ maximizerSet (vorticityEnergyField (ω t)),
        2 * ‖symmetricPart
          (fderiv ℝ (torusLift (velocity t)) (torus3Representative x))‖ ≤ k t) :
    ∀ t ∈ Ico a b, ∀ x ∈ maximizerSet (vorticityEnergyField (ω t)),
      stretchingEnergy t x ≤ k t * vorticityEnergyField (ω t) x := by
  intro t ht x hx
  rw [hstretchingEnergy t ht x, hstretchingVector t ht x]
  exact inner_torusStretching_le_strainRate_energy (velocity t) (ω t) x (k t)
    (hstrain t ht x hx)
