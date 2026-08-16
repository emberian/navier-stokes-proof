import NSFormal.Domain
import NSFormal.MaxEnvelope
import NSFormal.VorticityMaximum

/-!
# Periodic lifts and calculus at torus maxima

Spatial derivatives on the additive quotient are represented through the canonical
periodic lift to `ℝ³`.  This file proves that a torus maximizer lifts to a genuine
local maximum in `ℝ³`, so Fermat's theorem makes every first-order transport term
vanish there.  No representative is postulated: one is constructed coordinatewise
from `AddCircle.equivIco`.
-/

open Filter Set
open scoped Topology

noncomputable section

theorem taylorWithinEval_two_univ (f : ℝ → ℝ) (x y : ℝ) :
    taylorWithinEval f 2 Set.univ x y =
      f x + (y - x) * deriv f x +
        ((2 : ℝ)⁻¹ * (y - x) ^ 2) * iteratedDeriv 2 f x := by
  rw [show 2 = 1 + 1 by norm_num, taylorWithinEval_succ,
    taylorWithinEval_succ, taylor_within_zero_eval]
  norm_num [iteratedDerivWithin_univ, iteratedDeriv_zero, iteratedDeriv_one]

/-- The one-dimensional second derivative test in the form needed for each
coordinate line through a spatial maximum. -/
theorem iteratedDeriv_two_nonpos_of_isLocalMax
    {f : ℝ → ℝ} {x : ℝ} (hf : ContDiff ℝ 2 f) (hmax : IsLocalMax f x) :
    iteratedDeriv 2 f x ≤ 0 := by
  by_contra hnot
  have hd : 0 < iteratedDeriv 2 f x := lt_of_not_ge hnot
  let R : ℝ → ℝ := fun y =>
    ((y - x) ^ 2)⁻¹ * (f y - taylorWithinEval f 2 Set.univ x y)
  have hTaylor : Tendsto R (𝓝 x) (𝓝 0) := by
    simpa [R] using taylor_tendsto convex_univ (Set.mem_univ x) hf.contDiffOn
  have hR : Tendsto R (𝓝[>] x) (𝓝 0) := hTaylor.mono_left inf_le_left
  have hlower : ∀ᶠ y in 𝓝[>] x, -(iteratedDeriv 2 f x) / 4 < R y :=
    (tendsto_order.mp hR).1 (-(iteratedDeriv 2 f x) / 4) (by linarith)
  have hupper : ∀ᶠ y in 𝓝[>] x, f y ≤ f x :=
    hmax.filter_mono inf_le_left
  have he := (hlower.and hupper).and
    (@self_mem_nhdsWithin ℝ _ x (Set.Ioi x))
  obtain ⟨y, ⟨hyR, hymax⟩, hyx⟩ := he.exists
  have hyne : y - x ≠ 0 := sub_ne_zero.mpr hyx.ne'
  have hderiv : deriv f x = 0 := hmax.deriv_eq_zero
  have hratio : R y ≤ -(iteratedDeriv 2 f x) / 2 := by
    dsimp [R]
    rw [taylorWithinEval_two_univ, hderiv, mul_zero, add_zero]
    have hsq : 0 < (y - x) ^ 2 := sq_pos_of_ne_zero hyne
    rw [inv_mul_le_iff₀ hsq]
    field_simp [hyne]
    nlinarith
  linarith

/-- The quotient covering map `ℝ³ → (ℝ / 2πℤ)³`. -/
def torus3Mk (x : Vec3) : Torus3 := fun i => (x i : AddCircle ((2 : ℝ) * Real.pi))

theorem continuous_torus3Mk : Continuous torus3Mk := by
  unfold torus3Mk
  fun_prop

/-- The coordinatewise representative in the fundamental cube `[0, 2π)³`. -/
def torus3Representative (x : Torus3) : Vec3 :=
  WithLp.toLp 2 fun i => (AddCircle.equivIco ((2 : ℝ) * Real.pi) 0 (x i) : ℝ)

@[simp]
theorem torus3Mk_representative (x : Torus3) :
    torus3Mk (torus3Representative x) = x := by
  ext i
  change (((AddCircle.equivIco ((2 : ℝ) * Real.pi) 0 (x i) : ℝ) :
    AddCircle ((2 : ℝ) * Real.pi))) = x i
  exact AddCircle.coe_equivIco

/-- Lift a torus-valued field to its canonical periodic function on `ℝ³`. -/
def torusLift {E : Type*} (f : Torus3 → E) : Vec3 → E := fun x => f (torus3Mk x)

theorem ContinuousMap.continuous_torusLift
    {E : Type*} [TopologicalSpace E] (f : C(Torus3, E)) : Continuous (torusLift f) :=
  f.continuous.comp continuous_torus3Mk

/-- Add one full period in a selected coordinate. -/
def torusPeriodShift (i : Fin 3) (x : Vec3) : Vec3 :=
  WithLp.toLp 2 fun j => if j = i then x j + (2 : ℝ) * Real.pi else x j

@[simp]
theorem torus3Mk_periodShift (i : Fin 3) (x : Vec3) :
    torus3Mk (torusPeriodShift i x) = torus3Mk x := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [torus3Mk, torusPeriodShift]
  · simp [torus3Mk, torusPeriodShift, hji]

theorem torusLift_periodic {E : Type*} (f : Torus3 → E) (i : Fin 3) (x : Vec3) :
    torusLift f (torusPeriodShift i x) = torusLift f x := by
  simp [torusLift]

/-- A torus maximizer becomes a global maximum of the lifted field on `ℝ³`. -/
theorem torusLift_le_at_representative_of_mem_maximizer
    (f : C(Torus3, ℝ)) {x : Torus3} (hx : x ∈ maximizerSet f) (y : Vec3) :
    torusLift f y ≤ torusLift f (torus3Representative x) := by
  have hy := le_spatialMax f (torus3Mk y)
  change f (torus3Mk y) ≤ f (torus3Mk (torus3Representative x))
  rw [torus3Mk_representative]
  exact hy.trans_eq hx.symm

theorem isLocalMax_torusLift_at_representative
    (f : C(Torus3, ℝ)) {x : Torus3} (hx : x ∈ maximizerSet f) :
    IsLocalMax (torusLift f) (torus3Representative x) := by
  apply IsMaxOn.isLocalMax (s := Set.univ)
  · intro y _hy
    exact torusLift_le_at_representative_of_mem_maximizer f hx y
  · exact Filter.univ_mem

/-- The first spatial derivative, hence every transport pairing, vanishes at
a lifted torus maximizer. -/
theorem fderiv_torusLift_apply_eq_zero_at_maximizer
    (f : C(Torus3, ℝ)) {x : Torus3} (hx : x ∈ maximizerSet f) (v : Vec3) :
    fderiv ℝ (torusLift f) (torus3Representative x) v = 0 := by
  rw [(isLocalMax_torusLift_at_representative f hx).fderiv_eq_zero]
  rfl

/-- The coordinate line through `x` in direction `eᵢ`. -/
def coordinateLine (x : Vec3) (i : Fin 3) (s : ℝ) : Vec3 :=
  x + s • EuclideanSpace.single i (1 : ℝ)

/-- Second coordinate derivative of a lifted scalar field. -/
def torusLiftCoordinateSecond (f : C(Torus3, ℝ)) (x : Vec3) (i : Fin 3) : ℝ :=
  iteratedDeriv 2 (fun s => torusLift f (coordinateLine x i s)) 0

/-- The coordinate-sum Laplacian of a lifted scalar field. -/
def torusLiftLaplacian (f : C(Torus3, ℝ)) (x : Vec3) : ℝ :=
  ∑ i : Fin 3, torusLiftCoordinateSecond f x i

theorem torusLiftCoordinateSecond_nonpos_at_maximizer
    (f : C(Torus3, ℝ)) {x : Torus3} (hx : x ∈ maximizerSet f)
    (hf : ContDiff ℝ 2 (torusLift f)) (i : Fin 3) :
    torusLiftCoordinateSecond f (torus3Representative x) i ≤ 0 := by
  apply iteratedDeriv_two_nonpos_of_isLocalMax
  · exact hf.comp (by unfold coordinateLine; fun_prop)
  · have hmax := isLocalMax_torusLift_at_representative f hx
    have hmax0 : IsLocalMax (torusLift f)
        (coordinateLine (torus3Representative x) i 0) := by
      simpa [coordinateLine] using hmax
    have hline : IsLocalMax
        ((torusLift f) ∘ fun s : ℝ => coordinateLine (torus3Representative x) i s) 0 := by
      exact hmax0.comp_continuous
        (b := (0 : ℝ))
        (g := fun s : ℝ => coordinateLine (torus3Representative x) i s)
        (by unfold coordinateLine; fun_prop)
    simpa [Function.comp_def, coordinateLine] using hline

/-- The lifted scalar Laplacian is nonpositive at every torus maximizer. -/
theorem torusLiftLaplacian_nonpos_at_maximizer
    (f : C(Torus3, ℝ)) {x : Torus3} (hx : x ∈ maximizerSet f)
    (hf : ContDiff ℝ 2 (torusLift f)) :
    torusLiftLaplacian f (torus3Representative x) ≤ 0 := by
  exact Finset.sum_nonpos fun i _hi =>
    torusLiftCoordinateSecond_nonpos_at_maximizer f hx hf i

/-- First coordinate derivative of a lifted vector field. -/
def torusLiftCoordinateFirstVector
    (w : C(Torus3, Vec3)) (x : Vec3) (i : Fin 3) : Vec3 :=
  deriv (fun s => torusLift w (coordinateLine x i s)) 0

/-- Second coordinate derivative of a lifted vector field. -/
def torusLiftCoordinateSecondVector
    (w : C(Torus3, Vec3)) (x : Vec3) (i : Fin 3) : Vec3 :=
  iteratedDeriv 2 (fun s => torusLift w (coordinateLine x i s)) 0

/-- Coordinate-sum vector Laplacian. -/
def torusLiftVectorLaplacian (w : C(Torus3, Vec3)) (x : Vec3) : Vec3 :=
  ∑ i : Fin 3, torusLiftCoordinateSecondVector w x i

/-- The Frobenius square `|∇w|²`, expressed in the standard coordinate frame. -/
def torusLiftGradientSq (w : C(Torus3, Vec3)) (x : Vec3) : ℝ :=
  ∑ i : Fin 3, ‖torusLiftCoordinateFirstVector w x i‖ ^ 2

theorem torusLiftGradientSq_nonneg (w : C(Torus3, Vec3)) (x : Vec3) :
    0 ≤ torusLiftGradientSq w x := by
  exact Finset.sum_nonneg fun i _hi => sq_nonneg _

/-- Coordinate form of the viscous energy identity. -/
theorem torusLiftCoordinateSecond_vorticityEnergy
    (w : C(Torus3, Vec3)) (x : Vec3) (i : Fin 3)
    (hw : ContDiff ℝ 2 (torusLift w)) :
    torusLiftCoordinateSecond (vorticityEnergyField w) x i =
      inner ℝ (torusLift w x) (torusLiftCoordinateSecondVector w x i) +
        ‖torusLiftCoordinateFirstVector w x i‖ ^ 2 := by
  have hline : ContDiff ℝ 2 (fun s => torusLift w (coordinateLine x i s)) :=
    hw.comp (by unfold coordinateLine; fun_prop)
  simpa [torusLiftCoordinateSecond, torusLiftCoordinateSecondVector,
    torusLiftCoordinateFirstVector, torusLift, vorticityEnergyField, coordinateLine] using
      iteratedDeriv_two_vorticityEnergy hline 0

/-- Correct diffusion identity on the periodic lift:
`⟪w, Δw⟫ = Δ(|w|²/2) - |∇w|²`. -/
theorem inner_torusLiftVectorLaplacian_eq
    (w : C(Torus3, Vec3)) (x : Vec3) (hw : ContDiff ℝ 2 (torusLift w)) :
    inner ℝ (torusLift w x) (torusLiftVectorLaplacian w x) =
      torusLiftLaplacian (vorticityEnergyField w) x - torusLiftGradientSq w x := by
  rw [torusLiftVectorLaplacian, torusLiftLaplacian, torusLiftGradientSq, inner_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  have h := torusLiftCoordinateSecond_vorticityEnergy w x i hw
  linarith
