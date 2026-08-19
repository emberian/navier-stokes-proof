/-
Copyright (c) 2026 The navier-stokes-proof contributors. All rights reserved.
Released under CC BY 4.0 license as described in the file LICENSE.
Authors: Ember Arlynx
-/

import NSFormal.ForTauCeti.PeriodicIntegration

-- The repository is licensed under CC BY 4.0 rather than Mathlib's Apache 2.0 template.
set_option linter.style.header false

/-!
# Smooth flat vector fields on finite unit tori

This file develops the first vector-calculus consequences of the scalar periodic integration
kernel in `NSFormal.ForTauCeti.PeriodicIntegration`.  The dimension is arbitrary and positive:
the coordinate type is `Fin (n + 1)`, and both the torus and the vector values use that same
coordinate type.

All analytic hypotheses remain visible.  Coordinate smoothness is stated on the real lifts of
circle slices, while integrability assumptions are precisely those used to exchange finite sums
and integrals or invoke scalar integration by parts.

The final theorem is the nonlinear kinetic-energy cancellation

`integral x, u(x) dot ((u(x) dot nabla) u(x)) = 0`

for a divergence-free field.  It is derived from periodic integration by parts and the product
rule; it is not included among the assumptions.
-/

open Function MeasureTheory

noncomputable section

namespace ForTauCeti

section ScalarCalculus

variable {n : ℕ}

/-- A scalar field is `C^1` along coordinate `i` when every corresponding real coordinate
slice is `C^1`. -/
def ContDiffUnitTorusAlongCoordinate
    (f : UnitAddTorus (Fin (n + 1)) → ℝ) (i : Fin (n + 1)) : Prop :=
  ∀ y : UnitTorusCoordinateComplement n,
    ContDiff ℝ 1 (unitTorusCoordinateSliceLift f i y)

/-- A scalar field is coordinatewise `C^1` on the finite unit torus. -/
def ContDiffUnitTorus
    (f : UnitAddTorus (Fin (n + 1)) → ℝ) : Prop :=
  ∀ i : Fin (n + 1), ContDiffUnitTorusAlongCoordinate f i

theorem contDiffUnitTorusAlongCoordinate_const (c : ℝ) (i : Fin (n + 1)) :
    ContDiffUnitTorusAlongCoordinate
      (fun _ : UnitAddTorus (Fin (n + 1)) => c) i := by
  intro y
  exact contDiff_const

theorem ContDiffUnitTorusAlongCoordinate.mul
    {f g : UnitAddTorus (Fin (n + 1)) → ℝ} {i : Fin (n + 1)}
    (hf : ContDiffUnitTorusAlongCoordinate f i)
    (hg : ContDiffUnitTorusAlongCoordinate g i) :
    ContDiffUnitTorusAlongCoordinate (fun x => f x * g x) i := by
  intro y
  exact (hf y).mul (hg y)

/-- Leibniz rule for the classical coordinate derivative on a finite unit torus. -/
theorem unitTorusCoordinateDerivative_mul
    (f g : UnitAddTorus (Fin (n + 1)) → ℝ) (i : Fin (n + 1))
    (x : UnitAddTorus (Fin (n + 1)))
    (hf : ContDiffUnitTorusAlongCoordinate f i)
    (hg : ContDiffUnitTorusAlongCoordinate g i) :
    unitTorusCoordinateDerivative (fun z => f z * g z) i x =
      unitTorusCoordinateDerivative f i x * g x +
        f x * unitTorusCoordinateDerivative g i x := by
  unfold unitTorusCoordinateDerivative unitTorusCoordinateSliceDerivative
  rw [show unitTorusCoordinateSliceLift (fun z => f z * g z) i (Fin.removeNth i x) =
      fun r => unitTorusCoordinateSliceLift f i (Fin.removeNth i x) r *
        unitTorusCoordinateSliceLift g i (Fin.removeNth i x) r by rfl]
  have hderiv : deriv (fun r =>
      unitTorusCoordinateSliceLift f i (Fin.removeNth i x) r *
        unitTorusCoordinateSliceLift g i (Fin.removeNth i x) r) =
      fun r => deriv (unitTorusCoordinateSliceLift f i (Fin.removeNth i x)) r *
          unitTorusCoordinateSliceLift g i (Fin.removeNth i x) r +
        unitTorusCoordinateSliceLift f i (Fin.removeNth i x) r *
          deriv (unitTorusCoordinateSliceLift g i (Fin.removeNth i x)) r := by
    funext r
    exact ((((hf _).differentiable one_ne_zero).differentiableAt.hasDerivAt).mul
      (((hg _).differentiable one_ne_zero).differentiableAt.hasDerivAt)).deriv
  rw [hderiv]
  change
    AddCircle.liftIoc 1 0
        (fun r => deriv (unitTorusCoordinateSliceLift f i (Fin.removeNth i x)) r *
            unitTorusCoordinateSliceLift g i (Fin.removeNth i x) r +
          unitTorusCoordinateSliceLift f i (Fin.removeNth i x) r *
            deriv (unitTorusCoordinateSliceLift g i (Fin.removeNth i x)) r) (x i) = _
  simp only [AddCircle.liftIoc]
  simp [unitTorusCoordinateSliceLift, unitTorusCoordinateSlice]

end ScalarCalculus

section VectorCalculus

variable {n : ℕ}

/-- Scalar fields on a normalized unit torus of arbitrary positive finite dimension. -/
abbrev UnitTorusScalarField (n : ℕ) :=
  UnitAddTorus (Fin (n + 1)) → ℝ

/-- Flat vector fields whose components are indexed by the coordinates of their unit torus. -/
abbrev UnitTorusVectorField (n : ℕ) :=
  UnitAddTorus (Fin (n + 1)) → (Fin (n + 1) → ℝ)

/-- The derivative of component `j` in coordinate direction `i`. -/
def unitTorusVectorCoordinateDerivative
    (u : UnitTorusVectorField n) (i j : Fin (n + 1)) : UnitTorusScalarField n :=
  unitTorusCoordinateDerivative (fun x => u x j) i

/-- Coordinate divergence of a flat vector field. -/
def unitTorusDivergence
    (u : UnitTorusVectorField n) : UnitTorusScalarField n :=
  fun x => ∑ i : Fin (n + 1), unitTorusVectorCoordinateDerivative u i i x

/-- Transport of a scalar field by a flat vector field. -/
def unitTorusScalarTransport
    (u : UnitTorusVectorField n) (f : UnitTorusScalarField n) : UnitTorusScalarField n :=
  fun x => ∑ i : Fin (n + 1), u x i * unitTorusCoordinateDerivative f i x

/-- Self-transport `(u dot nabla)u`, defined componentwise. -/
def unitTorusSelfTransport
    (u : UnitTorusVectorField n) : UnitTorusVectorField n :=
  fun x j => unitTorusScalarTransport u (fun z => u z j) x

/-- Euclidean coordinate pairing of finite-dimensional flat vector fields. -/
def unitTorusVectorPairing
    (u v : UnitTorusVectorField n) : UnitTorusScalarField n :=
  fun x => ∑ j : Fin (n + 1), u x j * v x j

/-- The nonlinear kinetic-energy production density `u dot ((u dot nabla)u)`. -/
def unitTorusSelfTransportEnergyDensity
    (u : UnitTorusVectorField n) : UnitTorusScalarField n :=
  unitTorusVectorPairing u (unitTorusSelfTransport u)

/-- Coordinatewise `C^1` regularity of every component of a vector field. -/
def ContDiffUnitTorusVectorField (u : UnitTorusVectorField n) : Prop :=
  ∀ (i j : Fin (n + 1)),
    ContDiffUnitTorusAlongCoordinate (fun x => u x j) i

@[simp]
theorem unitTorusVectorCoordinateDerivative_const
    (c : Fin (n + 1) → ℝ) (i j : Fin (n + 1))
    (x : UnitAddTorus (Fin (n + 1))) :
    unitTorusVectorCoordinateDerivative (fun _ => c) i j x = 0 := by
  exact unitTorusCoordinateDerivative_const (c j) i x

@[simp]
theorem unitTorusDivergence_const
    (c : Fin (n + 1) → ℝ) (x : UnitAddTorus (Fin (n + 1))) :
    unitTorusDivergence (fun _ => c) x = 0 := by
  simp [unitTorusDivergence]

@[simp]
theorem unitTorusSelfTransport_const
    (c : Fin (n + 1) → ℝ) (x : UnitAddTorus (Fin (n + 1)))
    (j : Fin (n + 1)) :
    unitTorusSelfTransport (fun _ => c) x j = 0 := by
  simp [unitTorusSelfTransport, unitTorusScalarTransport]

@[simp]
theorem unitTorusSelfTransportEnergyDensity_const
    (c : Fin (n + 1) → ℝ) (x : UnitAddTorus (Fin (n + 1))) :
    unitTorusSelfTransportEnergyDensity (fun _ => c) x = 0 := by
  simp [unitTorusSelfTransportEnergyDensity, unitTorusVectorPairing]

/-- Every diagonal derivative has zero integral, hence the integral of a smooth periodic
divergence vanishes. -/
theorem integral_unitTorusDivergence_eq_zero
    (u : UnitTorusVectorField n)
    (hu : ContDiffUnitTorusVectorField u)
    (hint : ∀ i : Fin (n + 1),
      Integrable (unitTorusVectorCoordinateDerivative u i i)) :
    (∫ x, unitTorusDivergence u x) = 0 := by
  rw [show (∫ x, unitTorusDivergence u x) =
      ∑ i : Fin (n + 1), ∫ x, unitTorusVectorCoordinateDerivative u i i x by
    simp only [unitTorusDivergence]
    exact MeasureTheory.integral_finsetSum Finset.univ (fun i _ => hint i)]
  apply Finset.sum_eq_zero
  intro i _hi
  have hparts := unitTorus_integral_mul_coordinateDerivative_eq_neg
    (fun _ : UnitAddTorus (Fin (n + 1)) => (1 : ℝ)) (fun x => u x i) i
    (contDiffUnitTorusAlongCoordinate_const 1 i) (hu i i)
    (by simpa only [unitTorusVectorCoordinateDerivative, one_mul] using hint i)
    (by simp)
  simpa [unitTorusVectorCoordinateDerivative] using hparts

/-- One coordinate of transport integration by parts.  The derivative of the transporting
component is retained explicitly; summing these terms produces `div u`. -/
theorem unitTorus_transportComponent_integration_by_parts
    (b f g : UnitTorusScalarField n) (i : Fin (n + 1))
    (hb : ContDiffUnitTorusAlongCoordinate b i)
    (hf : ContDiffUnitTorusAlongCoordinate f i)
    (hg : ContDiffUnitTorusAlongCoordinate g i)
    (hleft : Integrable (fun x =>
      (f x * b x) * unitTorusCoordinateDerivative g i x))
    (hright : Integrable (fun x =>
      unitTorusCoordinateDerivative (fun z => f z * b z) i x * g x)) :
    (∫ x, (f x * b x) * unitTorusCoordinateDerivative g i x) =
      -(∫ x,
        (unitTorusCoordinateDerivative f i x * b x +
          f x * unitTorusCoordinateDerivative b i x) * g x) := by
  have hparts := unitTorus_integral_mul_coordinateDerivative_eq_neg
    (fun x => f x * b x) g i (hf.mul hb) hg hleft hright
  calc
    (∫ x, (f x * b x) * unitTorusCoordinateDerivative g i x) =
        -(∫ x, unitTorusCoordinateDerivative (fun z => f z * b z) i x * g x) :=
      hparts
    _ = -(∫ x,
        (unitTorusCoordinateDerivative f i x * b x +
          f x * unitTorusCoordinateDerivative b i x) * g x) := by
      congr 2
      funext x
      rw [unitTorusCoordinateDerivative_mul f b i x hf hb]

/-- Full smooth transport integration by parts on a finite unit torus:
`integral f (u dot nabla g) = -integral ((u dot nabla f) + f div u) g`. -/
theorem unitTorus_transport_integration_by_parts
    (u : UnitTorusVectorField n) (f g : UnitTorusScalarField n)
    (hu : ContDiffUnitTorusVectorField u)
    (hf : ContDiffUnitTorus f)
    (hg : ContDiffUnitTorus g)
    (hleft : ∀ i : Fin (n + 1), Integrable (fun x =>
      (f x * u x i) * unitTorusCoordinateDerivative g i x))
    (hright : ∀ i : Fin (n + 1), Integrable (fun x =>
      unitTorusCoordinateDerivative (fun z => f z * u z i) i x * g x)) :
    (∫ x, f x * unitTorusScalarTransport u g x) =
      -(∫ x,
        (unitTorusScalarTransport u f x + f x * unitTorusDivergence u x) * g x) := by
  have hcomponent : ∀ i : Fin (n + 1),
      (∫ x, (f x * u x i) * unitTorusCoordinateDerivative g i x) =
        -(∫ x,
          unitTorusCoordinateDerivative (fun z => f z * u z i) i x * g x) := by
    intro i
    exact unitTorus_integral_mul_coordinateDerivative_eq_neg
      (fun x => f x * u x i) g i ((hf i).mul (hu i i)) (hg i)
        (hleft i) (hright i)
  calc
    (∫ x, f x * unitTorusScalarTransport u g x) =
        ∫ x, ∑ i : Fin (n + 1),
          (f x * u x i) * unitTorusCoordinateDerivative g i x := by
      congr 1
      funext x
      simp only [unitTorusScalarTransport, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = ∑ i : Fin (n + 1),
        ∫ x, (f x * u x i) * unitTorusCoordinateDerivative g i x := by
      exact MeasureTheory.integral_finsetSum Finset.univ
        (fun i _hi => hleft i)
    _ = ∑ i : Fin (n + 1),
        -(∫ x, unitTorusCoordinateDerivative (fun z => f z * u z i) i x * g x) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact hcomponent i
    _ = -(∑ i : Fin (n + 1),
        ∫ x, unitTorusCoordinateDerivative (fun z => f z * u z i) i x * g x) := by
      rw [Finset.sum_neg_distrib]
    _ = -(∫ x, ∑ i : Fin (n + 1),
        unitTorusCoordinateDerivative (fun z => f z * u z i) i x * g x) := by
      rw [MeasureTheory.integral_finsetSum Finset.univ
        (fun i _hi => hright i)]
    _ = -(∫ x,
        (unitTorusScalarTransport u f x + f x * unitTorusDivergence u x) * g x) := by
      congr 2
      funext x
      calc
        (∑ i : Fin (n + 1),
            unitTorusCoordinateDerivative (fun z => f z * u z i) i x * g x) =
            ∑ i : Fin (n + 1),
              (unitTorusCoordinateDerivative f i x * u x i +
                f x * unitTorusCoordinateDerivative (fun z => u z i) i x) * g x := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [unitTorusCoordinateDerivative_mul f (fun z => u z i) i x
            (hf i) (hu i i)]
        _ = (unitTorusScalarTransport u f x + f x * unitTorusDivergence u x) * g x := by
          simp only [unitTorusScalarTransport, unitTorusDivergence,
            unitTorusVectorCoordinateDerivative]
          simp_rw [add_mul]
          rw [Finset.sum_add_distrib]
          congr 1
          · rw [← Finset.sum_mul]
            congr 1
            apply Finset.sum_congr rfl
            intro i _hi
            ring
          · rw [← Finset.sum_mul, Finset.mul_sum]

/-- For a divergence-free field, scalar transport is skew-adjoint in the volume pairing. -/
theorem unitTorus_divergenceFree_transport_skew
    (u : UnitTorusVectorField n) (f g : UnitTorusScalarField n)
    (hu : ContDiffUnitTorusVectorField u)
    (hf : ContDiffUnitTorus f)
    (hg : ContDiffUnitTorus g)
    (hleft : ∀ i : Fin (n + 1), Integrable (fun x =>
      (f x * u x i) * unitTorusCoordinateDerivative g i x))
    (hright : ∀ i : Fin (n + 1), Integrable (fun x =>
      unitTorusCoordinateDerivative (fun z => f z * u z i) i x * g x))
    (hdiv : ∀ x, unitTorusDivergence u x = 0) :
    (∫ x, f x * unitTorusScalarTransport u g x) =
      -(∫ x, unitTorusScalarTransport u f x * g x) := by
  rw [unitTorus_transport_integration_by_parts u f g hu hf hg hleft hright]
  congr 2
  funext x
  rw [hdiv]
  ring

/-- A divergence-free field does no net work against its own advective derivative:
`integral u dot ((u dot nabla)u) = 0`.  This is the smooth periodic nonlinear
kinetic-energy cancellation in arbitrary positive finite dimension. -/
theorem integral_unitTorusSelfTransportEnergyDensity_eq_zero
    (u : UnitTorusVectorField n)
    (hu : ContDiffUnitTorusVectorField u)
    (hleft : ∀ (i j : Fin (n + 1)), Integrable (fun x =>
      (u x j * u x i) *
        unitTorusCoordinateDerivative (fun z => u z j) i x))
    (hright : ∀ (i j : Fin (n + 1)), Integrable (fun x =>
      unitTorusCoordinateDerivative (fun z => u z j * u z i) i x * u x j))
    (hdiv : ∀ x, unitTorusDivergence u x = 0) :
    (∫ x, unitTorusSelfTransportEnergyDensity u x) = 0 := by
  have henergyIntegrable : ∀ j : Fin (n + 1), Integrable (fun x =>
      u x j * unitTorusScalarTransport u (fun z => u z j) x) := by
    intro j
    simp only [unitTorusScalarTransport, Finset.mul_sum]
    exact integrable_finsetSum Finset.univ
      (fun i _hi => by simpa only [mul_assoc] using hleft i j)
  have hcomponentZero : ∀ j : Fin (n + 1),
      (∫ x, u x j * unitTorusScalarTransport u (fun z => u z j) x) = 0 := by
    intro j
    have hskew := unitTorus_divergenceFree_transport_skew
      u (fun x => u x j) (fun x => u x j) hu
      (fun i => hu i j) (fun i => hu i j)
      (fun i => hleft i j) (fun i => hright i j) hdiv
    have hsame :
        (∫ x, unitTorusScalarTransport u (fun z => u z j) x * u x j) =
          ∫ x, u x j * unitTorusScalarTransport u (fun z => u z j) x := by
      congr 1
      funext x
      ring
    rw [hsame] at hskew
    linarith
  calc
    (∫ x, unitTorusSelfTransportEnergyDensity u x) =
        ∫ x, ∑ j : Fin (n + 1),
          u x j * unitTorusScalarTransport u (fun z => u z j) x := by
      rfl
    _ = ∑ j : Fin (n + 1),
        ∫ x, u x j * unitTorusScalarTransport u (fun z => u z j) x := by
      exact MeasureTheory.integral_finsetSum Finset.univ
        (fun j _hi => henergyIntegrable j)
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro j _hi
      exact hcomponentZero j

end VectorCalculus

end ForTauCeti
