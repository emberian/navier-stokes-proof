import NSFormal.PeriodicCalculus

/-!
# Classical periodic Navier--Stokes fields

This file defines the spatial operators and the classical incompressible
Navier--Stokes predicate on the concrete period-`2π` three-torus.  The predicate
is not an assumed typeclass and no global solution is postulated.  Its
consistency is witnessed below by the identically-zero solution.
-/

open Set
open scoped Topology

noncomputable section

/-- Directional derivative of a periodic field, computed on its canonical lift. -/
def torusDirectionalDerivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : C(Torus3, E)) (x : Torus3) (v : Vec3) : E :=
  fderiv ℝ (torusLift f) (torus3Representative x) v

/-- Coordinate derivative in the standard Euclidean frame. -/
def torusPartial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : C(Torus3, E)) (x : Torus3) (i : Fin 3) : E :=
  torusDirectionalDerivative f x (EuclideanSpace.single i (1 : ℝ))

/-- Gradient of a scalar periodic field. -/
def torusGradient (p : C(Torus3, ℝ)) (x : Torus3) : Vec3 :=
  WithLp.toLp 2 fun i => torusPartial p x i

/-- Divergence of a vector periodic field. -/
def torusDivergence (u : C(Torus3, Vec3)) (x : Torus3) : ℝ :=
  ∑ i : Fin 3, torusPartial u x i i

/-- Curl of a vector periodic field in standard right-handed coordinates. -/
def torusCurl (u : C(Torus3, Vec3)) (x : Torus3) : Vec3 :=
  WithLp.toLp 2 ![
    torusPartial u x 1 2 - torusPartial u x 2 1,
    torusPartial u x 2 0 - torusPartial u x 0 2,
    torusPartial u x 0 1 - torusPartial u x 1 0]

/-- The advective derivative `(u · ∇)v`. -/
def torusTransport (u v : C(Torus3, Vec3)) (x : Torus3) : Vec3 :=
  torusDirectionalDerivative v x (u x)

/-- The vortex-stretching vector `(ω · ∇)u`. -/
def torusStretching (u ω : C(Torus3, Vec3)) (x : Torus3) : Vec3 :=
  torusDirectionalDerivative u x (ω x)

/-- Coordinate Laplacian of a vector field at a torus point. -/
def torusVectorLaplacian (u : C(Torus3, Vec3)) (x : Torus3) : Vec3 :=
  torusLiftVectorLaplacian u (torus3Representative x)

/-- Gradient evaluated directly on an arbitrary point of the periodic lift. -/
def torusLiftGradient (p : C(Torus3, ℝ)) (y : Vec3) : Vec3 :=
  WithLp.toLp 2 fun i =>
    fderiv ℝ (torusLift p) y (EuclideanSpace.single i (1 : ℝ))

/-- Divergence evaluated directly on an arbitrary point of the periodic lift. -/
def torusLiftDivergence (u : C(Torus3, Vec3)) (y : Vec3) : ℝ :=
  ∑ i : Fin 3,
    fderiv ℝ (torusLift u) y (EuclideanSpace.single i (1 : ℝ)) i

/-- Advective derivative evaluated directly on an arbitrary point of the
periodic lift. -/
def torusLiftTransport
    (u v : C(Torus3, Vec3)) (y : Vec3) : Vec3 :=
  fderiv ℝ (torusLift v) y (torusLift u y)

/-- A concrete classical solution predicate for the velocity-pressure system on
`[a,b]`.  The time derivative is in the sup norm on continuous torus fields;
the PDE and incompressibility equations are pointwise. -/
def IsClassicalNavierStokesOn
    (ν a b : ℝ) (u uTime : ℝ → C(Torus3, Vec3))
    (p : ℝ → C(Torus3, ℝ)) : Prop :=
  0 < ν ∧
  ContinuousOn u (Icc a b) ∧
  (∀ t ∈ Ico a b, HasDerivAt u (uTime t) t) ∧
  (∀ t ∈ Icc a b, ContDiff ℝ 2 (torusLift (u t))) ∧
  (∀ t ∈ Icc a b, ContDiff ℝ 1 (torusLift (p t))) ∧
  (∀ t ∈ Icc a b, ∀ x : Torus3, torusDivergence (u t) x = 0) ∧
  ∀ t ∈ Ico a b, ∀ x : Torus3,
    uTime t x + torusTransport (u t) (u t) x =
      ν • torusVectorLaplacian (u t) x - torusGradient (p t) x

/-- Joint time-space lift of a time-dependent periodic field.  Joint
regularity, rather than separate regularity in the two variables, is what
justifies commuting a time derivative with curl. -/
def torusSpaceTimeLift
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → C(Torus3, E)) (q : ℝ × Vec3) : E :=
  torusLift (f q.1) q.2

/-- Smooth refinement of the classical Navier--Stokes predicate used for the
derived vorticity equation.  Besides joint regularity, it records the same
incompressibility and momentum equations directly on every point of the smooth
periodic lift.  This avoids differentiating through the discontinuous choice of
a canonical quotient representative. -/
def IsSmoothNavierStokesOn
    (ν a b : ℝ) (u uTime : ℝ → C(Torus3, Vec3))
    (p : ℝ → C(Torus3, ℝ)) : Prop :=
  IsClassicalNavierStokesOn ν a b u uTime p ∧
  ContDiff ℝ 3 (torusSpaceTimeLift u) ∧
  ContDiff ℝ 2 (torusSpaceTimeLift p) ∧
  (∀ t ∈ Icc a b, ∀ y : Vec3, torusLiftDivergence (u t) y = 0) ∧
  ∀ t ∈ Ico a b, ∀ y : Vec3,
    torusLift (uTime t) y + torusLiftTransport (u t) (u t) y =
      ν • torusLiftVectorLaplacian (u t) y - torusLiftGradient (p t) y

/-- A concrete vorticity field is the curl of the velocity field. -/
def IsVorticityOfOn (a b : ℝ) (u ω : ℝ → C(Torus3, Vec3)) : Prop :=
  ∀ t ∈ Icc a b, ∀ x : Torus3, ω t x = torusCurl (u t) x

/-- The classical viscous vector-vorticity equation on the concrete torus. -/
def IsClassicalVorticityEquationOn
    (ν a b : ℝ) (u ω ωTime : ℝ → C(Torus3, Vec3)) : Prop :=
  0 ≤ ν ∧
  ContinuousOn ω (Icc a b) ∧
  (∀ t ∈ Ico a b, HasDerivAt ω (ωTime t) t) ∧
  (∀ t ∈ Icc a b, ContDiff ℝ 2 (torusLift (ω t))) ∧
  ∀ t ∈ Ico a b, ∀ x : Torus3,
    ωTime t x = torusStretching (u t) (ω t) x +
      ν • torusVectorLaplacian (ω t) x - torusTransport (u t) (ω t) x

@[simp]
theorem torusDirectionalDerivative_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : Torus3) (v : Vec3) :
    torusDirectionalDerivative (0 : C(Torus3, E)) x v = 0 := by
  have hzero : torusLift (0 : C(Torus3, E)) = fun _ : Vec3 => (0 : E) := by
    funext y
    rfl
  rw [torusDirectionalDerivative, hzero]
  simp

@[simp]
theorem torusPartial_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : Torus3) (i : Fin 3) :
    torusPartial (0 : C(Torus3, E)) x i = 0 := by
  simp [torusPartial]

@[simp]
theorem torusGradient_zero (x : Torus3) :
    torusGradient (0 : C(Torus3, ℝ)) x = 0 := by
  ext i
  simp [torusGradient]

@[simp]
theorem torusDivergence_zero (x : Torus3) :
    torusDivergence (0 : C(Torus3, Vec3)) x = 0 := by
  simp [torusDivergence]

@[simp]
theorem torusCurl_zero (x : Torus3) :
    torusCurl (0 : C(Torus3, Vec3)) x = 0 := by
  ext i
  fin_cases i <;> simp [torusCurl]

@[simp]
theorem torusTransport_zero_left (v : C(Torus3, Vec3)) (x : Torus3) :
    torusTransport 0 v x = 0 := by
  simp [torusTransport, torusDirectionalDerivative]

@[simp]
theorem torusTransport_zero_right (u : C(Torus3, Vec3)) (x : Torus3) :
    torusTransport u 0 x = 0 := by
  simp [torusTransport]

@[simp]
theorem torusStretching_zero_left (ω : C(Torus3, Vec3)) (x : Torus3) :
    torusStretching 0 ω x = 0 := by
  simp [torusStretching]

@[simp]
theorem torusStretching_zero_right (u : C(Torus3, Vec3)) (x : Torus3) :
    torusStretching u 0 x = 0 := by
  simp [torusStretching, torusDirectionalDerivative]

@[simp]
theorem torusVectorLaplacian_zero (x : Torus3) :
    torusVectorLaplacian (0 : C(Torus3, Vec3)) x = 0 := by
  simp [torusVectorLaplacian, torusLiftVectorLaplacian,
    torusLiftCoordinateSecondVector, torusLift, coordinateLine]

/-- The concrete classical solution predicate is nonvacuous for every positive
viscosity and time interval: zero velocity and zero pressure solve the system. -/
theorem isClassicalNavierStokesOn_zero {ν a b : ℝ} (hν : 0 < ν) :
    IsClassicalNavierStokesOn ν a b
      (fun _ => (0 : C(Torus3, Vec3)))
      (fun _ => (0 : C(Torus3, Vec3)))
      (fun _ => (0 : C(Torus3, ℝ))) := by
  refine ⟨hν, continuous_const.continuousOn, ?_, ?_, ?_, ?_, ?_⟩
  · intro t _ht
    exact hasDerivAt_const t 0
  · intro t _ht
    have hzero : torusLift (0 : C(Torus3, Vec3)) =
        fun _ : Vec3 => (0 : Vec3) := by
      funext y
      rfl
    rw [hzero]
    exact contDiff_const
  · intro t _ht
    have hzero : torusLift (0 : C(Torus3, ℝ)) =
        fun _ : Vec3 => (0 : ℝ) := by
      funext y
      rfl
    rw [hzero]
    exact contDiff_const
  · intro t _ht x
    exact torusDivergence_zero x
  · intro t _ht x
    simp

/-- The joint-smooth refinement is likewise inhabited by the zero solution. -/
theorem isSmoothNavierStokesOn_zero {ν a b : ℝ} (hν : 0 < ν) :
    IsSmoothNavierStokesOn ν a b
      (fun _ => (0 : C(Torus3, Vec3)))
      (fun _ => (0 : C(Torus3, Vec3)))
      (fun _ => (0 : C(Torus3, ℝ))) := by
  refine ⟨isClassicalNavierStokesOn_zero hν, ?_, ?_, ?_, ?_⟩
  · have hzero : torusSpaceTimeLift
        (fun _ => (0 : C(Torus3, Vec3))) =
        fun _ : ℝ × Vec3 => (0 : Vec3) := by
      funext q
      rfl
    rw [hzero]
    exact contDiff_const
  · have hzero : torusSpaceTimeLift
        (fun _ => (0 : C(Torus3, ℝ))) =
        fun _ : ℝ × Vec3 => (0 : ℝ) := by
      funext q
      rfl
    rw [hzero]
    exact contDiff_const
  · intro t _ht y
    have hzero : torusLift (0 : C(Torus3, Vec3)) =
        fun _ : Vec3 => (0 : Vec3) := by
      funext z
      rfl
    rw [torusLiftDivergence, hzero]
    simp
  · intro t _ht y
    have hzeroV : torusLift (0 : C(Torus3, Vec3)) =
        fun _ : Vec3 => (0 : Vec3) := by
      funext z
      rfl
    have hzeroP : torusLift (0 : C(Torus3, ℝ)) =
        fun _ : Vec3 => (0 : ℝ) := by
      funext z
      rfl
    simp only [torusLiftTransport, torusLiftGradient,
      torusLiftVectorLaplacian, torusLiftCoordinateSecondVector,
      coordinateLine]
    rw [hzeroV, hzeroP]
    simp
    ext i
    rfl

theorem isVorticityOfOn_zero (a b : ℝ) :
    IsVorticityOfOn a b
      (fun _ => (0 : C(Torus3, Vec3)))
      (fun _ => (0 : C(Torus3, Vec3))) := by
  intro t _ht x
  exact (torusCurl_zero x).symm

theorem isClassicalVorticityEquationOn_zero
    {ν a b : ℝ} (hν : 0 ≤ ν) :
    IsClassicalVorticityEquationOn ν a b
      (fun _ => (0 : C(Torus3, Vec3)))
      (fun _ => (0 : C(Torus3, Vec3)))
      (fun _ => (0 : C(Torus3, Vec3))) := by
  refine ⟨hν, continuous_const.continuousOn, ?_, ?_, ?_⟩
  · intro t _ht
    exact hasDerivAt_const t 0
  · intro t _ht
    have hzero : torusLift (0 : C(Torus3, Vec3)) =
        fun _ : Vec3 => (0 : Vec3) := by
      funext y
      rfl
    rw [hzero]
    exact contDiff_const
  · intro t _ht x
    simp

theorem exists_classicalNavierStokesOn_zero {ν a b : ℝ} (hν : 0 < ν) :
    ∃ u uTime p, IsClassicalNavierStokesOn ν a b u uTime p :=
  ⟨fun _ => 0, fun _ => 0, fun _ => 0, isClassicalNavierStokesOn_zero hν⟩

theorem exists_smoothNavierStokesOn_zero {ν a b : ℝ} (hν : 0 < ν) :
    ∃ u uTime p, IsSmoothNavierStokesOn ν a b u uTime p :=
  ⟨fun _ => 0, fun _ => 0, fun _ => 0, isSmoothNavierStokesOn_zero hν⟩

/-- A simultaneous concrete witness for the velocity-pressure and vorticity
predicates.  Thus later conditional theorems cannot be true merely because the
formal solution interfaces have no inhabitants. -/
theorem exists_compatible_classical_zero_solution
    {ν a b : ℝ} (hν : 0 < ν) :
    ∃ u uTime p ω ωTime,
      IsClassicalNavierStokesOn ν a b u uTime p ∧
      IsVorticityOfOn a b u ω ∧
      IsClassicalVorticityEquationOn ν a b u ω ωTime := by
  refine ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0,
    isClassicalNavierStokesOn_zero hν, isVorticityOfOn_zero a b, ?_⟩
  exact isClassicalVorticityEquationOn_zero hν.le
