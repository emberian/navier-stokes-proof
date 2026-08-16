import Mathlib

/-!
# The periodic spatial domain

The paper works on the concrete period-`2π` three-torus.  This file fixes that
domain as an actual compact, nonempty type rather than leaving the spatial domain
as a field of a hypothesis structure.
-/

noncomputable section

/-- Positivity of the physical period, used by Mathlib's compact `AddCircle`
instance. -/
instance torusPeriodPositive : Fact (0 < (2 : ℝ) * Real.pi) := ⟨by positivity⟩

/-- The spatial torus `(ℝ / 2πℤ)³`. -/
abbrev Torus3 := Fin 3 → AddCircle ((2 : ℝ) * Real.pi)

/-- Three-component real vectors, used for velocity and vorticity. -/
abbrev Vec3 := EuclideanSpace ℝ (Fin 3)

/-- The distinguished origin proves constructively that `Torus3` is inhabited. -/
def torus3Origin : Torus3 := 0

instance : Inhabited Torus3 := ⟨torus3Origin⟩

theorem torus3_univ_nonempty : (Set.univ : Set Torus3).Nonempty :=
  ⟨torus3Origin, Set.mem_univ _⟩

theorem torus3_univ_compact : IsCompact (Set.univ : Set Torus3) :=
  isCompact_univ

/-- Continuous scalar fields on the physical torus. -/
abbrev ContinuousScalarField := C(Torus3, ℝ)

/-- Continuous vector fields on the physical torus. -/
abbrev ContinuousVectorField := C(Torus3, Vec3)

