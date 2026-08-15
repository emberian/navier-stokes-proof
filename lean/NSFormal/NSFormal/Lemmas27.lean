import Mathlib

/-!
# Lean gate, target 4: the algebraic cores of Lemmas 2, 3, 5, 7
(Lemma 1 is Financing.lean; Lemmas 4 and 6 are integral/ODE class — deferred with the
torus-by-parts phase.) Statements from NS_Proof.md's lemma ledger.
-/

open Matrix

/-- Lemma 2's core (pancake extremal), squared form: under Σλ = 0,
(Σλ²)³ − 54(λ₀λ₁λ₂)² = 2·[(λ₀−λ₁)(λ₁−λ₂)(λ₀−λ₂)]² ≥ 0 — an exact discriminant identity;
equality iff two eigenvalues coincide (the degenerate pancake). This is the algebra behind
−λ₁λ₂λ₃ ≤ (1/(3√6))(trS²)^{3/2}. -/
theorem pancake_extremal_sq (l0 l1 l2 : ℝ) (h : l0 + l1 + l2 = 0) :
    54 * (l0*l1*l2)^2 ≤ (l0^2 + l1^2 + l2^2)^3 := by
  have key : (l0^2 + l1^2 + l2^2)^3 - 54*(l0*l1*l2)^2
      = 2*((l0-l1)*(l1-l2)*(l0-l2))^2 := by
    have h2 : l2 = -l0 - l1 := by linarith
    subst h2; ring
  nlinarith [sq_nonneg ((l0-l1)*(l1-l2)*(l0-l2)), key]

/-- Lemma 3's core (the veto): a z-invariant flow's gradient has vanishing third row and
column; its symmetric part then annihilates ẑ exactly — Sẑ = 0, hence ẑ·Sẑ = 0. -/
theorem veto_algebra (g11 g12 g21 g22 : ℝ) :
    (((1:ℝ)/2) • (!![g11, g12, 0; g21, g22, 0; 0, 0, 0] +
      (!![g11, g12, 0; g21, g22, 0; 0, 0, 0])ᵀ)).mulVec ![0, 0, 1] = 0 := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- Lemma 5's core (parity): the Constantin kernel's O(y) term
D(y) = (y·ξ)·(y·((My)×ξ)) is odd under y → −y — the principal value annihilates it, so
uniform bending does not stretch. Fully scalar form (M the frozen direction gradient). -/
theorem parity_kernel_odd (x1 x2 x3 m11 m12 m13 m21 m22 m23 m31 m32 m33 y1 y2 y3 : ℝ) :
    (let D := fun (z1 z2 z3 : ℝ) =>
      (z1*x1 + z2*x2 + z3*x3) *
      (z1*((m21*z1 + m22*z2 + m23*z3)*x3 - (m31*z1 + m32*z2 + m33*z3)*x2)
       + z2*((m31*z1 + m32*z2 + m33*z3)*x1 - (m11*z1 + m12*z2 + m13*z3)*x3)
       + z3*((m11*z1 + m12*z2 + m13*z3)*x2 - (m21*z1 + m22*z2 + m23*z3)*x1))
     D (-y1) (-y2) (-y3) = - D y1 y2 y3) := by
  simp only []
  ring

/-- Lemma 7's core (Rayleigh monotonicity): (1+x)e^{−x} < 1 for x > 0 — the sign of
Ω′(r) = (2/r³)((1+r²)e^{−r²} − 1) < 0: the Lamb–Oseen angular velocity is strictly
decreasing, so the critical radius is unique. -/
theorem rayleigh_core (x : ℝ) (hx : 0 < x) : (1 + x) * Real.exp (-x) < 1 := by
  have h := Real.add_one_lt_exp (ne_of_gt hx)
  have hpos := Real.exp_pos x
  rw [Real.exp_neg]
  rw [mul_inv_lt_iff₀ hpos, one_mul]
  linarith
