import Mathlib

/-!
# Lean gate, target 1: the financing identity's pointwise algebra
The campaign identity ∫ω·Sω = −4∫λ₁λ₂λ₃ (NS_Proof, Lemma ledger §119) rests on three exact
pointwise identities; integration by parts on T³ is the only analytic step. These are the
three, machine-checked. sympy cross-check: results/sympy_financing.log.
-/

open Matrix

/-- Symmetric trace-free strain matrix from its five components. -/
noncomputable def Smat (s11 s12 s13 s22 s23 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![s11, s12, s13; s12, s22, s23; s13, s23, -s11 - s22]

/-- Rotation part: W v = (1/2) ω × v. -/
noncomputable def Wmat (w1 w2 w3 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, -w3/2, w2/2; w3/2, 0, -w1/2; -w2/2, w1/2, 0]

/-- L1: tr((S+W)³) = tr S³ + 3 tr(S·W·W). -/
theorem trace_cube_split (s11 s12 s13 s22 s23 w1 w2 w3 : ℝ) :
    trace ((Smat s11 s12 s13 s22 s23 + Wmat w1 w2 w3) *
           (Smat s11 s12 s13 s22 s23 + Wmat w1 w2 w3) *
           (Smat s11 s12 s13 s22 s23 + Wmat w1 w2 w3))
      = trace (Smat s11 s12 s13 s22 s23 * Smat s11 s12 s13 s22 s23 *
               Smat s11 s12 s13 s22 s23)
        + 3 * trace (Smat s11 s12 s13 s22 s23 * (Wmat w1 w2 w3 * Wmat w1 w2 w3)) := by
  simp [Smat, Wmat, trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three]
  ring

/-- L2 (the sign the campaign's instruments were once wrong about, machine-fixed):
tr(S·W·W) = (1/4)·ωᵀSω. -/
theorem trace_SWW (s11 s12 s13 s22 s23 w1 w2 w3 : ℝ) :
    trace (Smat s11 s12 s13 s22 s23 * (Wmat w1 w2 w3 * Wmat w1 w2 w3))
      = (1/4) * (![w1, w2, w3] ⬝ᵥ (Smat s11 s12 s13 s22 s23).mulVec ![w1, w2, w3]) := by
  simp [Smat, Wmat, trace_fin_three, Matrix.mul_apply, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three]
  ring

/-- L3: for the trace-free symmetric S, tr S³ = 3 det S (= 3λ₁λ₂λ₃). -/
theorem trace_cube_det (s11 s12 s13 s22 s23 : ℝ) :
    trace (Smat s11 s12 s13 s22 s23 * Smat s11 s12 s13 s22 s23 * Smat s11 s12 s13 s22 s23)
      = 3 * det (Smat s11 s12 s13 s22 s23) := by
  simp [Smat, trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three, det_fin_three]
  ring

/-- The assembled pointwise financing algebra: tr((S+W)³) = 3 det S + (3/4) ωᵀSω.
With ∫tr((∇u)³) = 0 on T³ (integration by parts, div-free), this yields
∫ωᵀSω = −4∫det S = −4∫λ₁λ₂λ₃ — the financing identity, sign machine-certified. -/
theorem financing_pointwise (s11 s12 s13 s22 s23 w1 w2 w3 : ℝ) :
    trace ((Smat s11 s12 s13 s22 s23 + Wmat w1 w2 w3) *
           (Smat s11 s12 s13 s22 s23 + Wmat w1 w2 w3) *
           (Smat s11 s12 s13 s22 s23 + Wmat w1 w2 w3))
      = 3 * det (Smat s11 s12 s13 s22 s23)
        + (3/4) * (![w1, w2, w3] ⬝ᵥ (Smat s11 s12 s13 s22 s23).mulVec ![w1, w2, w3]) := by
  rw [trace_cube_split, trace_cube_det, trace_SWW]; ring
