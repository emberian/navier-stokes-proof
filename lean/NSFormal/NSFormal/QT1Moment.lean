import Mathlib

/-!
# Lean gate, target 3: QT-1's scaling algebra and the moment law's assembly
Honest scope: the integration-by-parts facts enter as hypotheses (their instances are
sympy-certified on exact decaying families: results/sympy_qt1_moment.log; full
measure-theoretic by-parts is a later Lean phase). What the kernel certifies here is the
coefficient arithmetic — the −1/4 of QT-1 and the 4ν − αm₂ of the moment law — the layer
where sign/factor errors live.
-/

/-- QT-1's scaling coefficient: if the by-parts value of the drift term is T = −3e − b
(e the localized energy, b the cutoff tail), then the scaling combination
½e + ¼T = −¼e − ¼b — the −1/4 balance of the defect energy identity. -/
theorem qt1_scaling_coefficient (e b T : ℝ) (h : T = -3*e - b) :
    (1/2)*e + (1/4)*T = -(1/4)*e - (1/4)*b := by
  rw [h]; ring

/-- QT-1 assembled: the localized identity ∫|∇v|²φ² − ¼∫|v|²φ² = defect + tails, given the
gradient/energy/defect/tail values and the equation's tested form. -/
theorem qt1_energy_identity (G e b defect : ℝ)
    (tested : G + ((1/2)*e + (1/4)*(-3*e - b)) + defect = 0) :
    G - (1/4)*e = -defect + (1/4)*b := by
  have h := tested
  nlinarith [h]

/-- The moment law's assembly: advection contributes −2αm₂, stretching +αm₂, viscosity +4ν
(each by-parts instance sympy-certified); the sum is the law dm₂/dt = 4ν − αm₂. -/
theorem moment_law_assembly (a m2 nu adv str visc : ℝ)
    (hadv : adv = -2*a*m2) (hstr : str = a*m2) (hvisc : visc = 4*nu) :
    adv + str + visc = 4*nu - a*m2 := by
  rw [hadv, hstr, hvisc]; ring

/-- The Burgers equilibrium of the law: if 4ν − αm₂ = 0 with α > 0 then m₂ = 4ν/α —
the profile-free equilibrium radius every worm measurement compares against. -/
theorem moment_law_equilibrium (a m2 nu : ℝ) (ha : a ≠ 0) (h : 4*nu - a*m2 = 0) :
    m2 = 4*nu/a := by
  field_simp
  linarith
