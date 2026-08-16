import Mathlib

/-!
# Analytic part of the strain budget

This file starts replacing the scalar exponent checks in `CampaignAlgebra` by the
measure-theoretic estimates used in the paper.  In particular, the theorem below
is the Hölder step in the time integration of the strain budget:

`∫ Ω^(5/6) ≤ (∫ Ω)^(5/6) μ(univ)^(1/6)`.

Unlike `w10_holder_exponents`, this theorem quantifies over a measurable function
and proves the integral inequality itself.
-/

open MeasureTheory

/-- Hölder's inequality in the exact exponents used to integrate the enstrophy
contribution to the strain budget. -/
theorem integral_rpow_five_six_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {Ω : α → ℝ} (hΩ : Integrable Ω μ) (hΩ_nonneg : 0 ≤ᵐ[μ] Ω) :
    (∫ t, Ω t ^ ((5 : ℝ) / 6) ∂μ) ≤
      (∫ t, Ω t ∂μ) ^ ((5 : ℝ) / 6) * μ.real Set.univ ^ ((1 : ℝ) / 6) := by
  have hpq : ((6 : ℝ) / 5).HolderConjugate 6 := by
    rw [Real.holderConjugate_iff]
    constructor <;> norm_num
  have hΩ_mem : MemLp Ω 1 μ := memLp_one_iff_integrable.mpr hΩ
  have hexp : ENNReal.ofReal ((6 : ℝ) / 5) = (ENNReal.ofReal ((5 : ℝ) / 6))⁻¹ := by
    rw [← ENNReal.ofReal_inv_of_pos (by norm_num : 0 < (5 : ℝ) / 6)]
    norm_num
  have hpow_mem : MemLp (fun t => ‖Ω t‖ ^ ((5 : ℝ) / 6)) (ENNReal.ofReal ((6 : ℝ) / 5)) μ := by
    convert hΩ_mem.norm_rpow_div (ENNReal.ofReal ((5 : ℝ) / 6)) using 1
    · norm_num
    · simpa [one_div] using hexp
  have hone_mem : MemLp (fun _ : α => (1 : ℝ)) (ENNReal.ofReal (6 : ℝ)) μ :=
    memLp_const 1
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hpq
    (f := fun t => ‖Ω t‖ ^ ((5 : ℝ) / 6)) (g := fun _ => (1 : ℝ))
    (Filter.Eventually.of_forall fun _ => Real.rpow_nonneg (norm_nonneg _) _)
    (Filter.Eventually.of_forall fun _ => zero_le_one) hpow_mem hone_mem
  have hnorm : (fun t => ‖Ω t‖) =ᵐ[μ] Ω := by
    filter_upwards [hΩ_nonneg] with t ht
    exact Real.norm_of_nonneg ht
  calc
    (∫ t, Ω t ^ ((5 : ℝ) / 6) ∂μ)
        = ∫ t, ‖Ω t‖ ^ ((5 : ℝ) / 6) * 1 ∂μ := by
            apply integral_congr_ae
            filter_upwards [hΩ_nonneg] with t ht
            rw [Real.norm_of_nonneg ht, mul_one]
    _ ≤ (∫ t, (‖Ω t‖ ^ ((5 : ℝ) / 6)) ^ ((6 : ℝ) / 5) ∂μ) ^ ((5 : ℝ) / 6) *
          (∫ _ : α, (1 : ℝ) ^ (6 : ℝ) ∂μ) ^ ((1 : ℝ) / 6) := by
            simpa using hholder
    _ = (∫ t, Ω t ∂μ) ^ ((5 : ℝ) / 6) * μ.real Set.univ ^ ((1 : ℝ) / 6) := by
          congr 2
          · apply integral_congr_ae
            filter_upwards [hnorm] with t ht
            rw [← ht, ← Real.rpow_mul (norm_nonneg _)]
            norm_num
          · simp

/-- The finite-time form used in the paper: an `L¹` enstrophy budget `∫ Ω ≤ B`
implies the claimed `T^(1/6)` bound. -/
theorem integral_Icc_rpow_five_six_le
    {Ω : ℝ → ℝ} {T B : ℝ} (hT : 0 ≤ T)
    (hΩ : IntegrableOn Ω (Set.Icc 0 T))
    (hΩ_nonneg : 0 ≤ᵐ[volume.restrict (Set.Icc 0 T)] Ω)
    (hbudget : (∫ t in Set.Icc 0 T, Ω t) ≤ B) :
    (∫ t in Set.Icc 0 T, Ω t ^ ((5 : ℝ) / 6)) ≤
      B ^ ((5 : ℝ) / 6) * T ^ ((1 : ℝ) / 6) := by
  have hholder := integral_rpow_five_six_le
    (μ := volume.restrict (Set.Icc 0 T)) hΩ hΩ_nonneg
  have hholder' :
      (∫ t in Set.Icc 0 T, Ω t ^ ((5 : ℝ) / 6)) ≤
        (∫ t in Set.Icc 0 T, Ω t) ^ ((5 : ℝ) / 6) * T ^ ((1 : ℝ) / 6) := by
    simpa [Measure.real, Real.volume_Icc, hT] using hholder
  have hint_nonneg : 0 ≤ ∫ t in Set.Icc 0 T, Ω t := integral_nonneg_of_ae hΩ_nonneg
  have hpow :
      (∫ t in Set.Icc 0 T, Ω t) ^ ((5 : ℝ) / 6) ≤ B ^ ((5 : ℝ) / 6) :=
    Real.rpow_le_rpow hint_nonneg hbudget (by norm_num)
  exact hholder'.trans (mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hT _))

/-- A continuous pointwise strain estimate closes to the finite-time integrated
budget used by the maximum principle.  The three terms represent the
subcritical `Ω^(5/6)` contribution, the linear enstrophy contribution, and a
bounded background contribution. -/
theorem intervalIntegral_strain_budget_le
    {Ω γ : ℝ → ℝ} {T B C5 C1 C0 : ℝ}
    (hT : 0 ≤ T) (hC5 : 0 ≤ C5) (hC1 : 0 ≤ C1)
    (hΩ_cont : Continuous Ω) (hγ_cont : Continuous γ)
    (hΩ_nonneg : ∀ t, 0 ≤ Ω t)
    (hbudget : (∫ t in Set.Icc 0 T, Ω t) ≤ B)
    (hγ_bound : ∀ t ∈ Set.Icc 0 T,
      γ t ≤ C5 * Ω t ^ ((5 : ℝ) / 6) + C1 * Ω t + C0) :
    (∫ t in (0 : ℝ)..T, γ t) ≤
      C5 * B ^ ((5 : ℝ) / 6) * T ^ ((1 : ℝ) / 6) + C1 * B + C0 * T := by
  have hΩ_integrableOn : IntegrableOn Ω (Set.Icc 0 T) :=
    hΩ_cont.integrableOn_Icc
  have hΩ_ae : 0 ≤ᵐ[volume.restrict (Set.Icc 0 T)] Ω :=
    Filter.Eventually.of_forall hΩ_nonneg
  have hholder_set := integral_Icc_rpow_five_six_le
    hT hΩ_integrableOn hΩ_ae hbudget
  have hholder_interval :
      (∫ t in (0 : ℝ)..T, Ω t ^ ((5 : ℝ) / 6)) ≤
        B ^ ((5 : ℝ) / 6) * T ^ ((1 : ℝ) / 6) := by
    rw [intervalIntegral.integral_of_le hT,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    exact hholder_set
  have hΩ_interval : (∫ t in (0 : ℝ)..T, Ω t) ≤ B := by
    rw [intervalIntegral.integral_of_le hT,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    exact hbudget
  have hpow_cont : Continuous (fun t => Ω t ^ ((5 : ℝ) / 6)) :=
    hΩ_cont.rpow_const (fun _ => Or.inr (by norm_num))
  have h5_cont : Continuous (fun t => C5 * Ω t ^ ((5 : ℝ) / 6)) := by
    fun_prop
  have h1_cont : Continuous (fun t => C1 * Ω t) := by
    fun_prop
  have h0_cont : Continuous (fun _ : ℝ => C0) := continuous_const
  have hright_cont : Continuous
      (fun t => C5 * Ω t ^ ((5 : ℝ) / 6) + C1 * Ω t + C0) := by
    fun_prop
  have hmono :
      (∫ t in (0 : ℝ)..T, γ t) ≤
        ∫ t in (0 : ℝ)..T,
          (C5 * Ω t ^ ((5 : ℝ) / 6) + C1 * Ω t + C0) :=
    intervalIntegral.integral_mono_on hT
      (hγ_cont.intervalIntegrable 0 T)
      (hright_cont.intervalIntegrable 0 T) hγ_bound
  calc
    (∫ t in (0 : ℝ)..T, γ t)
        ≤ ∫ t in (0 : ℝ)..T,
            (C5 * Ω t ^ ((5 : ℝ) / 6) + C1 * Ω t + C0) := hmono
    _ = C5 * (∫ t in (0 : ℝ)..T, Ω t ^ ((5 : ℝ) / 6)) +
          C1 * (∫ t in (0 : ℝ)..T, Ω t) + C0 * T := by
          calc
            (∫ t in (0 : ℝ)..T,
                (C5 * Ω t ^ ((5 : ℝ) / 6) + C1 * Ω t + C0)) =
                (∫ t in (0 : ℝ)..T,
                  (C5 * Ω t ^ ((5 : ℝ) / 6) + C1 * Ω t)) +
                ∫ _ in (0 : ℝ)..T, C0 := by
                  simpa only [Pi.add_apply] using
                    intervalIntegral.integral_add
                      ((h5_cont.add h1_cont).intervalIntegrable
                        (μ := volume) 0 T)
                      (h0_cont.intervalIntegrable (μ := volume) 0 T)
            _ = ((∫ t in (0 : ℝ)..T, C5 * Ω t ^ ((5 : ℝ) / 6)) +
                  ∫ t in (0 : ℝ)..T, C1 * Ω t) +
                ∫ _ in (0 : ℝ)..T, C0 := by
                  congr 1
                  simpa only [Pi.add_apply] using
                    intervalIntegral.integral_add
                      (h5_cont.intervalIntegrable (μ := volume) 0 T)
                      (h1_cont.intervalIntegrable (μ := volume) 0 T)
            _ = C5 * (∫ t in (0 : ℝ)..T, Ω t ^ ((5 : ℝ) / 6)) +
                  C1 * (∫ t in (0 : ℝ)..T, Ω t) + C0 * T := by
                  simp only [intervalIntegral.integral_const_mul,
                    intervalIntegral.integral_const, sub_zero, smul_eq_mul]
                  ring
    _ ≤ C5 * (B ^ ((5 : ℝ) / 6) * T ^ ((1 : ℝ) / 6)) +
          C1 * B + C0 * T := by
          gcongr
    _ = C5 * B ^ ((5 : ℝ) / 6) * T ^ ((1 : ℝ) / 6) + C1 * B + C0 * T := by
          ring
