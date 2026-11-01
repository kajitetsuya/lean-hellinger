/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.Comparison.DensityTailBridge
public import Hellinger.Comparison.FiniteMoment
public import Hellinger.HellingerBasic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The source power-density separation: the uniform law on `(0,1)` and density `2x`.
All measures below are actual Borel measures on the real line. -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Hellinger.Comparison.Examples.Power

noncomputable def uniformLaw : Measure ℝ := volume.restrict (Ioo 0 1)

noncomputable def linearDensity (x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (2 * x)

noncomputable def linearLaw : Measure ℝ := uniformLaw.withDensity linearDensity

theorem measurable_linearDensity : Measurable linearDensity :=
  (measurable_const.mul measurable_id).ennreal_ofReal

theorem uniformLaw_eq_volume_withDensity :
    uniformLaw = volume.withDensity ((Ioo (0 : ℝ) 1).indicator 1) :=
  (withDensity_indicator_one measurableSet_Ioo).symm

theorem linearLaw_eq_volume_withDensity :
    linearLaw = volume.withDensity ((Ioo (0 : ℝ) 1).indicator linearDensity) :=
  (withDensity_indicator measurableSet_Ioo linearDensity).symm

instance uniformLaw_isProbabilityMeasure : IsProbabilityMeasure uniformLaw where
  measure_univ := by norm_num [uniformLaw, Measure.restrict_apply, Real.volume_Ioo]

theorem uniformLaw_ae_mem : ∀ᵐ x ∂uniformLaw, x ∈ Ioo (0 : ℝ) 1 :=
  self_mem_ae_restrict measurableSet_Ioo

theorem integrable_linear : Integrable (fun x : ℝ ↦ 2 * x) uniformLaw := by
  change IntegrableOn (fun x : ℝ ↦ 2 * x) (Ioo 0 1)
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le
    (by norm_num : (0 : ℝ) ≤ 1)).mp
    ((continuous_const.mul continuous_id).intervalIntegrable 0 1)

theorem integral_linear : ∫ x, 2 * x ∂uniformLaw = 1 := by
  change (∫ x in Ioo (0 : ℝ) 1, 2 * x) = 1
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_const_mul, integral_id]
  norm_num

theorem linearLaw_mass_univ : linearLaw univ = 1 := by
  change uniformLaw.withDensity linearDensity univ = 1
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  change (∫⁻ x, ENNReal.ofReal (2 * x) ∂uniformLaw) = 1
  have hnonneg : 0 ≤ᵐ[uniformLaw] (fun x : ℝ ↦ 2 * x) := by
    filter_upwards [uniformLaw_ae_mem] with x hx
    exact mul_nonneg (by norm_num) hx.1.le
  rw [← ofReal_integral_eq_lintegral_ofReal integrable_linear hnonneg, integral_linear]
  norm_num

instance linearLaw_isProbabilityMeasure : IsProbabilityMeasure linearLaw where
  measure_univ := linearLaw_mass_univ

theorem rnDeriv_linearLaw_ae : linearLaw.rnDeriv uniformLaw =ᵐ[uniformLaw] linearDensity :=
  Measure.rnDeriv_withDensity uniformLaw measurable_linearDensity

theorem uniformLaw_absolutelyContinuous_linearLaw : uniformLaw ≪ linearLaw := by
  apply withDensity_absolutelyContinuous' measurable_linearDensity.aemeasurable
  filter_upwards [uniformLaw_ae_mem] with x hx
  exact (ENNReal.ofReal_pos.mpr (mul_pos (by norm_num) hx.1)).ne'

/-- The actual source ratio is `1/(2x)` on its probability space. -/
theorem dominatedRatio_ae_eq_inverse_linear :
    dominatedRatio uniformLaw linearLaw uniformLaw =ᵐ[uniformLaw]
      fun x ↦ ENNReal.ofReal ((2 * x)⁻¹) := by
  filter_upwards [dominatedRatio_ae_eq_inv_rnDeriv
      (μ := uniformLaw) (ν := linearLaw) (κ := uniformLaw) Measure.AbsolutelyContinuous.rfl,
    rnDeriv_linearLaw_ae, uniformLaw_ae_mem] with x hratio hrn hx
  rw [hratio, hrn, linearDensity,
    ← ENNReal.ofReal_inv_of_pos (mul_pos (by norm_num) hx.1)]

theorem not_integrable_inverse : ¬ Integrable (fun x : ℝ ↦ x⁻¹) uniformLaw := by
  intro h
  have hr : IntegrableOn (fun x : ℝ ↦ x ^ (-1 : ℝ)) (Ioo 0 1) := by
    simpa only [uniformLaw, IntegrableOn, Real.rpow_neg_one] using h
  have hs := (intervalIntegral.integrableOn_Ioo_rpow_iff (s := (-1 : ℝ))
    (by norm_num : (0 : ℝ) < 1)).mp hr
  linarith

theorem not_integrable_inverse_linear :
    ¬ Integrable (fun x : ℝ ↦ (2 * x)⁻¹) uniformLaw := by
  intro h
  apply not_integrable_inverse
  have h2 := h.const_mul 2
  have heq : (fun x : ℝ ↦ 2 * (2 * x)⁻¹) = fun x ↦ x⁻¹ := by
    funext x
    rw [mul_inv_rev]
    ring
  rwa [heq] at h2

/-- The genuine full first ratio moment diverges at zero. -/
theorem fullRatioMoment_eq_top : fullRatioMoment uniformLaw linearLaw = ∞ := by
  rw [fullRatioMoment_eq_lintegral_dominatedRatio
    (κ := uniformLaw) Measure.AbsolutelyContinuous.rfl,
    lintegral_congr_ae dominatedRatio_ae_eq_inverse_linear]
  have hnn : 0 ≤ᵐ[uniformLaw] (fun x : ℝ ↦ (2 * x)⁻¹) := by
    filter_upwards [uniformLaw_ae_mem] with x hx
    exact inv_nonneg.mpr (mul_nonneg (by norm_num) hx.1.le)
  by_contra hfinite
  exact not_integrable_inverse_linear
    ((lintegral_ofReal_ne_top_iff_integrable
      (measurable_const.mul measurable_id).inv.aestronglyMeasurable hnn).mp hfinite)

/-- Finiteness of `x^(-1/2)` establishes the literal half-power ratio moment. -/
theorem integrable_inverse_linear_half :
    Integrable (fun x : ℝ ↦ ((2 * x)⁻¹) ^ (1 / 2 : ℝ)) uniformLaw := by
  have hp : Integrable (fun x : ℝ ↦ x ^ (-(1 / 2 : ℝ))) uniformLaw := by
    change IntegrableOn (fun x : ℝ ↦ x ^ (-(1 / 2 : ℝ))) (Ioo 0 1)
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)).mpr
      (by norm_num)
  apply (hp.const_mul ((2 : ℝ) ^ (-(1 / 2 : ℝ)))).congr
  filter_upwards [uniformLaw_ae_mem] with x hx
  rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hx.1.le,
    Real.rpow_neg_eq_inv_rpow]

/-- Every fixed ordinary cutoff greater than one has a finite half-power tail. -/
theorem tailPower_half_lt_top {q : ℝ} (hq : 1 < q) :
    tailPower uniformLaw linearLaw q (1 / 2) < ∞ := by
  have hkernel : (fun x ↦ dominatedRatio uniformLaw linearLaw uniformLaw x ^ (1 / 2 : ℝ))
      =ᵐ[uniformLaw] fun x ↦ ENNReal.ofReal (((2 * x)⁻¹) ^ (1 / 2 : ℝ)) := by
    filter_upwards [dominatedRatio_ae_eq_inverse_linear, uniformLaw_ae_mem] with x hr hx
    rw [hr, ENNReal.ofReal_rpow_of_pos (inv_pos.mpr (mul_pos (by norm_num) hx.1))]
  have hnn : 0 ≤ᵐ[uniformLaw] (fun x : ℝ ↦ ((2 * x)⁻¹) ^ (1 / 2 : ℝ)) := by
    filter_upwards [uniformLaw_ae_mem] with x hx
    exact Real.rpow_nonneg (inv_nonneg.mpr (mul_nonneg (by norm_num) hx.1.le)) _
  calc
    tailPower uniformLaw linearLaw q (1 / 2) =
        ∫⁻ x in dominatedStrictTailEvent uniformLaw linearLaw uniformLaw q,
          dominatedRatio uniformLaw linearLaw uniformLaw x ^ (1 / 2 : ℝ) ∂uniformLaw :=
      tailPower_eq_setLIntegral_dominatedRatio_rpow Measure.AbsolutelyContinuous.rfl hq
        (by norm_num)
    _ ≤ ∫⁻ x, dominatedRatio uniformLaw linearLaw uniformLaw x ^ (1 / 2 : ℝ) ∂uniformLaw :=
      setLIntegral_le_lintegral _ _
    _ = ∫⁻ x, ENNReal.ofReal (((2 * x)⁻¹) ^ (1 / 2 : ℝ)) ∂uniformLaw :=
      lintegral_congr_ae hkernel
    _ < ∞ := lt_top_iff_ne_top.mpr
      ((lintegral_ofReal_ne_top_iff_integrable
        integrable_inverse_linear_half.aestronglyMeasurable hnn).mpr
          integrable_inverse_linear_half)

/-- The full-moment/tail equivalence retains divergence for every fixed cutoff. -/
theorem tailPower_one_eq_top {q : ℝ} (hq : 1 < q) :
    tailPower uniformLaw linearLaw q 1 = ∞ := by
  by_contra htail
  have hfull := (fullRatioMoment_lt_top_iff_tailPower_one_lt_top hq).mpr
    (lt_top_iff_ne_top.mpr htail)
  rw [fullRatioMoment_eq_top] at hfull
  exact lt_irrefl _ hfull

theorem hellingerSq_pos : 0 < hellingerSq uniformLaw linearLaw := by
  apply pos_iff_ne_zero.mpr
  intro hz
  have heq := (hellingerSq_eq_zero_iff uniformLaw linearLaw).mp hz
  have hself : fullRatioMoment uniformLaw uniformLaw = 1 := by
    rw [fullRatioMoment_eq_lintegral_rnDeriv Measure.AbsolutelyContinuous.rfl]
    calc
      _ = ∫⁻ _x, (1 : ℝ≥0∞) ∂uniformLaw := lintegral_congr_ae uniformLaw.rnDeriv_self
      _ = 1 := by simp
  have htop := fullRatioMoment_eq_top
  rw [← heq, hself] at htop
  exact ENNReal.one_ne_top htop

/-- The paper's smaller-exponent Hellinger multiplier is genuinely finite. -/
theorem exists_half_tail_multiplier {q : ℝ} (hq : 1 < q) :
    ∃ M : ℝ≥0, tailPower uniformLaw linearLaw q (1 / 2) ≤
      (M : ℝ≥0∞) * hellingerSq uniformLaw linearLaw := by
  have hH0 := hellingerSq_pos.ne'
  have hHtop := hellingerSq_ne_top uniformLaw linearLaw
  have hC := ENNReal.div_lt_top (tailPower_half_lt_top hq).ne hH0
  refine ⟨(tailPower uniformLaw linearLaw q (1 / 2) /
    hellingerSq uniformLaw linearLaw).toNNReal, ?_⟩
  rw [ENNReal.coe_toNNReal hC.ne, ENNReal.div_mul_cancel hH0 hHtop]

theorem no_one_tail_multiplier {q : ℝ} (hq : 1 < q) (M : ℝ≥0) :
    ¬ tailPower uniformLaw linearLaw q 1 ≤
      (M : ℝ≥0∞) * hellingerSq uniformLaw linearLaw := by
  intro h
  have hfin : (M : ℝ≥0∞) * hellingerSq uniformLaw linearLaw < ∞ :=
    ENNReal.mul_lt_top ENNReal.coe_lt_top (hellingerSq_ne_top uniformLaw linearLaw).lt_top
  have ht := h.trans_lt hfin
  rw [tailPower_one_eq_top hq] at ht
  exact lt_irrefl _ ht

/-- The literal two densities give the asserted exponent separation for every fixed cutoff. -/
theorem power_density_separation {q : ℝ} (hq : 1 < q) :
    0 < hellingerSq uniformLaw linearLaw ∧
      tailPower uniformLaw linearLaw q (1 / 2) < ∞ ∧
      tailPower uniformLaw linearLaw q 1 = ∞ :=
  ⟨hellingerSq_pos, tailPower_half_lt_top hq, tailPower_one_eq_top hq⟩

theorem power_density_separation_four :
    0 < hellingerSq uniformLaw linearLaw ∧
      tailPower uniformLaw linearLaw 4 (1 / 2) < ∞ ∧
      tailPower uniformLaw linearLaw 4 1 = ∞ :=
  power_density_separation (by norm_num)

end Hellinger.Comparison.Examples.Power
