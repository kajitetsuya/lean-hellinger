/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.Comparison.Examples.Normal
public import Hellinger.Comparison.FiniteMoment
public import Mathlib.Probability.CDF
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Genuine standard-normal upper tails and their analytic primitives.
The integrability proof precedes all use of the real improper integral. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace Hellinger.Comparison.Examples.Normal

noncomputable def phi (x : ℝ) : ℝ := gaussianPDFReal 0 1 x

theorem phi_pos (x : ℝ) : 0 < phi x := gaussianPDFReal_pos 0 1 x (by norm_num)

theorem continuous_phi : Continuous phi := by
  unfold phi gaussianPDFReal
  fun_prop

theorem integrable_phi : Integrable phi := integrable_gaussianPDFReal 0 1

/-- The upper tail is an actual integrable Gaussian density integral. -/
noncomputable def upperTail (z : ℝ) : ℝ := ∫ x in Ioi z, phi x

theorem ofReal_upperTail_eq_measure (z : ℝ) :
    ENNReal.ofReal (upperTail z) = normalLaw 0 (Ioi z) := by
  simpa only [normalLaw, upperTail, phi] using
    (gaussianReal_apply_eq_integral 0 (by norm_num : (1 : ℝ≥0) ≠ 0) (Ioi z)).symm

theorem ofReal_upperTail_eq_measure_closed (z : ℝ) :
    ENNReal.ofReal (upperTail z) = normalLaw 0 (Ici z) :=
  (ofReal_upperTail_eq_measure z).trans (measure_congr Ioi_ae_eq_Ici)

theorem upperTail_pos (z : ℝ) : 0 < upperTail z := by
  apply ENNReal.ofReal_pos.mp
  rw [ofReal_upperTail_eq_measure]
  exact (volume_absolutelyContinuous_normalLaw 0).pos_mono
    (isOpen_Ioi.measure_pos volume nonempty_Ioi)

theorem upperTail_le_one (z : ℝ) : upperTail z ≤ 1 := by
  apply (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 1)).mp
  rw [ofReal_upperTail_eq_measure, ENNReal.ofReal_one]
  exact prob_le_one

theorem upperTail_eq_zero_sub_integral (z : ℝ) :
    upperTail z = upperTail 0 - ∫ x in (0 : ℝ)..z, phi x := by
  have hh := intervalIntegral.integral_Ioi_sub_Ioi'
    (integrable_phi.integrableOn (s := Ioi (0 : ℝ)))
    (integrable_phi.integrableOn (s := Ioi z))
  change upperTail 0 - upperTail z = (∫ x in (0 : ℝ)..z, phi x) at hh
  linarith

/-- Differentiation of the tail uses a finite continuous primitive, not an assumed CDF formula. -/
theorem hasDerivAt_upperTail (z : ℝ) : HasDerivAt upperTail (-phi z) z := by
  convert (continuous_phi.integral_hasStrictDerivAt 0 z).hasDerivAt.const_sub (upperTail 0) using 1
  funext y
  exact upperTail_eq_zero_sub_integral y

theorem continuous_upperTail : Continuous upperTail :=
  continuous_iff_continuousAt.mpr fun z ↦ (hasDerivAt_upperTail z).continuousAt

theorem tendsto_upperTail_atTop : Tendsto upperTail atTop (𝓝 0) := by
  exact tendsto_integral_Ioi_zero (f := phi) (μ := volume) tendsto_id

theorem standardLaw_map_neg : (normalLaw 0).map (fun x : ℝ ↦ -x) = normalLaw 0 := by
  simpa only [normalLaw, neg_zero] using (gaussianReal_map_neg (μ := 0) (v := 1))

/-- Reflection identifies the actual upper tail with the standard-normal CDF. -/
theorem upperTail_eq_cdf_neg (z : ℝ) : upperTail z = cdf (normalLaw 0) (-z) := by
  have hreflect : normalLaw 0 (Iic (-z)) = normalLaw 0 (Ici z) := by
    calc
      normalLaw 0 (Iic (-z)) = (normalLaw 0).map (fun x : ℝ ↦ -x) (Iic (-z)) := by
        rw [standardLaw_map_neg]
      _ = normalLaw 0 ((fun x : ℝ ↦ -x) ⁻¹' Iic (-z)) :=
        Measure.map_apply measurable_neg measurableSet_Iic
      _ = normalLaw 0 (Ici z) := by
        congr 1
        ext x
        simp only [mem_preimage, mem_Iic, neg_le_neg_iff, mem_Ici]
  apply (ENNReal.ofReal_eq_ofReal_iff (upperTail_pos z).le (cdf_nonneg _ _)).mp
  rw [ofReal_upperTail_eq_measure, ofReal_cdf]
  exact (measure_congr Ioi_ae_eq_Ici).trans hreflect.symm

/-- The density tilt is proved pointwise before it is integrated over a tail. -/
theorem gaussian_density_mul_ratio (theta x : ℝ) :
    gaussianPDFReal 0 1 x * ratio theta x =
      Real.exp (theta ^ 2) * gaussianPDFReal (-theta) 1 x := by
  have hh := NormalScalar.gaussianPDFReal_exp_tilt 0 1 (-theta) x
  simp only [NNReal.coe_one, zero_mul, zero_add, one_mul, neg_sq] at hh
  rw [ratio, Real.exp_add, ← mul_assoc, hh]
  have he : Real.exp (theta ^ 2 / 2) * Real.exp (theta ^ 2 / 2) =
      Real.exp (theta ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.exp (theta ^ 2 / 2) * Real.exp (theta ^ 2 / 2)) *
        gaussianPDFReal (-theta) 1 x := by ring
    _ = _ := by rw [he]

/-- Weighting the genuine source Gaussian by its likelihood ratio gives a scaled
oppositely shifted Gaussian. This identity applies to every measurable truncation. -/
theorem normalLaw_withDensity_ratio (theta : ℝ) :
    (normalLaw 0).withDensity (fun x ↦ ENNReal.ofReal (ratio theta x)) =
      ENNReal.ofReal (Real.exp (theta ^ 2)) • normalLaw (-theta) := by
  have hR : Measurable (fun x ↦ ENNReal.ofReal (ratio theta x)) :=
    (continuous_ratio theta).measurable.ennreal_ofReal
  have hd : (gaussianPDF 0 1 * fun x ↦ ENNReal.ofReal (ratio theta x)) =
      ENNReal.ofReal (Real.exp (theta ^ 2)) • gaussianPDF (-theta) 1 := by
    funext x
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, gaussianPDF]
    rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 1 x),
      gaussian_density_mul_ratio,
      ENNReal.ofReal_mul (Real.exp_pos (theta ^ 2)).le]
  have h0 : normalLaw 0 = volume.withDensity (gaussianPDF 0 1) :=
    gaussianReal_of_var_ne_zero 0 (by norm_num)
  have ht : normalLaw (-theta) = volume.withDensity (gaussianPDF (-theta) 1) :=
    gaussianReal_of_var_ne_zero (-theta) (by norm_num)
  rw [h0, ht, ← withDensity_mul volume (measurable_gaussianPDF 0 1) hR,
    hd, withDensity_smul _ (measurable_gaussianPDF (-theta) 1)]

theorem setLIntegral_ratio (theta : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    (∫⁻ x in A, ENNReal.ofReal (ratio theta x) ∂normalLaw 0) =
      ENNReal.ofReal (Real.exp (theta ^ 2)) * normalLaw (-theta) A := by
  have hh := congrArg (fun m : Measure ℝ ↦ m A) (normalLaw_withDensity_ratio theta)
  simpa only [withDensity_apply _ hA, Measure.coe_smul, Pi.smul_apply, smul_eq_mul] using hh

theorem fullRatioMoment_normalLaw (theta : ℝ) :
    fullRatioMoment (normalLaw 0) (normalLaw theta) =
      ENNReal.ofReal (Real.exp (theta ^ 2)) := by
  rw [fullRatioMoment_eq_lintegral_dominatedRatio (normalLaw_absolutelyContinuous_volume 0),
    lintegral_congr_ae (dominatedRatio_ae_eq_ratio theta)]
  have hh := setLIntegral_ratio theta MeasurableSet.univ
  simpa only [setLIntegral_univ, measure_univ, mul_one] using hh

/-- Memberwise finiteness is distinct from the still-required local uniform CM estimate. -/
theorem conditionalMoment_normalLaw_lt_top (theta : ℝ) :
    conditionalMoment (normalLaw 0) (normalLaw theta) < ∞ := by
  apply conditionalMoment_lt_top_of_fullRatioMoment_lt_top
  rw [fullRatioMoment_normalLaw]
  exact ENNReal.ofReal_lt_top

theorem closedTailEvent_normalLaw_ae (theta : ℝ) {t : ℝ} (ht : 0 < t) :
    closedTailEvent (normalLaw 0) (normalLaw theta) t =ᵐ[normalLaw 0]
      {x | t ≤ ratio theta x} := by
  apply Filter.eventuallyEqSet_iff.mpr
  filter_upwards [llr_normalLaw_ae theta] with x hx
  change (Real.log t ≤ llr (normalLaw 0) (normalLaw theta) x) ↔ t ≤ ratio theta x
  rw [hx]
  exact Real.log_le_iff_le_exp ht

theorem closedTailMoment_normalLaw_eq_setLIntegral_ratio (theta : ℝ) {t : ℝ}
    (ht : 0 < t) :
    closedTailMoment (normalLaw 0) (normalLaw theta) t =
      ∫⁻ x in {x | t ≤ ratio theta x}, ENNReal.ofReal (ratio theta x) ∂normalLaw 0 := by
  have hm : MeasurableSet {x | t ≤ ratio theta x} :=
    measurableSet_le measurable_const (continuous_ratio theta).measurable
  rw [closedTailMoment_of_ac (normalLaw_absolutelyContinuous 0 theta),
    ← lintegral_indicator (measurableSet_closedTailEvent (normalLaw 0) (normalLaw theta) t),
    ← lintegral_indicator hm]
  apply lintegral_congr_ae
  filter_upwards [llr_normalLaw_ae theta] with x hx
  simp only [Set.indicator_apply, closedTailEvent, Set.mem_ofPred_eq, hx, ratio,
    Real.log_le_iff_le_exp ht]

/-- Reflection in the sign of theta preserves standard-normal variance. -/
noncomputable def reflectedSign (theta : ℝ) : ℝ := -theta / |theta|

noncomputable def ratioCutoff (theta b : ℝ) : ℝ :=
  (Real.log b - theta ^ 2 / 2) / |theta|

theorem reflectedSign_sq {theta : ℝ} (htheta : theta ≠ 0) :
    reflectedSign theta ^ 2 = 1 := by
  unfold reflectedSign
  rw [div_pow, neg_sq, sq_abs, div_self (pow_ne_zero 2 htheta)]

theorem reflectedSign_mul_neg_theta {theta : ℝ} (htheta : theta ≠ 0) :
    reflectedSign theta * (-theta) = |theta| := by
  have hs : |theta| ≠ 0 := abs_ne_zero.mpr htheta
  unfold reflectedSign
  calc
    (-theta / |theta|) * (-theta) = theta ^ 2 / |theta| := by ring
    _ = |theta| := (div_eq_iff hs).mpr (by nlinarith [sq_abs theta])

theorem reflectedSign_mul_abs {theta : ℝ} (htheta : theta ≠ 0) (x : ℝ) :
    (reflectedSign theta * x) * |theta| = -theta * x := by
  unfold reflectedSign
  calc
    (-theta / |theta| * x) * |theta| = (-theta * x) * (|theta|⁻¹ * |theta|) := by ring
    _ = -theta * x := by rw [inv_mul_cancel₀ (abs_ne_zero.mpr htheta), mul_one]

theorem ratioCutoff_eq {theta : ℝ} (htheta : theta ≠ 0) (b : ℝ) :
    ratioCutoff theta b = Real.log b / |theta| - |theta| / 2 := by
  unfold ratioCutoff
  rw [← sq_abs theta]
  field_simp [abs_ne_zero.mpr htheta]

theorem ratio_ge_iff_reflectedSign {theta b : ℝ} (htheta : theta ≠ 0)
    (hb : 0 < b) (x : ℝ) :
    b ≤ ratio theta x ↔ ratioCutoff theta b ≤ reflectedSign theta * x := by
  have hs : 0 < |theta| := abs_pos.mpr htheta
  change b ≤ Real.exp (-theta * x + theta ^ 2 / 2) ↔
    (Real.log b - theta ^ 2 / 2) / |theta| ≤ reflectedSign theta * x
  rw [← Real.log_le_iff_le_exp hb, div_le_iff₀ hs, reflectedSign_mul_abs htheta x]
  constructor <;> intro h <;> linarith

theorem normalLaw_map_reflectedSign {theta : ℝ} (htheta : theta ≠ 0) (eta : ℝ) :
    (normalLaw eta).map (fun x ↦ reflectedSign theta * x) =
      normalLaw (reflectedSign theta * eta) := by
  simpa only [normalLaw, reflectedSign_sq htheta, mul_one, NNReal.mk_one] using
    (gaussianReal_map_const_mul (μ := eta) (v := 1) (reflectedSign theta))

theorem normalLaw_apply_Ici (eta z : ℝ) :
    normalLaw eta (Ici z) = ENNReal.ofReal (upperTail (z - eta)) := by
  have hshift : (normalLaw 0).map (fun x : ℝ ↦ x + eta) = normalLaw eta := by
    simpa only [normalLaw, zero_add] using
      (gaussianReal_map_add_const (μ := 0) (v := 1) eta)
  calc
    normalLaw eta (Ici z) = (normalLaw 0).map (fun x : ℝ ↦ x + eta) (Ici z) := by
      rw [hshift]
    _ = normalLaw 0 ((fun x : ℝ ↦ x + eta) ⁻¹' Ici z) :=
      Measure.map_apply (by fun_prop) measurableSet_Ici
    _ = normalLaw 0 (Ici (z - eta)) := by
      congr 1
      ext x
      simp only [mem_preimage, mem_Ici]
      constructor <;> intro h <;> linarith
    _ = _ := (ofReal_upperTail_eq_measure_closed (z - eta)).symm

/-- A single sign-reflection argument handles both signs of theta exactly. -/
theorem normalLaw_ratio_event_measure {theta b : ℝ} (htheta : theta ≠ 0)
    (hb : 0 < b) (eta : ℝ) :
    normalLaw eta {x | b ≤ ratio theta x} =
      ENNReal.ofReal (upperTail (ratioCutoff theta b - reflectedSign theta * eta)) := by
  have hset : (fun x ↦ reflectedSign theta * x) ⁻¹' Ici (ratioCutoff theta b) =
      {x | b ≤ ratio theta x} := by
    ext x
    exact (ratio_ge_iff_reflectedSign htheta hb x).symm
  calc
    normalLaw eta {x | b ≤ ratio theta x} =
        normalLaw eta ((fun x ↦ reflectedSign theta * x) ⁻¹' Ici (ratioCutoff theta b)) := by
      rw [hset]
    _ = (normalLaw eta).map (fun x ↦ reflectedSign theta * x) (Ici (ratioCutoff theta b)) :=
      (Measure.map_apply (by fun_prop) measurableSet_Ici).symm
    _ = normalLaw (reflectedSign theta * eta) (Ici (ratioCutoff theta b)) := by
      rw [normalLaw_map_reflectedSign htheta eta]
    _ = _ := normalLaw_apply_Ici _ _

theorem closedTailEvent_normalLaw_measure {theta b : ℝ} (htheta : theta ≠ 0) (hb : 0 < b) :
    normalLaw 0 (closedTailEvent (normalLaw 0) (normalLaw theta) b) =
      ENNReal.ofReal (upperTail (ratioCutoff theta b)) := by
  rw [measure_congr (closedTailEvent_normalLaw_ae theta hb)]
  simpa only [mul_zero, sub_zero] using normalLaw_ratio_event_measure htheta hb 0

theorem closedTailMoment_normalLaw_formula {theta b : ℝ} (htheta : theta ≠ 0) (hb : 0 < b) :
    closedTailMoment (normalLaw 0) (normalLaw theta) b =
      ENNReal.ofReal (Real.exp (theta ^ 2) * upperTail (ratioCutoff theta b - |theta|)) := by
  rw [closedTailMoment_normalLaw_eq_setLIntegral_ratio theta hb,
    setLIntegral_ratio theta (measurableSet_le measurable_const (continuous_ratio theta).measurable),
    normalLaw_ratio_event_measure htheta hb (-theta), reflectedSign_mul_neg_theta htheta,
    ← ENNReal.ofReal_mul (Real.exp_pos (theta ^ 2)).le]

/-- The actual conditional numerator/denominator identity; theta zero is handled
by its separate null-event theorem in Normal. -/
theorem conditionalRatioMean_normalLaw_formula {theta b : ℝ} (htheta : theta ≠ 0)
    (hb : 0 < b) :
    conditionalRatioMean (normalLaw 0) (normalLaw theta) b =
      ENNReal.ofReal (Real.exp (theta ^ 2) * upperTail (ratioCutoff theta b - |theta|) /
        upperTail (ratioCutoff theta b)) := by
  have hnonzero : normalLaw 0 (closedTailEvent (normalLaw 0) (normalLaw theta) b) ≠ 0 := by
    rw [closedTailEvent_normalLaw_measure htheta hb]
    exact (ENNReal.ofReal_pos.mpr (upperTail_pos _)).ne'
  rw [conditionalRatioMean_of_nonnull (normalLaw_absolutelyContinuous 0 theta) hnonzero,
    closedTailMoment_normalLaw_formula htheta hb, closedTailEvent_normalLaw_measure htheta hb,
    ← ENNReal.ofReal_div_of_pos (upperTail_pos _)]

theorem conditionalRatioMean_normalLaw_cdf {theta b : ℝ} (htheta : theta ≠ 0)
    (hb : 0 < b) :
    conditionalRatioMean (normalLaw 0) (normalLaw theta) b =
      ENNReal.ofReal (Real.exp (theta ^ 2) *
        cdf (normalLaw 0) (3 * |theta| / 2 - Real.log b / |theta|) /
        cdf (normalLaw 0) (|theta| / 2 - Real.log b / |theta|)) := by
  rw [conditionalRatioMean_normalLaw_formula htheta hb]
  simp only [upperTail_eq_cdf_neg, ratioCutoff_eq htheta]
  rw [show -(Real.log b / |theta| - |theta| / 2 - |theta|) =
      3 * |theta| / 2 - Real.log b / |theta| by ring,
    show -(Real.log b / |theta| - |theta| / 2) =
      |theta| / 2 - Real.log b / |theta| by ring]

/-- The literal printed CDF quotient, on its actual nonzero-parameter domain. -/
theorem conditionalRatioMean_normalLaw_exp_one {theta : ℝ} (htheta : theta ≠ 0) :
    conditionalRatioMean (normalLaw 0) (normalLaw theta) (Real.exp 1) =
      ENNReal.ofReal (Real.exp (theta ^ 2) *
        cdf (normalLaw 0) (|theta| / 2 - 1 / |theta| + |theta|) /
        cdf (normalLaw 0) (|theta| / 2 - 1 / |theta|)) := by
  have hh := conditionalRatioMean_normalLaw_cdf htheta (Real.exp_pos 1)
  have harg : 3 * |theta| / 2 - 1 / |theta| =
      |theta| / 2 - 1 / |theta| + |theta| := by ring
  simpa only [Real.log_exp, harg] using hh

end Hellinger.Comparison.Examples.Normal
