/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.Comparison.Examples.Power
public import Hellinger.Comparison.ConditionalMoment
public import Hellinger.HellingerBridge

/-! The literal three-piece real-line family separating uniform NC from uniform CM.
The third source height is simplified for positive parameters; the zero parameter
has only its middle cell of positive base mass. -/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open Hellinger.Comparison.Examples.Power

namespace Hellinger.Comparison.Examples.CMSeparation

noncomputable def height (θ x : ℝ) : ℝ :=
  if x < θ ^ 2 then θ else if x < 1 - θ then 1 - θ else 2 * (1 - θ ^ 2)

noncomputable def density (θ x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (height θ x)

noncomputable def law (θ : ℝ) : Measure ℝ := uniformLaw.withDensity (density θ)

theorem height_third_eq_source {θ : ℝ} (hθ : θ ≠ 0) :
    2 * (1 - θ ^ 2) = (1 - θ ^ 3 - (1 - θ) * (1 - θ - θ ^ 2)) / θ := by
  field_simp [hθ]
  ring

theorem measurable_height (θ : ℝ) : Measurable (height θ) :=
  measurable_const.piecewise measurableSet_Iio
    (measurable_const.piecewise measurableSet_Iio measurable_const)

theorem measurable_density (θ : ℝ) : Measurable (density θ) :=
  (measurable_height θ).ennreal_ofReal

theorem law_eq_volume_withDensity (θ : ℝ) :
    law θ = volume.withDensity ((Ioo (0 : ℝ) 1).indicator (density θ)) :=
  (withDensity_indicator measurableSet_Ioo (density θ)).symm

theorem parameter_geometry {θ : ℝ} (h0 : 0 ≤ θ) (h4 : θ < 1 / 4) :
    0 ≤ θ ^ 2 ∧ θ ^ 2 ≤ 1 - θ ∧ 1 - θ ≤ 1 ∧
      0 < 1 - θ - θ ^ 2 ∧ 1 < 2 * (1 - θ ^ 2) := by
  have hp : 0 ≤ θ * (1 / 4 - θ) := mul_nonneg h0 (sub_nonneg.mpr h4.le)
  constructor
  · exact sq_nonneg _
  constructor
  · nlinarith
  constructor
  · linarith
  constructor <;> nlinarith

theorem height_nonneg {θ : ℝ} (h0 : 0 ≤ θ) (h4 : θ < 1 / 4) (x : ℝ) :
    0 ≤ height θ x := by
  have hg := parameter_geometry h0 h4
  unfold height
  split_ifs <;> linarith [hg.2.2.2.2]

theorem uniformLaw_Ioo_subinterval {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    uniformLaw (Ioo a b) = ENNReal.ofReal (b - a) := by
  have hsub : Ioo a b ⊆ Ioo (0 : ℝ) 1 := fun x hx ↦
    ⟨ha.trans_lt hx.1, hx.2.trans_le hb⟩
  rw [uniformLaw, Measure.restrict_apply measurableSet_Ioo,
    Set.inter_eq_left.mpr hsub, Real.volume_Ioo]

theorem uniformLaw_Iio {s : ℝ} (_h0 : 0 ≤ s) (h1 : s ≤ 1) :
    uniformLaw (Iio s) = ENNReal.ofReal s := by
  have heq : Iio s ∩ Ioo (0 : ℝ) 1 = Ioo 0 s := by
    ext x
    simp only [mem_inter_iff, mem_Iio, mem_Ioo]
    constructor
    · rintro ⟨hx, hx0, _⟩
      exact ⟨hx0, hx⟩
    · rintro ⟨hx0, hx⟩
      exact ⟨hx, hx0, hx.trans_le h1⟩
  rw [uniformLaw, Measure.restrict_apply measurableSet_Iio, heq, Real.volume_Ioo]
  simp

theorem uniformLaw_Ici {s : ℝ} (h0 : 0 ≤ s) (_h1 : s ≤ 1) :
    uniformLaw (Ici s) = ENNReal.ofReal (1 - s) := by
  letI : NullSingletonClass uniformLaw := by unfold uniformLaw; infer_instance
  have heq : Ioi s ∩ Ioo (0 : ℝ) 1 = Ioo s 1 := by
    ext x
    simp only [mem_inter_iff, mem_Ioi, mem_Ioo]
    constructor
    · rintro ⟨hx, _, hx1⟩
      exact ⟨hx, hx1⟩
    · rintro ⟨hx, hx1⟩
      exact ⟨hx, h0.trans_lt hx, hx1⟩
  calc
    uniformLaw (Ici s) = uniformLaw (Ioi s) := measure_congr Ioi_ae_eq_Ici.symm
    _ = _ := by
      rw [uniformLaw, Measure.restrict_apply measurableSet_Ioi, heq, Real.volume_Ioo]

/-- Exact integration on the three actual real intervals, including endpoint null sets. -/
theorem lintegral_step {θ : ℝ} (h0 : 0 ≤ θ) (h4 : θ < 1 / 4) (a b c : ℝ≥0∞) :
    (∫⁻ x, (if x < θ ^ 2 then a else if x < 1 - θ then b else c) ∂uniformLaw) =
      a * ENNReal.ofReal (θ ^ 2) + b * ENNReal.ofReal (1 - θ - θ ^ 2) +
        c * ENNReal.ofReal θ := by
  classical
  letI : NullSingletonClass uniformLaw := by unfold uniformLaw; infer_instance
  have hg := parameter_geometry h0 h4
  have hfun : (fun x : ℝ ↦ if x < θ ^ 2 then a else if x < 1 - θ then b else c) =
      (fun x ↦ (Iio (θ ^ 2)).indicator (fun _ ↦ a) x +
        (Ico (θ ^ 2) (1 - θ)).indicator (fun _ ↦ b) x +
        (Ici (1 - θ)).indicator (fun _ ↦ c) x) := by
    funext x
    rcases lt_or_ge x (θ ^ 2) with hx | hx
    · have hx1 : x < 1 - θ := hx.trans_le hg.2.1
      simp [hx, hx1, Set.indicator, not_le.mpr hx, not_le.mpr hx1]
    · rcases lt_or_ge x (1 - θ) with hx1 | hx1
      · simp [hx, hx1, Set.indicator, not_lt.mpr hx, not_le.mpr hx1]
      · simp [hx, hx1, Set.indicator, not_lt.mpr hx, not_lt.mpr hx1]
  have hma : Measurable ((Iio (θ ^ 2)).indicator (fun _ : ℝ ↦ a)) :=
    measurable_const.indicator measurableSet_Iio
  have hmb : Measurable ((Ico (θ ^ 2) (1 - θ)).indicator (fun _ : ℝ ↦ b)) :=
    measurable_const.indicator measurableSet_Ico
  have hmab : Measurable (fun x ↦ (Iio (θ ^ 2)).indicator (fun _ : ℝ ↦ a) x +
      (Ico (θ ^ 2) (1 - θ)).indicator (fun _ : ℝ ↦ b) x) := hma.add hmb
  rw [hfun, lintegral_add_left hmab _, lintegral_add_left hma _,
    lintegral_indicator_const measurableSet_Iio,
    lintegral_indicator_const measurableSet_Ico,
    lintegral_indicator_const measurableSet_Ici]
  rw [uniformLaw_Iio hg.1 (hg.2.1.trans hg.2.2.1),
    measure_congr (Ioo_ae_eq_Ico (μ := uniformLaw) (a := θ ^ 2) (b := 1 - θ)).symm,
    uniformLaw_Ioo_subinterval hg.1 hg.2.2.1,
    uniformLaw_Ici (by linarith : 0 ≤ 1 - θ) hg.2.2.1]
  congr 3
  ring

theorem lintegral_height_apply {θ : ℝ} (h0 : 0 ≤ θ) (h4 : θ < 1 / 4)
    (f : ℝ → ℝ≥0∞) :
    (∫⁻ x, f (height θ x) ∂uniformLaw) =
      f θ * ENNReal.ofReal (θ ^ 2) + f (1 - θ) * ENNReal.ofReal (1 - θ - θ ^ 2) +
        f (2 * (1 - θ ^ 2)) * ENNReal.ofReal θ := by
  have hfun : (fun x ↦ f (height θ x)) =
      (fun x ↦ if x < θ ^ 2 then f θ else if x < 1 - θ then f (1 - θ) else
        f (2 * (1 - θ ^ 2))) := by
    funext x
    unfold height
    split_ifs <;> rfl
  rw [hfun]
  exact lintegral_step h0 h4 _ _ _

theorem law_mass_univ {θ : ℝ} (h0 : 0 ≤ θ) (h4 : θ < 1 / 4) : law θ univ = 1 := by
  have hg := parameter_geometry h0 h4
  have h1 : 0 ≤ 1 - θ := by linarith
  have hthird : 0 ≤ 2 * (1 - θ ^ 2) := by linarith [hg.2.2.2.2]
  change uniformLaw.withDensity (density θ) univ = 1
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  change (∫⁻ x, ENNReal.ofReal (height θ x) ∂uniformLaw) = 1
  rw [lintegral_height_apply h0 h4]
  rw [← ENNReal.ofReal_mul h0, ← ENNReal.ofReal_mul h1,
    ← ENNReal.ofReal_mul hthird,
    ← ENNReal.ofReal_add (mul_nonneg h0 hg.1) (mul_nonneg h1 hg.2.2.2.1.le),
    ← ENNReal.ofReal_add
      (add_nonneg (mul_nonneg h0 hg.1) (mul_nonneg h1 hg.2.2.2.1.le))
      (mul_nonneg hthird h0)]
  have hid : θ * θ ^ 2 + (1 - θ) * (1 - θ - θ ^ 2) +
      2 * (1 - θ ^ 2) * θ = 1 := by ring
  rw [hid, ENNReal.ofReal_one]

theorem law_isProbabilityMeasure {θ : ℝ} (h0 : 0 ≤ θ) (h4 : θ < 1 / 4) :
    IsProbabilityMeasure (law θ) := ⟨law_mass_univ h0 h4⟩

theorem law_absolutelyContinuous_uniformLaw (θ : ℝ) : law θ ≪ uniformLaw :=
  withDensity_absolutelyContinuous _ _

theorem rnDeriv_law_ae (θ : ℝ) : (law θ).rnDeriv uniformLaw =ᵐ[uniformLaw] density θ :=
  Measure.rnDeriv_withDensity uniformLaw (measurable_density θ)

noncomputable def sourceSlope : ℝ := 3 - 2 * Real.sqrt 2

noncomputable def hellingerExpr (θ : ℝ) : ℝ :=
  θ ^ 2 * (Real.sqrt θ - 1) ^ 2 +
    (1 - θ - θ ^ 2) * (Real.sqrt (1 - θ) - 1) ^ 2 +
    θ * (Real.sqrt (2 * (1 - θ ^ 2)) - 1) ^ 2

theorem sourceSlope_pos : 0 < sourceSlope := by
  have hs : Real.sqrt 2 < (3 / 2 : ℝ) :=
    (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)
  unfold sourceSlope
  linarith

/-- A global inequality, rather than an inference from the asymptotic slope. -/
theorem hellingerExpr_lower {θ : ℝ} (h0 : 0 ≤ θ) (h4 : θ < 1 / 4) :
    sourceSlope * θ ≤ hellingerExpr θ := by
  have hg := parameter_geometry h0 h4
  let u := Real.sqrt 2
  let v := Real.sqrt (2 * (1 - θ ^ 2))
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hv2 : v ^ 2 = 2 * (1 - θ ^ 2) := Real.sq_sqrt (by linarith [hg.2.2.2.2])
  have hvu : v ≤ u := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg θ])
  have hu4 : u ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hp : 0 ≤ (u - v) * (4 - u - v) :=
    mul_nonneg (sub_nonneg.mpr hvu) (by linarith)
  have hgap : θ ^ 2 ≤ 2 * (u - v) := by nlinarith
  have hthird : sourceSlope - θ ^ 2 ≤ (v - 1) ^ 2 := by
    change 3 - 2 * u - θ ^ 2 ≤ (v - 1) ^ 2
    nlinarith
  have hsθ : Real.sqrt θ ≤ (1 / 2 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hs0 : 0 ≤ Real.sqrt θ := Real.sqrt_nonneg _
  have hrootprod : 0 ≤ (1 / 2 - Real.sqrt θ) * (3 / 2 - Real.sqrt θ) :=
    mul_nonneg (by linarith) (by linarith)
  have hfirst : (1 / 4 : ℝ) ≤ (Real.sqrt θ - 1) ^ 2 := by nlinarith
  have hf := mul_le_mul_of_nonneg_left hfirst (sq_nonneg θ)
  have ht := mul_le_mul_of_nonneg_left hthird h0
  have hm : 0 ≤ (1 - θ - θ ^ 2) * (Real.sqrt (1 - θ) - 1) ^ 2 :=
    mul_nonneg hg.2.2.2.1.le (sq_nonneg _)
  have hc : 0 ≤ θ ^ 2 * (1 / 4 - θ) :=
    mul_nonneg (sq_nonneg _) (sub_nonneg.mpr h4.le)
  change sourceSlope * θ ≤ θ ^ 2 * (Real.sqrt θ - 1) ^ 2 +
    (1 - θ - θ ^ 2) * (Real.sqrt (1 - θ) - 1) ^ 2 + θ * (v - 1) ^ 2
  nlinarith

theorem height_pos {θ : ℝ} (h0 : 0 < θ) (h4 : θ < 1 / 4) (x : ℝ) :
    0 < height θ x := by
  have hg := parameter_geometry h0.le h4
  unfold height
  split_ifs <;> linarith [hg.2.2.2.2]

theorem law_zero : law 0 = uniformLaw := by
  have hden : density 0 =ᵐ[uniformLaw] fun _ ↦ (1 : ℝ≥0∞) := by
    filter_upwards [uniformLaw_ae_mem] with x hx
    simp [density, height, not_lt.mpr hx.1.le, hx.2]
  calc
    law 0 = uniformLaw.withDensity (fun _ ↦ 1) := withDensity_congr_ae hden
    _ = uniformLaw := withDensity_one

theorem uniformLaw_absolutelyContinuous_law {θ : ℝ} (h0 : 0 < θ) (h4 : θ < 1 / 4) :
    uniformLaw ≪ law θ := by
  apply withDensity_absolutelyContinuous' (measurable_density θ).aemeasurable
  exact ae_of_all _ fun x ↦ (ENNReal.ofReal_pos.mpr (height_pos h0 h4 x)).ne'

theorem dominatedRatio_ae_eq_inverse_height {θ : ℝ} (h0 : 0 < θ) (h4 : θ < 1 / 4) :
    dominatedRatio uniformLaw (law θ) uniformLaw =ᵐ[uniformLaw]
      fun x ↦ ENNReal.ofReal ((height θ x)⁻¹) := by
  letI := law_isProbabilityMeasure h0.le h4
  filter_upwards [dominatedRatio_ae_eq_inv_rnDeriv
      (μ := uniformLaw) (ν := law θ) (κ := uniformLaw) Measure.AbsolutelyContinuous.rfl,
    rnDeriv_law_ae θ] with x hr hden
  rw [hr, hden, density, ← ENNReal.ofReal_inv_of_pos (height_pos h0 h4 x)]

/-- Exact genuine Hellinger distance of the real-line density family. -/
theorem hellingerSq_eq_expr {θ : ℝ} (h0 : 0 ≤ θ) (h4 : θ < 1 / 4) :
    hellingerSq uniformLaw (law θ) = ENNReal.ofReal (hellingerExpr θ) := by
  letI := law_isProbabilityMeasure h0 h4
  have hg := parameter_geometry h0 h4
  rw [hellingerSq_symm uniformLaw (law θ),
    hellingerSq_eq_lintegral_of_ac (law_absolutelyContinuous_uniformLaw θ)]
  calc
    _ = ∫⁻ x, ENNReal.ofReal ((Real.sqrt (height θ x) - 1) ^ 2) ∂uniformLaw := by
      apply lintegral_congr_ae
      filter_upwards [rnDeriv_law_ae θ] with x hx
      rw [hx, density, ENNReal.toReal_ofReal (height_nonneg h0 h4 x)]
    _ = ENNReal.ofReal ((Real.sqrt θ - 1) ^ 2) * ENNReal.ofReal (θ ^ 2) +
        ENNReal.ofReal ((Real.sqrt (1 - θ) - 1) ^ 2) * ENNReal.ofReal (1 - θ - θ ^ 2) +
        ENNReal.ofReal ((Real.sqrt (2 * (1 - θ ^ 2)) - 1) ^ 2) * ENNReal.ofReal θ :=
      lintegral_height_apply h0 h4 (fun z ↦ ENNReal.ofReal ((Real.sqrt z - 1) ^ 2))
    _ = _ := by
      rw [← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (sq_nonneg _),
        ← ENNReal.ofReal_mul (sq_nonneg _),
        ← ENNReal.ofReal_add (mul_nonneg (sq_nonneg _) hg.1)
          (mul_nonneg (sq_nonneg _) hg.2.2.2.1.le),
        ← ENNReal.ofReal_add
          (add_nonneg (mul_nonneg (sq_nonneg _) hg.1)
            (mul_nonneg (sq_nonneg _) hg.2.2.2.1.le)) (mul_nonneg (sq_nonneg _) h0)]
      congr 1
      unfold hellingerExpr
      ring

theorem ratio_height_order {θ : ℝ} (h0 : 0 < θ) (h4 : θ < 1 / 4) :
    4 < θ⁻¹ ∧ (1 - θ)⁻¹ < 4 / 3 ∧ (2 * (1 - θ ^ 2))⁻¹ < 1 := by
  have hg := parameter_geometry h0.le h4
  have hm : 0 < 1 - θ := by linarith
  have hc : 0 < 2 * (1 - θ ^ 2) := by linarith [hg.2.2.2.2]
  constructor
  · simpa only [one_div] using
      ((lt_div_iff₀ h0).mpr (by nlinarith) : (4 : ℝ) < 1 / θ)
  constructor
  · simpa only [one_div] using
      ((div_lt_iff₀ hm).mpr (by linarith) : 1 / (1 - θ) < (4 / 3 : ℝ))
  · simpa only [one_div] using
      ((div_lt_iff₀ hc).mpr (by linarith [hg.2.2.2.2]) : 1 / (2 * (1 - θ ^ 2)) < (1 : ℝ))

theorem tailPower_four_eq_of_pos {θ : ℝ} (h0 : 0 < θ) (h4 : θ < 1 / 4) :
    tailPower uniformLaw (law θ) 4 1 = ENNReal.ofReal θ := by
  classical
  letI := law_isProbabilityMeasure h0.le h4
  have hr := ratio_height_order h0 h4
  have hm : 0 < 1 - θ := by linarith
  have hg := parameter_geometry h0.le h4
  have hc : 0 < 2 * (1 - θ ^ 2) := by linarith [hg.2.2.2.2]
  rw [tailPower_eq_setLIntegral_dominatedRatio_rpow (κ := uniformLaw)
    Measure.AbsolutelyContinuous.rfl (by norm_num : (1 : ℝ) < 4) zero_lt_one]
  simp only [ENNReal.rpow_one]
  rw [← lintegral_indicator (measurableSet_dominatedStrictTailEvent uniformLaw (law θ) uniformLaw 4)]
  have hkernel : (fun x ↦ (dominatedStrictTailEvent uniformLaw (law θ) uniformLaw 4).indicator
      (dominatedRatio uniformLaw (law θ) uniformLaw) x) =ᵐ[uniformLaw]
      (fun x ↦ if x < θ ^ 2 then ENNReal.ofReal θ⁻¹ else 0) := by
    filter_upwards [dominatedRatio_ae_eq_inverse_height h0 h4] with x hx
    simp only [Set.indicator_apply, dominatedStrictTailEvent, Set.mem_ofPred_eq, hx]
    have hhigh : ENNReal.ofReal 4 < ENNReal.ofReal θ⁻¹ :=
      (ENNReal.ofReal_lt_ofReal_iff (inv_pos.mpr h0)).mpr hr.1
    have hmid : ¬ ENNReal.ofReal 4 < ENNReal.ofReal (1 - θ)⁻¹ := by
      rw [ENNReal.ofReal_lt_ofReal_iff (inv_pos.mpr hm)]
      linarith [hr.2.1]
    have hlow : ¬ ENNReal.ofReal 4 < ENNReal.ofReal (2 * (1 - θ ^ 2))⁻¹ := by
      rw [ENNReal.ofReal_lt_ofReal_iff (inv_pos.mpr hc)]
      linarith [hr.2.2]
    by_cases hxA : x < θ ^ 2
    · simp only [height, hxA, ite_true, hhigh]
    · by_cases hxB : x < 1 - θ
      · simp only [height, hxA, hxB, ite_false, ite_true, hmid]
      · simp only [height, hxA, hxB, ite_false, hlow]
  rw [lintegral_congr_ae hkernel]
  have hs := lintegral_step h0.le h4 (ENNReal.ofReal θ⁻¹) 0 0
  simp only [ite_self, zero_mul, add_zero] at hs
  rw [hs, ← ENNReal.ofReal_mul (inv_nonneg.mpr h0.le)]
  congr 1
  field_simp [h0.ne']

/-- Zero parameter is the identical-measure endpoint, rather than a reciprocal formula. -/
theorem tailPower_four_zero : tailPower uniformLaw (law 0) 4 1 = 0 := by
  rw [law_zero, tailPower_of_ac Measure.AbsolutelyContinuous.rfl]
  have hnull : uniformLaw (tailEvent uniformLaw uniformLaw 4) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [MeasureTheory.llr_self uniformLaw] with x hx
    change ¬ Real.log 4 < llr uniformLaw uniformLaw x
    rw [hx]
    exact not_lt.mpr (Real.log_pos (by norm_num : (1 : ℝ) < 4)).le
  rw [Measure.restrict_eq_zero.mpr hnull, lintegral_zero_measure]

theorem tailPower_four_eq {θ : ℝ} (h0 : 0 ≤ θ) (h4 : θ < 1 / 4) :
    tailPower uniformLaw (law θ) 4 1 = ENNReal.ofReal θ := by
  rcases eq_or_lt_of_le h0 with heq | hpos
  · subst θ
    simpa using tailPower_four_zero
  · exact tailPower_four_eq_of_pos hpos h4

/-- The printed constant works throughout the whole source parameter interval. -/
theorem tailPower_four_le_sourceCoeff {θ : ℝ} (h0 : 0 ≤ θ) (h4 : θ < 1 / 4) :
    tailPower uniformLaw (law θ) 4 1 ≤
      ENNReal.ofReal sourceSlope⁻¹ * hellingerSq uniformLaw (law θ) := by
  rw [tailPower_four_eq h0 h4, hellingerSq_eq_expr h0 h4,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr sourceSlope_pos.le)]
  apply ENNReal.ofReal_le_ofReal
  have h : θ ≤ hellingerExpr θ / sourceSlope := (le_div_iff₀ sourceSlope_pos).mpr
    (by simpa only [mul_comm] using hellingerExpr_lower h0 h4)
  simpa only [div_eq_mul_inv, mul_comm] using h

/-- Exact integration on a closed native-range ratio event; equality includes the middle cell. -/
theorem lintegral_closed_ratio_kernel {θ t : ℝ} (h0 : 0 < θ) (h4 : θ < 1 / 4)
    (ht : 1 < t) (htop : t ≤ 9 / 4) (f : ℝ≥0∞ → ℝ≥0∞) :
    (∫⁻ x, (if ENNReal.ofReal t ≤ dominatedRatio uniformLaw (law θ) uniformLaw x then
        f (dominatedRatio uniformLaw (law θ) uniformLaw x) else 0) ∂uniformLaw) =
      f (ENNReal.ofReal θ⁻¹) * ENNReal.ofReal (θ ^ 2) +
        (if t ≤ (1 - θ)⁻¹ then f (ENNReal.ofReal (1 - θ)⁻¹) else 0) *
          ENNReal.ofReal (1 - θ - θ ^ 2) := by
  classical
  letI := law_isProbabilityMeasure h0.le h4
  have hr := ratio_height_order h0 h4
  have hm : 0 < 1 - θ := by linarith
  have hg := parameter_geometry h0.le h4
  have hc : 0 < 2 * (1 - θ ^ 2) := by linarith [hg.2.2.2.2]
  have hhigh : ENNReal.ofReal t ≤ ENNReal.ofReal θ⁻¹ :=
    ENNReal.ofReal_le_ofReal (by linarith [hr.1])
  have hmid : ENNReal.ofReal t ≤ ENNReal.ofReal (1 - θ)⁻¹ ↔ t ≤ (1 - θ)⁻¹ :=
    ENNReal.ofReal_le_ofReal_iff (inv_nonneg.mpr hm.le)
  have hlow : ¬ ENNReal.ofReal t ≤ ENNReal.ofReal (2 * (1 - θ ^ 2))⁻¹ := by
    rw [ENNReal.ofReal_le_ofReal_iff (inv_nonneg.mpr hc.le)]
    linarith [hr.2.2]
  have hkernel : (fun x ↦ if ENNReal.ofReal t ≤ dominatedRatio uniformLaw (law θ) uniformLaw x
      then f (dominatedRatio uniformLaw (law θ) uniformLaw x) else 0) =ᵐ[uniformLaw]
      (fun x ↦ if x < θ ^ 2 then f (ENNReal.ofReal θ⁻¹) else if x < 1 - θ then
        (if t ≤ (1 - θ)⁻¹ then f (ENNReal.ofReal (1 - θ)⁻¹) else 0) else 0) := by
    filter_upwards [dominatedRatio_ae_eq_inverse_height h0 h4] with x hx
    rw [hx]
    by_cases hxA : x < θ ^ 2
    · simp only [height, hxA, ite_true, hhigh]
    · by_cases hxB : x < 1 - θ
      · simp only [height, hxA, hxB, ite_false, ite_true, hmid]
      · simp only [height, hxA, hxB, ite_false, hlow]
  rw [lintegral_congr_ae hkernel, lintegral_step h0.le h4]
  simp only [zero_mul, add_zero]

theorem closed_ratio_event_mass {θ t : ℝ} (h0 : 0 < θ) (h4 : θ < 1 / 4)
    (ht : 1 < t) (htop : t ≤ 9 / 4) :
    uniformLaw (dominatedClosedTailEvent uniformLaw (law θ) uniformLaw t) =
      if t ≤ (1 - θ)⁻¹ then ENNReal.ofReal (1 - θ) else ENNReal.ofReal (θ ^ 2) := by
  classical
  have hg := parameter_geometry h0.le h4
  calc
    _ = ∫⁻ x, (if ENNReal.ofReal t ≤ dominatedRatio uniformLaw (law θ) uniformLaw x
          then (1 : ℝ≥0∞) else 0) ∂uniformLaw :=
      by simpa only [Set.indicator_apply, dominatedClosedTailEvent, Set.mem_ofPred_eq,
          Pi.one_apply] using (lintegral_indicator_one (μ := uniformLaw)
          (measurableSet_dominatedClosedTailEvent uniformLaw (law θ) uniformLaw t)).symm
    _ = (1 : ℝ≥0∞) * ENNReal.ofReal (θ ^ 2) +
        (if t ≤ (1 - θ)⁻¹ then 1 else 0) * ENNReal.ofReal (1 - θ - θ ^ 2) :=
      lintegral_closed_ratio_kernel h0 h4 ht htop (fun _ ↦ 1)
    _ = _ := by
      by_cases h : t ≤ (1 - θ)⁻¹
      · simp only [h, ite_true, one_mul]
        rw [← ENNReal.ofReal_add (sq_nonneg θ) hg.2.2.2.1.le]
        congr 1
        ring
      · simp only [h, ite_false, one_mul, zero_mul, add_zero]

theorem closed_ratio_moment {θ t : ℝ} (h0 : 0 < θ) (h4 : θ < 1 / 4)
    (ht : 1 < t) (htop : t ≤ 9 / 4) :
    (∫⁻ x in dominatedClosedTailEvent uniformLaw (law θ) uniformLaw t,
      dominatedRatio uniformLaw (law θ) uniformLaw x ∂uniformLaw) =
      if t ≤ (1 - θ)⁻¹ then
        ENNReal.ofReal (θ + (1 - θ - θ ^ 2) / (1 - θ)) else ENNReal.ofReal θ := by
  classical
  have hg := parameter_geometry h0.le h4
  have hm : 0 < 1 - θ := by linarith
  rw [← lintegral_indicator
    (measurableSet_dominatedClosedTailEvent uniformLaw (law θ) uniformLaw t)]
  simp only [Set.indicator_apply, dominatedClosedTailEvent, Set.mem_ofPred_eq]
  rw [lintegral_closed_ratio_kernel h0 h4 ht htop (fun z ↦ z)]
  by_cases h : t ≤ (1 - θ)⁻¹
  · simp only [h, ite_true]
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr h0.le),
      ← ENNReal.ofReal_mul (inv_nonneg.mpr hm.le),
      ← ENNReal.ofReal_add (mul_nonneg (inv_nonneg.mpr h0.le) hg.1)
        (mul_nonneg (inv_nonneg.mpr hm.le) hg.2.2.2.1.le)]
    congr 1
    field_simp [h0.ne', hm.ne']
  · simp only [h, ite_false, zero_mul, add_zero]
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr h0.le)]
    congr 1
    field_simp [h0.ne']

noncomputable def combinedMean (θ : ℝ) : ℝ :=
  (θ + (1 - θ - θ ^ 2) / (1 - θ)) / (1 - θ)

/-- The closed-event formula includes the threshold equality in the two-cell branch. -/
theorem conditionalRatioMean_formula {θ t : ℝ} (h0 : 0 < θ) (h4 : θ < 1 / 4)
    (ht : 1 < t) (htop : t ≤ 9 / 4) :
    conditionalRatioMean uniformLaw (law θ) t =
      if t ≤ (1 - θ)⁻¹ then ENNReal.ofReal (combinedMean θ) else ENNReal.ofReal θ⁻¹ := by
  classical
  letI := law_isProbabilityMeasure h0.le h4
  have hm : 0 < 1 - θ := by linarith
  rw [conditionalRatioMean_eq_dominatedConditionalRatioMean (κ := uniformLaw)
    Measure.AbsolutelyContinuous.rfl (zero_lt_one.trans ht)]
  unfold dominatedConditionalRatioMean
  rw [closed_ratio_event_mass h0 h4 ht htop, closed_ratio_moment h0 h4 ht htop]
  by_cases h : t ≤ (1 - θ)⁻¹
  · simp only [h, ite_true]
    rw [ite_eq_right (ENNReal.ofReal_pos.mpr hm).ne', ← ENNReal.ofReal_div_of_pos hm]
    rfl
  · simp only [h, ite_false]
    rw [ite_eq_right (ENNReal.ofReal_pos.mpr (sq_pos_of_pos h0)).ne',
      ← ENNReal.ofReal_div_of_pos (sq_pos_of_pos h0)]
    congr 1
    field_simp [h0.ne']

theorem cmCutoff_ge_one_add_div {a : ℝ} (ha : 1 ≤ a) :
    1 + 1 / a ≤ cmCutoff a := by
  have ha0 : 0 < a := by linarith
  have hid : 2 * (1 / (2 * a)) = 1 / a := by field_simp [ha0.ne']
  unfold cmCutoff
  nlinarith [sq_nonneg (1 / (2 * a))]

theorem optimizer_parameter_lower {θ a : ℝ} (h0 : 0 < θ) (h4 : θ < 1 / 4)
    (ha : 1 ≤ a) (hinclude : cmCutoff a ≤ (1 - θ)⁻¹) :
    (1 - θ) / θ ≤ a := by
  have hm : 0 < 1 - θ := by linarith
  have ha0 : 0 < a := by linarith
  have hbound := (cmCutoff_ge_one_add_div ha).trans hinclude
  have hfrac : 1 / a ≤ θ / (1 - θ) := by
    have hid : (1 - θ)⁻¹ - 1 = θ / (1 - θ) := by field_simp [hm.ne']; ring
    rw [← hid]
    linarith
  have hmul := (div_le_div_iff₀ ha0 hm).mp hfrac
  apply (div_le_iff₀ h0).mpr
  nlinarith

theorem combinedMean_ge_inverse {θ : ℝ} (h0 : 0 < θ) (h4 : θ < 1 / 4) :
    (1 - θ)⁻¹ ≤ combinedMean θ := by
  have hm : 0 < 1 - θ := by linarith
  have hid : θ + (1 - θ - θ ^ 2) / (1 - θ) = (1 - 2 * θ ^ 2) / (1 - θ) := by
    field_simp [hm.ne']
    ring
  have hnum : 1 ≤ θ + (1 - θ - θ ^ 2) / (1 - θ) := by
    rw [hid]
    apply (le_div_iff₀ hm).mpr
    have hp : 0 ≤ θ * (1 - 2 * θ) := mul_nonneg h0.le (by linarith)
    nlinarith
  unfold combinedMean
  simpa only [one_div] using div_le_div_of_nonneg_right hnum hm.le

theorem cmObjective_lower {θ a : ℝ} (h0 : 0 < θ) (h4 : θ < 1 / 4) (ha : 1 ≤ a) :
    ENNReal.ofReal θ⁻¹ ≤ cmObjective uniformLaw (law θ) a := by
  classical
  have ha0 : 0 ≤ a := by linarith
  have hm : 0 < 1 - θ := by linarith
  rw [cmObjective, conditionalRatioMean_formula h0 h4 (one_lt_cmCutoff ha)
    (cmCutoff_le_nine_fourths ha)]
  by_cases h : cmCutoff a ≤ (1 - θ)⁻¹
  · simp only [h, ite_true]
    rw [← ENNReal.ofReal_mul ha0]
    apply ENNReal.ofReal_le_ofReal
    calc
      θ⁻¹ = ((1 - θ) / θ) * (1 - θ)⁻¹ := by field_simp [h0.ne', hm.ne']
      _ ≤ a * combinedMean θ :=
        mul_le_mul (optimizer_parameter_lower h0 h4 ha h)
          (combinedMean_ge_inverse h0 h4) (inv_nonneg.mpr hm.le) ha0
  · simp only [h, ite_false]
    rw [← ENNReal.ofReal_mul ha0]
    apply ENNReal.ofReal_le_ofReal
    have hp : 0 ≤ (a - 1) * θ⁻¹ := mul_nonneg (sub_nonneg.mpr ha) (inv_nonneg.mpr h0.le)
    nlinarith

theorem cmObjective_one_eq {θ : ℝ} (h0 : 0 < θ) (h4 : θ < 1 / 4) :
    cmObjective uniformLaw (law θ) 1 = ENNReal.ofReal θ⁻¹ := by
  have hnot : ¬ (9 / 4 : ℝ) ≤ (1 - θ)⁻¹ := by
    linarith [(ratio_height_order h0 h4).2.1]
  rw [cmObjective, ENNReal.ofReal_one, one_mul,
    conditionalRatioMean_formula h0 h4 (one_lt_cmCutoff (by norm_num : (1 : ℝ) ≤ 1))
      (cmCutoff_le_nine_fourths (by norm_num : (1 : ℝ) ≤ 1)),
    cmCutoff_one, ite_eq_right hnot]

/-- All real optimization parameters are covered; the exact minimum occurs at one. -/
theorem conditionalMoment_eq_inverse {θ : ℝ} (h0 : 0 < θ) (h4 : θ < 1 / 4) :
    conditionalMoment uniformLaw (law θ) = ENNReal.ofReal θ⁻¹ := by
  apply le_antisymm
  · exact (conditionalMoment_le 1 (by norm_num)).trans_eq (cmObjective_one_eq h0 h4)
  · exact le_conditionalMoment fun a ha ↦ cmObjective_lower h0 h4 ha

theorem conditionalMoment_zero : conditionalMoment uniformLaw (law 0) = 0 := by
  rw [law_zero]
  have ht : 1 < cmCutoff 1 := one_lt_cmCutoff (by norm_num)
  have hnull : uniformLaw (closedTailEvent uniformLaw uniformLaw (cmCutoff 1)) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [MeasureTheory.llr_self uniformLaw] with x hx
    change ¬ Real.log (cmCutoff 1) ≤ llr uniformLaw uniformLaw x
    rw [hx]
    exact not_le.mpr (Real.log_pos ht)
  have hmean := conditionalRatioMean_of_null Measure.AbsolutelyContinuous.rfl hnull
  apply bot_unique
  calc
    conditionalMoment uniformLaw uniformLaw ≤ cmObjective uniformLaw uniformLaw 1 :=
      conditionalMoment_le 1 (by norm_num)
    _ = 0 := by simp only [cmObjective, hmean, mul_zero]

def family : Set (Measure ℝ) :=
  {ν | ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 / 4 ∧ ν = law θ}

theorem law_mem_family {θ : ℝ} (h0 : 0 ≤ θ) (h4 : θ < 1 / 4) : law θ ∈ family :=
  ⟨θ, h0, h4, rfl⟩

theorem family_probability {ν : Measure ℝ} (hν : ν ∈ family) : IsProbabilityMeasure ν := by
  obtain ⟨θ, h0, h4, rfl⟩ := hν
  exact law_isProbabilityMeasure h0 h4

theorem uniform_tailPower_four :
    UniformHellingerBound uniformLaw family (fun ν ↦ tailPower uniformLaw ν 4 1) := by
  refine ⟨Real.toNNReal sourceSlope⁻¹, ?_⟩
  intro ν hν
  obtain ⟨θ, h0, h4, rfl⟩ := hν
  simpa only [ENNReal.ofReal] using tailPower_four_le_sourceCoeff h0 h4

theorem uniform_tailPower {q : ℝ} (hq : 1 < q) :
    UniformHellingerBound uniformLaw family (fun ν ↦ tailPower uniformLaw ν q 1) := by
  apply uniform_tailPower_four.tailPower_cutoff (fun ν hν ↦ ?_) hq
    (by norm_num : (1 : ℝ) < 4) zero_lt_one
  letI := family_probability hν
  infer_instance

theorem no_uniform_conditionalMoment :
    ¬ ∃ M : ℝ≥0, ∀ ν ∈ family, conditionalMoment uniformLaw ν ≤ (M : ℝ≥0∞) := by
  rintro ⟨M, hM⟩
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := NNReal.coe_nonneg M
  let θ : ℝ := 1 / (8 * ((M : ℝ) + 1))
  have h0 : 0 < θ := by dsimp [θ]; positivity
  have h4 : θ < 1 / 4 := by
    dsimp [θ]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 8 * ((M : ℝ) + 1))).mpr
    linarith only [hM0]
  have hbound := hM (law θ) (law_mem_family h0.le h4)
  rw [conditionalMoment_eq_inverse h0 h4] at hbound
  have hreal : θ⁻¹ ≤ (M : ℝ) := ENNReal.ofReal_le_coe.mp hbound
  have hinv : θ⁻¹ = 8 * ((M : ℝ) + 1) := by dsimp [θ]; rw [one_div, inv_inv]
  rw [hinv] at hreal
  linarith only [hreal, hM0]

theorem cm_family_separation {q : ℝ} (hq : 1 < q) :
    UniformHellingerBound uniformLaw family (fun ν ↦ tailPower uniformLaw ν q 1) ∧
      ¬ (∃ M : ℝ≥0, ∀ ν ∈ family, conditionalMoment uniformLaw ν ≤ (M : ℝ≥0∞)) :=
  ⟨uniform_tailPower hq, no_uniform_conditionalMoment⟩

/-- Rationalization gives a continuous expression for the normalized Hellinger distance. -/
noncomputable def normalizedHellingerExpr (θ : ℝ) : ℝ :=
  θ * (Real.sqrt θ - 1) ^ 2 +
    (1 - θ - θ ^ 2) * θ / (Real.sqrt (1 - θ) + 1) ^ 2 +
    (Real.sqrt (2 * (1 - θ ^ 2)) - 1) ^ 2

theorem hellingerExpr_div_eq_normalized {θ : ℝ} (h0 : 0 < θ) (h4 : θ < 1 / 4) :
    hellingerExpr θ / θ = normalizedHellingerExpr θ := by
  have hm : 0 ≤ 1 - θ := by linarith
  have hd : 0 < Real.sqrt (1 - θ) + 1 := by positivity
  have hs : Real.sqrt (1 - θ) - 1 = -θ / (Real.sqrt (1 - θ) + 1) := by
    field_simp [hd.ne']
    nlinarith [Real.sq_sqrt hm]
  unfold hellingerExpr normalizedHellingerExpr
  rw [hs]
  field_simp [h0.ne', hd.ne']

theorem normalizedHellingerExpr_zero : normalizedHellingerExpr 0 = sourceSlope := by
  unfold normalizedHellingerExpr sourceSlope
  norm_num
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- The printed right-hand slope is proved separately from the global coefficient. -/
theorem hellingerSq_div_parameter_tendsto :
    Tendsto (fun θ : ℝ ↦ (hellingerSq uniformLaw (law θ)).toReal / θ)
      (𝓝[>] 0) (𝓝 sourceSlope) := by
  have hc : Continuous normalizedHellingerExpr := by
    have hfirst : Continuous (fun θ : ℝ ↦ θ * (Real.sqrt θ - 1) ^ 2) := by fun_prop
    have hnum : Continuous (fun θ : ℝ ↦ (1 - θ - θ ^ 2) * θ) := by fun_prop
    have hden : Continuous (fun θ : ℝ ↦ (Real.sqrt (1 - θ) + 1) ^ 2) := by fun_prop
    have hnz : ∀ θ : ℝ, (Real.sqrt (1 - θ) + 1) ^ 2 ≠ 0 := by intro θ; positivity
    have hthird : Continuous (fun θ : ℝ ↦ (Real.sqrt (2 * (1 - θ ^ 2)) - 1) ^ 2) := by fun_prop
    exact (hfirst.add (hnum.div₀ hden hnz)).add hthird
  have hlim : Tendsto normalizedHellingerExpr (𝓝[>] (0 : ℝ)) (𝓝 sourceSlope) := by
    rw [← normalizedHellingerExpr_zero]
    exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  refine hlim.congr' ?_
  have hsmall : ∀ᶠ θ : ℝ in 𝓝[>] 0, θ < 1 / 4 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  filter_upwards [self_mem_nhdsWithin, hsmall] with θ h0 h4
  change 0 < θ at h0
  have hnn : 0 ≤ hellingerExpr θ :=
    (mul_nonneg sourceSlope_pos.le h0.le).trans (hellingerExpr_lower h0.le h4)
  rw [hellingerSq_eq_expr h0.le h4, ENNReal.toReal_ofReal hnn,
    hellingerExpr_div_eq_normalized h0 h4]

end Hellinger.Comparison.Examples.CMSeparation
