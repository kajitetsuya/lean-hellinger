/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.Comparison.Examples.Power
public import Hellinger.UniformBernstein

/-! The literal two-piece source family: a uniform base law on `(0,1)`, with
height theta on `(0,theta]` and height `1+theta` on `(theta,1)`. -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Hellinger.Comparison.Examples.FMSeparation

open Power

/-- The complete source parameter interval, retaining its zero endpoint. -/
abbrev Parameter := {θ : ℝ // 0 ≤ θ ∧ θ < 1 / 4}

noncomputable def zeroParameter : Parameter := ⟨0, by constructor <;> norm_num⟩

noncomputable def density (θ : Parameter) (x : ℝ) : ℝ≥0∞ :=
  if x ≤ θ.1 then ENNReal.ofReal θ.1 else ENNReal.ofReal (1 + θ.1)

noncomputable def modelLaw (θ : Parameter) : Measure ℝ := uniformLaw.withDensity (density θ)

theorem parameter_lt_one (θ : Parameter) : θ.1 < 1 := by linarith [θ.2.2]

theorem measurable_density (θ : Parameter) : Measurable (density θ) :=
  Measurable.ite measurableSet_Iic measurable_const measurable_const

theorem modelLaw_eq_volume_withDensity (θ : Parameter) :
    modelLaw θ = volume.withDensity ((Ioo (0 : ℝ) 1).indicator (density θ)) :=
  (withDensity_indicator measurableSet_Ioo (density θ)).symm

theorem uniformLaw_Iic {θ : ℝ} (_hθ : 0 ≤ θ) (hθ1 : θ < 1) :
    uniformLaw (Iic θ) = ENNReal.ofReal θ := by
  have hs : Iic θ ∩ Ioo (0 : ℝ) 1 = Ioc 0 θ := by
    ext x
    constructor
    · rintro ⟨hx, hx0, hx1⟩
      exact ⟨hx0, hx⟩
    · rintro ⟨hx0, hxθ⟩
      exact ⟨hxθ, hx0, hxθ.trans_lt hθ1⟩
  rw [uniformLaw, Measure.restrict_apply measurableSet_Iic, hs, Real.volume_Ioc]
  simp

theorem uniformLaw_Ioi {θ : ℝ} (hθ : 0 ≤ θ) (_hθ1 : θ < 1) :
    uniformLaw (Ioi θ) = ENNReal.ofReal (1 - θ) := by
  have hs : Ioi θ ∩ Ioo (0 : ℝ) 1 = Ioo θ 1 := by
    ext x
    constructor
    · rintro ⟨hx, hx0, hx1⟩
      exact ⟨hx, hx1⟩
    · rintro ⟨hxθ, hx1⟩
      exact ⟨hxθ, hθ.trans_lt hxθ, hx1⟩
  rw [uniformLaw, Measure.restrict_apply measurableSet_Ioi, hs, Real.volume_Ioo]

theorem lintegral_two_piece {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1) (a b : ℝ≥0∞) :
    (∫⁻ x, (if x ≤ θ then a else b) ∂uniformLaw) =
      a * ENNReal.ofReal θ + b * ENNReal.ofReal (1 - θ) := by
  classical
  change (∫⁻ x, (Iic θ).piecewise (fun _ ↦ a) (fun _ ↦ b) x ∂uniformLaw) = _
  rw [lintegral_piecewise measurableSet_Iic.nullMeasurableSet,
    setLIntegral_const, setLIntegral_const, compl_Iic,
    uniformLaw_Iic hθ hθ1, uniformLaw_Ioi hθ hθ1]

theorem lintegral_two_piece_ofReal {θ a b : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫⁻ x, (if x ≤ θ then ENNReal.ofReal a else ENNReal.ofReal b) ∂uniformLaw) =
      ENNReal.ofReal (a * θ + b * (1 - θ)) := by
  rw [lintegral_two_piece hθ hθ1,
    ENNReal.ofReal_add (mul_nonneg ha hθ) (mul_nonneg hb (by linarith)),
    ENNReal.ofReal_mul ha, ENNReal.ofReal_mul hb]

theorem modelLaw_mass_univ (θ : Parameter) : modelLaw θ univ = 1 := by
  rw [modelLaw, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  change (∫⁻ x, (if x ≤ θ.1 then ENNReal.ofReal θ.1 else ENNReal.ofReal (1 + θ.1))
    ∂uniformLaw) = 1
  rw [lintegral_two_piece_ofReal θ.2.1 (parameter_lt_one θ) θ.2.1 (by linarith [θ.2.1])]
  have hid : θ.1 * θ.1 + (1 + θ.1) * (1 - θ.1) = 1 := by ring
  rw [hid, ENNReal.ofReal_one]

instance modelLaw_isProbabilityMeasure (θ : Parameter) : IsProbabilityMeasure (modelLaw θ) where
  measure_univ := modelLaw_mass_univ θ

theorem rnDeriv_modelLaw_ae (θ : Parameter) :
    (modelLaw θ).rnDeriv uniformLaw =ᵐ[uniformLaw] density θ :=
  Measure.rnDeriv_withDensity uniformLaw (measurable_density θ)

theorem uniformLaw_absolutelyContinuous_modelLaw (θ : Parameter) : uniformLaw ≪ modelLaw θ := by
  apply withDensity_absolutelyContinuous' (measurable_density θ).aemeasurable
  filter_upwards [uniformLaw_ae_mem] with x hx
  unfold density
  split_ifs with hbranch
  · exact (ENNReal.ofReal_pos.mpr (hx.1.trans_le hbranch)).ne'
  · exact (ENNReal.ofReal_pos.mpr (by linarith [θ.2.1])).ne'

theorem modelLaw_zero : modelLaw zeroParameter = uniformLaw := by
  rw [modelLaw]
  have heq : density zeroParameter =ᵐ[uniformLaw] fun _ ↦ 1 := by
    filter_upwards [uniformLaw_ae_mem] with x hx
    have hn : ¬ x ≤ (0 : ℝ) := not_le_of_gt hx.1
    simp [density, zeroParameter, hn]
  rw [withDensity_congr_ae heq]
  exact withDensity_one

/-- The source ratio on the actual interval measure, with the zero-parameter null
first branch removed by its probability-zero event. -/
theorem dominatedRatio_ae_eq_piecewise_inverse (θ : Parameter) :
    dominatedRatio uniformLaw (modelLaw θ) uniformLaw =ᵐ[uniformLaw]
      fun x ↦ ENNReal.ofReal (if x ≤ θ.1 then θ.1⁻¹ else (1 + θ.1)⁻¹) := by
  filter_upwards [dominatedRatio_ae_eq_inv_rnDeriv
      (μ := uniformLaw) (ν := modelLaw θ) (κ := uniformLaw) Measure.AbsolutelyContinuous.rfl,
    rnDeriv_modelLaw_ae θ, uniformLaw_ae_mem] with x hratio hrn hx
  rw [hratio, hrn, density]
  split_ifs with hbranch
  · rw [← ENNReal.ofReal_inv_of_pos (hx.1.trans_le hbranch)]
  · rw [← ENNReal.ofReal_inv_of_pos (by linarith [θ.2.1])]

/-- An endpoint-safe full-moment identity, before cancelling theta. -/
theorem fullRatioMoment_eq_piecewise (θ : Parameter) :
    fullRatioMoment uniformLaw (modelLaw θ) =
      ENNReal.ofReal (θ.1⁻¹ * θ.1 + (1 + θ.1)⁻¹ * (1 - θ.1)) := by
  rw [fullRatioMoment_eq_lintegral_dominatedRatio
    (κ := uniformLaw) Measure.AbsolutelyContinuous.rfl,
    lintegral_congr_ae (dominatedRatio_ae_eq_piecewise_inverse θ)]
  simp_rw [apply_ite ENNReal.ofReal]
  exact lintegral_two_piece_ofReal θ.2.1 (parameter_lt_one θ)
    (inv_nonneg.mpr θ.2.1) (inv_nonneg.mpr (by linarith [θ.2.1]))

theorem fullRatioMoment_zero : fullRatioMoment uniformLaw (modelLaw zeroParameter) = 1 := by
  rw [fullRatioMoment_eq_piecewise]
  norm_num [zeroParameter]

/-- The printed positive-parameter full moment, with its necessary domain. -/
theorem fullRatioMoment_eq_of_pos {θ : Parameter} (hθ : 0 < θ.1) :
    fullRatioMoment uniformLaw (modelLaw θ) =
      ENNReal.ofReal (1 + (1 - θ.1) / (1 + θ.1)) := by
  rw [fullRatioMoment_eq_piecewise, inv_mul_cancel₀ hθ.ne']
  congr 1
  ring

theorem fullRatioMoment_le_two (θ : Parameter) :
    fullRatioMoment uniformLaw (modelLaw θ) ≤ 2 := by
  by_cases hθ : θ.1 = 0
  · rw [fullRatioMoment_eq_piecewise, hθ]
    norm_num
  · rw [fullRatioMoment_eq_of_pos (lt_of_le_of_ne θ.2.1 (Ne.symm hθ))]
    have hfrac : (1 - θ.1) / (1 + θ.1) ≤ 1 :=
      (div_le_one (by linarith [θ.2.1])).mpr (by linarith [θ.2.1])
    exact (ENNReal.ofReal_le_ofReal (by linarith : 1 + (1 - θ.1) / (1 + θ.1) ≤ 2)).trans_eq
      (by norm_num)

/-- The corrected exact Hellinger expression: the second interval has length
`1-theta`, as forced by the literal density. -/
theorem hellingerSq_eq (θ : Parameter) :
    hellingerSq uniformLaw (modelLaw θ) = ENNReal.ofReal
      (θ.1 * (1 - Real.sqrt θ.1) ^ 2 + (1 - θ.1) * (1 - Real.sqrt (1 + θ.1)) ^ 2) := by
  have hmodel : modelLaw θ ≪ uniformLaw :=
    withDensity_absolutelyContinuous uniformLaw (density θ)
  rw [hellingerSq_symm, hellingerSq_eq_lintegral_of_ac hmodel]
  calc
    _ = ∫⁻ x, (if x ≤ θ.1 then ENNReal.ofReal ((1 - Real.sqrt θ.1) ^ 2)
        else ENNReal.ofReal ((1 - Real.sqrt (1 + θ.1)) ^ 2)) ∂uniformLaw := by
      apply lintegral_congr_ae
      filter_upwards [rnDeriv_modelLaw_ae θ] with x hx
      rw [hx, density]
      split_ifs with hbranch
      · rw [ENNReal.toReal_ofReal θ.2.1]
        congr 1
        ring
      · rw [ENNReal.toReal_ofReal (by linarith [θ.2.1])]
        congr 1
        ring
    _ = ENNReal.ofReal (((1 - Real.sqrt θ.1) ^ 2) * θ.1 +
        ((1 - Real.sqrt (1 + θ.1)) ^ 2) * (1 - θ.1)) :=
      lintegral_two_piece_ofReal θ.2.1 (parameter_lt_one θ) (sq_nonneg _) (sq_nonneg _)
    _ = _ := by congr 1; ring

/-- A convenient global linear Hellinger upper bound for the full parameter range. -/
theorem hellingerSq_le_two_mul_parameter (θ : Parameter) :
    hellingerSq uniformLaw (modelLaw θ) ≤ ENNReal.ofReal (2 * θ.1) := by
  rw [hellingerSq_eq]
  apply ENNReal.ofReal_le_ofReal
  have hθ0 := θ.2.1
  have hθ1 : θ.1 ≤ 1 := (parameter_lt_one θ).le
  have hs0 : 0 ≤ Real.sqrt θ.1 := Real.sqrt_nonneg _
  have hs1 : Real.sqrt θ.1 ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hθ1
  have hA : (1 - Real.sqrt θ.1) ^ 2 ≤ 1 := by nlinarith
  have ht1 : 1 ≤ Real.sqrt (1 + θ.1) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (by linarith : (1 : ℝ) ≤ 1 + θ.1)
  have htθ : Real.sqrt (1 + θ.1) ≤ 1 + θ.1 :=
    Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  have hB : (1 - Real.sqrt (1 + θ.1)) ^ 2 ≤ θ.1 ^ 2 := by
    have hh := pow_le_pow_left₀ (by linarith : 0 ≤ Real.sqrt (1 + θ.1) - 1)
      (by linarith : Real.sqrt (1 + θ.1) - 1 ≤ θ.1) 2
    nlinarith
  calc
    _ ≤ θ.1 * 1 + (1 - θ.1) * θ.1 ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left hA hθ0)
        (mul_le_mul_of_nonneg_left hB (by linarith))
    _ ≤ θ.1 + θ.1 ^ 2 := by nlinarith [mul_nonneg hθ0 (sq_nonneg θ.1)]
    _ ≤ 2 * θ.1 := by nlinarith [mul_nonneg hθ0 (sub_nonneg.mpr hθ1)]

/-- Every positive real power has the exact small-parameter tail from the first interval. -/
theorem tailPower_eq_of_pos {θ : Parameter} {q δ : ℝ}
    (hθ : 0 < θ.1) (hq : 1 < q) (hθq : θ.1 < 1 / q) (hδ : 0 < δ) :
    tailPower uniformLaw (modelLaw θ) q δ = ENNReal.ofReal (θ.1 ^ (1 - δ)) := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  have htail : q < θ.1⁻¹ := by
    rw [← one_div]
    apply (lt_div_iff₀ hθ).mpr
    have hh := (lt_div_iff₀ hq0).mp hθq
    nlinarith
  have hother : (1 + θ.1)⁻¹ ≤ 1 := by
    simpa only [one_div, inv_one] using
      one_div_le_one_div_of_le zero_lt_one (by linarith [θ.2.1] : (1 : ℝ) ≤ 1 + θ.1)
  have htailE : ENNReal.ofReal q < ENNReal.ofReal θ.1⁻¹ :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hq0.le).mpr htail
  have hotherE : ¬ ENNReal.ofReal q < ENNReal.ofReal (1 + θ.1)⁻¹ :=
    not_lt_of_ge (ENNReal.ofReal_le_ofReal (hother.trans hq.le))
  rw [tailPower_eq_setLIntegral_dominatedRatio_rpow
    (κ := uniformLaw) Measure.AbsolutelyContinuous.rfl hq hδ,
    ← lintegral_indicator (measurableSet_dominatedStrictTailEvent _ _ _ _)]
  calc
    _ = ∫⁻ x, (if x ≤ θ.1 then ENNReal.ofReal θ.1⁻¹ ^ δ else 0) ∂uniformLaw := by
      apply lintegral_congr_ae
      filter_upwards [dominatedRatio_ae_eq_piecewise_inverse θ] with x hx
      simp only [Set.indicator_apply, dominatedStrictTailEvent, Set.mem_ofPred_eq]
      simp only [hx]
      split_ifs with hbranch
      · rfl
      · rfl
    _ = ENNReal.ofReal θ.1⁻¹ ^ δ * ENNReal.ofReal θ.1 := by
      rw [lintegral_two_piece θ.2.1 (parameter_lt_one θ)]
      simp
    _ = ENNReal.ofReal ((θ.1⁻¹) ^ δ * θ.1) := by
      rw [ENNReal.ofReal_rpow_of_pos (inv_pos.mpr hθ),
        ENNReal.ofReal_mul (Real.rpow_nonneg (inv_nonneg.mpr θ.2.1) _)]
    _ = _ := by
      congr 1
      calc
        (θ.1⁻¹) ^ δ * θ.1 = θ.1 ^ (-δ) * θ.1 ^ (1 : ℝ) := by
          rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_one]
        _ = θ.1 ^ (1 - δ) := by
          rw [← Real.rpow_add hθ]
          congr 1
          ring

theorem tailPower_zero {q δ : ℝ} (hq : 1 < q) :
    tailPower uniformLaw (modelLaw zeroParameter) q δ = 0 := by
  rw [modelLaw_zero, tailPower_of_ac Measure.AbsolutelyContinuous.rfl]
  rw [← lintegral_indicator (measurableSet_tailEvent _ _ _)]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [uniformLaw.rnDeriv_self] with x hx
  have hn : ¬ Real.log q < 0 := not_lt_of_ge (Real.log_pos hq).le
  simp [tailEvent, llr, hx, hn]

/-- The literal source half-tail equality, including theta zero. -/
theorem tailPower_half_four (θ : Parameter) :
    tailPower uniformLaw (modelLaw θ) 4 (1 / 2) = ENNReal.ofReal (Real.sqrt θ.1) := by
  by_cases hθ : θ.1 = 0
  · have heq : θ = zeroParameter := Subtype.ext hθ
    subst θ
    rw [tailPower_zero (by norm_num)]
    norm_num [zeroParameter]
  · rw [tailPower_eq_of_pos (lt_of_le_of_ne θ.2.1 (Ne.symm hθ))
      (by norm_num : (1 : ℝ) < 4) θ.2.2 (by norm_num)]
    rw [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]

/-- One actual model family, with the source parameter range fixed once and for all. -/
def modelFamily : Set (Measure ℝ) := Set.range modelLaw

theorem modelFamily_probability : ∀ ν ∈ modelFamily, IsProbabilityMeasure ν := by
  rintro ν ⟨θ, rfl⟩
  infer_instance

theorem uniform_fullRatioMoment_le_two :
    ∃ B : ℝ≥0, ∀ ν ∈ modelFamily, fullRatioMoment uniformLaw ν ≤ (B : ℝ≥0∞) := by
  refine ⟨2, ?_⟩
  rintro ν ⟨θ, rfl⟩
  exact fullRatioMoment_le_two θ

/-- An explicit small positive parameter defeats any proposed finite multiplier.
No asymptotic assertion is used in place of a family quantifier. -/
theorem exists_small_parameter {q δ M : ℝ} (hq : 1 < q) (hδ : 0 < δ) (hM : 0 ≤ M) :
    ∃ θ : Parameter, 0 < θ.1 ∧ θ.1 < 1 / q ∧ 2 * M * θ.1 ^ δ < 1 := by
  let c : ℝ := 1 / (2 * M + 1)
  have hden : 0 < 2 * M + 1 := by linarith
  have hc : 0 < c := one_div_pos.mpr hden
  have heps : 0 < min (1 / 4 : ℝ) (min (1 / q) (c ^ δ⁻¹)) := by
    exact lt_min (by norm_num) (lt_min (one_div_pos.mpr (zero_lt_one.trans hq))
      (Real.rpow_pos_of_pos hc _))
  obtain ⟨x, hx0, hxeps⟩ := exists_between heps
  have hx4 : x < (1 / 4 : ℝ) := (lt_min_iff.mp hxeps).1
  have hxq : x < 1 / q := (lt_min_iff.mp (lt_min_iff.mp hxeps).2).1
  have hxr : x < c ^ δ⁻¹ := (lt_min_iff.mp (lt_min_iff.mp hxeps).2).2
  have hpow : x ^ δ < c := (Real.lt_rpow_inv_iff_of_pos hx0.le hc.le hδ).mp hxr
  have hm := mul_lt_mul_of_pos_left hpow hden
  have hid : (2 * M + 1) * c = 1 := by dsimp [c]; field_simp [hden.ne']
  rw [hid] at hm
  refine ⟨⟨x, hx0.le, hx4⟩, hx0, hxq, ?_⟩
  nlinarith [Real.rpow_nonneg hx0.le δ]

/-- Uniformly bounded full moments do not give NC for any fixed positive real exponent. -/
theorem not_uniform_tailPower {q δ : ℝ} (hq : 1 < q) (hδ : 0 < δ) :
    ¬ UniformHellingerBound uniformLaw modelFamily (fun ν ↦ tailPower uniformLaw ν q δ) := by
  rintro ⟨M, hM⟩
  obtain ⟨θ, hθ, hθq, hsmall⟩ := exists_small_parameter hq hδ M.property
  have hh := (hM (modelLaw θ) ⟨θ, rfl⟩).trans
    (mul_le_mul_right (hellingerSq_le_two_mul_parameter θ) (M : ℝ≥0∞))
  change tailPower uniformLaw (modelLaw θ) q δ ≤
    (M : ℝ≥0∞) * ENNReal.ofReal (2 * θ.1) at hh
  rw [tailPower_eq_of_pos hθ hq hθq hδ] at hh
  have hmE : (M : ℝ≥0∞) * ENNReal.ofReal (2 * θ.1) =
      ENNReal.ofReal ((M : ℝ) * (2 * θ.1)) := by
    calc
      _ = ENNReal.ofReal (M : ℝ) * ENNReal.ofReal (2 * θ.1) := by
        rw [ENNReal.ofReal_coe_nnreal]
      _ = _ := (ENNReal.ofReal_mul M.property).symm
  rw [hmE] at hh
  have hreal : θ.1 ^ (1 - δ) ≤ (M : ℝ) * (2 * θ.1) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh
  have hmul := mul_le_mul_of_nonneg_right hreal (Real.rpow_nonneg θ.2.1 δ)
  have hid : θ.1 ^ (1 - δ) * θ.1 ^ δ = θ.1 := by
    rw [← Real.rpow_add hθ, sub_add_cancel, Real.rpow_one]
  rw [hid] at hmul
  have hstrict : (M : ℝ) * (2 * θ.1) * θ.1 ^ δ < θ.1 := by
    calc
      _ = θ.1 * (2 * (M : ℝ) * θ.1 ^ δ) := by ring
      _ < θ.1 * 1 := mul_lt_mul_of_pos_left hsmall hθ
      _ = θ.1 := mul_one _
  exact (not_lt_of_ge hmul) hstrict

theorem not_uniform_bernsteinSq {q δ : ℝ} (hq : 1 < q) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ¬ UniformHellingerBound uniformLaw modelFamily (fun ν ↦ bernsteinSq uniformLaw ν δ) := by
  intro h
  exact not_uniform_tailPower hq hδ
    ((uniform_bernsteinSq_iff_tailPower uniformLaw modelFamily modelFamily_probability hq hδ hδ1).mp h)

/-- The full source family separation, with both uniform and real-exponent quantifiers explicit. -/
theorem fm_family_separation {q : ℝ} (hq : 1 < q) :
    (∀ ν ∈ modelFamily, IsProbabilityMeasure ν) ∧
    (∃ B : ℝ≥0, ∀ ν ∈ modelFamily, fullRatioMoment uniformLaw ν ≤ (B : ℝ≥0∞)) ∧
    ∀ δ : ℝ, 0 < δ → δ < 1 →
      (¬ UniformHellingerBound uniformLaw modelFamily (fun ν ↦ tailPower uniformLaw ν q δ)) ∧
      (¬ UniformHellingerBound uniformLaw modelFamily (fun ν ↦ bernsteinSq uniformLaw ν δ)) :=
  ⟨modelFamily_probability, uniform_fullRatioMoment_le_two,
    fun _ hδ hδ1 ↦ ⟨not_uniform_tailPower hq hδ, not_uniform_bernsteinSq hq hδ hδ1.le⟩⟩

/-- Every positive member has positive Hellinger distance, so the comparison is a
literal ratio divergence as well as failure of a common multiplier. -/
theorem hellingerSq_pos_of_pos {θ : Parameter} (hθ : 0 < θ.1) :
    0 < hellingerSq uniformLaw (modelLaw θ) := by
  rw [hellingerSq_eq]
  apply ENNReal.ofReal_pos.mpr
  have hs : Real.sqrt θ.1 < 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt θ.2.1 (parameter_lt_one θ)
  have hfirst : 0 < θ.1 * (1 - Real.sqrt θ.1) ^ 2 :=
    mul_pos hθ (sq_pos_of_pos (sub_pos.mpr hs))
  have hsecond : 0 ≤ (1 - θ.1) * (1 - Real.sqrt (1 + θ.1)) ^ 2 :=
    mul_nonneg (by linarith [parameter_lt_one θ]) (sq_nonneg _)
  linarith

/-- An explicit punctured-neighborhood form of divergence: every proposed finite
multiplier fails for all sufficiently small positive source parameters. -/
theorem eventually_tailPower_gt_mul {q δ : ℝ} (hq : 1 < q) (hδ : 0 < δ) (M : ℝ≥0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ θ : Parameter, 0 < θ.1 → θ.1 < ε →
      (M : ℝ≥0∞) * hellingerSq uniformLaw (modelLaw θ) <
        tailPower uniformLaw (modelLaw θ) q δ := by
  let c : ℝ := 1 / (2 * (M : ℝ) + 1)
  have hden : 0 < 2 * (M : ℝ) + 1 := by positivity
  have hc : 0 < c := one_div_pos.mpr hden
  refine ⟨min (1 / q) (c ^ δ⁻¹),
    lt_min (one_div_pos.mpr (zero_lt_one.trans hq)) (Real.rpow_pos_of_pos hc _), ?_⟩
  intro θ hθ hθε
  have hθq : θ.1 < 1 / q := (lt_min_iff.mp hθε).1
  have hpow : θ.1 ^ δ < c :=
    (Real.lt_rpow_inv_iff_of_pos θ.2.1 hc.le hδ).mp (lt_min_iff.mp hθε).2
  have hm := mul_lt_mul_of_pos_left hpow hden
  have hidc : (2 * (M : ℝ) + 1) * c = 1 := by dsimp [c]; field_simp [hden.ne']
  rw [hidc] at hm
  have hsmall : 2 * (M : ℝ) * θ.1 ^ δ < 1 := by
    nlinarith [Real.rpow_nonneg θ.2.1 δ]
  apply lt_of_not_ge
  intro hbad
  have hh := hbad.trans
    (mul_le_mul_right (hellingerSq_le_two_mul_parameter θ) (M : ℝ≥0∞))
  rw [tailPower_eq_of_pos hθ hq hθq hδ] at hh
  have hmE : (M : ℝ≥0∞) * ENNReal.ofReal (2 * θ.1) =
      ENNReal.ofReal ((M : ℝ) * (2 * θ.1)) := by
    calc
      _ = ENNReal.ofReal (M : ℝ) * ENNReal.ofReal (2 * θ.1) := by
        rw [ENNReal.ofReal_coe_nnreal]
      _ = _ := (ENNReal.ofReal_mul M.property).symm
  rw [hmE] at hh
  have hreal : θ.1 ^ (1 - δ) ≤ (M : ℝ) * (2 * θ.1) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh
  have hmul := mul_le_mul_of_nonneg_right hreal (Real.rpow_nonneg θ.2.1 δ)
  have hid : θ.1 ^ (1 - δ) * θ.1 ^ δ = θ.1 := by
    rw [← Real.rpow_add hθ, sub_add_cancel, Real.rpow_one]
  rw [hid] at hmul
  have hstrict : (M : ℝ) * (2 * θ.1) * θ.1 ^ δ < θ.1 := by
    calc
      _ = θ.1 * (2 * (M : ℝ) * θ.1 ^ δ) := by ring
      _ < θ.1 * 1 := mul_lt_mul_of_pos_left hsmall hθ
      _ = θ.1 := mul_one _
  exact (not_lt_of_ge hmul) hstrict

end Hellinger.Comparison.Examples.FMSeparation
