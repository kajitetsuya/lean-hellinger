/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.Comparison.DensityBridge
public import Hellinger.Comparison.Examples.NormalScalar
public import Mathlib.MeasureTheory.Measure.OpenPos

/-! Actual normal-location measures, likelihood ratios, and positive-mass failure
of boundedness. The conditional-tail formula and its rare-tail estimates are
separate modules; the paper's undefined zero-parameter quotient is not used. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Hellinger.Comparison.Examples.Normal

noncomputable def normalLaw (theta : ℝ) : Measure ℝ := gaussianReal theta 1

instance normalLaw_isProbabilityMeasure (theta : ℝ) :
    IsProbabilityMeasure (normalLaw theta) := by
  dsimp [normalLaw]
  infer_instance

instance normalLaw_nullSingletonClass (theta : ℝ) :
    NullSingletonClass (normalLaw theta) :=
  nullSingletonClass_gaussianReal (μ := theta) (v := 1) (by norm_num)

theorem normalLaw_absolutelyContinuous_volume (theta : ℝ) :
    normalLaw theta ≪ volume :=
  gaussianReal_absolutelyContinuous theta (by norm_num)

theorem volume_absolutelyContinuous_normalLaw (theta : ℝ) :
    volume ≪ normalLaw theta :=
  gaussianReal_absolutelyContinuous' theta (by norm_num)

theorem normalLaw_absolutelyContinuous (theta eta : ℝ) :
    normalLaw theta ≪ normalLaw eta :=
  (normalLaw_absolutelyContinuous_volume theta).trans
    (volume_absolutelyContinuous_normalLaw eta)

/-- The paper's total, everywhere-positive real density ratio. -/
noncomputable def ratio (theta x : ℝ) : ℝ :=
  Real.exp (-theta * x + theta ^ 2 / 2)

theorem ratio_pos (theta x : ℝ) : 0 < ratio theta x := Real.exp_pos _

theorem continuous_ratio (theta : ℝ) : Continuous (ratio theta) := by
  unfold ratio
  fun_prop

theorem ratio_eq_density_ratio (theta x : ℝ) :
    ratio theta x = gaussianPDFReal 0 1 x / gaussianPDFReal theta 1 x :=
  (NormalScalar.gaussianPDFReal_zero_div_location theta x).symm

theorem ratio_zero (x : ℝ) : ratio 0 x = 1 := by
  simp [ratio]

/-- The density quotient agrees with the intrinsic common-dominator ratio on
the source probability space, including theta zero. -/
theorem dominatedRatio_ae_eq_ratio (theta : ℝ) :
    dominatedRatio (normalLaw 0) (normalLaw theta) volume =ᵐ[normalLaw 0]
      fun x ↦ ENNReal.ofReal (ratio theta x) := by
  have hp := (normalLaw_absolutelyContinuous_volume 0).ae_le
    (rnDeriv_gaussianReal 0 1)
  have hq := (normalLaw_absolutelyContinuous_volume 0).ae_le
    (rnDeriv_gaussianReal theta 1)
  filter_upwards [hp, hq] with x hx0 hxt
  change (gaussianReal 0 1).rnDeriv volume x / (gaussianReal theta 1).rnDeriv volume x = _
  rw [hx0, hxt, gaussianPDF, gaussianPDF,
    ← ENNReal.ofReal_div_of_pos (gaussianPDFReal_pos theta 1 x (by norm_num)),
    NormalScalar.gaussianPDFReal_zero_div_location]
  rfl

/-- The actual measure-theoretic log likelihood ratio has the source affine form. -/
theorem llr_normalLaw_ae (theta : ℝ) :
    llr (normalLaw 0) (normalLaw theta) =ᵐ[normalLaw 0]
      fun x ↦ -theta * x + theta ^ 2 / 2 := by
  have hbridge := exp_llr_ae_eq_dominatedRatio
    (normalLaw_absolutelyContinuous_volume 0) (normalLaw_absolutelyContinuous 0 theta)
  filter_upwards [hbridge, dominatedRatio_ae_eq_ratio theta] with x hx hy
  have he := congrArg ENNReal.toReal (hx.trans hy)
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le,
    ENNReal.toReal_ofReal (ratio_pos theta x).le] at he
  exact Real.exp_injective he

/-- An explicit point exceeds every finite proposed bound, for either sign of theta. -/
theorem exists_ratio_gt {theta : ℝ} (htheta : theta ≠ 0) (B : ℝ≥0) :
    ∃ x : ℝ, (B : ℝ) < ratio theta x := by
  let x := (theta ^ 2 / 2 - Real.log ((B : ℝ) + 1)) / theta
  have hx : -theta * x + theta ^ 2 / 2 = Real.log ((B : ℝ) + 1) := by
    dsimp [x]
    field_simp [htheta]
    ring
  refine ⟨x, ?_⟩
  rw [ratio, hx, Real.exp_log (by positivity : 0 < (B : ℝ) + 1)]
  linarith

/-- Failure of UB is witnessed by a set of positive source probability,
not merely by a value at a null point. -/
theorem ratio_large_set_pos {theta : ℝ} (htheta : theta ≠ 0) (B : ℝ≥0) :
    0 < normalLaw 0 {x | (B : ℝ) < ratio theta x} := by
  have hopen : IsOpen {x | (B : ℝ) < ratio theta x} :=
    isOpen_lt continuous_const (continuous_ratio theta)
  have hvolume : 0 < volume {x | (B : ℝ) < ratio theta x} :=
    hopen.measure_pos volume (exists_ratio_gt htheta B)
  exact (volume_absolutelyContinuous_normalLaw 0).pos_mono hvolume

/-- The same positive-probability witness holds for the intrinsic extended ratio. -/
theorem dominatedRatio_large_set_pos {theta : ℝ} (htheta : theta ≠ 0) (B : ℝ≥0) :
    0 < normalLaw 0 {x | (B : ℝ≥0∞) <
      dominatedRatio (normalLaw 0) (normalLaw theta) volume x} := by
  have hevent : {x | (B : ℝ≥0∞) <
      dominatedRatio (normalLaw 0) (normalLaw theta) volume x} =ᵐ[normalLaw 0]
      {x | (B : ℝ) < ratio theta x} := by
    filter_upwards [dominatedRatio_ae_eq_ratio theta] with x hx
    simp only [hx, ENNReal.coe_lt_ofReal]
  rw [measure_congr hevent]
  exact ratio_large_set_pos htheta B

theorem not_ae_bounded_dominatedRatio {theta : ℝ} (htheta : theta ≠ 0) :
    ¬ ∃ B : ℝ≥0, ∀ᵐ x ∂normalLaw 0,
      dominatedRatio (normalLaw 0) (normalLaw theta) volume x ≤ (B : ℝ≥0∞) := by
  rintro ⟨B, hB⟩
  have hz : normalLaw 0 {x | (B : ℝ≥0∞) <
      dominatedRatio (normalLaw 0) (normalLaw theta) volume x} = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hB] with x hx
    exact not_lt_of_ge hx
  exact (dominatedRatio_large_set_pos htheta B).ne' hz

theorem not_pointwise_bounded_ratio {theta : ℝ} (htheta : theta ≠ 0) :
    ¬ ∃ B : ℝ≥0, ∀ x, ratio theta x ≤ (B : ℝ) := by
  rintro ⟨B, hB⟩
  obtain ⟨x, hx⟩ := exists_ratio_gt htheta B
  exact (not_lt_of_ge (hB x)) hx

/-- The zero-parameter conditional mean is the paper's null-event value zero. -/
theorem conditionalRatioMean_zero {t : ℝ} (ht : 1 < t) :
    conditionalRatioMean (normalLaw 0) (normalLaw 0) t = 0 := by
  have hz : normalLaw 0 (closedTailEvent (normalLaw 0) (normalLaw 0) t) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [llr_normalLaw_ae 0] with x hx
    have hllr : llr (normalLaw 0) (normalLaw 0) x = 0 := by simpa using hx
    change ¬ Real.log t ≤ llr (normalLaw 0) (normalLaw 0) x
    rw [hllr]
    exact not_le_of_gt (Real.log_pos ht)
  exact conditionalRatioMean_of_null (normalLaw_absolutelyContinuous 0 0) hz

theorem conditionalMoment_zero : conditionalMoment (normalLaw 0) (normalLaw 0) = 0 := by
  apply le_antisymm _ bot_le
  calc
    _ ≤ cmObjective (normalLaw 0) (normalLaw 0) 1 := conditionalMoment_le 1 le_rfl
    _ = 0 := by
      rw [cmObjective, conditionalRatioMean_zero (one_lt_cmCutoff le_rfl), mul_zero]

/-- Exact source ratio and positive-mass unboundedness, on the genuine Gaussian laws. -/
theorem normal_location_fails_ub {theta : ℝ} (htheta : theta ≠ 0) :
    (llr (normalLaw 0) (normalLaw theta) =ᵐ[normalLaw 0]
      fun x ↦ -theta * x + theta ^ 2 / 2) ∧
    ∀ B : ℝ≥0, 0 < normalLaw 0 {x | (B : ℝ≥0∞) <
      dominatedRatio (normalLaw 0) (normalLaw theta) volume x} :=
  ⟨llr_normalLaw_ae theta, fun B ↦ dominatedRatio_large_set_pos htheta B⟩

end Hellinger.Comparison.Examples.Normal
