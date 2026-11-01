/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.Comparison.Definitions

/-! The literal extended density ratio for any common sigma-finite dominator.
The singular contribution is proved from the Lebesgue decomposition, rather than
being identified with infinity merely by the comparison definitions. -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Hellinger.Comparison

variable {α : Type*} [MeasurableSpace α] {μ ν κ : Measure α}

/-- The source likelihood ratio, keeping division by zero in `ENNReal`. -/
noncomputable def dominatedRatio (μ ν κ : Measure α) (x : α) : ℝ≥0∞ :=
  μ.rnDeriv κ x / ν.rnDeriv κ x

theorem measurable_dominatedRatio (μ ν κ : Measure α) :
    Measurable (dominatedRatio μ ν κ) :=
  (Measure.measurable_rnDeriv μ κ).div (Measure.measurable_rnDeriv ν κ)

/-- Closed source event; finite real cutoffs retain every infinite ratio. -/
noncomputable def dominatedClosedTailEvent (μ ν κ : Measure α) (t : ℝ) : Set α :=
  {x | ENNReal.ofReal t ≤ dominatedRatio μ ν κ x}

theorem measurableSet_dominatedClosedTailEvent (μ ν κ : Measure α) (t : ℝ) :
    MeasurableSet (dominatedClosedTailEvent μ ν κ t) :=
  measurableSet_le measurable_const (measurable_dominatedRatio μ ν κ)

section SigmaFinite

variable [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite κ]

/-- A common-dominator ratio is the reciprocal reverse RN density, even without
`μ ≪ ν`. In particular this identity does not erase singular mass. -/
theorem dominatedRatio_ae_eq_inv_rnDeriv (hμκ : μ ≪ κ) :
    dominatedRatio μ ν κ =ᵐ[μ] fun x ↦ (ν.rnDeriv μ x)⁻¹ := by
  filter_upwards [Measure.rnDeriv_mul_rnDeriv' (μ := ν) hμκ,
    Measure.rnDeriv_pos hμκ, hμκ.ae_le (Measure.rnDeriv_lt_top μ κ)]
    with x hchain hpos htop
  change μ.rnDeriv κ x / ν.rnDeriv κ x = _
  change ν.rnDeriv μ x * μ.rnDeriv κ x = ν.rnDeriv κ x at hchain
  rw [← hchain]
  simpa only [one_mul, one_div] using
    (ENNReal.mul_div_mul_right 1 (ν.rnDeriv μ x) hpos.ne' htop.ne)

/-- The generic quotient has its genuine infinite value on the singular part. -/
theorem dominatedRatio_ae_eq_top_singularPart (hμκ : μ ≪ κ) :
    dominatedRatio μ ν κ =ᵐ[μ.singularPart ν] fun _ ↦ ∞ := by
  filter_upwards [ae_mono (Measure.singularPart_le μ ν)
      (dominatedRatio_ae_eq_inv_rnDeriv (ν := ν) hμκ),
    Measure.rnDeriv_eq_zero_ae_singularPart ν μ] with x hratio hzero
  simpa only [hzero, ENNReal.inv_zero] using hratio

/-- Any kernel infinite on a nonzero singular part has infinite full integral. -/
theorem lintegral_eq_top_of_ae_top_singularPart {f : α → ℝ≥0∞}
    (hμν : ¬ μ ≪ ν) (hf : f =ᵐ[μ.singularPart ν] fun _ ↦ ∞) :
    ∫⁻ x, f x ∂μ = ∞ := by
  have hsing : μ.singularPart ν ≠ 0 := mt (Measure.singularPart_eq_zero μ ν).mp hμν
  have hsint : ∫⁻ x, f x ∂(μ.singularPart ν) = ∞ := by
    rw [lintegral_congr_ae hf, lintegral_const]
    exact ENNReal.top_mul (mt Measure.measure_univ_eq_zero.mp hsing)
  apply top_unique
  rw [← hsint]
  exact lintegral_mono' (Measure.singularPart_le μ ν) le_rfl

theorem lintegral_dominatedRatio_eq_top_of_not_ac (hμκ : μ ≪ κ) (hμν : ¬ μ ≪ ν) :
    ∫⁻ x, dominatedRatio μ ν κ x ∂μ = ∞ :=
  lintegral_eq_top_of_ae_top_singularPart hμν (dominatedRatio_ae_eq_top_singularPart hμκ)

/-- A finite-threshold source tail contains all singular mass, including atoms. -/
theorem setLIntegral_dominatedRatio_eq_top_of_not_ac
    (hμκ : μ ≪ κ) (hμν : ¬ μ ≪ ν) (t : ℝ) :
    ∫⁻ x in dominatedClosedTailEvent μ ν κ t, dominatedRatio μ ν κ x ∂μ = ∞ := by
  rw [← lintegral_indicator (measurableSet_dominatedClosedTailEvent μ ν κ t)]
  apply lintegral_eq_top_of_ae_top_singularPart hμν
  filter_upwards [dominatedRatio_ae_eq_top_singularPart (ν := ν) hμκ] with x hx
  have hmem : x ∈ dominatedClosedTailEvent μ ν κ t := by
    change ENNReal.ofReal t ≤ dominatedRatio μ ν κ x
    rw [hx]
    exact le_top
  rw [Set.indicator_of_mem hmem, hx]

end SigmaFinite

section Finite

variable [IsFiniteMeasure μ] [IsFiniteMeasure ν] [SigmaFinite κ]

theorem exp_llr_ae_eq_dominatedRatio (hμκ : μ ≪ κ) (hμν : μ ≪ ν) :
    (fun x ↦ ENNReal.ofReal (Real.exp (llr μ ν x))) =ᵐ[μ] dominatedRatio μ ν κ :=
  (exp_llr_ae_eq_rnDeriv hμν).trans
    ((Measure.inv_rnDeriv' hμν).symm.trans (dominatedRatio_ae_eq_inv_rnDeriv hμκ).symm)

/-- Source full moment for any common dominator. Both extended branches are proved. -/
theorem fullRatioMoment_eq_lintegral_dominatedRatio (hμκ : μ ≪ κ) :
    fullRatioMoment μ ν = ∫⁻ x, dominatedRatio μ ν κ x ∂μ := by
  by_cases hμν : μ ≪ ν
  · rw [fullRatioMoment_of_ac hμν]
    exact lintegral_congr_ae (exp_llr_ae_eq_dominatedRatio hμκ hμν)
  · rw [fullRatioMoment_of_not_ac hμν,
      lintegral_dominatedRatio_eq_top_of_not_ac hμκ hμν]

/-- The exact closed source event in the AC branch, including threshold atoms. -/
theorem closedTailEvent_ae_eq_dominatedClosedTailEvent (hμκ : μ ≪ κ) (hμν : μ ≪ ν)
    {t : ℝ} (ht : 0 < t) :
    closedTailEvent μ ν t =ᵐ[μ] dominatedClosedTailEvent μ ν κ t := by
  filter_upwards [exp_llr_ae_eq_dominatedRatio hμκ hμν] with x hx
  apply propext
  change (x ∈ closedTailEvent μ ν t) ↔ ENNReal.ofReal t ≤ dominatedRatio μ ν κ x
  rw [mem_closedTailEvent_iff ht, ← hx]
  exact (ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).symm

/-- Source closed first moment for any common dominator and positive finite cutoff. -/
theorem closedTailMoment_eq_setLIntegral_dominatedRatio (hμκ : μ ≪ κ)
    {t : ℝ} (ht : 0 < t) :
    closedTailMoment μ ν t =
      ∫⁻ x in dominatedClosedTailEvent μ ν κ t, dominatedRatio μ ν κ x ∂μ := by
  by_cases hμν : μ ≪ ν
  · rw [closedTailMoment_of_ac hμν]
    calc
      _ = ∫⁻ x in closedTailEvent μ ν t, dominatedRatio μ ν κ x ∂μ :=
        lintegral_congr_ae (ae_restrict_of_ae (exp_llr_ae_eq_dominatedRatio hμκ hμν))
      _ = _ := setLIntegral_congr
        (closedTailEvent_ae_eq_dominatedClosedTailEvent hμκ hμν ht)
  · rw [closedTailMoment_of_not_ac hμν,
      setLIntegral_dominatedRatio_eq_top_of_not_ac hμκ hμν]

/-- Conditional density-ratio mean, with value zero on null conditioning events. -/
noncomputable def dominatedConditionalRatioMean (μ ν κ : Measure α) (t : ℝ) : ℝ≥0∞ :=
  if μ (dominatedClosedTailEvent μ ν κ t) = 0 then 0 else
    (∫⁻ x in dominatedClosedTailEvent μ ν κ t, dominatedRatio μ ν κ x ∂μ) /
      μ (dominatedClosedTailEvent μ ν κ t)

theorem conditionalRatioMean_eq_dominatedConditionalRatioMean (hμκ : μ ≪ κ)
    {t : ℝ} (ht : 0 < t) :
    conditionalRatioMean μ ν t = dominatedConditionalRatioMean μ ν κ t := by
  classical
  unfold dominatedConditionalRatioMean
  by_cases hμν : μ ≪ ν
  · have hmass := measure_congr
      (closedTailEvent_ae_eq_dominatedClosedTailEvent hμκ hμν ht)
    rw [conditionalRatioMean_of_ac hμν, hmass,
      closedTailMoment_eq_setLIntegral_dominatedRatio hμκ ht]
  · have hintegral := setLIntegral_dominatedRatio_eq_top_of_not_ac hμκ hμν t
    have hmass : μ (dominatedClosedTailEvent μ ν κ t) ≠ 0 := by
      intro hz
      rw [Measure.restrict_eq_zero.mpr hz, lintegral_zero_measure] at hintegral
      exact ENNReal.zero_ne_top hintegral
    rw [conditionalRatioMean_of_not_ac hμν, ite_eq_right hmass, hintegral,
      ENNReal.top_div_of_ne_top (measure_ne_top _ _)]

/-- The source CM infimum is independent of the chosen common dominator. -/
theorem conditionalMoment_eq_iInf_dominatedConditionalRatioMean (hμκ : μ ≪ κ) :
    conditionalMoment μ ν =
      ⨅ a : {a : ℝ // 1 ≤ a},
        ENNReal.ofReal a.1 * dominatedConditionalRatioMean μ ν κ (cmCutoff a.1) := by
  unfold conditionalMoment cmObjective
  apply iInf_congr
  intro a
  rw [conditionalRatioMean_eq_dominatedConditionalRatioMean hμκ (cmCutoff_pos a.2)]

end Finite

end Hellinger.Comparison
