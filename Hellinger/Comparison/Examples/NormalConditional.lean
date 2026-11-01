/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.Comparison.Examples.NormalTail

/-! The literal source upper bound by the conditional ratio mean at threshold e.
The upper-tail monotonicity lemma requires its higher event to have positive
mass, so it does not confuse a null high event with a smaller conditional mean. -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Hellinger.Comparison

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α}

/-- Removing a lower-valued part of a nonnull event increases its average.
All integrals remain extended-valued; no integrability assumption is needed. -/
theorem setLIntegral_div_measure_mono_of_separated [IsFiniteMeasure μ]
    {f : α → ℝ≥0∞} (hf : Measurable f) {A B : Set α}
    (hB : MeasurableSet B) (hBA : B ⊆ A) (hB0 : μ B ≠ 0) (c : ℝ≥0∞)
    (hlow : ∀ x ∈ A \ B, f x ≤ c) (hhigh : ∀ x ∈ B, c ≤ f x) :
    (∫⁻ x in A, f x ∂μ) / μ A ≤ (∫⁻ x in B, f x ∂μ) / μ B := by
  have hA0 : μ A ≠ 0 := by
    intro hzero
    exact hB0 (le_antisymm ((measure_mono hBA).trans_eq hzero) bot_le)
  have hinter : A ∩ B = B := inter_eq_right.mpr hBA
  have hsplit : (∫⁻ x in A, f x ∂μ) =
      (∫⁻ x in B, f x ∂μ) + ∫⁻ x in A \ B, f x ∂μ := by
    simpa only [hinter] using (lintegral_inter_add_sdiff f A hB).symm
  have hmass : μ A = μ B + μ (A \ B) := by
    simpa only [hinter] using (measure_inter_add_sdiff (μ := μ) A hB).symm
  have hlowint : (∫⁻ x in A \ B, f x ∂μ) ≤ c * μ (A \ B) := by
    calc
      _ ≤ ∫⁻ _x in A \ B, c ∂μ := setLIntegral_mono measurable_const hlow
      _ = _ := setLIntegral_const _ _
  have hhighint : c * μ B ≤ ∫⁻ x in B, f x ∂μ := by
    calc
      _ = ∫⁻ _x in B, c ∂μ := (setLIntegral_const _ _).symm
      _ ≤ _ := setLIntegral_mono hf hhigh
  have hband : (∫⁻ x in A \ B, f x ∂μ) * μ B ≤
      (∫⁻ x in B, f x ∂μ) * μ (A \ B) := by
    calc
      _ ≤ (c * μ (A \ B)) * μ B := mul_le_mul' hlowint le_rfl
      _ = (c * μ B) * μ (A \ B) := by ac_rfl
      _ ≤ _ := mul_le_mul' hhighint le_rfl
  have hcross : (∫⁻ x in A, f x ∂μ) * μ B ≤
      (∫⁻ x in B, f x ∂μ) * μ A := by
    rw [hsplit, hmass, add_mul, mul_add]
    exact add_le_add le_rfl hband
  apply (ENNReal.div_le_iff hA0 (measure_ne_top μ A)).2
  rw [show ((∫⁻ x in B, f x ∂μ) / μ B) * μ A =
      ((∫⁻ x in B, f x ∂μ) * μ A) / μ B by
    simp only [div_eq_mul_inv]
    ac_rfl]
  exact (ENNReal.le_div_iff_mul_le (Or.inl hB0) (Or.inl (measure_ne_top μ B))).2 hcross

/-- Closed upper ratio means are monotone whenever the higher event is nonnull.
The hypothesis is essential under the paper's zero value for a null event. -/
theorem conditionalRatioMean_mono_of_nonnull [IsFiniteMeasure μ] (hμν : μ ≪ ν)
    {t b : ℝ} (ht : 0 < t) (htb : t ≤ b)
    (hb0 : μ (closedTailEvent μ ν b) ≠ 0) :
    conditionalRatioMean μ ν t ≤ conditionalRatioMean μ ν b := by
  have hb : 0 < b := ht.trans_le htb
  have hsub : closedTailEvent μ ν b ⊆ closedTailEvent μ ν t := by
    intro x hx
    exact (mem_closedTailEvent_iff ht x).2
      (htb.trans ((mem_closedTailEvent_iff hb x).1 hx))
  have ht0 : μ (closedTailEvent μ ν t) ≠ 0 := by
    intro hzero
    exact hb0 (le_antisymm ((measure_mono hsub).trans_eq hzero) bot_le)
  rw [conditionalRatioMean_of_nonnull hμν ht0, conditionalRatioMean_of_nonnull hμν hb0,
    closedTailMoment_of_ac hμν, closedTailMoment_of_ac hμν]
  apply setLIntegral_div_measure_mono_of_separated
    (measurable_llr μ ν).exp.ennreal_ofReal
    (measurableSet_closedTailEvent μ ν b) hsub hb0 (ENNReal.ofReal b)
  · intro x hx
    apply ENNReal.ofReal_le_ofReal
    apply le_of_lt
    apply lt_of_not_ge
    intro hbx
    exact hx.2 ((mem_closedTailEvent_iff hb x).2 hbx)
  · intro x hx
    exact ENNReal.ofReal_le_ofReal ((mem_closedTailEvent_iff hb x).1 hx)

namespace Examples.Normal

/-- The admissible native optimizer one has cutoff 9/4, at most e. -/
theorem cmCutoff_one_le_exp_one : cmCutoff 1 ≤ Real.exp 1 := by
  have hh : (3 / 2 : ℝ) ≤ Real.exp (1 / 2) := by
    linarith [Real.add_one_le_exp (1 / 2 : ℝ)]
  rw [cmCutoff_one]
  calc
    (9 / 4 : ℝ) = (3 / 2) * (3 / 2) := by norm_num
    _ ≤ Real.exp (1 / 2) * Real.exp (1 / 2) :=
      mul_le_mul hh hh (by norm_num) (Real.exp_pos _).le
    _ = Real.exp 1 := by rw [← Real.exp_add]; norm_num

/-- The literal source upper bound, including the actual null-event endpoint. -/
theorem normal_conditionalMoment_le_exp_one (theta : ℝ) :
    conditionalMoment (normalLaw 0) (normalLaw theta) ≤
      conditionalRatioMean (normalLaw 0) (normalLaw theta) (Real.exp 1) := by
  by_cases htheta : theta = 0
  · subst theta
    rw [conditionalMoment_zero,
      conditionalRatioMean_zero ((one_lt_cmCutoff le_rfl).trans_le cmCutoff_one_le_exp_one)]
  · have hnonnull : normalLaw 0
        (closedTailEvent (normalLaw 0) (normalLaw theta) (Real.exp 1)) ≠ 0 := by
      rw [closedTailEvent_normalLaw_measure htheta (Real.exp_pos 1)]
      exact (ENNReal.ofReal_pos.mpr (upperTail_pos _)).ne'
    calc
      conditionalMoment (normalLaw 0) (normalLaw theta) ≤
          cmObjective (normalLaw 0) (normalLaw theta) 1 := conditionalMoment_le 1 le_rfl
      _ = conditionalRatioMean (normalLaw 0) (normalLaw theta) (cmCutoff 1) := by
        simp only [cmObjective, ENNReal.ofReal_one, one_mul]
      _ ≤ _ := conditionalRatioMean_mono_of_nonnull (normalLaw_absolutelyContinuous 0 theta)
        (cmCutoff_pos le_rfl) cmCutoff_one_le_exp_one hnonnull

end Examples.Normal

end Hellinger.Comparison
