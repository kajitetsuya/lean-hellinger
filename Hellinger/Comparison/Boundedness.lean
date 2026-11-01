/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.Comparison.DensityBridge
public import Hellinger.Comparison.FiniteMoment

/-! Uniformly bounded likelihood ratios imply a uniform native CM bound.
Pointwise bounds are related explicitly to their almost-everywhere consequences. -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Hellinger.Comparison

variable {α : Type*} [MeasurableSpace α] {μ ν κ : Measure α}

theorem conditionalRatioMean_le_of_exp_llr_le [IsFiniteMeasure μ]
    (hμν : μ ≪ ν) {B : ℝ≥0} (hB : ∀ᵐ x ∂μ,
      ENNReal.ofReal (Real.exp (llr μ ν x)) ≤ (B : ℝ≥0∞)) (t : ℝ) :
    conditionalRatioMean μ ν t ≤ (B : ℝ≥0∞) := by
  by_cases hz : μ (closedTailEvent μ ν t) = 0
  · rw [conditionalRatioMean_of_null hμν hz]
    exact zero_le
  · rw [conditionalRatioMean_of_nonnull hμν hz, closedTailMoment_of_ac hμν]
    apply ENNReal.div_le_of_le_mul
    calc
      _ ≤ ∫⁻ _x in closedTailEvent μ ν t, (B : ℝ≥0∞) ∂μ :=
        lintegral_mono_ae (ae_restrict_of_ae hB)
      _ = _ := by simp

/-- A literal source-density bound excludes singular mass as a consequence. -/
theorem conditionalMoment_le_of_dominatedRatio_le [IsProbabilityMeasure μ]
    [IsFiniteMeasure ν] [SigmaFinite κ] (hμκ : μ ≪ κ) {B : ℝ≥0}
    (hB : ∀ᵐ x ∂μ, dominatedRatio μ ν κ x ≤ (B : ℝ≥0∞)) :
    conditionalMoment μ ν ≤ (B : ℝ≥0∞) := by
  have hfull : fullRatioMoment μ ν ≤ (B : ℝ≥0∞) := by
    rw [fullRatioMoment_eq_lintegral_dominatedRatio hμκ]
    calc
      _ ≤ ∫⁻ _x, (B : ℝ≥0∞) ∂μ := lintegral_mono_ae hB
      _ = _ := by simp
  have hμν : μ ≪ ν := ac_of_fullRatioMoment_lt_top (hfull.trans_lt ENNReal.coe_lt_top)
  have hexp : ∀ᵐ x ∂μ, ENNReal.ofReal (Real.exp (llr μ ν x)) ≤ (B : ℝ≥0∞) := by
    filter_upwards [exp_llr_ae_eq_dominatedRatio hμκ hμν, hB] with x hx hbx
    exact hx.trans_le hbx
  calc
    conditionalMoment μ ν ≤ cmObjective μ ν 1 := conditionalMoment_le 1 le_rfl
    _ = conditionalRatioMean μ ν (cmCutoff 1) := by
      simp only [cmObjective, ENNReal.ofReal_one, one_mul]
    _ ≤ (B : ℝ≥0∞) := conditionalRatioMean_le_of_exp_llr_le hμν hexp _

/-- Dominators may be chosen separately for each family member. -/
theorem uniform_conditionalMoment_of_uniform_dominatedRatio_bound
    (μ : Measure α) [IsProbabilityMeasure μ] (F : Set (Measure α))
    (hF : ∀ ν ∈ F, IsProbabilityMeasure ν) (κ : Measure α → Measure α)
    (hκ : ∀ ν ∈ F, SigmaFinite (κ ν)) (hμκ : ∀ ν ∈ F, μ ≪ κ ν)
    (hUB : ∃ B : ℝ≥0, ∀ ν ∈ F, ∀ᵐ x ∂μ, dominatedRatio μ ν (κ ν) x ≤ (B : ℝ≥0∞)) :
    ∃ M : ℝ≥0, ∀ ν ∈ F, conditionalMoment μ ν ≤ (M : ℝ≥0∞) := by
  obtain ⟨B, hB⟩ := hUB
  refine ⟨B, ?_⟩
  intro ν hν
  let : IsProbabilityMeasure ν := hF ν hν
  let : SigmaFinite (κ ν) := hκ ν hν
  exact conditionalMoment_le_of_dominatedRatio_le (hμκ ν hν) (hB ν hν)

/-- The source pointwise UB condition implies CM via its explicit AE consequence. -/
theorem uniform_conditionalMoment_of_uniform_pointwise_ratio_bound
    (μ : Measure α) [IsProbabilityMeasure μ] (F : Set (Measure α))
    (hF : ∀ ν ∈ F, IsProbabilityMeasure ν) (κ : Measure α → Measure α)
    (hκ : ∀ ν ∈ F, SigmaFinite (κ ν)) (hμκ : ∀ ν ∈ F, μ ≪ κ ν)
    (hUB : ∃ B : ℝ≥0, ∀ ν ∈ F, ∀ x, dominatedRatio μ ν (κ ν) x ≤ (B : ℝ≥0∞)) :
    ∃ M : ℝ≥0, ∀ ν ∈ F, conditionalMoment μ ν ≤ (M : ℝ≥0∞) := by
  apply uniform_conditionalMoment_of_uniform_dominatedRatio_bound μ F hF κ hκ hμκ
  obtain ⟨B, hB⟩ := hUB
  exact ⟨B, fun ν hν ↦ Filter.Eventually.of_forall (hB ν hν)⟩

/-- A supplied total ratio representative may differ from the canonical ratio
on null sets. Its pointwise bound transfers through the explicit AE identity. -/
theorem uniform_conditionalMoment_of_uniform_ratio_representative_bound
    (μ : Measure α) [IsProbabilityMeasure μ] (F : Set (Measure α))
    (hF : ∀ ν ∈ F, IsProbabilityMeasure ν) (κ : Measure α → Measure α)
    (hκ : ∀ ν ∈ F, SigmaFinite (κ ν)) (hμκ : ∀ ν ∈ F, μ ≪ κ ν)
    (r : Measure α → α → ℝ≥0∞)
    (hr : ∀ ν ∈ F, r ν =ᵐ[μ] dominatedRatio μ ν (κ ν))
    (hUB : ∃ B : ℝ≥0, ∀ ν ∈ F, ∀ x, r ν x ≤ (B : ℝ≥0∞)) :
    ∃ M : ℝ≥0, ∀ ν ∈ F, conditionalMoment μ ν ≤ (M : ℝ≥0∞) := by
  apply uniform_conditionalMoment_of_uniform_dominatedRatio_bound μ F hF κ hκ hμκ
  obtain ⟨B, hB⟩ := hUB
  refine ⟨B, ?_⟩
  intro ν hν
  filter_upwards [hr ν hν] with x hx
  rw [← hx]
  exact hB ν hν x

end Hellinger.Comparison
