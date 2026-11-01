/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.Comparison.Examples.NormalMoment
public import Hellinger.Comparison.Examples.NormalRare
public import Mathlib.Topology.Order.Compact

/-! Compact parameter control, with the zero-parameter null event handled
separately from the nonzero Gaussian tail quotient. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace Hellinger.Comparison.Examples.Normal

/-- A right limit and continuity away from zero give one bound on each bounded
positive parameter interval. No value for the function at zero is assumed. -/
theorem bounded_on_positive_interval_of_tendsto {f : ℝ → ℝ} {L : ℝ}
    (hf : ContinuousOn f (Ioi 0)) (hlim : Tendsto f (𝓝[>] 0) (𝓝 L)) (B : ℝ) :
    ∃ C : ℝ, ∀ s : ℝ, 0 < s → s ≤ B → f s ≤ C := by
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), f s < L + 1 :=
    hlim.eventually (eventually_lt_nhds (by linarith : L < L + 1))
  obtain ⟨ε, hε, hsmall⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  have hc : ContinuousOn f (Icc ε B) :=
    hf.mono (fun s hs ↦ lt_of_lt_of_le hε hs.1)
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hc
  refine ⟨max (L + 1) C, ?_⟩
  intro s hs hsB
  by_cases hse : s < ε
  · exact (hsmall ⟨hs, hse⟩).le.trans (le_max_left _ _)
  · exact (hC ⟨s, ⟨le_of_not_gt hse, hsB⟩, rfl⟩).trans (le_max_right _ _)

/-- Use the admissible optimizer a=1, whose native cutoff is 9/4. -/
theorem normal_conditionalMoment_le_formula {theta : ℝ} (htheta : theta ≠ 0) :
    conditionalMoment (normalLaw 0) (normalLaw theta) ≤
      ENNReal.ofReal (conditionalTailFormula (9 / 4) |theta|) := by
  calc
    _ ≤ cmObjective (normalLaw 0) (normalLaw theta) 1 := conditionalMoment_le 1 le_rfl
    _ = _ := by
      rw [cmObjective, cmCutoff_one,
        conditionalRatioMean_eq_conditionalTailFormula htheta (by norm_num : (0 : ℝ) < 9 / 4)]
      simp

/-- One finite constant controls the entire bounded parameter interval,
including the distinct null-event value at theta=0. -/
theorem bounded_normal_conditionalMoment (B : ℝ) :
    ∃ M : ℝ≥0, ∀ theta : ℝ, |theta| ≤ B →
      conditionalMoment (normalLaw 0) (normalLaw theta) ≤ (M : ℝ≥0∞) := by
  obtain ⟨C, hC⟩ := bounded_on_positive_interval_of_tendsto
    (continuousOn_conditionalTailFormula (9 / 4))
    (tendsto_conditionalTailFormula_zero (by norm_num : (1 : ℝ) < 9 / 4)) B
  refine ⟨Real.toNNReal C, ?_⟩
  intro theta hthetaB
  change conditionalMoment (normalLaw 0) (normalLaw theta) ≤ ENNReal.ofReal C
  by_cases htheta : theta = 0
  · subst theta
    rw [conditionalMoment_zero]
    exact bot_le
  · exact (normal_conditionalMoment_le_formula htheta).trans
      (ENNReal.ofReal_le_ofReal (hC |theta| (abs_pos.mpr htheta) hthetaB))

def normalFamily (S : Set ℝ) : Set (Measure ℝ) := normalLaw '' S

theorem normalFamily_probability (S : Set ℝ) :
    ∀ ν ∈ normalFamily S, IsProbabilityMeasure ν := by
  rintro ν ⟨theta, _htheta, rfl⟩
  infer_instance

/-- The original bounded-family conclusion, with a constant chosen before
every member and without a closedness, nonemptiness or exclusion-of-zero assumption. -/
theorem uniform_conditionalMoment_normalFamily {S : Set ℝ} (hS : Bornology.IsBounded S) :
    ∃ M : ℝ≥0, ∀ ν ∈ normalFamily S,
      conditionalMoment (normalLaw 0) ν ≤ (M : ℝ≥0∞) := by
  obtain ⟨B, hB⟩ := hS.exists_norm_le
  obtain ⟨M, hM⟩ := bounded_normal_conditionalMoment B
  refine ⟨M, ?_⟩
  rintro ν ⟨theta, htheta, rfl⟩
  exact hM theta (by simpa only [Real.norm_eq_abs] using hB theta htheta)

/-- Every bounded parameter set containing a nonzero location witnesses
uniform CM together with failure of the paper's literal pointwise UB. -/
theorem normal_bounded_family_cm_not_ub {S : Set ℝ} (hS : Bornology.IsBounded S)
    {theta : ℝ} (htheta : theta ∈ S) (hne : theta ≠ 0) :
    (∀ ν ∈ normalFamily S, IsProbabilityMeasure ν) ∧
    (∃ M : ℝ≥0, ∀ ν ∈ normalFamily S,
      conditionalMoment (normalLaw 0) ν ≤ (M : ℝ≥0∞)) ∧
    ¬ ∃ B : ℝ≥0, ∀ eta ∈ S, ∀ x : ℝ, ratio eta x ≤ (B : ℝ) := by
  refine ⟨normalFamily_probability S, uniform_conditionalMoment_normalFamily hS, ?_⟩
  rintro ⟨B, hB⟩
  exact not_pointwise_bounded_ratio hne ⟨B, hB theta htheta⟩

end Hellinger.Comparison.Examples.Normal
