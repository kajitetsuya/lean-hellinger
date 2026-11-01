/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.Comparison.Definitions
public import Hellinger.Uniform
public import Hellinger.HellingerBasic

/-! Full-moment finiteness and the fixed-pair reverse CM implication. -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Hellinger.Comparison

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α}

theorem closedTailMoment_le_fullRatioMoment (t : ℝ) :
    closedTailMoment μ ν t ≤ fullRatioMoment μ ν := by
  by_cases hμν : μ ≪ ν
  · rw [closedTailMoment_of_ac hμν, fullRatioMoment_of_ac hμν]
    exact setLIntegral_le_lintegral _ _
  · simp [closedTailMoment_of_not_ac hμν, fullRatioMoment_of_not_ac hμν]

theorem tailPower_one_le_fullRatioMoment (q : ℝ) :
    tailPower μ ν q 1 ≤ fullRatioMoment μ ν := by
  by_cases hμν : μ ≪ ν
  · rw [tailPower_of_ac hμν, fullRatioMoment_of_ac hμν]
    simpa only [one_mul] using
      (setLIntegral_le_lintegral (tailEvent μ ν q)
        (fun x ↦ ENNReal.ofReal (Real.exp (llr μ ν x))))
  · simp [tailPower_of_not_ac hμν, fullRatioMoment_of_not_ac hμν]

/-- A finite full moment makes the native CM infimum finite, without uniformizing it. -/
theorem conditionalMoment_lt_top_of_fullRatioMoment_lt_top
    (hfull : fullRatioMoment μ ν < ∞) : conditionalMoment μ ν < ∞ := by
  have hμν := ac_of_fullRatioMoment_lt_top hfull
  have htail : closedTailMoment μ ν (cmCutoff 1) < ∞ :=
    (closedTailMoment_le_fullRatioMoment _).trans_lt hfull
  have hc : conditionalRatioMean μ ν (cmCutoff 1) < ∞ := by
    rw [conditionalRatioMean_of_ac hμν]
    split_ifs with hzero
    · exact ENNReal.zero_lt_top
    · exact ENNReal.div_lt_top htail.ne hzero
  have h := conditionalMoment_le (μ := μ) (ν := ν) 1 le_rfl
  have h' : conditionalMoment μ ν ≤ conditionalRatioMean μ ν (cmCutoff 1) := by
    simpa only [cmObjective, ENNReal.ofReal_one, one_mul] using h
  exact h'.trans_lt hc

variable [IsProbabilityMeasure μ]

/-- The bounded lower band shows that the full first moment is finite iff its tail is. -/
theorem fullRatioMoment_le_tailPower_add_cutoff {q : ℝ} (hq : 1 < q) :
    fullRatioMoment μ ν ≤ tailPower μ ν q 1 + ENNReal.ofReal q := by
  classical
  by_cases hμν : μ ≪ ν
  · rw [fullRatioMoment_of_ac hμν, tailPower_of_ac hμν]
    simp only [one_mul]
    let f : α → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (Real.exp (llr μ ν x))
    have hs := measurableSet_tailEvent μ ν q
    change (∫⁻ x, f x ∂μ) ≤ (∫⁻ x in tailEvent μ ν q, f x ∂μ) + _
    calc
      _ = (∫⁻ x in tailEvent μ ν q, f x ∂μ) +
          (∫⁻ x in (tailEvent μ ν q)ᶜ, f x ∂μ) := (lintegral_add_compl f hs).symm
      _ ≤ (∫⁻ x in tailEvent μ ν q, f x ∂μ) +
          (∫⁻ _x in (tailEvent μ ν q)ᶜ, ENNReal.ofReal q ∂μ) := by
        apply add_le_add le_rfl
        apply setLIntegral_mono measurable_const
        intro x hx
        have hl : llr μ ν x ≤ Real.log q := le_of_not_gt hx
        apply ENNReal.ofReal_le_ofReal
        exact (Real.exp_le_exp.mpr hl).trans_eq
          (Real.exp_log (lt_trans (by norm_num) hq))
      _ ≤ (∫⁻ x in tailEvent μ ν q, f x ∂μ) +
          (∫⁻ _x, ENNReal.ofReal q ∂μ) :=
        add_le_add le_rfl (setLIntegral_le_lintegral _ _)
      _ = _ := by simp
  · simp [fullRatioMoment_of_not_ac hμν, tailPower_of_not_ac hμν]

theorem fullRatioMoment_lt_top_iff_tailPower_one_lt_top {q : ℝ} (hq : 1 < q) :
    fullRatioMoment μ ν < ∞ ↔ tailPower μ ν q 1 < ∞ := by
  constructor
  · intro h
    exact (tailPower_one_le_fullRatioMoment q).trans_lt h
  · intro h
    exact (fullRatioMoment_le_tailPower_add_cutoff hq).trans_lt
      (ENNReal.add_lt_top.mpr ⟨h, ENNReal.ofReal_lt_top⟩)

/-- Fixed-pair NC at exponent one implies CM finiteness; this is not a uniform-CM bound. -/
theorem conditionalMoment_lt_top_of_tailPower_one_lt_top {q : ℝ} (hq : 1 < q)
    (h : tailPower μ ν q 1 < ∞) : conditionalMoment μ ν < ∞ :=
  conditionalMoment_lt_top_of_fullRatioMoment_lt_top
    ((fullRatioMoment_lt_top_iff_tailPower_one_lt_top hq).mpr h)

/-- A single tail multiplier supplies a single finite full-moment bound for the family. -/
theorem uniform_fullRatioMoment_of_uniform_tailPower_one
    (F : Set (Measure α)) (hF : ∀ ν ∈ F, IsProbabilityMeasure ν)
    {q : ℝ} (hq : 1 < q)
    (hNC : UniformHellingerBound μ F (fun ν ↦ tailPower μ ν q 1)) :
    ∃ C : ℝ≥0, ∀ ν ∈ F, fullRatioMoment μ ν ≤ (C : ℝ≥0∞) := by
  obtain ⟨M, hM⟩ := hNC
  refine ⟨M * 2 + Real.toNNReal q, ?_⟩
  intro ν hν
  let : IsProbabilityMeasure ν := hF ν hν
  calc
    fullRatioMoment μ ν ≤ tailPower μ ν q 1 + ENNReal.ofReal q :=
      fullRatioMoment_le_tailPower_add_cutoff hq
    _ ≤ (M : ℝ≥0∞) * hellingerSq μ ν + ENNReal.ofReal q :=
      add_le_add (hM ν hν) le_rfl
    _ ≤ (M : ℝ≥0∞) * 2 + ENNReal.ofReal q :=
      add_le_add (mul_le_mul' le_rfl (hellingerSq_le_two μ ν)) le_rfl
    _ = _ := by
      simp only [ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_ofNat, ENNReal.ofReal]

end Hellinger.Comparison
