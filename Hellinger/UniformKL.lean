/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.Uniform
public import Hellinger.KLBounds

/-! The Kullback–Leibler divergence uniform-family equivalence for each fixed cutoff greater than
one. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace Hellinger

variable {α : Type*} [MeasurableSpace α]

/-- Fixed-cutoff equivalence with a single multiplier for the entire family.
No common dominating measure for the family or nonempty-family premise is used. -/
theorem uniform_kl_iff_tailLogMoment (μ : Measure α) [IsProbabilityMeasure μ]
    (F : Set (Measure α)) (hF : ∀ ν ∈ F, IsProbabilityMeasure ν)
    {c : ℝ} (hc : 1 < c) :
    UniformHellingerBound μ F (fun ν ↦ kl μ ν) ↔
      UniformHellingerBound μ F (fun ν ↦ tailLogMoment μ ν c 1) := by
  let a : ℝ≥0 := Real.toNNReal (klTailLowerCoeff c)
  let b : ℝ≥0 := Real.toNNReal (klUpperCoeff c)
  have ha : a ≠ 0 := (Real.toNNReal_pos.mpr (klTailLowerCoeff_pos hc)).ne'
  apply uniformHellingerBound_iff_of_comparisons μ F _ _ a b ha
  · intro ν hν
    let : IsProbabilityMeasure ν := hF ν hν
    simpa only [a, ENNReal.ofReal] using
      (klTailLowerCoeff_mul_tailLogMoment_le_kl (μ := μ) (ν := ν) hc)
  · intro ν hν
    let : IsProbabilityMeasure ν := hF ν hν
    simpa only [b, ENNReal.ofReal] using
      (kl_le_hellinger_add_tailLogMoment (μ := μ) (ν := ν) hc)

end Hellinger
