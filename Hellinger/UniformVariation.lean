/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.Uniform
public import Hellinger.VariationBounds

/-! Uniform real-order Kullback–Leibler variation control for a single fixed cutoff and exponent. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace Hellinger

variable {α : Type*} [MeasurableSpace α]

theorem uniform_logMoment_iff_tailLogMoment (μ : Measure α) [IsProbabilityMeasure μ]
    (F : Set (Measure α)) (hF : ∀ ν ∈ F, IsProbabilityMeasure ν)
    {c k : ℝ} (hc : 1 < c) (hk : 2 ≤ k) :
    UniformHellingerBound μ F (fun ν ↦ logMoment μ ν k) ↔
      UniformHellingerBound μ F (fun ν ↦ tailLogMoment μ ν c k) := by
  let b : ℝ≥0 := Real.toNNReal (variationUpperCoeff c k)
  apply uniformHellingerBound_iff_of_comparisons μ F _ _ 1 b one_ne_zero
  · intro ν hν
    let : IsProbabilityMeasure ν := hF ν hν
    simpa using (tailLogMoment_le_logMoment (μ := μ) (ν := ν) hc k)
  · intro ν hν
    let : IsProbabilityMeasure ν := hF ν hν
    simpa only [b, ENNReal.ofReal] using
      (logMoment_le_hellinger_add_tailLogMoment (μ := μ) (ν := ν) hc hk)

end Hellinger
