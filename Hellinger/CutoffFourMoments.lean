/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.VariationBounds
public import Hellinger.Interpolation

/-! Cutoff-four corollaries for real log moments and interpolation. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Hellinger

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α}

theorem logMoment_upper_four [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {k : ℝ} (hk : 2 ≤ k) :
    logMoment μ ν k ≤ ENNReal.ofReal
      (4 * max (2 * (Real.log 4) ^ (k - 2)) ((k / Real.exp 1) ^ k)) *
        hellingerSq μ ν + tailLogMoment μ ν 4 k := by
  simpa only [variationUpperCoeff_four] using
    (logMoment_le_hellinger_add_tailLogMoment (μ := μ) (ν := ν) (c := 4) (by norm_num) hk)

theorem tailLogMoment_interpolation_four [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {k k' : ℝ} (hk : 0 < k) (hkk' : k ≤ k') :
    tailLogMoment μ ν 4 k ≤ 4 * hellingerSq μ ν ^ (1 - k / k') *
      tailLogMoment μ ν 4 k' ^ (k / k') := by
  simpa only [interpolationCoeff_four, ENNReal.ofReal_ofNat] using
    (tailLogMoment_interpolation (μ := μ) (ν := ν) (c := 4) (by norm_num) hk hkk')

theorem tailLogMoment_le_four_mul_self [IsFiniteMeasure μ] [IsFiniteMeasure ν] (k : ℝ) :
    tailLogMoment μ ν 4 k ≤ 4 * tailLogMoment μ ν 4 k := by
  simpa only [interpolationCoeff_four, ENNReal.ofReal_ofNat] using
    (tailLogMoment_le_interpolationCoeff_mul_self (μ := μ) (ν := ν) (c := 4) (by norm_num) k)

end Hellinger
