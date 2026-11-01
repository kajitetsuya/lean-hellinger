/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.KLPower
public import Hellinger.BernsteinBounds

/-! Cutoff-four corollaries of the general fixed-cutoff bounds. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Hellinger

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α}
variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]

theorem bernstein_lower_four {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ENNReal.ofReal ((1 - (4 : ℝ) ^ (-δ)) ^ 2) * tailPower μ ν 4 δ ≤
      bernsteinSq μ ν δ := by
  exact bernsteinLowerCoeff_mul_tailPower_le_bernsteinSq (by norm_num) hδ hδ1

theorem bernstein_upper_four {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    bernsteinSq μ ν δ ≤ ENNReal.ofReal (18 * δ) * hellingerSq μ ν +
      2 * tailPower μ ν 4 δ := by
  simpa only [bernsteinUpperCoeff_four] using
    (bernsteinSq_le_hellinger_add_tailPower (μ := μ) (ν := ν) (c := 4)
      (by norm_num) hδ hδ1)

theorem kl_upper_tailPower_four {δ : ℝ} (hδ : 0 < δ) :
    kl μ ν ≤ 3 * hellingerSq μ ν + ENNReal.ofReal δ⁻¹ * tailPower μ ν 4 δ := by
  simpa only [klUpperCoeff_four, ENNReal.ofReal_ofNat] using
    (kl_le_hellinger_add_tailPower μ ν (c := 4) (by norm_num) hδ)

theorem kl_lower_tailLogMoment_four :
    ENNReal.ofReal (1 / 3 : ℝ) * tailLogMoment μ ν 4 1 ≤ kl μ ν := by
  simpa only [klTailLowerCoeff_four] using
    (klTailLowerCoeff_mul_tailLogMoment_le_kl (μ := μ) (ν := ν) (c := 4) (by norm_num))

theorem kl_upper_tailLogMoment_four :
    kl μ ν ≤ 3 * hellingerSq μ ν + tailLogMoment μ ν 4 1 := by
  simpa only [klUpperCoeff_four, ENNReal.ofReal_ofNat] using
    (kl_le_hellinger_add_tailLogMoment (μ := μ) (ν := ν) (c := 4) (by norm_num))

end Hellinger
