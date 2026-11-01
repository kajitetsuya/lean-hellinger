/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.HellingerBridge
public import Hellinger.Scalar

/-! Measure-level Hellinger and KL comparisons. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Hellinger

variable {α : Type*} [MeasurableSpace α]

/-- The full lower Hellinger bound, including failure of absolute continuity.
It holds for finite measures, hence in particular for the required probability measures. -/
theorem hellingerSq_le_kl (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    hellingerSq μ ν ≤ kl μ ν := by
  by_cases hμν : μ ≪ ν
  · rw [hellingerSq_eq_lintegral_of_ac hμν]
    unfold kl
    rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac hμν]
    apply lintegral_mono
    intro x
    exact ENNReal.ofReal_le_ofReal (sqrt_sub_one_sq_le_klFun ENNReal.toReal_nonneg)
  · simp [kl, InformationTheory.klDiv_of_not_ac hμν]

end Hellinger
