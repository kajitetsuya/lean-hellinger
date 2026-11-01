/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.MLE.WeakLawStatements
public import Hellinger.MLE.MixLog

/-! Measurability of the extended and truncated log tails of condition (W). -/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace Hellinger.MLE

variable {𝒳 : Type*} [MeasurableSpace 𝒳] {p₀ q : 𝒳 → ℝ≥0}

omit [MeasurableSpace 𝒳] in
theorem extTail_eq_ofReal_logRatio {x : 𝒳} (h1 : ¬ (0 < p₀ x ∧ q x = 0)) (h2 : 4 * q x < p₀ x) :
    extTail p₀ q x = ENNReal.ofReal (logRatio p₀ q x) := by
  simp only [extTail, h1, h2, ↓reduceIte, logRatio]

theorem measurable_extTail (hp₀ : Measurable p₀) (hq : Measurable q) :
    Measurable (extTail p₀ q) := by
  have hs : MeasurableSet {x | 0 < p₀ x ∧ q x = 0} :=
    (measurableSet_lt measurable_const hp₀).inter (measurableSet_eq_fun hq measurable_const)
  have ht : MeasurableSet {x | 4 * q x < p₀ x} := measurableSet_lt (hq.const_mul 4) hp₀
  exact Measurable.ite hs measurable_const
    (Measurable.ite ht (measurable_logRatio hp₀ hq).ennreal_ofReal measurable_const)

theorem measurable_truncTail (hp₀ : Measurable p₀) (hq : Measurable q) (L : ℝ≥0∞) :
    Measurable (truncTail p₀ q L) :=
  Measurable.ite (measurableSet_le (measurable_extTail hp₀ hq) measurable_const)
    (measurable_extTail hp₀ hq) measurable_const

end Hellinger.MLE
