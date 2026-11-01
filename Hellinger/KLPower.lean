/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.KLBounds

/-! The KL side bound obtained from a positive power tail. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Hellinger

variable {α : Type*} [MeasurableSpace α]

/-- A logarithmic tail is bounded by any positive exponential scale, including infinity. -/
theorem tailLogMoment_one_le_inv_mul_tailPower (μ ν : Measure α) (c : ℝ) {δ : ℝ}
    (hδ : 0 < δ) :
    tailLogMoment μ ν c 1 ≤ ENNReal.ofReal δ⁻¹ * tailPower μ ν c δ := by
  classical
  by_cases h : μ ≪ ν
  · rw [tailLogMoment_of_ac h, tailPower_of_ac h]
    calc
      (∫⁻ x in tailEvent μ ν c, ENNReal.ofReal (llr μ ν x ^ (1 : ℝ)) ∂μ) ≤
          ∫⁻ x in tailEvent μ ν c,
            ENNReal.ofReal δ⁻¹ * ENNReal.ofReal (Real.exp (δ * llr μ ν x)) ∂μ := by
        apply lintegral_mono
        intro x
        dsimp only
        rw [Real.rpow_one, ← ENNReal.ofReal_mul (inv_pos.mpr hδ).le]
        apply ENNReal.ofReal_le_ofReal
        calc
          llr μ ν x ≤ Real.exp (δ * llr μ ν x) / δ := by
            apply (le_div_iff₀ hδ).mpr
            nlinarith [Real.add_one_le_exp (δ * llr μ ν x)]
          _ = δ⁻¹ * Real.exp (δ * llr μ ν x) := by
            rw [div_eq_mul_inv, mul_comm]
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  · rw [tailLogMoment_of_not_ac h, tailPower_of_not_ac h]
    rw [ENNReal.mul_top (ENNReal.ofReal_pos.mpr (inv_pos.mpr hδ)).ne']

/-- The generalized Theorem 1 KL upper bound; no finite-KL assumption is used. -/
theorem kl_le_hellinger_add_tailPower (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {c δ : ℝ} (hc : 1 < c) (hδ : 0 < δ) :
    kl μ ν ≤ ENNReal.ofReal (klUpperCoeff c) * hellingerSq μ ν +
      ENNReal.ofReal δ⁻¹ * tailPower μ ν c δ :=
  (kl_le_hellinger_add_tailLogMoment hc).trans
    (add_le_add_right (tailLogMoment_one_le_inv_mul_tailPower μ ν c hδ) _)

end Hellinger
