/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.Definitions
public import Hellinger.GammaScalar

/-! The Gamma comparison for the extended nonnegative Kullback–Leibler variations. -/

public section

open MeasureTheory
open scoped ENNReal

namespace Hellinger

/-- The exact moment multiplier is positive for every positive scale and real `k ≥ 2`. -/
theorem gammaMomentCoeff_pos {δ k : ℝ} (hδ : 0 < δ) (hk : 2 ≤ k) :
    0 < (Real.Gamma (k + 1) / 2) * δ ^ (-k) := by
  exact mul_pos (div_pos (Real.Gamma_pos_of_pos (by linarith)) (by norm_num))
    (Real.rpow_pos_of_pos hδ _)

/-- The scalar Gamma comparison with the exact Bernstein factor `1/2`. -/
theorem abs_rpow_le_gamma_bernsteinKernel {δ k : ℝ} (hδ : 0 < δ) (hk : 2 ≤ k)
    (l : ℝ) :
    |l| ^ k ≤ ((Real.Gamma (k + 1) / 2) * δ ^ (-k)) * bernsteinKernel δ l := by
  calc
    |l| ^ k = δ ^ (-k) * |δ * l| ^ k := by
      rw [abs_mul, abs_of_pos hδ, Real.mul_rpow hδ.le (abs_nonneg l)]
      rw [← mul_assoc, ← Real.rpow_add hδ]
      simp
    _ ≤ δ ^ (-k) *
        (Real.Gamma (k + 1) * (Real.exp |δ * l| - 1 - |δ * l|)) :=
      mul_le_mul_of_nonneg_left (rpow_le_Gamma_mul_exp_remainder hk (abs_nonneg _))
        (Real.rpow_pos_of_pos hδ _).le
    _ = _ := by unfold bernsteinKernel; ring

variable {α : Type*} [MeasurableSpace α]

/-- The full Gamma moment bound, including infinite moments and failure of absolute continuity.
No finite Kullback–Leibler divergence, finite-moment or finite-measure assumption is needed.
The positive-scale domain is stronger than the paper's `0 < δ ≤ 1` domain for this clause. -/
theorem logMoment_le_gamma_bernsteinSq (μ ν : Measure α) {δ k : ℝ}
    (hδ : 0 < δ) (hk : 2 ≤ k) :
    logMoment μ ν k ≤
      ENNReal.ofReal ((Real.Gamma (k + 1) / 2) * δ ^ (-k)) * bernsteinSq μ ν δ := by
  classical
  have hcpos := gammaMomentCoeff_pos hδ hk
  by_cases hμν : μ ≪ ν
  · rw [logMoment_of_ac hμν, bernsteinSq_of_ac hμν]
    calc
      (∫⁻ x, ENNReal.ofReal (|llr μ ν x| ^ k) ∂μ) ≤
          ∫⁻ x, ENNReal.ofReal ((Real.Gamma (k + 1) / 2) * δ ^ (-k)) *
            ENNReal.ofReal (bernsteinKernel δ (llr μ ν x)) ∂μ := by
        apply lintegral_mono
        intro x
        dsimp only
        rw [← ENNReal.ofReal_mul hcpos.le]
        exact ENNReal.ofReal_le_ofReal (abs_rpow_le_gamma_bernsteinKernel hδ hk _)
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  · rw [logMoment_of_not_ac hμν, bernsteinSq_of_not_ac hμν]
    have hcne : ENNReal.ofReal ((Real.Gamma (k + 1) / 2) * δ ^ (-k)) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr hcpos).ne'
    rw [ENNReal.mul_top hcne]

end Hellinger
