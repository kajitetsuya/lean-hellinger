/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.BernsteinScalar
public import Hellinger.HellingerBridge
public import Hellinger.TailIntegration

/-! Extended Bernstein bounds for every fixed real cutoff greater than one. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Hellinger

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α}
variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]

theorem powerTailDensityKernel_nonneg {c δ x : ℝ} (hx : 0 ≤ x) :
    0 ≤ powerTailDensityKernel c δ x := by
  unfold powerTailDensityKernel
  split_ifs
  · exact mul_nonneg hx (Real.exp_pos _).le
  · exact le_rfl

theorem tailPower_eq_lintegral_densityKernel (h : μ ≪ ν) (c δ : ℝ) :
    tailPower μ ν c δ =
      ∫⁻ x, ENNReal.ofReal (powerTailDensityKernel c δ ((μ.rnDeriv ν x).toReal)) ∂ν := by
  rw [tailPower_eq_lintegral_density h]
  apply lintegral_congr
  intro x
  by_cases ht : Real.log c < Real.log ((μ.rnDeriv ν x).toReal)
  · simp [powerTailDensityKernel, llr, ht]
  · simp [powerTailDensityKernel, llr, ht]

/-- Theorem 1's lower Bernstein bound, including singular measures and infinite tails. -/
theorem bernsteinLowerCoeff_mul_tailPower_le_bernsteinSq {c δ : ℝ}
    (hc : 1 < c) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ENNReal.ofReal (bernsteinLowerCoeff c δ) * tailPower μ ν c δ ≤
      bernsteinSq μ ν δ := by
  by_cases h : μ ≪ ν
  · rw [tailPower_eq_lintegral_densityKernel h, bernsteinSq_eq_lintegral_density h]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono
    intro x
    dsimp only
    rw [← ENNReal.ofReal_mul (bernsteinLowerCoeff_pos hc hδ).le]
    exact ENNReal.ofReal_le_ofReal
      (bernstein_density_lower hc hδ hδ1 ENNReal.toReal_nonneg)
  · simp [tailPower_of_not_ac h, bernsteinSq_of_not_ac h]

/-- Theorem 1's upper Bernstein bound, without any finiteness assumption on the discrepancy. -/
theorem bernsteinSq_le_hellinger_add_tailPower {c δ : ℝ}
    (hc : 1 < c) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    bernsteinSq μ ν δ ≤ ENNReal.ofReal (bernsteinUpperCoeff c δ) * hellingerSq μ ν +
      2 * tailPower μ ν c δ := by
  by_cases h : μ ≪ ν
  · rw [bernsteinSq_eq_lintegral_density h]
    have hg : Measurable (fun x ↦ ENNReal.ofReal
        ((Real.sqrt ((μ.rnDeriv ν x).toReal) - 1) ^ 2)) := by fun_prop
    calc
      _ ≤ ∫⁻ x, ENNReal.ofReal (bernsteinUpperCoeff c δ) *
            ENNReal.ofReal ((Real.sqrt ((μ.rnDeriv ν x).toReal) - 1) ^ 2) +
            (2 : ℝ≥0∞) * ENNReal.ofReal
              (powerTailDensityKernel c δ ((μ.rnDeriv ν x).toReal)) ∂ν := by
        apply lintegral_mono
        intro x
        have hp := ENNReal.ofReal_le_ofReal
          (bernstein_density_upper hc hδ hδ1 (x := (μ.rnDeriv ν x).toReal)
            ENNReal.toReal_nonneg)
        rwa [ENNReal.ofReal_add
          (mul_nonneg (bernsteinUpperCoeff_pos hc hδ).le (sq_nonneg _))
          (mul_nonneg (by norm_num) (powerTailDensityKernel_nonneg ENNReal.toReal_nonneg)),
          ENNReal.ofReal_mul (bernsteinUpperCoeff_pos hc hδ).le,
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat] at hp
      _ = ENNReal.ofReal (bernsteinUpperCoeff c δ) *
            (∫⁻ x, ENNReal.ofReal ((Real.sqrt ((μ.rnDeriv ν x).toReal) - 1) ^ 2) ∂ν) +
            2 * (∫⁻ x, ENNReal.ofReal
              (powerTailDensityKernel c δ ((μ.rnDeriv ν x).toReal)) ∂ν) := by
        calc
          _ = (∫⁻ x, ENNReal.ofReal (bernsteinUpperCoeff c δ) *
                ENNReal.ofReal ((Real.sqrt ((μ.rnDeriv ν x).toReal) - 1) ^ 2) ∂ν) +
              (∫⁻ x, (2 : ℝ≥0∞) * ENNReal.ofReal
                (powerTailDensityKernel c δ ((μ.rnDeriv ν x).toReal)) ∂ν) := by
            simpa only [Pi.mul_apply] using
              (lintegral_add_left (measurable_const.mul hg)
                (fun x ↦ (2 : ℝ≥0∞) * ENNReal.ofReal
                  (powerTailDensityKernel c δ ((μ.rnDeriv ν x).toReal))))
          _ = _ := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
              lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
      _ = _ := by
        rw [← hellingerSq_eq_lintegral_of_ac h, ← tailPower_eq_lintegral_densityKernel h]
  · simp [bernsteinSq_of_not_ac h, tailPower_of_not_ac h]

end Hellinger
