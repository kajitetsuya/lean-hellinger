/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.VariationScalar
public import Hellinger.HellingerBridge
public import Hellinger.TailIntegration

/-! Theorem 2 Kullback–Leibler variation bounds for arbitrary finite measures, including infinite
moments. -/
@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Hellinger

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α}
variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- The exact density representation of the real-order strict log tail. -/
theorem tailLogMoment_eq_lintegral_densityKernel (h : μ ≪ ν) (c k : ℝ) :
    tailLogMoment μ ν c k =
      ∫⁻ x, ENNReal.ofReal (logMomentTailDensityKernel c k ((μ.rnDeriv ν x).toReal)) ∂ν := by
  rw [tailLogMoment_eq_lintegral_density h]
  apply lintegral_congr
  intro x
  by_cases ht : Real.log c < Real.log ((μ.rnDeriv ν x).toReal)
  · simp [logMomentTailDensityKernel, llr, ht]
  · simp [logMomentTailDensityKernel, llr, ht]

/-- Theorem 2's lower moment bound, without an absolute-continuity or finite-moment premise. -/
theorem tailLogMoment_le_logMoment {c : ℝ} (hc : 1 < c) (k : ℝ) :
    tailLogMoment μ ν c k ≤ logMoment μ ν k := by
  by_cases h : μ ≪ ν
  · rw [tailLogMoment_eq_lintegral_densityKernel h, logMoment_eq_lintegral_density h]
    apply lintegral_mono
    intro x
    simpa only [llr] using ENNReal.ofReal_le_ofReal
      (variation_density_lower hc k (r := (μ.rnDeriv ν x).toReal) ENNReal.toReal_nonneg)
  · simp [tailLogMoment_of_not_ac h, logMoment_of_not_ac h]

/-- Theorem 2's exact upper Kullback–Leibler variation bound for every real exponent at least
two. -/
theorem logMoment_le_hellinger_add_tailLogMoment {c k : ℝ} (hc : 1 < c) (hk : 2 ≤ k) :
    logMoment μ ν k ≤ ENNReal.ofReal (variationUpperCoeff c k) * hellingerSq μ ν +
      tailLogMoment μ ν c k := by
  have hk0 : 0 < k := lt_of_lt_of_le (by norm_num) hk
  by_cases h : μ ≪ ν
  · rw [logMoment_eq_lintegral_density h]
    have hg : Measurable (fun x ↦ ENNReal.ofReal
        ((Real.sqrt ((μ.rnDeriv ν x).toReal) - 1) ^ 2)) := by fun_prop
    calc
      _ ≤ ∫⁻ x, ENNReal.ofReal (variationUpperCoeff c k) *
            ENNReal.ofReal ((Real.sqrt ((μ.rnDeriv ν x).toReal) - 1) ^ 2) +
            ENNReal.ofReal (logMomentTailDensityKernel c k ((μ.rnDeriv ν x).toReal)) ∂ν := by
        apply lintegral_mono
        intro x
        have hp := ENNReal.ofReal_le_ofReal
          (variation_density_upper hc hk (r := (μ.rnDeriv ν x).toReal) ENNReal.toReal_nonneg)
        rw [ENNReal.ofReal_add
          (mul_nonneg (variationUpperCoeff_pos hc hk0).le (sq_nonneg _))
          (logMomentTailDensityKernel_nonneg hc ENNReal.toReal_nonneg),
          ENNReal.ofReal_mul (variationUpperCoeff_pos hc hk0).le] at hp
        simpa only [llr] using hp
      _ = ENNReal.ofReal (variationUpperCoeff c k) *
            (∫⁻ x, ENNReal.ofReal ((Real.sqrt ((μ.rnDeriv ν x).toReal) - 1) ^ 2) ∂ν) +
            (∫⁻ x, ENNReal.ofReal (logMomentTailDensityKernel c k ((μ.rnDeriv ν x).toReal)) ∂ν) := by
        calc
          _ = (∫⁻ x, ENNReal.ofReal (variationUpperCoeff c k) *
                ENNReal.ofReal ((Real.sqrt ((μ.rnDeriv ν x).toReal) - 1) ^ 2) ∂ν) +
              (∫⁻ x, ENNReal.ofReal (logMomentTailDensityKernel c k ((μ.rnDeriv ν x).toReal)) ∂ν) := by
            simpa only [Pi.mul_apply] using
              (lintegral_add_left (measurable_const.mul hg)
                (fun x ↦ ENNReal.ofReal (logMomentTailDensityKernel c k ((μ.rnDeriv ν x).toReal))))
          _ = _ := by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ = _ := by
        rw [← hellingerSq_eq_lintegral_of_ac h, ← tailLogMoment_eq_lintegral_densityKernel h]
  · simp [logMoment_of_not_ac h, tailLogMoment_of_not_ac h]

end Hellinger
