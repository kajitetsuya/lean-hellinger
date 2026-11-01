/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.KL
public import Hellinger.KLDensityScalar
public import Hellinger.TailIntegration

/-! Two-sided cutoff bounds for the extended KL divergence. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Hellinger

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α}
variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]

theorem tailLogMoment_one_eq_densityKernel (h : μ ≪ ν) (c : ℝ) :
    tailLogMoment μ ν c 1 =
      ∫⁻ x, ENNReal.ofReal (logTailDensityKernel c ((μ.rnDeriv ν x).toReal)) ∂ν := by
  rw [tailLogMoment_eq_lintegral_density h]
  apply lintegral_congr
  intro x
  by_cases ht : Real.log c < Real.log ((μ.rnDeriv ν x).toReal)
  · simp [logTailDensityKernel, llr, ht]
  · simp [logTailDensityKernel, llr, ht]

/-- The cutoff log tail is controlled by KL without any finite-KL assumption. -/
theorem klTailLowerCoeff_mul_tailLogMoment_le_kl {c : ℝ} (hc : 1 < c) :
    ENNReal.ofReal (klTailLowerCoeff c) * tailLogMoment μ ν c 1 ≤ kl μ ν := by
  by_cases h : μ ≪ ν
  · rw [tailLogMoment_one_eq_densityKernel h]
    unfold kl
    rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac h]
    calc
      ENNReal.ofReal (klTailLowerCoeff c) *
          (∫⁻ x, ENNReal.ofReal (logTailDensityKernel c ((μ.rnDeriv ν x).toReal)) ∂ν)
          = ∫⁻ x, ENNReal.ofReal (klTailLowerCoeff c) *
              ENNReal.ofReal (logTailDensityKernel c ((μ.rnDeriv ν x).toReal)) ∂ν :=
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ x, ENNReal.ofReal (InformationTheory.klFun ((μ.rnDeriv ν x).toReal)) ∂ν := by
        apply lintegral_mono
        intro x
        dsimp only
        rw [← ENNReal.ofReal_mul (klTailLowerCoeff_pos hc).le]
        exact ENNReal.ofReal_le_ofReal
          (klTailLowerCoeff_mul_logTail_le_klFun hc ENNReal.toReal_nonneg)
  · simp [kl, InformationTheory.klDiv_of_not_ac h]

/-- KL is bounded by squared Hellinger distance and the strictly truncated log tail. -/
theorem kl_le_hellinger_add_tailLogMoment {c : ℝ} (hc : 1 < c) :
    kl μ ν ≤ ENNReal.ofReal (klUpperCoeff c) * hellingerSq μ ν +
      tailLogMoment μ ν c 1 := by
  by_cases h : μ ≪ ν
  · unfold kl
    rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac h]
    have hg : Measurable (fun x ↦ ENNReal.ofReal
        ((Real.sqrt ((μ.rnDeriv ν x).toReal) - 1) ^ 2)) := by fun_prop
    calc
      (∫⁻ x, ENNReal.ofReal (InformationTheory.klFun ((μ.rnDeriv ν x).toReal)) ∂ν)
          ≤ ∫⁻ x, ENNReal.ofReal (klUpperCoeff c) *
              ENNReal.ofReal ((Real.sqrt ((μ.rnDeriv ν x).toReal) - 1) ^ 2) +
              ENNReal.ofReal (logTailDensityKernel c ((μ.rnDeriv ν x).toReal)) ∂ν := by
        apply lintegral_mono
        intro x
        have hp := ENNReal.ofReal_le_ofReal
          (klFun_le_hellinger_add_logTail hc (x := (μ.rnDeriv ν x).toReal)
            ENNReal.toReal_nonneg)
        rwa [ENNReal.ofReal_add
          (mul_nonneg (klUpperCoeff_pos c).le (sq_nonneg _))
          (logTailDensityKernel_nonneg hc ENNReal.toReal_nonneg),
          ENNReal.ofReal_mul (klUpperCoeff_pos c).le] at hp
      _ = ENNReal.ofReal (klUpperCoeff c) *
            (∫⁻ x, ENNReal.ofReal ((Real.sqrt ((μ.rnDeriv ν x).toReal) - 1) ^ 2) ∂ν) +
            (∫⁻ x, ENNReal.ofReal (logTailDensityKernel c ((μ.rnDeriv ν x).toReal)) ∂ν) := by
        calc
          _ = (∫⁻ x, ENNReal.ofReal (klUpperCoeff c) *
                ENNReal.ofReal ((Real.sqrt ((μ.rnDeriv ν x).toReal) - 1) ^ 2) ∂ν) +
                (∫⁻ x, ENNReal.ofReal
                  (logTailDensityKernel c ((μ.rnDeriv ν x).toReal)) ∂ν) := by
            simpa only [Pi.mul_apply] using
              (lintegral_add_left (measurable_const.mul hg)
                (fun x ↦ ENNReal.ofReal (logTailDensityKernel c ((μ.rnDeriv ν x).toReal))))
          _ = _ := by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ = ENNReal.ofReal (klUpperCoeff c) * hellingerSq μ ν + tailLogMoment μ ν c 1 := by
        rw [← hellingerSq_eq_lintegral_of_ac h, ← tailLogMoment_one_eq_densityKernel h]
  · simp [kl, InformationTheory.klDiv_of_not_ac h, tailLogMoment_of_not_ac h]

end Hellinger
