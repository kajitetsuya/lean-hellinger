/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.Constants
public import Hellinger.HellingerBridge
public import Hellinger.TailIntegration

/-! Tail-event mass controlled by the full squared Hellinger distance. -/

public section

open MeasureTheory Set
open scoped ENNReal

namespace Hellinger

/-- Forward-density geometry on the large-likelihood tail. -/
theorem tail_density_mass_le_hellinger_kernel {c r : ℝ} (hc : 1 < c) (hcr : c ≤ r) :
    r ≤ tailMassCoeff c * (Real.sqrt r - 1) ^ 2 := by
  have hc0 : 0 < c := lt_trans (by norm_num) hc
  have hr0 : 0 ≤ r := le_trans hc0.le hcr
  have hgap : cutoffGap c = 1 - (Real.sqrt c)⁻¹ := by
    unfold cutoffGap
    rw [Real.rpow_neg hc0.le, ← Real.sqrt_eq_rpow]
  have hdiv : 1 ≤ Real.sqrt r / Real.sqrt c :=
    (one_le_div (Real.sqrt_pos.mpr hc0)).mpr (Real.sqrt_le_sqrt hcr)
  rw [div_eq_mul_inv] at hdiv
  have hsep : cutoffGap c * Real.sqrt r ≤ Real.sqrt r - 1 := by
    rw [hgap]
    nlinarith
  have hsq := pow_le_pow_left₀
    (mul_nonneg (cutoffGap_pos hc).le (Real.sqrt_nonneg r)) hsep 2
  rw [mul_pow, Real.sq_sqrt hr0] at hsq
  have hid : tailMassCoeff c * cutoffGap c ^ 2 = 1 := by
    unfold tailMassCoeff
    exact inv_mul_cancel₀ (sq_pos_of_pos (cutoffGap_pos hc)).ne'
  have h := mul_le_mul_of_nonneg_left hsq (tailMassCoeff_pos hc).le
  rwa [← mul_assoc, hid, one_mul] at h

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α}
variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- In the AC branch, the strict tail event has mass at most `J(c) H²`.
The Hellinger integral includes all reference-measure mass, including zero density. -/
theorem tailEvent_mass_le_tailMassCoeff_mul_hellingerSq (hμν : μ ≪ ν)
    {c : ℝ} (hc : 1 < c) :
    μ (tailEvent μ ν c) ≤ ENNReal.ofReal (tailMassCoeff c) * hellingerSq μ ν := by
  classical
  calc
    μ (tailEvent μ ν c) = ∫⁻ x in tailEvent μ ν c, ENNReal.ofReal (1 : ℝ) ∂μ := by
      simp
    _ = ∫⁻ x, (tailEvent μ ν c).indicator
        (fun y ↦ ENNReal.ofReal ((μ.rnDeriv ν y).toReal * (1 : ℝ))) x ∂ν :=
      setLIntegral_ofReal_eq_lintegral_density hμν measurable_const
        (measurableSet_tailEvent μ ν c)
    _ ≤ ∫⁻ x, ENNReal.ofReal (tailMassCoeff c) *
        ENNReal.ofReal ((Real.sqrt ((μ.rnDeriv ν x).toReal) - 1) ^ 2) ∂ν := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [Set.indicator_apply]
      split_ifs with hx
      · have hxlog : Real.log c < Real.log ((μ.rnDeriv ν x).toReal) := hx
        have hr1 : 1 < (μ.rnDeriv ν x).toReal :=
          (Real.log_pos_iff ENNReal.toReal_nonneg).mp ((Real.log_pos hc).trans hxlog)
        have hcr := (Real.log_lt_log_iff (lt_trans (by norm_num) hc)
          (lt_trans (by norm_num) hr1)).mp hxlog
        rw [← ENNReal.ofReal_mul (tailMassCoeff_pos hc).le]
        simp only [mul_one]
        exact ENNReal.ofReal_le_ofReal (tail_density_mass_le_hellinger_kernel hc hcr.le)
      · exact zero_le
    _ = ENNReal.ofReal (tailMassCoeff c) * hellingerSq μ ν := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        ← hellingerSq_eq_lintegral_of_ac hμν]

end Hellinger
