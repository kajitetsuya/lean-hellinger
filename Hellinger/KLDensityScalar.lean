/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.KLScalar
public import Hellinger.HellingerBridge
public import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Forward-density Kullback–Leibler kernels for nonnegative integration under the reference
measure. -/

@[expose] public section

namespace Hellinger

/-- The likelihood-weighted log tail, with the power formed on its positive event. -/
noncomputable def logTailDensityKernel (c x : ℝ) : ℝ :=
  if Real.log c < Real.log x then x * Real.log x else 0

theorem logTailDensityKernel_nonneg {c x : ℝ} (hc : 1 < c) (hx : 0 ≤ x) :
    0 ≤ logTailDensityKernel c x := by
  unfold logTailDensityKernel
  split_ifs with ht
  · exact mul_nonneg hx ((Real.log_pos hc).trans ht).le
  · exact le_rfl

theorem klFun_eq_mul_reverseKL {x : ℝ} (hx : 0 < x) :
    InformationTheory.klFun x = x * (x⁻¹ - 1 - Real.log x⁻¹) := by
  unfold InformationTheory.klFun
  rw [Real.log_inv]
  field_simp [hx.ne']
  ring

theorem mul_inverse_hellinger_kernel {x : ℝ} (hx : 0 < x) :
    x * (Real.sqrt x⁻¹ - 1) ^ 2 = (Real.sqrt x - 1) ^ 2 := by
  have h := sqrt_sub_sqrt_sq_homogeneous (inv_nonneg.mpr hx.le)
    (by norm_num : (0 : ℝ) ≤ 1) hx.le
  simp only [inv_mul_cancel₀ hx.ne', one_mul, Real.sqrt_one] at h
  calc
    x * (Real.sqrt x⁻¹ - 1) ^ 2 = (1 - Real.sqrt x) ^ 2 := h
    _ = (Real.sqrt x - 1) ^ 2 := by ring

theorem klFun_le_klUpperCoeff_mul_hellinger {c x : ℝ}
    (hc : 1 < c) (hx : 0 < x) (hxc : x ≤ c) :
    InformationTheory.klFun x ≤ klUpperCoeff c * (Real.sqrt x - 1) ^ 2 := by
  have hinv : 1 / c ≤ x⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hx hxc
  have h := reverseKL_le_klUpperCoeff hc hinv
  calc
    InformationTheory.klFun x = x * (x⁻¹ - 1 - Real.log x⁻¹) := klFun_eq_mul_reverseKL hx
    _ ≤ x * (klUpperCoeff c * (Real.sqrt x⁻¹ - 1) ^ 2) :=
      mul_le_mul_of_nonneg_left h hx.le
    _ = klUpperCoeff c * (x * (Real.sqrt x⁻¹ - 1) ^ 2) := by ring
    _ = klUpperCoeff c * (Real.sqrt x - 1) ^ 2 := by rw [mul_inverse_hellinger_kernel hx]

theorem klFun_le_hellinger_add_logTail {c x : ℝ} (hc : 1 < c) (hx : 0 ≤ x) :
    InformationTheory.klFun x ≤
      klUpperCoeff c * (Real.sqrt x - 1) ^ 2 + logTailDensityKernel c x := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · simpa [InformationTheory.klFun, logTailDensityKernel] using one_le_klUpperCoeff c
  · by_cases ht : Real.log c < Real.log x
    · have hcx : c < x := (Real.log_lt_log_iff (by linarith : 0 < c) hx).mp ht
      have hnonneg := mul_nonneg (klUpperCoeff_pos c).le (sq_nonneg (Real.sqrt x - 1))
      simp only [logTailDensityKernel, if_pos ht]
      unfold InformationTheory.klFun
      linarith
    · have hxc : x ≤ c := (Real.log_le_log_iff hx (by linarith : 0 < c)).mp (not_lt.mp ht)
      simpa only [logTailDensityKernel, if_neg ht, add_zero] using
        klFun_le_klUpperCoeff_mul_hellinger hc hx hxc

theorem klTailLowerCoeff_mul_logTail_le_klFun {c x : ℝ}
    (hc : 1 < c) (hx : 0 ≤ x) :
    klTailLowerCoeff c * logTailDensityKernel c x ≤ InformationTheory.klFun x := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · simp [logTailDensityKernel, InformationTheory.klFun]
  · by_cases ht : Real.log c < Real.log x
    · have hc0 : 0 < c := by linarith
      have hcx : c < x := (Real.log_lt_log_iff hc0 hx).mp ht
      have hinv : x⁻¹ < 1 / c := by
        simpa only [one_div] using one_div_lt_one_div_of_lt hc0 hcx
      have h := klTailLowerCoeff_mul_neg_log_le_reverseKL hc (inv_pos.mpr hx) hinv
      calc
        klTailLowerCoeff c * logTailDensityKernel c x =
            x * (klTailLowerCoeff c * (-Real.log x⁻¹)) := by
          simp only [logTailDensityKernel, if_pos ht, Real.log_inv, neg_neg]
          ring
        _ ≤ x * (x⁻¹ - 1 - Real.log x⁻¹) := mul_le_mul_of_nonneg_left h hx.le
        _ = InformationTheory.klFun x := (klFun_eq_mul_reverseKL hx).symm
    · simpa only [logTailDensityKernel, if_neg ht, mul_zero] using
        InformationTheory.klFun_nonneg hx.le

end Hellinger
