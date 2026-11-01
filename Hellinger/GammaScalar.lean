/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Linarith

/-! Real-exponent Gamma bounds for the exponential remainder. -/

public section

open MeasureTheory Set
open scoped Interval

namespace Hellinger

/-- A tail of Euler's Gamma integral bounds the exponential-power kernel. -/
theorem rpow_mul_exp_neg_le_Gamma {s t : ℝ} (hs : 1 ≤ s) (ht : 0 < t) :
    t ^ (s - 1) * Real.exp (-t) ≤ Real.Gamma s := by
  have hspos : 0 < s := by linarith
  have hsub : Ioi t ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi ht.le
  have hGamma := Real.GammaIntegral_convergent hspos
  calc
    t ^ (s - 1) * Real.exp (-t) =
        ∫ z in Ioi t, Real.exp (-z) * t ^ (s - 1) := by
      rw [integral_mul_const, integral_exp_neg_Ioi]
      ring
    _ ≤ ∫ z in Ioi t, Real.exp (-z) * z ^ (s - 1) := by
      apply setIntegral_mono_on
        ((integrableOn_exp_neg_Ioi t).mul_const _) (hGamma.mono_set hsub)
        measurableSet_Ioi
      intro z hz
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow ht.le hz.le (by linarith)) (Real.exp_pos _).le
    _ ≤ ∫ z in Ioi (0 : ℝ), Real.exp (-z) * z ^ (s - 1) := by
      apply setIntegral_mono_set hGamma
      · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
        exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hz.le _)
      · exact Filter.Eventually.of_forall fun z hz ↦ hsub hz
    _ = Real.Gamma s := (Real.Gamma_eq_integral hspos).symm

/-- The Gamma tail estimate, after multiplication by the positive exponential. -/
theorem rpow_le_Gamma_mul_exp {s t : ℝ} (hs : 1 ≤ s) (ht : 0 < t) :
    t ^ (s - 1) ≤ Real.Gamma s * Real.exp t := by
  calc
    t ^ (s - 1) = (t ^ (s - 1) * Real.exp (-t)) * Real.exp t := by
      rw [mul_assoc, ← Real.exp_add]
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (rpow_mul_exp_neg_le_Gamma hs ht)
      (Real.exp_pos _).le

/-- One integration of the Gamma tail estimate, valid for every real `s ≥ 1`. -/
theorem rpow_le_Gamma_mul_exp_sub_one {s x : ℝ} (hs : 1 ≤ s) (hx : 0 ≤ x) :
    x ^ s ≤ Real.Gamma (s + 1) * (Real.exp x - 1) := by
  have hspos : 0 < s := by linarith
  have hpow : IntervalIntegrable (fun t : ℝ ↦ t ^ (s - 1)) volume 0 x :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hexp : IntervalIntegrable (fun t : ℝ ↦ Real.Gamma s * Real.exp t) volume 0 x :=
    (Real.continuous_exp.const_mul _).intervalIntegrable 0 x
  have hi := intervalIntegral.integral_mono_on_of_le_Ioo hx hpow hexp
    (fun t ht ↦ rpow_le_Gamma_mul_exp hs ht.1)
  have hp : (∫ t : ℝ in 0..x, t ^ (s - 1)) = x ^ s / s := by
    rw [integral_rpow (Or.inl (by linarith))]
    simp [Real.zero_rpow hspos.ne']
  have he : (∫ t : ℝ in 0..x, Real.Gamma s * Real.exp t) =
      Real.Gamma s * (Real.exp x - 1) := by
    rw [intervalIntegral.integral_const_mul, integral_exp]
    simp
  rw [hp, he] at hi
  have hi' := (div_le_iff₀ hspos).mp hi
  rw [Real.Gamma_add_one hspos.ne']
  nlinarith [hi']

/-- The exact Gamma bound for the exponential remainder, for all real exponents `k ≥ 2`.
This is a scalar inequality; no moment or measure-level theorem is asserted here. -/
theorem rpow_le_Gamma_mul_exp_remainder {k x : ℝ} (hk : 2 ≤ k) (hx : 0 ≤ x) :
    x ^ k ≤ Real.Gamma (k + 1) * (Real.exp x - 1 - x) := by
  have hkpos : 0 < k := by linarith
  have hpow : IntervalIntegrable (fun t : ℝ ↦ t ^ (k - 1)) volume 0 x :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hexp : IntervalIntegrable (fun t : ℝ ↦ Real.Gamma k * (Real.exp t - 1)) volume 0 x :=
    (Real.continuous_exp.sub continuous_const |>.const_mul _).intervalIntegrable 0 x
  have hi := intervalIntegral.integral_mono_on_of_le_Ioo hx hpow hexp (fun t ht ↦ by
    have h := rpow_le_Gamma_mul_exp_sub_one (s := k - 1) (by linarith) ht.1.le
    simpa using h)
  have hp : (∫ t : ℝ in 0..x, t ^ (k - 1)) = x ^ k / k := by
    rw [integral_rpow (Or.inl (by linarith))]
    simp [Real.zero_rpow hkpos.ne']
  have he : (∫ t : ℝ in 0..x, Real.Gamma k * (Real.exp t - 1)) =
      Real.Gamma k * (Real.exp x - 1 - x) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
      (Real.continuous_exp.intervalIntegrable 0 x) (continuous_const.intervalIntegrable 0 x),
      integral_exp, intervalIntegral.integral_const]
    simp
  rw [hp, he] at hi
  have hi' := (div_le_iff₀ hkpos).mp hi
  rw [Real.Gamma_add_one hkpos.ne']
  nlinarith [hi']

/-- Division form of the exact Gamma comparison; the denominator is strictly positive. -/
theorem rpow_div_Gamma_le_exp_remainder {k x : ℝ} (hk : 2 ≤ k) (hx : 0 ≤ x) :
    x ^ k / Real.Gamma (k + 1) ≤ Real.exp x - 1 - x := by
  apply (div_le_iff₀ (Real.Gamma_pos_of_pos (by linarith : 0 < k + 1))).mpr
  simpa only [mul_comm] using rpow_le_Gamma_mul_exp_remainder hk hx

end Hellinger
