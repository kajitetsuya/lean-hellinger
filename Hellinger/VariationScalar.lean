/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.BernsteinScalar
public import Hellinger.PowerExponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Real-exponent weighted variation comparisons and cutoff geometry. -/
@[expose] public section

namespace Hellinger

/-- Forward density of the strictly truncated real log moment. -/
noncomputable def logMomentTailDensityKernel (c k r : ℝ) : ℝ :=
  if Real.log c < Real.log r then r * (Real.log r) ^ k else 0

/-- Weighted squared logarithms are controlled by the Hellinger kernel. -/
theorem mul_sq_log_le_four_sqrt_mul_hellinger {r : ℝ} (hr : 0 < r) :
    r * (Real.log r) ^ 2 ≤ 4 * Real.sqrt r * (Real.sqrt r - 1) ^ 2 := by
  have h := mul_le_mul_of_nonneg_left (sq_le_expSymmKernel (Real.log (Real.sqrt r)))
    (Real.sqrt_nonneg r)
  rw [mul_expSymmKernel_log (Real.sqrt_pos.mpr hr), Real.log_sqrt hr.le] at h
  calc
    _ = (4 * Real.sqrt r) * (Real.sqrt r * (Real.log r / 2) ^ 2) := by
      nlinarith [Real.sq_sqrt hr.le]
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by linarith [Real.sqrt_nonneg r])

theorem cutoffGap_eq_one_sub_inv_sqrt {c : ℝ} (hc : 0 < c) :
    cutoffGap c = 1 - (Real.sqrt c)⁻¹ := by
  unfold cutoffGap
  rw [Real.rpow_neg hc.le, ← Real.sqrt_eq_rpow]

/-- Small forward densities are separated from one by the cutoff gap. -/
theorem cutoffGap_sq_le_hellinger_of_le_inv {c r : ℝ} (hc : 1 < c)
    (hrr : r ≤ 1 / c) : cutoffGap c ^ 2 ≤ (Real.sqrt r - 1) ^ 2 := by
  have hs := Real.sqrt_le_sqrt hrr
  rw [one_div, Real.sqrt_inv] at hs
  have hgap : cutoffGap c ≤ 1 - Real.sqrt r := by
    rw [cutoffGap_eq_one_sub_inv_sqrt (lt_trans (by norm_num) hc)]
    linarith
  have hsq := pow_le_pow_left₀ (cutoffGap_pos hc).le hgap 2
  nlinarith

/-- Reciprocal cutoff geometry, useful for both variation and interpolation. -/
theorem one_le_tailMassCoeff_mul_hellinger_of_le_inv {c r : ℝ} (hc : 1 < c)
    (hrr : r ≤ 1 / c) : 1 ≤ tailMassCoeff c * (Real.sqrt r - 1) ^ 2 := by
  have h := mul_le_mul_of_nonneg_left (cutoffGap_sq_le_hellinger_of_le_inv hc hrr)
    (tailMassCoeff_pos hc).le
  have hid : tailMassCoeff c * cutoffGap c ^ 2 = 1 := by
    unfold tailMassCoeff
    exact inv_mul_cancel₀ (ne_of_gt (sq_pos_of_pos (cutoffGap_pos hc)))
  rwa [hid] at h

/-- Middle-region comparison with the exact first branch of the coefficient maximum. -/
theorem variation_density_middle {c k r : ℝ} (hc : 1 < c) (hk : 2 ≤ k)
    (hrlo : 1 / c ≤ r) (hrhi : r ≤ c) :
    r * |Real.log r| ^ k ≤
      (4 * Real.sqrt c * (Real.log c) ^ (k - 2)) * (Real.sqrt r - 1) ^ 2 := by
  have hc0 : 0 < c := lt_trans (by norm_num) hc
  have hr : 0 < r := lt_of_lt_of_le (one_div_pos.mpr hc0) hrlo
  have hlo : -Real.log c ≤ Real.log r := by
    have h := Real.log_le_log (one_div_pos.mpr hc0) hrlo
    simpa only [one_div, Real.log_inv] using h
  have hhi : Real.log r ≤ Real.log c := Real.log_le_log hr hrhi
  have habs : |Real.log r| ≤ Real.log c := abs_le.mpr ⟨hlo, hhi⟩
  have hpow := Real.rpow_le_rpow (abs_nonneg (Real.log r)) habs (by linarith : 0 ≤ k - 2)
  have hsplit : |Real.log r| ^ k = (Real.log r) ^ 2 * |Real.log r| ^ (k - 2) := by
    calc
      _ = |Real.log r| ^ ((2 : ℝ) + (k - 2)) := by congr 1; ring
      _ = |Real.log r| ^ (2 : ℝ) * |Real.log r| ^ (k - 2) :=
        Real.rpow_add' (abs_nonneg _) (by linarith)
      _ = _ := by rw [Real.rpow_two, sq_abs]
  have hbase := mul_sq_log_le_four_sqrt_mul_hellinger hr
  have hcp : 0 ≤ (Real.log c) ^ (k - 2) := Real.rpow_nonneg (Real.log_pos hc).le _
  have hsqrt := Real.sqrt_le_sqrt hrhi
  calc
    _ = (r * (Real.log r) ^ 2) * |Real.log r| ^ (k - 2) := by rw [hsplit]; ring
    _ ≤ (r * (Real.log r) ^ 2) * (Real.log c) ^ (k - 2) :=
      mul_le_mul_of_nonneg_left hpow (mul_nonneg hr.le (sq_nonneg _))
    _ ≤ (4 * Real.sqrt r * (Real.sqrt r - 1) ^ 2) * (Real.log c) ^ (k - 2) :=
      mul_le_mul_of_nonneg_right hbase hcp
    _ = (4 * (Real.sqrt r - 1) ^ 2 * (Real.log c) ^ (k - 2)) * Real.sqrt r := by ring
    _ ≤ (4 * (Real.sqrt r - 1) ^ 2 * (Real.log c) ^ (k - 2)) * Real.sqrt c :=
      mul_le_mul_of_nonneg_left hsqrt (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hcp)
    _ = _ := by ring

/-- Far small-density comparison with the exact second branch of the coefficient maximum. -/
theorem variation_density_small {c k r : ℝ} (hc : 1 < c) (hk : 0 < k)
    (hr : 0 < r) (hrlo : r ≤ 1 / c) :
    r * |Real.log r| ^ k ≤
      (tailMassCoeff c * (k / Real.exp 1) ^ k) * (Real.sqrt r - 1) ^ 2 := by
  have hc0 : 0 < c := lt_trans (by norm_num) hc
  have hr1 : r ≤ 1 := hrlo.trans ((div_le_one hc0).mpr hc.le)
  have hlog : Real.log r ≤ 0 := Real.log_nonpos hr.le hr1
  have hm := rpow_mul_exp_neg_le hk (neg_nonneg.mpr hlog)
  have hmax : r * |Real.log r| ^ k ≤ (k / Real.exp 1) ^ k := by
    simpa only [neg_neg, Real.exp_log hr, abs_of_nonpos hlog, mul_comm] using hm
  have hgeom := one_le_tailMassCoeff_mul_hellinger_of_le_inv hc hrlo
  have hmax0 : 0 ≤ (k / Real.exp 1) ^ k :=
    Real.rpow_nonneg (div_nonneg hk.le (Real.exp_pos 1).le) _
  calc
    _ ≤ (k / Real.exp 1) ^ k := hmax
    _ = (k / Real.exp 1) ^ k * 1 := (mul_one _).symm
    _ ≤ (k / Real.exp 1) ^ k * (tailMassCoeff c * (Real.sqrt r - 1) ^ 2) :=
      mul_le_mul_of_nonneg_left hgeom hmax0
    _ = _ := by ring

theorem logMomentTailDensityKernel_nonneg {c k r : ℝ} (hc : 1 < c) (hr : 0 ≤ r) :
    0 ≤ logMomentTailDensityKernel c k r := by
  unfold logMomentTailDensityKernel
  split_ifs with ht
  · exact mul_nonneg hr (Real.rpow_nonneg ((Real.log_pos hc).trans ht).le _)
  · exact le_rfl

/-- Restriction to the positive-log tail is bounded by the full absolute moment density. -/
theorem variation_density_lower {c r : ℝ} (hc : 1 < c) (k : ℝ) (hr : 0 ≤ r) :
    logMomentTailDensityKernel c k r ≤ r * |Real.log r| ^ k := by
  unfold logMomentTailDensityKernel
  split_ifs with ht
  · rw [abs_of_pos ((Real.log_pos hc).trans ht)]
  · exact mul_nonneg hr (Real.rpow_nonneg (abs_nonneg _) _)

/-- The weighted scalar variation split, including zero density. -/
theorem variation_density_upper {c k r : ℝ} (hc : 1 < c) (hk : 2 ≤ k) (hr : 0 ≤ r) :
    r * |Real.log r| ^ k ≤ variationUpperCoeff c k * (Real.sqrt r - 1) ^ 2 +
      logMomentTailDensityKernel c k r := by
  have hk0 : 0 < k := lt_of_lt_of_le (by norm_num) hk
  by_cases hr0 : r = 0
  · subst r
    simpa [logMomentTailDensityKernel] using (variationUpperCoeff_pos hc hk0).le
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    by_cases ht : Real.log c < Real.log r
    · rw [logMomentTailDensityKernel, ite_eq_left ht, abs_of_pos ((Real.log_pos hc).trans ht)]
      exact le_add_of_nonneg_left
        (mul_nonneg (variationUpperCoeff_pos hc hk0).le (sq_nonneg _))
    · have hc0 : 0 < c := lt_trans (by norm_num) hc
      have hrhi : r ≤ c := (Real.log_le_log_iff hrpos hc0).mp (le_of_not_gt ht)
      have hbound : r * |Real.log r| ^ k ≤ variationUpperCoeff c k * (Real.sqrt r - 1) ^ 2 := by
        by_cases hrlo : r ≤ 1 / c
        · exact (variation_density_small hc hk0 hrpos hrlo).trans
            (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))
        · exact (variation_density_middle hc hk (lt_of_not_ge hrlo).le hrhi).trans
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
      simpa only [logMomentTailDensityKernel, ite_eq_right ht, add_zero] using hbound

end Hellinger
