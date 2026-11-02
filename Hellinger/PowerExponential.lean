/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! The exact real-exponent polynomial/exponential maximum for Kullback–Leibler variation bounds. -/

@[expose] public section

namespace Hellinger

/-- The global maximum is valid regardless of the location of a later cutoff. -/
theorem rpow_mul_exp_neg_le {k u : ℝ} (hk : 0 < k) (hu : 0 ≤ u) :
    u ^ k * Real.exp (-u) ≤ (k / Real.exp 1) ^ k := by
  rcases eq_or_lt_of_le hu with rfl | hu
  · simp only [Real.zero_rpow hk.ne', zero_mul]
    exact (Real.rpow_pos_of_pos (div_pos hk (Real.exp_pos 1)) k).le
  · have hlog := Real.log_le_sub_one_of_pos (div_pos hu hk)
    rw [Real.log_div hu.ne' hk.ne'] at hlog
    have hm := mul_le_mul_of_nonneg_left hlog hk.le
    have hdiv : k * (u / k) = u := by field_simp
    rw [Real.rpow_def_of_pos hu,
      Real.rpow_def_of_pos (div_pos hk (Real.exp_pos 1)),
      Real.log_div hk.ne' (Real.exp_ne_zero 1), Real.log_exp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [hm, hdiv]

end Hellinger
