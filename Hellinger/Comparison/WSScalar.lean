/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.PowerExponential
import Mathlib.Tactic.Ring

/-! Scalar optimization for the WS logarithmic-tail bound, including zero multipliers. -/

@[expose] public section

namespace Hellinger.Comparison

/-- The zero-inclusive coefficient base, defined also when `M = 0`. -/
noncomputable def wsLogScale (k M : ℝ) : ℝ := Real.log (max (Real.exp k) M)

theorem le_wsLogScale (k M : ℝ) : k ≤ wsLogScale k M := by
  simpa only [wsLogScale, Real.log_exp] using
    Real.log_le_log (Real.exp_pos k) (le_max_left (Real.exp k) M)

theorem wsLogScale_pos {k M : ℝ} (hk : 0 < k) : 0 < wsLogScale k M :=
  hk.trans_le (le_wsLogScale k M)

theorem wsLogScale_zero (k : ℝ) : wsLogScale k 0 = k := by
  simp only [wsLogScale, max_eq_left (Real.exp_pos k).le, Real.log_exp]

theorem wsLogScale_eq_max {k M : ℝ} (hM : 0 < M) :
    wsLogScale k M = max k (Real.log M) := by
  by_cases h : M ≤ Real.exp k
  · rw [wsLogScale, max_eq_left h, Real.log_exp, max_eq_left]
    simpa only [Real.log_exp] using Real.log_le_log hM h
  · have he : Real.exp k ≤ M := (lt_of_not_ge h).le
    rw [wsLogScale, max_eq_right he, max_eq_right]
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos k) he

/-- The optimizing exponent lies in the entire admissible interval `(0,1]`. -/
theorem ws_exponent_pos_le_one {k M : ℝ} (hk : 0 < k) :
    0 < k / wsLogScale k M ∧ k / wsLogScale k M ≤ 1 := by
  exact ⟨div_pos hk (wsLogScale_pos hk),
    (div_le_one (wsLogScale_pos hk)).mpr (le_wsLogScale k M)⟩

/-- This bound uses a defined expression at zero, rather than a totalized `log M`. -/
theorem ws_multiplier_rpow_le_exp {k M : ℝ} (hk : 0 < k) (hM : 0 ≤ M) :
    M ^ (k / wsLogScale k M) ≤ Real.exp k := by
  have hr := (ws_exponent_pos_le_one (M := M) hk).1
  calc
    M ^ (k / wsLogScale k M) ≤
        (max (Real.exp k) M) ^ (k / wsLogScale k M) :=
      Real.rpow_le_rpow hM (le_max_right _ _) hr.le
    _ = Real.exp k := by
      rw [Real.rpow_def_of_pos ((Real.exp_pos k).trans_le (le_max_left _ _))]
      congr 1
      change wsLogScale k M * (k / wsLogScale k M) = k
      field_simp [(wsLogScale_pos (M := M) hk).ne']

/-- Polynomial growth is bounded by an exponential, for every positive real power. -/
theorem rpow_le_scaled_exp {k s u : ℝ} (hk : 0 < k) (hs : 0 < s) (hu : 0 ≤ u) :
    u ^ k ≤ (k / (Real.exp 1 * s)) ^ k * Real.exp (s * u) := by
  have hh := rpow_mul_exp_neg_le hk (mul_nonneg hs.le hu)
  have hmul := mul_le_mul_of_nonneg_right hh (Real.exp_pos (s * u)).le
  rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at hmul
  rw [Real.mul_rpow hs.le hu] at hmul
  have hsPow : 0 < s ^ k := Real.rpow_pos_of_pos hs k
  calc
    u ^ k ≤ ((k / Real.exp 1) ^ k * Real.exp (s * u)) / s ^ k :=
      (le_div_iff₀ hsPow).mpr (by simpa only [mul_comm] using hmul)
    _ = (k / (Real.exp 1 * s)) ^ k * Real.exp (s * u) := by
      rw [Real.div_rpow hk.le (Real.exp_pos 1).le,
        Real.div_rpow hk.le (mul_pos (Real.exp_pos 1) hs).le,
        Real.mul_rpow (Real.exp_pos 1).le hs.le]
      ring

/-- A concrete admissible exponent gives the printed WS coefficient, with no minimum
attainment or integer-power restriction. -/
theorem ws_optimized_scalar {k δ M : ℝ} (hk : 0 < k) (hδ : 0 < δ) (hM : 0 ≤ M) :
    (k / (Real.exp 1 * ((k / wsLogScale k M) * δ))) ^ k *
        M ^ (k / wsLogScale k M) ≤ δ ^ (-k) * (wsLogScale k M) ^ k := by
  have hL : 0 < wsLogScale k M := wsLogScale_pos hk
  have hbase : k / (Real.exp 1 * ((k / wsLogScale k M) * δ)) =
      (wsLogScale k M / δ) / Real.exp 1 := by
    field_simp [hk.ne', hL.ne', hδ.ne', Real.exp_ne_zero]
    <;> ring
  rw [hbase]
  calc
    _ ≤ ((wsLogScale k M / δ) / Real.exp 1) ^ k * Real.exp k :=
      mul_le_mul_of_nonneg_left (ws_multiplier_rpow_le_exp hk hM)
        (Real.rpow_nonneg (by positivity) _)
    _ = (wsLogScale k M / δ) ^ k := by
      rw [Real.div_rpow (div_pos hL hδ).le (Real.exp_pos 1).le, Real.exp_one_rpow]
      exact div_mul_cancel₀ _ (Real.exp_ne_zero _)
    _ = δ ^ (-k) * wsLogScale k M ^ k := by
      rw [Real.div_rpow hL.le hδ.le, Real.rpow_neg hδ.le]
      ring

end Hellinger.Comparison
