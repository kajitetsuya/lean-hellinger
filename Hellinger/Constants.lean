/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-! Explicit coefficients for fixed-cutoff Hellinger bounds.
The coefficients and their positivity are independent of the measures. -/

@[expose] public section

namespace Hellinger

/-- `(1-c^(-δ))²`, the coefficient of the lower Bernstein tail bound. -/
noncomputable def bernsteinLowerCoeff (c δ : ℝ) : ℝ := (1 - c ^ (-δ)) ^ 2

/-- `C_B(c,δ) = 2δ(1+√c)²`. -/
noncomputable def bernsteinUpperCoeff (c δ : ℝ) : ℝ :=
  2 * δ * (1 + Real.sqrt c) ^ 2

/-- `C_K(c) = 1+√c`. -/
noncomputable def klUpperCoeff (c : ℝ) : ℝ := 1 + Real.sqrt c

/-- `a_K(c) = min(1/3, (1-1/c)/2)`. -/
noncomputable def klTailLowerCoeff (c : ℝ) : ℝ := min (1 / 3) ((1 - 1 / c) / 2)

/-- The positive square-root separation at the cutoff. -/
noncomputable def cutoffGap (c : ℝ) : ℝ := 1 - c ^ (-(1 / 2 : ℝ))

/-- `J(c) = (1-c^(-1/2))^(-2)`, written with an integer inverse-square. -/
noncomputable def tailMassCoeff (c : ℝ) : ℝ := ((cutoffGap c) ^ 2)⁻¹

/-- `C_V(c,k) = max(4√c (log c)^(k-2), J(c)(k/e)^k)`. -/
noncomputable def variationUpperCoeff (c k : ℝ) : ℝ :=
  max (4 * Real.sqrt c * (Real.log c) ^ (k - 2))
    (tailMassCoeff c * (k / Real.exp 1) ^ k)

/-- The fixed-cutoff interpolation constant `C_I(c) = J(c)`. -/
noncomputable def interpolationCoeff (c : ℝ) : ℝ := tailMassCoeff c

/-- The coefficient of the centered Kullback–Leibler variation lower comparison. -/
noncomputable def centeredLowerCoeff (k : ℝ) : ℝ := (2 : ℝ) ^ (-k)

theorem bernsteinLowerCoeff_pos {c δ : ℝ} (hc : 1 < c) (hδ : 0 < δ) :
    0 < bernsteinLowerCoeff c δ := by
  apply sq_pos_of_pos
  exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg hc (neg_neg_of_pos hδ))

theorem bernsteinUpperCoeff_pos {c δ : ℝ} (_hc : 1 < c) (hδ : 0 < δ) :
    0 < bernsteinUpperCoeff c δ := by
  unfold bernsteinUpperCoeff
  exact mul_pos (mul_pos (by norm_num) hδ)
    (sq_pos_of_pos (by linarith [Real.sqrt_nonneg c]))

theorem klUpperCoeff_pos (c : ℝ) : 0 < klUpperCoeff c := by
  unfold klUpperCoeff
  linarith [Real.sqrt_nonneg c]

theorem one_le_klUpperCoeff (c : ℝ) : 1 ≤ klUpperCoeff c := by
  unfold klUpperCoeff
  linarith [Real.sqrt_nonneg c]

theorem klTailLowerCoeff_pos {c : ℝ} (hc : 1 < c) : 0 < klTailLowerCoeff c := by
  unfold klTailLowerCoeff
  apply lt_min (by norm_num)
  apply div_pos
  · have hi : 1 / c < (1 : ℝ) := by
      simpa using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hc
    exact sub_pos.mpr hi
  · norm_num

theorem klTailLowerCoeff_le_third (c : ℝ) : klTailLowerCoeff c ≤ 1 / 3 :=
  min_le_left _ _

theorem cutoffGap_pos {c : ℝ} (hc : 1 < c) : 0 < cutoffGap c := by
  exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg hc (by norm_num))

theorem cutoffGap_lt_one {c : ℝ} (hc : 1 < c) : cutoffGap c < 1 := by
  have h := Real.rpow_pos_of_pos (lt_trans (by norm_num) hc) (-(1 / 2 : ℝ))
  unfold cutoffGap
  linarith

theorem tailMassCoeff_pos {c : ℝ} (hc : 1 < c) : 0 < tailMassCoeff c := by
  exact inv_pos.mpr (sq_pos_of_pos (cutoffGap_pos hc))

theorem one_le_tailMassCoeff {c : ℝ} (hc : 1 < c) : 1 ≤ tailMassCoeff c := by
  have hg := cutoffGap_pos hc
  have hg1 := cutoffGap_lt_one hc
  have hs : (cutoffGap c) ^ 2 ≤ 1 := by nlinarith
  unfold tailMassCoeff
  exact (one_le_inv₀ (sq_pos_of_pos hg)).2 hs

theorem variationUpperCoeff_pos {c k : ℝ} (hc : 1 < c) (hk : 0 < k) :
    0 < variationUpperCoeff c k := by
  apply lt_of_lt_of_le _ (le_max_right _ _)
  exact mul_pos (tailMassCoeff_pos hc)
    (Real.rpow_pos_of_pos (div_pos hk (Real.exp_pos 1)) k)

theorem one_le_interpolationCoeff {c : ℝ} (hc : 1 < c) :
    1 ≤ interpolationCoeff c := one_le_tailMassCoeff hc

theorem centeredLowerCoeff_pos (k : ℝ) : 0 < centeredLowerCoeff k :=
  Real.rpow_pos_of_pos (by norm_num) _

/-- Coefficient specialization only; this does not assert a Bernstein bound. -/
theorem bernsteinUpperCoeff_four (δ : ℝ) : bernsteinUpperCoeff 4 δ = 18 * δ := by
  have hs : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num [bernsteinUpperCoeff, hs]
  ring

@[simp] theorem klUpperCoeff_four : klUpperCoeff 4 = 3 := by
  have hs : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num [klUpperCoeff, hs]

@[simp] theorem klTailLowerCoeff_four : klTailLowerCoeff 4 = 1 / 3 := by
  norm_num [klTailLowerCoeff]

@[simp] theorem cutoffGap_four : cutoffGap 4 = 1 / 2 := by
  unfold cutoffGap
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4), ← Real.sqrt_eq_rpow]
  have hs : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num [hs]

@[simp] theorem tailMassCoeff_four : tailMassCoeff 4 = 4 := by
  norm_num [tailMassCoeff]

@[simp] theorem interpolationCoeff_four : interpolationCoeff 4 = 4 := by
  simp [interpolationCoeff]

/-- The selected Kullback–Leibler variation coefficient specializes to the paper's exact
coefficient. -/
theorem variationUpperCoeff_four (k : ℝ) :
    variationUpperCoeff 4 k =
      4 * max (2 * (Real.log 4) ^ (k - 2)) ((k / Real.exp 1) ^ k) := by
  have hs : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num [variationUpperCoeff, hs]
  rw [mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 4)]
  congr 1
  ring

end Hellinger
