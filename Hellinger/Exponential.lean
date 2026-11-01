/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.Linarith

/-! Convex scaling of the even exponential kernel used in Bernstein bounds. -/
public section

namespace Hellinger

/-- Convexity contracts the even exponential kernel by a factor in `[0, 1]`. -/
theorem exp_symm_scaling (t δ : ℝ) (hδ : 0 ≤ δ) (hδ_le : δ ≤ 1) :
    Real.exp (δ * t) + Real.exp (-(δ * t)) - 2 ≤
      δ * (Real.exp t + Real.exp (-t) - 2) := by
  have hδ_compl : 0 ≤ 1 - δ := sub_nonneg.mpr hδ_le
  have hweights : δ + (1 - δ) = 1 := by ring
  have hpos := convexOn_exp.2
    (Set.mem_univ t) (Set.mem_univ (0 : ℝ)) hδ hδ_compl hweights
  have hneg := convexOn_exp.2
    (Set.mem_univ (-t)) (Set.mem_univ (0 : ℝ)) hδ hδ_compl hweights
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at hpos
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one, mul_neg] at hneg
  linarith

end Hellinger
