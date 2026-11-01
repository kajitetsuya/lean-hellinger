/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
Exact scalar identities for the normal-location example. These statements use mathlib's
actual normalized Gaussian density. They do not assume a likelihood-ratio or tail formula.
Normal and NormalTail establish the density-ratio bridge and exact Gaussian tail formulas.
-/

@[expose] public section

open ProbabilityTheory Real
open scoped NNReal

namespace Hellinger.Comparison.Examples.NormalScalar

/-- Completing the square in a Gaussian density under an exponential tilt.
The zero-variance case is included: mathlib's real Gaussian PDF is then zero. -/
theorem gaussianPDFReal_exp_tilt (mu : ℝ) (v : ℝ≥0) (t x : ℝ) :
    gaussianPDFReal mu v x * Real.exp (t * x) =
      Real.exp (mu * t + (v : ℝ) * t ^ 2 / 2) *
        gaussianPDFReal (mu + (v : ℝ) * t) v x := by
  by_cases hv : v = 0
  · simp [hv]
  have hvR : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  have hsq : -(x - mu) ^ 2 / (2 * (v : ℝ)) + t * x =
      (mu * t + (v : ℝ) * t ^ 2 / 2) +
        -(x - (mu + (v : ℝ) * t)) ^ 2 / (2 * (v : ℝ)) := by
    field_simp [hvR]
    <;> ring
  calc
    gaussianPDFReal mu v x * Real.exp (t * x) =
        (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
          Real.exp (-(x - mu) ^ 2 / (2 * (v : ℝ)) + t * x) := by
      rw [gaussianPDFReal, Real.exp_add, mul_assoc]
    _ = (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
          Real.exp ((mu * t + (v : ℝ) * t ^ 2 / 2) +
            -(x - (mu + (v : ℝ) * t)) ^ 2 / (2 * (v : ℝ))) := by rw [hsq]
    _ = Real.exp (mu * t + (v : ℝ) * t ^ 2 / 2) *
          gaussianPDFReal (mu + (v : ℝ) * t) v x := by
      rw [Real.exp_add, gaussianPDFReal]
      ring

/-- The source normal-location ratio, for the actual unit-variance densities.
Both densities are strictly positive, including at parameter zero. -/
theorem gaussianPDFReal_zero_div_location (theta x : ℝ) :
    gaussianPDFReal 0 1 x / gaussianPDFReal theta 1 x =
      Real.exp (-theta * x + theta ^ 2 / 2) := by
  apply (div_eq_iff (ne_of_gt (gaussianPDFReal_pos theta 1 x (by norm_num)))).2
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  conv_rhs => rw [mul_left_comm]
  rw [← Real.exp_add]
  congr 1
  congr 1
  ring

/-- The logarithm of the density ratio has no exceptional zero-parameter case. -/
theorem log_gaussianPDFReal_zero_div_location (theta x : ℝ) :
    Real.log (gaussianPDFReal 0 1 x / gaussianPDFReal theta 1 x) =
      -theta * x + theta ^ 2 / 2 := by
  rw [gaussianPDFReal_zero_div_location, Real.log_exp]

end Hellinger.Comparison.Examples.NormalScalar
