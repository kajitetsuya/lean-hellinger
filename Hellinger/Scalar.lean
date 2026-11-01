/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.KLFun
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-! Scalar kernels used by the Hellinger bounds. -/

@[expose] public section

namespace Hellinger

/-- The squared Hellinger kernel at a square is bounded by the KL kernel. -/
theorem sq_sub_one_le_klFun_sq {x : ℝ} (hx : 0 ≤ x) :
    (x - 1) ^ 2 ≤ InformationTheory.klFun (x ^ 2) := by
  have h := mul_nonneg (show (0 : ℝ) ≤ 2 * x by linarith)
    (InformationTheory.klFun_nonneg hx)
  simp only [InformationTheory.klFun, Real.log_pow, Nat.cast_ofNat] at *
  nlinarith

/-- The pointwise lower Hellinger bound, including the zero-density endpoint. -/
theorem sqrt_sub_one_sq_le_klFun {x : ℝ} (hx : 0 ≤ x) :
    (Real.sqrt x - 1) ^ 2 ≤ InformationTheory.klFun x := by
  simpa only [Real.sq_sqrt hx] using
    sq_sub_one_le_klFun_sq (Real.sqrt_nonneg x)

end Hellinger
