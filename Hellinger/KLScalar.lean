/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.Constants
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Scalar comparisons for the reverse-density Kullback–Leibler kernel `x - 1 - log x` on
`x > 0`. -/
@[expose] public section

namespace Hellinger

/-- The reverse-density Kullback–Leibler kernel dominates the squared Hellinger kernel. -/
theorem sqrt_sub_one_sq_le_reverseKL {x : ℝ} (hx : 0 < x) :
    (Real.sqrt x - 1) ^ 2 ≤ x - 1 - Real.log x := by
  have hlog := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx)
  rw [Real.log_sqrt hx.le] at hlog
  nlinarith [Real.sq_sqrt hx.le]

/-- Derivative of the rational lower-logarithm comparison gap. -/
theorem hasDerivAt_neg_log_sub_ratio {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ ↦ -Real.log y - 2 * (1 - y) / (1 + y))
      (-((1 - x) ^ 2) / (x * (1 + x) ^ 2)) x := by
  have hden : 1 + x ≠ 0 := ne_of_gt (by linarith)
  have hd := (Real.hasDerivAt_log hx.ne').neg.sub
    ((((hasDerivAt_id x).const_sub 1).const_mul 2).div
      ((hasDerivAt_id x).const_add 1) hden)
  change HasDerivAt (fun y : ℝ ↦ -Real.log y - 2 * (1 - y) / (1 + y))
    (-x⁻¹ - (2 * (-1) * (1 + x) - 2 * (1 - x) * 1) / (1 + x) ^ 2) x at hd
  convert hd using 1
  field_simp [hx.ne', hden]
  ring

/-- The sharp rational lower-logarithm inequality on `(0,1]`. -/
theorem two_mul_one_sub_div_le_neg_log {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    2 * (1 - x) / (1 + x) ≤ -Real.log x := by
  let q : ℝ → ℝ := fun y ↦ -Real.log y - 2 * (1 - y) / (1 + y)
  have hd (y : ℝ) (hy : y ∈ Set.Icc x 1) :
      HasDerivAt q (-((1 - y) ^ 2) / (y * (1 + y) ^ 2)) y :=
    hasDerivAt_neg_log_sub_ratio (lt_of_lt_of_le hx hy.1)
  have hanti : AntitoneOn q (Set.Icc x 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc x 1)
      (fun y hy ↦ (hd y hy).continuousAt.continuousWithinAt)
      (fun y hy ↦ (hd y (interior_subset hy)).hasDerivWithinAt)
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le hx (interior_subset hy).1
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _))
      (mul_nonneg hy0.le (sq_nonneg _))
  have hq := hanti (show x ∈ Set.Icc x 1 from ⟨le_rfl, hx1⟩)
    (show (1 : ℝ) ∈ Set.Icc x 1 from ⟨hx1, le_rfl⟩) hx1
  have hzero : 0 ≤ q x := by simpa [q] using hq
  dsimp [q] at hzero
  linarith

/-- On the strict cutoff tail, the reverse-density Kullback–Leibler kernel controls the log tail. -/
theorem klTailLowerCoeff_mul_neg_log_le_reverseKL {c x : ℝ}
    (hc : 1 < c) (hx : 0 < x) (hxc : x < 1 / c) :
    klTailLowerCoeff c * (-Real.log x) ≤ x - 1 - Real.log x := by
  have hc0 : 0 < c := lt_trans (by norm_num) hc
  have hinv : 1 / c < (1 : ℝ) := (div_lt_one hc0).mpr hc
  have hx1 : x ≤ 1 := (hxc.trans hinv).le
  have hL : 0 ≤ -Real.log x := neg_nonneg.mpr (Real.log_nonpos hx.le hx1)
  have hlog := two_mul_one_sub_div_le_neg_log hx hx1
  have hcross : 2 * (1 - x) ≤ (-Real.log x) * (1 + x) :=
    (div_le_iff₀ (show 0 < 1 + x by linarith)).mp hlog
  have hphi : ((1 - x) / 2) * (-Real.log x) ≤ x - 1 - Real.log x := by
    nlinarith
  have hcoeff : klTailLowerCoeff c ≤ (1 - x) / 2 := by
    unfold klTailLowerCoeff
    exact (min_le_right _ _).trans (by linarith)
  exact (mul_le_mul_of_nonneg_right hcoeff hL).trans hphi

/-- Derivative factorization for the gap in the upper Kullback–Leibler kernel comparison. -/
theorem hasDerivAt_klUpper_gap (a : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt
      (fun v : ℝ ↦ (1 + a) * (v - 1) ^ 2 - (v ^ 2 - 1 - 2 * Real.log v))
      (2 * (a * u - 1) * (u - 1) / u) u := by
  have hd : HasDerivAt
      (fun v : ℝ ↦ (1 + a) * (v - 1) ^ 2 - (v ^ 2 - 1 - 2 * Real.log v))
      ((1 + a) * (2 * (u - 1) ^ 1 * 1) - (2 * u ^ 1 - 2 * u⁻¹)) u :=
    ((((hasDerivAt_id u).sub_const 1).pow 2).const_mul (1 + a)).sub
      (((hasDerivAt_pow 2 u).sub_const 1).sub ((Real.hasDerivAt_log hu.ne').const_mul 2))
  convert hd using 1
  field_simp [hu.ne']
  ring

/-- The upper comparison in square-root coordinates, including its minimum at one. -/
theorem reverseKL_sq_le_mul_sq_sub_one {a u : ℝ}
    (ha : 1 ≤ a) (hu : 0 < u) (hau : 1 ≤ a * u) :
    u ^ 2 - 1 - 2 * Real.log u ≤ (1 + a) * (u - 1) ^ 2 := by
  let D : ℝ → ℝ := fun v ↦
    (1 + a) * (v - 1) ^ 2 - (v ^ 2 - 1 - 2 * Real.log v)
  have hd (v : ℝ) (hv : 0 < v) :
      HasDerivAt D (2 * (a * v - 1) * (v - 1) / v) v :=
    hasDerivAt_klUpper_gap a hv
  have hD1 : D 1 = 0 := by simp [D]
  have ha0 : 0 ≤ a := le_trans (by norm_num) ha
  have hmin : 0 ≤ D u := by
    rcases le_total u 1 with hu1 | h1u
    · have hanti : AntitoneOn D (Set.Icc u 1) := by
        apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc u 1)
          (fun v hv ↦ (hd v (lt_of_lt_of_le hu hv.1)).continuousAt.continuousWithinAt)
          (fun v hv ↦ (hd v (lt_of_lt_of_le hu (interior_subset hv).1)).hasDerivWithinAt)
        intro v hv
        have hvI := interior_subset hv
        have hv0 : 0 < v := lt_of_lt_of_le hu hvI.1
        have hav : 0 ≤ a * v - 1 := by
          have hmul := mul_le_mul_of_nonneg_left hvI.1 ha0
          linarith
        exact div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos
            (mul_nonneg (by norm_num) hav) (sub_nonpos.mpr hvI.2)) hv0.le
      have h := hanti (show u ∈ Set.Icc u 1 from ⟨le_rfl, hu1⟩)
        (show (1 : ℝ) ∈ Set.Icc u 1 from ⟨hu1, le_rfl⟩) hu1
      simpa only [hD1] using h
    · have hmono : MonotoneOn D (Set.Icc 1 u) := by
        apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 1 u)
          (fun v hv ↦ (hd v (lt_of_lt_of_le (by norm_num) hv.1)).continuousAt.continuousWithinAt)
          (fun v hv ↦ (hd v (lt_of_lt_of_le (by norm_num) (interior_subset hv).1)).hasDerivWithinAt)
        intro v hv
        have hvI := interior_subset hv
        have hv0 : 0 < v := lt_of_lt_of_le (by norm_num) hvI.1
        have hav : 0 ≤ a * v - 1 := by
          have hmul := mul_le_mul_of_nonneg_left hvI.1 ha0
          nlinarith
        exact div_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) hav) (sub_nonneg.mpr hvI.1)) hv0.le
      have h := hmono (show (1 : ℝ) ∈ Set.Icc 1 u from ⟨le_rfl, h1u⟩)
        (show u ∈ Set.Icc 1 u from ⟨h1u, le_rfl⟩) h1u
      simpa only [hD1] using h
  dsimp [D] at hmin
  linarith

/-- On the closed regular region, the selected cutoff coefficient controls the
reverse-density Kullback–Leibler kernel. -/
theorem reverseKL_le_klUpperCoeff {c x : ℝ} (hc : 1 < c) (hxc : 1 / c ≤ x) :
    x - 1 - Real.log x ≤ klUpperCoeff c * (Real.sqrt x - 1) ^ 2 := by
  have hc0 : 0 < c := lt_trans (by norm_num) hc
  have hx0 : 0 < x := lt_of_lt_of_le (one_div_pos.mpr hc0) hxc
  have ha : 1 ≤ Real.sqrt c := by
    nlinarith [Real.sq_sqrt hc0.le, Real.sqrt_nonneg c]
  have hcx : 1 ≤ c * x := by
    have h := (div_le_iff₀ hc0).mp hxc
    nlinarith
  have hsquare : (Real.sqrt c * Real.sqrt x) ^ 2 = c * x := by
    rw [mul_pow, Real.sq_sqrt hc0.le, Real.sq_sqrt hx0.le]
  have hau : 1 ≤ Real.sqrt c * Real.sqrt x := by
    have hnonneg := mul_nonneg (Real.sqrt_nonneg c) (Real.sqrt_nonneg x)
    nlinarith
  have h := reverseKL_sq_le_mul_sq_sub_one ha (Real.sqrt_pos.mpr hx0) hau
  rw [Real.sq_sqrt hx0.le, Real.log_sqrt hx0.le] at h
  unfold klUpperCoeff
  nlinarith

end Hellinger
