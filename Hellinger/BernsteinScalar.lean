/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.Definitions
public import Hellinger.Constants
public import Hellinger.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Forward-density scalar Bernstein comparisons for arbitrary fixed cutoffs. -/
@[expose] public section

namespace Hellinger

/-- The even exponential kernel. -/
noncomputable def expSymmKernel (t : ℝ) : ℝ := Real.exp t + Real.exp (-t) - 2

/-- The forward density of the strict exponential tail. -/
noncomputable def powerTailDensityKernel (c δ x : ℝ) : ℝ :=
  if Real.log c < Real.log x then x * Real.exp (δ * Real.log x) else 0

@[simp] theorem expSymmKernel_abs (t : ℝ) : expSymmKernel |t| = expSymmKernel t := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg (lt_of_not_ge ht)]
    unfold expSymmKernel
    rw [neg_neg]
    ring

theorem expSymmKernel_nonneg (t : ℝ) : 0 ≤ expSymmKernel t := by
  have hpos := Real.add_one_le_exp t
  have hneg := Real.add_one_le_exp (-t)
  unfold expSymmKernel
  linarith

/-- The lower half of the even-exponential/Bernstein sandwich. -/
theorem expSymmKernel_mul_le_bernsteinKernel (δ t : ℝ) :
    expSymmKernel (δ * t) ≤ bernsteinKernel δ t := by
  have hs := Real.self_le_sinh_iff.mpr (abs_nonneg (δ * t))
  rw [Real.sinh_eq] at hs
  rw [← expSymmKernel_abs (δ * t)]
  unfold expSymmKernel bernsteinKernel
  nlinarith

/-- The upper half of the sandwich, retaining the exact factor two. -/
theorem bernsteinKernel_le_two_mul_expSymmKernel (δ t : ℝ) :
    bernsteinKernel δ t ≤ 2 * expSymmKernel (δ * t) := by
  have h := Real.add_one_le_exp (-|δ * t|)
  rw [← expSymmKernel_abs (δ * t)]
  unfold expSymmKernel bernsteinKernel
  linarith

theorem expSymmKernel_scaling (t δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    expSymmKernel (δ * t) ≤ δ * expSymmKernel t :=
  exp_symm_scaling t δ hδ hδ1

/-- A factorization used on the strict tail. -/
theorem expSymmKernel_eq_exp_mul_sq (t : ℝ) :
    expSymmKernel t = Real.exp t * (1 - Real.exp (-t)) ^ 2 := by
  have hid : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hid2 : Real.exp t * Real.exp (-t) ^ 2 = Real.exp (-t) := by
    calc
      _ = (Real.exp t * Real.exp (-t)) * Real.exp (-t) := by ring
      _ = Real.exp (-t) := by rw [hid, one_mul]
  unfold expSymmKernel
  nlinarith

/-- Multiplication by the forward density removes the exponential denominator. -/
theorem mul_expSymmKernel_log {x : ℝ} (hx : 0 < x) :
    x * expSymmKernel (Real.log x) = (x - 1) ^ 2 := by
  unfold expSymmKernel
  rw [Real.exp_neg, Real.exp_log hx]
  field_simp [hx.ne']
  ring

/-- Exact square-root factorization for the regular-region coefficient. -/
theorem sq_sub_one_eq_sqrt_factor {x : ℝ} (hx : 0 ≤ x) :
    (x - 1) ^ 2 = (Real.sqrt x - 1) ^ 2 * (Real.sqrt x + 1) ^ 2 := by
  rw [← mul_pow]
  congr 1
  nlinarith [Real.sq_sqrt hx]

/-- The regular-region comparison with the selected exact cutoff coefficient. -/
theorem bernstein_density_regular_upper {c δ x : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hx : 0 < x) (hxc : x ≤ c) :
    x * bernsteinKernel δ (Real.log x) ≤
      bernsteinUpperCoeff c δ * (Real.sqrt x - 1) ^ 2 := by
  have hsand := bernsteinKernel_le_two_mul_expSymmKernel δ (Real.log x)
  have hscale := expSymmKernel_scaling (Real.log x) δ hδ hδ1
  have hb : bernsteinKernel δ (Real.log x) ≤ 2 * δ * expSymmKernel (Real.log x) := by
    nlinarith
  have hsqrt := Real.sqrt_le_sqrt hxc
  have hsquare : (Real.sqrt x + 1) ^ 2 ≤ (Real.sqrt c + 1) ^ 2 :=
    pow_le_pow_left₀ (by linarith [Real.sqrt_nonneg x]) (by linarith) 2
  calc
    _ ≤ x * (2 * δ * expSymmKernel (Real.log x)) := mul_le_mul_of_nonneg_left hb hx.le
    _ = (2 * δ * (Real.sqrt x - 1) ^ 2) * (Real.sqrt x + 1) ^ 2 := by
      calc
        _ = 2 * δ * (x * expSymmKernel (Real.log x)) := by ring
        _ = _ := by rw [mul_expSymmKernel_log hx, sq_sub_one_eq_sqrt_factor hx.le]; ring
    _ ≤ (2 * δ * (Real.sqrt x - 1) ^ 2) * (Real.sqrt c + 1) ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare
        (mul_nonneg (mul_nonneg (by norm_num) hδ) (sq_nonneg _))
    _ = _ := by unfold bernsteinUpperCoeff; ring

/-- On a nonnegative exponential argument, dropping the affine terms gives a tail bound. -/
theorem bernsteinKernel_le_two_mul_exp {δ t : ℝ} (ht : 0 ≤ δ * t) :
    bernsteinKernel δ t ≤ 2 * Real.exp (δ * t) := by
  unfold bernsteinKernel
  rw [abs_of_nonneg ht]
  linarith

/-- The exact lower-tail coefficient is controlled by the even exponential factorization. -/
theorem bernsteinLowerCoeff_mul_exp_le_bernsteinKernel {c δ t : ℝ}
    (hc : 1 < c) (hδ : 0 < δ) (ht : Real.log c < t) :
    bernsteinLowerCoeff c δ * Real.exp (δ * t) ≤ bernsteinKernel δ t := by
  have hc0 : 0 < c := lt_trans (by norm_num) hc
  have hlog : 0 < Real.log c := Real.log_pos hc
  have hpow : c ^ (-δ) = Real.exp (-(δ * Real.log c)) := by
    rw [Real.rpow_def_of_pos hc0]
    congr 1
    ring
  have ha1 : Real.exp (-(δ * Real.log c)) ≤ 1 := by
    calc
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by nlinarith)
      _ = 1 := Real.exp_zero
  have hba : Real.exp (-(δ * t)) ≤ Real.exp (-(δ * Real.log c)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hsquare : (1 - Real.exp (-(δ * Real.log c))) ^ 2 ≤
      (1 - Real.exp (-(δ * t))) ^ 2 :=
    pow_le_pow_left₀ (sub_nonneg.mpr ha1) (sub_le_sub_left hba 1) 2
  have hcoeff : bernsteinLowerCoeff c δ ≤ (1 - Real.exp (-(δ * t))) ^ 2 := by
    simpa only [bernsteinLowerCoeff, hpow] using hsquare
  calc
    _ = Real.exp (δ * t) * bernsteinLowerCoeff c δ := mul_comm _ _
    _ ≤ Real.exp (δ * t) * (1 - Real.exp (-(δ * t))) ^ 2 :=
      mul_le_mul_of_nonneg_left hcoeff (Real.exp_pos _).le
    _ = expSymmKernel (δ * t) := (expSymmKernel_eq_exp_mul_sq _).symm
    _ ≤ _ := expSymmKernel_mul_le_bernsteinKernel δ t

/-- The forward-density lower Bernstein bound, including zero density and the strict cutoff. -/
theorem bernstein_density_lower {c δ x : ℝ} (hc : 1 < c) (hδ : 0 < δ)
    (_hδ1 : δ ≤ 1) (hx : 0 ≤ x) :
    bernsteinLowerCoeff c δ * powerTailDensityKernel c δ x ≤
      x * bernsteinKernel δ (Real.log x) := by
  by_cases hx0 : x = 0
  · subst x
    simp [powerTailDensityKernel]
  · by_cases htail : Real.log c < Real.log x
    · rw [powerTailDensityKernel, ite_eq_left htail]
      calc
        _ = x * (bernsteinLowerCoeff c δ * Real.exp (δ * Real.log x)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (bernsteinLowerCoeff_mul_exp_le_bernsteinKernel hc hδ htail) hx
    · rw [powerTailDensityKernel, ite_eq_right htail, mul_zero]
      exact mul_nonneg hx (bernsteinKernel_nonneg _ _)

/-- The forward-density upper Bernstein bound with the exact selected cutoff coefficient. -/
theorem bernstein_density_upper {c δ x : ℝ} (hc : 1 < c) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hx : 0 ≤ x) :
    x * bernsteinKernel δ (Real.log x) ≤
      bernsteinUpperCoeff c δ * (Real.sqrt x - 1) ^ 2 +
        2 * powerTailDensityKernel c δ x := by
  by_cases hx0 : x = 0
  · subst x
    simpa [powerTailDensityKernel] using (bernsteinUpperCoeff_pos hc hδ).le
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    by_cases htail : Real.log c < Real.log x
    · have harg : 0 ≤ δ * Real.log x :=
        mul_nonneg hδ.le ((Real.log_pos hc).trans htail).le
      have hb := mul_le_mul_of_nonneg_left (bernsteinKernel_le_two_mul_exp harg) hx
      have hregular : 0 ≤ bernsteinUpperCoeff c δ * (Real.sqrt x - 1) ^ 2 :=
        mul_nonneg (bernsteinUpperCoeff_pos hc hδ).le (sq_nonneg _)
      rw [powerTailDensityKernel, ite_eq_left htail]
      calc
        _ ≤ 2 * (x * Real.exp (δ * Real.log x)) := by nlinarith
        _ ≤ _ := le_add_of_nonneg_left hregular
    · have hc0 : 0 < c := lt_trans (by norm_num) hc
      have hxc : x ≤ c := (Real.log_le_log_iff hxpos hc0).mp (le_of_not_gt htail)
      simpa only [powerTailDensityKernel, ite_eq_right htail, mul_zero, add_zero] using
        bernstein_density_regular_upper hδ.le hδ1 hxpos hxc

/-- A variation primitive: the even exponential kernel dominates the square. -/
theorem sq_le_expSymmKernel (t : ℝ) : t ^ 2 ≤ expSymmKernel t := by
  have hv0 : 0 ≤ |t| / 2 := div_nonneg (abs_nonneg _) (by norm_num)
  have hs := Real.self_le_sinh_iff.mpr hv0
  have hsquare := pow_le_pow_left₀ hv0 hs 2
  rw [Real.sinh_eq] at hsquare
  have hp : Real.exp (|t| / 2) ^ 2 = Real.exp |t| := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hn : Real.exp (-(|t| / 2)) ^ 2 = Real.exp (-|t|) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hm : Real.exp (|t| / 2) * Real.exp (-(|t| / 2)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [← expSymmKernel_abs t]
  unfold expSymmKernel
  nlinarith [sq_abs t]

end Hellinger
