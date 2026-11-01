/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.Comparison.FiniteMoment
public import Hellinger.Interpolation
public import Hellinger.HellingerBridge

/-! The refined full first-ratio moment bound.  Working under the reference measure
retains zero-density support and avoids division by the likelihood ratio. -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Hellinger.Comparison

/-- Explicit coefficient at a fixed arbitrary cutoff. -/
noncomputable def refinedMomentCoeff (q : ℝ) : ℝ := q + Real.sqrt q

theorem refinedMomentCoeff_pos {q : ℝ} (hq : 1 < q) : 0 < refinedMomentCoeff q := by
  unfold refinedMomentCoeff
  linarith [Real.sqrt_nonneg q]

theorem refinedMomentCoeff_four : refinedMomentCoeff 4 = 6 := by
  have hs : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num [refinedMomentCoeff, hs]

/-- The scalar remainder on the bounded ratio band. -/
theorem refined_moment_density_bound {q r : ℝ} (hq : 1 < q) (hr : 0 ≤ r) :
    r ^ 2 ≤ (if q < r then r ^ 2 else 0) + r +
      refinedMomentCoeff q * (Real.sqrt r * |Real.sqrt r - 1|) := by
  have hC : 0 ≤ refinedMomentCoeff q := (refinedMomentCoeff_pos hq).le
  have hcross : 0 ≤ Real.sqrt r * |Real.sqrt r - 1| :=
    mul_nonneg (Real.sqrt_nonneg r) (abs_nonneg _)
  by_cases htail : q < r
  · rw [ite_eq_left htail]
    nlinarith [mul_nonneg hC hcross]
  · rw [ite_eq_right htail]
    have hrq : r ≤ q := le_of_not_gt htail
    by_cases hr1 : r ≤ 1
    · nlinarith [mul_nonneg hr (sub_nonneg.mpr hr1), mul_nonneg hC hcross]
    · have hs1 : 1 ≤ Real.sqrt r := by
        simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (le_of_not_ge hr1)
      have hcoef : r + Real.sqrt r ≤ refinedMomentCoeff q :=
        add_le_add hrq (Real.sqrt_le_sqrt hrq)
      have hbound := mul_le_mul_of_nonneg_right hcoef hcross
      have hid : r + (r + Real.sqrt r) * (Real.sqrt r * |Real.sqrt r - 1|) = r ^ 2 := by
        rw [abs_of_nonneg (sub_nonneg.mpr hs1)]
        calc
          _ = r + r * (Real.sqrt r) ^ 2 - r * Real.sqrt r +
              Real.sqrt r * (Real.sqrt r) ^ 2 - (Real.sqrt r) ^ 2 := by ring
          _ = r ^ 2 := by rw [Real.sq_sqrt hr]; ring
      linarith

/-- At a cutoff greater than one, the totalized real logarithm introduces no false
positive tail at the zero-density value. -/
theorem log_cutoff_lt_log_iff {q r : ℝ} (hq : 1 < q) (hr : 0 ≤ r) :
    Real.log q < Real.log r ↔ q < r := by
  by_cases hr0 : r = 0
  · subst r
    simp only [Real.log_zero]
    constructor
    · intro h
      exact False.elim ((not_lt_of_ge (Real.log_pos hq).le) h)
    · intro h
      exact False.elim ((not_lt_of_ge (zero_lt_one.trans hq).le) h)
  · exact Real.log_lt_log_iff (zero_lt_one.trans hq) (lt_of_le_of_ne hr (Ne.symm hr0))

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α}

/-- A finite AC pair has its full ratio moment as the squared forward RN density
under the reference measure; no finite-moment hypothesis is imposed. -/
theorem fullRatioMoment_eq_lintegral_sq_density [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) :
    fullRatioMoment μ ν = ∫⁻ x, ENNReal.ofReal ((μ.rnDeriv ν x).toReal ^ 2) ∂ν := by
  rw [fullRatioMoment_eq_lintegral_rnDeriv hμν]
  rw [← lintegral_rnDeriv_mul hμν (Measure.measurable_rnDeriv μ ν).aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [Measure.rnDeriv_lt_top μ ν] with x hx
  have hreal : ENNReal.ofReal (μ.rnDeriv ν x).toReal = μ.rnDeriv ν x :=
    ENNReal.ofReal_toReal hx.ne
  calc
    μ.rnDeriv ν x * μ.rnDeriv ν x =
        ENNReal.ofReal (μ.rnDeriv ν x).toReal * ENNReal.ofReal (μ.rnDeriv ν x).toReal := by
      rw [hreal]
    _ = _ := by rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg, pow_two]

/-- The strict first-ratio tail is the matching truncated squared RN density. -/
theorem tailPower_one_eq_lintegral_sq_density [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) {q : ℝ} (hq : 1 < q) :
    tailPower μ ν q 1 = ∫⁻ x,
      (if q < (μ.rnDeriv ν x).toReal then ENNReal.ofReal ((μ.rnDeriv ν x).toReal ^ 2)
        else 0) ∂ν := by
  rw [tailPower_eq_lintegral_density hμν]
  apply lintegral_congr
  intro x
  simp only [llr, one_mul, log_cutoff_lt_log_iff hq ENNReal.toReal_nonneg]
  split_ifs with hx
  · rw [Real.exp_log ((zero_lt_one.trans hq).trans hx), pow_two]
  · rfl

/-- The forward RN density integrates to the probability mass. -/
theorem lintegral_ofReal_rnDeriv_eq_one [IsProbabilityMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) :
    ∫⁻ x, ENNReal.ofReal (μ.rnDeriv ν x).toReal ∂ν = 1 := by
  calc
    _ = ∫⁻ x, μ.rnDeriv ν x ∂ν := by
      apply lintegral_congr_ae
      filter_upwards [Measure.rnDeriv_lt_top μ ν] with x hx
      exact ENNReal.ofReal_toReal hx.ne
    _ = _ := by rw [Measure.lintegral_rnDeriv hμν]; simp

/-- Cauchy--Schwarz for the cross term, as an extended nonnegative Holder inequality. -/
theorem lintegral_sqrt_density_cross_le [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) :
    (∫⁻ x, ENNReal.ofReal (Real.sqrt (μ.rnDeriv ν x).toReal *
        |Real.sqrt (μ.rnDeriv ν x).toReal - 1|) ∂ν) ≤
      hellingerSq μ ν ^ (1 / 2 : ℝ) := by
  have hf : Measurable (fun x ↦ ENNReal.ofReal (μ.rnDeriv ν x).toReal) := by fun_prop
  have hg : Measurable (fun x ↦ ENNReal.ofReal ((Real.sqrt (μ.rnDeriv ν x).toReal - 1) ^ 2)) := by
    fun_prop
  have hh := ENNReal.lintegral_mul_norm_pow_le (μ := ν)
    (f := fun x ↦ ENNReal.ofReal (μ.rnDeriv ν x).toReal)
    (g := fun x ↦ ENNReal.ofReal ((Real.sqrt (μ.rnDeriv ν x).toReal - 1) ^ 2))
    hf.aemeasurable hg.aemeasurable
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  calc
    _ = ∫⁻ x, ENNReal.ofReal (μ.rnDeriv ν x).toReal ^ (1 / 2 : ℝ) *
        ENNReal.ofReal ((Real.sqrt (μ.rnDeriv ν x).toReal - 1) ^ 2) ^ (1 / 2 : ℝ) ∂ν := by
      apply lintegral_congr
      intro x
      rw [ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
        ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num),
        ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs,
        ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    _ ≤ _ := hh
    _ = _ := by
      rw [lintegral_ofReal_rnDeriv_eq_one hμν, ← hellingerSq_eq_lintegral_of_ac hμν]
      simp

/-- The refined full-moment bound at an arbitrary fixed cutoff. Singular support
and infinite full/tail moments are retained. -/
theorem fullRatioMoment_le_tailPower_add_sqrt_hellinger [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {q : ℝ} (hq : 1 < q) :
    fullRatioMoment μ ν ≤ tailPower μ ν q 1 +
      ENNReal.ofReal (refinedMomentCoeff q) * hellingerSq μ ν ^ (1 / 2 : ℝ) + 1 := by
  classical
  by_cases hμν : μ ≪ ν
  · let r : α → ℝ := fun x ↦ (μ.rnDeriv ν x).toReal
    let t : α → ℝ≥0∞ := fun x ↦ if q < r x then ENNReal.ofReal ((r x) ^ 2) else 0
    let c : α → ℝ := fun x ↦ Real.sqrt (r x) * |Real.sqrt (r x) - 1|
    have hr : ∀ x, 0 ≤ r x := fun _ ↦ ENNReal.toReal_nonneg
    have hc : ∀ x, 0 ≤ c x := fun x ↦ mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
    have hC : 0 ≤ refinedMomentCoeff q := (refinedMomentCoeff_pos hq).le
    have htmeas : Measurable t := by
      dsimp [t]
      exact Measurable.ite (measurableSet_lt measurable_const (by dsimp [r]; fun_prop))
        (by dsimp [r]; fun_prop) measurable_const
    have hrmeas : Measurable (fun x ↦ ENNReal.ofReal (r x)) := by dsimp [r]; fun_prop
    have hpoint : ∀ x, ENNReal.ofReal ((r x) ^ 2) ≤
        t x + ENNReal.ofReal (r x) + ENNReal.ofReal (refinedMomentCoeff q) * ENNReal.ofReal (c x) := by
      intro x
      have hh := ENNReal.ofReal_le_ofReal (refined_moment_density_bound hq (hr x))
      have htnonneg : 0 ≤ (if q < r x then (r x) ^ 2 else 0) := by split_ifs <;> positivity
      rw [ENNReal.ofReal_add (add_nonneg htnonneg (hr x)) (mul_nonneg hC (hc x)),
        ENNReal.ofReal_add htnonneg (hr x), ENNReal.ofReal_mul hC] at hh
      simpa only [t, c, apply_ite ENNReal.ofReal, ENNReal.ofReal_zero] using hh
    rw [fullRatioMoment_eq_lintegral_sq_density hμν]
    change (∫⁻ x, ENNReal.ofReal ((r x) ^ 2) ∂ν) ≤ _
    calc
      _ ≤ ∫⁻ x, t x + ENNReal.ofReal (r x) +
          ENNReal.ofReal (refinedMomentCoeff q) * ENNReal.ofReal (c x) ∂ν :=
        lintegral_mono hpoint
      _ = (∫⁻ x, t x ∂ν) + (∫⁻ x, ENNReal.ofReal (r x) ∂ν) +
          ENNReal.ofReal (refinedMomentCoeff q) * ∫⁻ x, ENNReal.ofReal (c x) ∂ν := by
        calc
          _ = (∫⁻ x, t x + ENNReal.ofReal (r x) ∂ν) +
              ∫⁻ x, ENNReal.ofReal (refinedMomentCoeff q) * ENNReal.ofReal (c x) ∂ν := by
            simpa only [Pi.add_apply] using
              (lintegral_add_left (htmeas.add hrmeas)
                (fun x ↦ ENNReal.ofReal (refinedMomentCoeff q) * ENNReal.ofReal (c x)))
          _ = _ := by
            have hadd : (∫⁻ x, t x + ENNReal.ofReal (r x) ∂ν) =
                (∫⁻ x, t x ∂ν) + (∫⁻ x, ENNReal.ofReal (r x) ∂ν) := by
              simpa only [Pi.add_apply] using
                (lintegral_add_left htmeas (fun x ↦ ENNReal.ofReal (r x)))
            rw [hadd, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ = tailPower μ ν q 1 + 1 +
          ENNReal.ofReal (refinedMomentCoeff q) * ∫⁻ x, ENNReal.ofReal (c x) ∂ν := by
        rw [tailPower_one_eq_lintegral_sq_density hμν hq, lintegral_ofReal_rnDeriv_eq_one hμν]
      _ ≤ tailPower μ ν q 1 + 1 +
          ENNReal.ofReal (refinedMomentCoeff q) * hellingerSq μ ν ^ (1 / 2 : ℝ) :=
        add_le_add le_rfl (mul_le_mul_right (lintegral_sqrt_density_cross_le hμν) _)
      _ = _ := by ac_rfl
  · simp [fullRatioMoment_of_not_ac hμν, tailPower_of_not_ac hμν]

/-- The exact printed coefficient six at the source cutoff four. -/
theorem fullRatioMoment_le_tailPower_four_add_sqrt_hellinger [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    fullRatioMoment μ ν ≤ tailPower μ ν 4 1 + 6 * hellingerSq μ ν ^ (1 / 2 : ℝ) + 1 := by
  simpa only [refinedMomentCoeff_four, ENNReal.ofReal_ofNat] using
    (fullRatioMoment_le_tailPower_add_sqrt_hellinger (μ := μ) (ν := ν) (q := 4) (by norm_num))

end Hellinger.Comparison
