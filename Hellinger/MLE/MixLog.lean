/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.MLE.Defs

/-!
The criterion of the direct proof: `m_f = log((p₀ + f)/(2 p₀))`, the log-ratio of the mixture
`(p₀ + f)/2` against `p₀`, set to `0` on the fixed set `{p₀ = 0}` (of `P₀`-probability zero).
It is defined for every nonnegative function `f`, so that bracket endpoints transform too.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Hellinger.MLE

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-- `m_f = log((p₀ + f)/(2 p₀))` on `{p₀ > 0}`, and `0` on `{p₀ = 0}`. -/
noncomputable def mixLog (p₀ f : 𝒳 → ℝ≥0) (x : 𝒳) : ℝ :=
  if p₀ x = 0 then 0 else Real.log (((p₀ x : ℝ) + f x) / (2 * p₀ x))

/-- The transformed class `{m_p : p ∈ F}`. -/
def mixLogClass (p₀ : 𝒳 → ℝ≥0) (F : Set (𝒳 → ℝ≥0)) : Set (𝒳 → ℝ) := mixLog p₀ '' F

/-- The mixture `(p₀ + f)/2`. -/
noncomputable def mixDensity (p₀ f : 𝒳 → ℝ≥0) : 𝒳 → ℝ≥0 := fun x ↦ (p₀ x + f x) / 2

/-- The log-ratio `log(p₀/q)` of real values; used only where both values are positive. -/
noncomputable def logRatio (p₀ q : 𝒳 → ℝ≥0) (x : 𝒳) : ℝ := Real.log ((p₀ x : ℝ) / q x)

omit [MeasurableSpace 𝒳] in
theorem mixLog_of_pos {p₀ f : 𝒳 → ℝ≥0} {x : 𝒳} (hx : 0 < p₀ x) :
    mixLog p₀ f x = Real.log (((p₀ x : ℝ) + f x) / (2 * p₀ x)) := by
  simp [mixLog, hx.ne']

omit [MeasurableSpace 𝒳] in
theorem mixLog_of_eq_zero {p₀ f : 𝒳 → ℝ≥0} {x : 𝒳} (hx : p₀ x = 0) : mixLog p₀ f x = 0 := by
  simp [mixLog, hx]

theorem measurable_mixLog {p₀ f : 𝒳 → ℝ≥0} (hp₀ : Measurable p₀) (hf : Measurable f) :
    Measurable (mixLog p₀ f) := by
  unfold mixLog
  refine Measurable.ite (measurableSet_eq_fun hp₀ measurable_const) measurable_const ?_
  exact Real.measurable_log.comp
    (((measurable_coe_nnreal_real.comp hp₀).add (measurable_coe_nnreal_real.comp hf)).div
      (measurable_const.mul (measurable_coe_nnreal_real.comp hp₀)))

theorem measurable_logRatio {p₀ q : 𝒳 → ℝ≥0} (hp₀ : Measurable p₀) (hq : Measurable q) :
    Measurable (logRatio p₀ q) :=
  Real.measurable_log.comp
    ((measurable_coe_nnreal_real.comp hp₀).div (measurable_coe_nnreal_real.comp hq))

omit [MeasurableSpace 𝒳] in
/-- `m_f` is monotone in `f`, so brackets transform to brackets. -/
theorem mixLog_mono (p₀ : 𝒳 → ℝ≥0) {f g : 𝒳 → ℝ≥0} (h : f ≤ g) : mixLog p₀ f ≤ mixLog p₀ g := by
  intro x
  rcases eq_zero_or_pos (p₀ x) with hx | hx
  · simp [mixLog_of_eq_zero hx]
  rw [mixLog_of_pos hx, mixLog_of_pos hx]
  have hpx : (0 : ℝ) < p₀ x := by exact_mod_cast hx
  refine Real.log_le_log (by positivity) ?_
  gcongr
  exact_mod_cast h x

omit [MeasurableSpace 𝒳] in
/-- `m_f ≥ -log 2` everywhere. -/
theorem neg_log_two_le_mixLog (p₀ f : 𝒳 → ℝ≥0) (x : 𝒳) : -Real.log 2 ≤ mixLog p₀ f x := by
  rcases eq_zero_or_pos (p₀ x) with hx | hx
  · rw [mixLog_of_eq_zero hx, neg_nonpos]; exact (Real.log_pos (by norm_num)).le
  rw [mixLog_of_pos hx, ← Real.log_inv]
  have hpx : (0 : ℝ) < p₀ x := by exact_mod_cast hx
  refine Real.log_le_log (by norm_num) ?_
  rw [le_div_iff₀ (by positivity)]
  have : (0 : ℝ) ≤ f x := (f x).coe_nonneg
  nlinarith

omit [MeasurableSpace 𝒳] in
theorem mixDensity_coe (p₀ f : 𝒳 → ℝ≥0) (x : 𝒳) :
    ((mixDensity p₀ f x : ℝ≥0) : ℝ) = ((p₀ x : ℝ) + f x) / 2 := by
  simp [mixDensity]

end Hellinger.MLE
