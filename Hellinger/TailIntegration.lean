/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.Definitions
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! Nonnegative density identities; no integrability or finite-moment premise is used. -/
@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Hellinger

variable {α : Type*} {mα : MeasurableSpace α}
variable {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- Change measure for any measurable real kernel after nonnegative truncation. -/
theorem lintegral_ofReal_eq_lintegral_density (h : μ ≪ ν) {f : α → ℝ}
    (hf : Measurable f) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ) =
      ∫⁻ x, ENNReal.ofReal ((μ.rnDeriv ν x).toReal * f x) ∂ν := by
  calc
    _ = ∫⁻ x, μ.rnDeriv ν x * ENNReal.ofReal (f x) ∂ν :=
      (lintegral_rnDeriv_mul h hf.ennreal_ofReal.aemeasurable).symm
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [Measure.rnDeriv_lt_top μ ν] with x hx
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx.ne]

/-- Restricted nonnegative change of measure, presented as a full density integral. -/
theorem setLIntegral_ofReal_eq_lintegral_density (h : μ ≪ ν) {f : α → ℝ}
    (hf : Measurable f) {s : Set α} (hs : MeasurableSet s) :
    (∫⁻ x in s, ENNReal.ofReal (f x) ∂μ) =
      ∫⁻ x, s.indicator (fun y ↦ ENNReal.ofReal ((μ.rnDeriv ν y).toReal * f y)) x ∂ν := by
  classical
  calc
    _ = ∫⁻ x in s, μ.rnDeriv ν x * ENNReal.ofReal (f x) ∂ν :=
      (setLIntegral_rnDeriv_mul h hf.ennreal_ofReal.aemeasurable hs).symm
    _ = ∫⁻ x in s, ENNReal.ofReal ((μ.rnDeriv ν x).toReal * f x) ∂ν := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_of_ae (Measure.rnDeriv_lt_top μ ν)] with x hx
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx.ne]
    _ = _ := (lintegral_indicator hs
      (fun x ↦ ENNReal.ofReal ((μ.rnDeriv ν x).toReal * f x))).symm

/-- The log tail as a density integral, with extended values and arbitrary real parameters. -/
theorem tailLogMoment_eq_lintegral_density (h : μ ≪ ν) (c k : ℝ) :
    tailLogMoment μ ν c k =
      ∫⁻ x, if Real.log c < llr μ ν x then
        ENNReal.ofReal ((μ.rnDeriv ν x).toReal * (llr μ ν x) ^ k) else 0 ∂ν := by
  rw [tailLogMoment_of_ac h]
  simpa only [Set.indicator_apply, tailEvent, Set.mem_ofPred_eq, Pi.mul_apply] using
    (setLIntegral_ofReal_eq_lintegral_density h ((measurable_llr μ ν).pow_const k)
      (measurableSet_tailEvent μ ν c))

/-- The power tail as a density integral, without a finite-tail assumption. -/
theorem tailPower_eq_lintegral_density (h : μ ≪ ν) (c δ : ℝ) :
    tailPower μ ν c δ =
      ∫⁻ x, if Real.log c < llr μ ν x then
        ENNReal.ofReal ((μ.rnDeriv ν x).toReal * Real.exp (δ * llr μ ν x)) else 0 ∂ν := by
  rw [tailPower_of_ac h]
  simpa only [Set.indicator_apply, tailEvent, Set.mem_ofPred_eq, Pi.mul_apply] using
    (setLIntegral_ofReal_eq_lintegral_density h
      (measurable_const.mul (measurable_llr μ ν)).exp (measurableSet_tailEvent μ ν c))

/-- The uncentered absolute log moment as a density integral, including infinity. -/
theorem logMoment_eq_lintegral_density (h : μ ≪ ν) (k : ℝ) :
    logMoment μ ν k =
      ∫⁻ x, ENNReal.ofReal ((μ.rnDeriv ν x).toReal * |llr μ ν x| ^ k) ∂ν := by
  rw [logMoment_of_ac h]
  apply lintegral_ofReal_eq_lintegral_density h
  simpa only [Real.norm_eq_abs] using (measurable_llr μ ν).norm.pow_const k

/-- The Bernstein functional as a density integral, including infinity. -/
theorem bernsteinSq_eq_lintegral_density (h : μ ≪ ν) (δ : ℝ) :
    bernsteinSq μ ν δ =
      ∫⁻ x, ENNReal.ofReal
        ((μ.rnDeriv ν x).toReal * bernsteinKernel δ (llr μ ν x)) ∂ν := by
  rw [bernsteinSq_of_ac h]
  apply lintegral_ofReal_eq_lintegral_density h
  unfold bernsteinKernel
  fun_prop

end Hellinger
