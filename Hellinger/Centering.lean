/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.Definitions
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Finite-KL centering of extended nonnegative log moments. -/

public section

open MeasureTheory Set
open scoped ENNReal

namespace Hellinger

variable {α : Type*} [MeasurableSpace α]

/-- For probabilities with finite KL, its real value is the integrable log-likelihood mean. -/
theorem kl_toReal_eq_integral_llr (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hKL : FiniteKL μ ν) :
    (kl μ ν).toReal = ∫ x, llr μ ν x ∂μ := by
  simpa [kl, measureReal_def] using
    (InformationTheory.toReal_klDiv (finiteKL_ac hKL) (finiteKL_integrable_llr hKL))

/-- The real-power triangle estimate obtained by convexity at the midpoint. -/
theorem abs_sub_rpow_le_two_rpow_half_mul {k : ℝ} (hk : 1 ≤ k) (a b : ℝ) :
    |a - b| ^ k ≤ ((2 : ℝ) ^ k / 2) * (|a| ^ k + |b| ^ k) := by
  have hk0 : 0 ≤ k := by linarith
  have hc := (convexOn_rpow hk).2
    (show (0 : ℝ) ≤ 2 * |a| by positivity)
    (show (0 : ℝ) ≤ 2 * |b| by positivity)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simp only [smul_eq_mul] at hc
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg a),
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg b)] at hc
  have hmid : (|a| + |b|) ^ k ≤ ((2 : ℝ) ^ k / 2) * (|a| ^ k + |b| ^ k) := by
    convert hc using 1
    · congr 1
      ring
    · ring
  exact (Real.rpow_le_rpow (abs_nonneg _)
    (by simpa only [Real.norm_eq_abs] using norm_sub_le a b) hk0).trans hmid

/-- Jensen bounds the finite log-likelihood mean by the uncentered extended moment.
No finite-moment hypothesis is needed in this statement. -/
theorem abs_kl_toReal_rpow_le_logMoment (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {k : ℝ}
    (hk : 1 ≤ k) (hKL : FiniteKL μ ν) :
    ENNReal.ofReal (|(kl μ ν).toReal| ^ k) ≤ logMoment μ ν k := by
  by_cases hV : logMoment μ ν k = ∞
  · simp [hV]
  have hac := finiteKL_ac hKL
  rw [logMoment_of_ac hac] at hV ⊢
  have hk0 : 0 ≤ k := by linarith
  have hpow_meas : Measurable (fun x ↦ |llr μ ν x| ^ k) :=
    (Real.continuous_rpow_const hk0).measurable.comp
      (continuous_abs.measurable.comp (measurable_llr μ ν))
  have hpow_nn : 0 ≤ᵐ[μ] (fun x ↦ |llr μ ν x| ^ k) :=
    Filter.Eventually.of_forall fun x ↦ Real.rpow_nonneg (abs_nonneg _) _
  have hpow_int : Integrable (fun x ↦ |llr μ ν x| ^ k) μ :=
    (lintegral_ofReal_ne_top_iff_integrable hpow_meas.aestronglyMeasurable hpow_nn).mp hV
  have hj := (convexOn_rpow hk).map_integral_le
    (Real.continuous_rpow_const hk0).continuousOn isClosed_Ici
    (Filter.Eventually.of_forall fun x ↦ abs_nonneg (llr μ ν x))
    (finiteKL_integrable_llr hKL).abs hpow_int
  have hr : |∫ x, llr μ ν x ∂μ| ^ k ≤ ∫ x, |llr μ ν x| ^ k ∂μ :=
    (Real.rpow_le_rpow (abs_nonneg _) abs_integral_le_integral_abs hk0).trans hj
  rw [← ofReal_integral_eq_lintegral_ofReal hpow_int hpow_nn,
    kl_toReal_eq_integral_llr μ ν hKL]
  exact ENNReal.ofReal_le_ofReal hr

/-- The upper form of the centered comparison. The uncentered moment may be infinite. -/
theorem centeredLogMoment_le_two_rpow_logMoment (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {k : ℝ}
    (hk : 2 ≤ k) (hKL : FiniteKL μ ν) :
    centeredLogMoment μ ν k hKL ≤ ENNReal.ofReal ((2 : ℝ) ^ k) * logMoment μ ν k := by
  have hk1 : 1 ≤ k := by linarith
  have hc0 : 0 ≤ (2 : ℝ) ^ k / 2 :=
    div_nonneg (Real.rpow_pos_of_pos (by norm_num) _).le (by norm_num)
  have hm := abs_kl_toReal_rpow_le_logMoment μ ν hk1 hKL
  have hcoeff : ENNReal.ofReal ((2 : ℝ) ^ k / 2) +
      ENNReal.ofReal ((2 : ℝ) ^ k / 2) = ENNReal.ofReal ((2 : ℝ) ^ k) := by
    rw [← ENNReal.ofReal_add hc0 hc0]
    congr 1
    ring
  unfold centeredLogMoment
  calc
    (∫⁻ x, ENNReal.ofReal (|llr μ ν x - (kl μ ν).toReal| ^ k) ∂μ) ≤
        ∫⁻ x, ENNReal.ofReal ((2 : ℝ) ^ k / 2) *
          (ENNReal.ofReal (|llr μ ν x| ^ k) +
            ENNReal.ofReal (|(kl μ ν).toReal| ^ k)) ∂μ := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [← ENNReal.ofReal_add (Real.rpow_nonneg (abs_nonneg _) _)
          (Real.rpow_nonneg (abs_nonneg _) _), ← ENNReal.ofReal_mul hc0]
      exact ENNReal.ofReal_le_ofReal (abs_sub_rpow_le_two_rpow_half_mul hk1 _ _)
    _ = ENNReal.ofReal ((2 : ℝ) ^ k / 2) *
        (logMoment μ ν k + ENNReal.ofReal (|(kl μ ν).toReal| ^ k)) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_add_right _ measurable_const]
      simp [logMoment_of_ac (finiteKL_ac hKL)]
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ k / 2) * (logMoment μ ν k + logMoment μ ν k) :=
      mul_le_mul' le_rfl (add_le_add le_rfl hm)
    _ = _ := by rw [mul_add, ← add_mul, hcoeff]

/-- The centered log-moment comparison with its exact coefficient `2^(-k)`.
Finite KL is required only to define its real mean; no finite-moment assumption is imposed. -/
theorem two_neg_rpow_mul_centeredLogMoment_le_logMoment (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {k : ℝ}
    (hk : 2 ≤ k) (hKL : FiniteKL μ ν) :
    ENNReal.ofReal ((2 : ℝ) ^ (-k)) * centeredLogMoment μ ν k hKL ≤ logMoment μ ν k := by
  calc
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (-k)) *
        (ENNReal.ofReal ((2 : ℝ) ^ k) * logMoment μ ν k) :=
      mul_le_mul' le_rfl (centeredLogMoment_le_two_rpow_logMoment μ ν hk hKL)
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul
        (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-k)).le,
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      simp

end Hellinger
