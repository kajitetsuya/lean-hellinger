/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.Comparison.Examples.NormalMills

/-! Rare-event normal conditional means. Their nonzero-parameter limit equals
the conditioning threshold; the actual null-event mean at zero is separate. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace Hellinger.Comparison.Examples.Normal

theorem tendsto_rareCutoff_zero {b : ℝ} (hb : 1 < b) :
    Tendsto (rareCutoff b) (𝓝[>] 0) atTop := by
  have hs : Tendsto (fun s : ℝ ↦ s) (𝓝[>] 0) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_right nhdsWithin_le_nhds
  have hc : Tendsto (fun s : ℝ ↦ Real.log b - s ^ 2 / 2)
      (𝓝[>] 0) (𝓝 (Real.log b)) := by
    simpa using tendsto_const_nhds.sub ((hs.pow 2).div_const 2)
  have hh := hc.pos_mul_atTop (Real.log_pos hb) tendsto_inv_nhdsGT_zero
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hsne : s ≠ 0 := (show 0 < s from hs).ne'
  unfold rareCutoff
  field_simp [hsne] <;> ring

theorem tendsto_shiftedRareCutoff_zero {b : ℝ} (hb : 1 < b) :
    Tendsto (fun s ↦ rareCutoff b s - s) (𝓝[>] 0) atTop := by
  have hs : Tendsto (fun s : ℝ ↦ s) (𝓝[>] 0) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_right nhdsWithin_le_nhds
  have hc : Tendsto (fun s : ℝ ↦ Real.log b - 3 * s ^ 2 / 2)
      (𝓝[>] 0) (𝓝 (Real.log b)) := by
    simpa using tendsto_const_nhds.sub ((tendsto_const_nhds.mul (hs.pow 2)).div_const 2)
  have hh := hc.pos_mul_atTop (Real.log_pos hb) tendsto_inv_nhdsGT_zero
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hsne : s ≠ 0 := (show 0 < s from hs).ne'
  unfold rareCutoff
  field_simp [hsne] <;> ring

theorem rare_density_tilt {b s : ℝ} (hb : 0 < b) (hs : s ≠ 0) :
    Real.exp (s ^ 2) * phi (rareCutoff b s - s) = b * phi (rareCutoff b s) := by
  have hform (x : ℝ) : phi x = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) := by
    simp [phi, gaussianPDFReal]
  have hexp : s ^ 2 + -(rareCutoff b s - s) ^ 2 / 2 =
      Real.log b + -(rareCutoff b s) ^ 2 / 2 := by
    unfold rareCutoff
    field_simp [hs] <;> ring
  rw [hform, hform]
  calc
    _ = (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.exp (s ^ 2 + -(rareCutoff b s - s) ^ 2 / 2) := by
      rw [Real.exp_add]
      ring
    _ = (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.exp (Real.log b + -(rareCutoff b s) ^ 2 / 2) := by rw [hexp]
    _ = _ := by rw [Real.exp_add, Real.exp_log hb]; ring

theorem conditionalTailFormula_eq_mills {b s : ℝ} (hb : 0 < b) (hs : 0 < s)
    (hz : 0 < rareCutoff b s) (hw : 0 < rareCutoff b s - s) :
    conditionalTailFormula b s = b * (rareCutoff b s / (rareCutoff b s - s)) *
      (millsRatio (rareCutoff b s - s) / millsRatio (rareCutoff b s)) := by
  have hpz := (phi_pos (rareCutoff b s)).ne'
  have hpw := (phi_pos (rareCutoff b s - s)).ne'
  have hq := (upperTail_pos (rareCutoff b s)).ne'
  have he : Real.exp (s ^ 2) * phi (rareCutoff b s - s) / phi (rareCutoff b s) = b :=
    (div_eq_iff hpz).mpr (rare_density_tilt hb hs.ne')
  calc
    _ = (Real.exp (s ^ 2) * phi (rareCutoff b s - s) / phi (rareCutoff b s)) *
        (rareCutoff b s / (rareCutoff b s - s)) *
        (millsRatio (rareCutoff b s - s) / millsRatio (rareCutoff b s)) := by
      unfold conditionalTailFormula millsRatio
      field_simp [hpz, hpw, hq, hz.ne', hw.ne'] <;> ring
    _ = _ := by rw [he]

theorem tendsto_rareCutoff_ratio_zero {b : ℝ} (hb : 1 < b) :
    Tendsto (fun s ↦ rareCutoff b s / (rareCutoff b s - s)) (𝓝[>] 0) (𝓝 1) := by
  have hs : Tendsto (fun s : ℝ ↦ s) (𝓝[>] 0) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_right nhdsWithin_le_nhds
  have hnum : Tendsto (fun s : ℝ ↦ Real.log b - s ^ 2 / 2)
      (𝓝[>] 0) (𝓝 (Real.log b)) := by
    simpa using tendsto_const_nhds.sub ((hs.pow 2).div_const 2)
  have hden : Tendsto (fun s : ℝ ↦ Real.log b - 3 * s ^ 2 / 2)
      (𝓝[>] 0) (𝓝 (Real.log b)) := by
    simpa using tendsto_const_nhds.sub ((tendsto_const_nhds.mul (hs.pow 2)).div_const 2)
  have hh : Tendsto (fun s : ℝ ↦
      (Real.log b - s ^ 2 / 2) / (Real.log b - 3 * s ^ 2 / 2)) (𝓝[>] 0) (𝓝 1) := by
    have hquot := hnum.div hden (Real.log_pos hb).ne'
    change Tendsto (fun s : ℝ ↦
      (Real.log b - s ^ 2 / 2) / (Real.log b - 3 * s ^ 2 / 2))
      (𝓝[>] 0) (𝓝 (Real.log b / Real.log b)) at hquot
    simpa only [div_self (Real.log_pos hb).ne'] using hquot
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin,
    (tendsto_shiftedRareCutoff_zero hb).eventually_gt_atTop 0] with s hs hw
  have hsne : s ≠ 0 := (show 0 < s from hs).ne'
  have hwne : rareCutoff b s - s ≠ 0 := hw.ne'
  have hdenne : Real.log b - 3 * s ^ 2 / 2 ≠ 0 := by
    have hid : Real.log b - 3 * s ^ 2 / 2 = s * (rareCutoff b s - s) := by
      unfold rareCutoff
      field_simp [hsne] <;> ring
    rw [hid]
    exact mul_ne_zero hsne hwne
  unfold rareCutoff at *
  field_simp [hsne, hdenne, hwne] <;> ring

/-- For every threshold b>1 the genuine Gaussian rare-tail mean tends to b. -/
theorem tendsto_conditionalTailFormula_zero {b : ℝ} (hb : 1 < b) :
    Tendsto (conditionalTailFormula b) (𝓝[>] 0) (𝓝 b) := by
  have hM := (tendsto_millsRatio_atTop.comp (tendsto_shiftedRareCutoff_zero hb)).div
    (tendsto_millsRatio_atTop.comp (tendsto_rareCutoff_zero hb)) (by norm_num : (1 : ℝ) ≠ 0)
  have hh : Tendsto (fun s ↦ b * (rareCutoff b s / (rareCutoff b s - s)) *
      (millsRatio (rareCutoff b s - s) / millsRatio (rareCutoff b s))) (𝓝[>] 0) (𝓝 b) := by
    simpa using (tendsto_const_nhds.mul (tendsto_rareCutoff_ratio_zero hb)).mul hM
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin,
    (tendsto_rareCutoff_zero hb).eventually_gt_atTop 0,
    (tendsto_shiftedRareCutoff_zero hb).eventually_gt_atTop 0] with s hs hz hw
  exact (conditionalTailFormula_eq_mills (lt_trans zero_lt_one hb) hs hz hw).symm

/-- The paper's displayed threshold-e CDF quotient has limit e through
nonzero parameters, whereas its actual theta-zero conditional mean is zero. -/
theorem normal_exp_one_cdf_limit :
    Tendsto (fun theta : ℝ ↦ Real.exp (theta ^ 2) *
      cdf (normalLaw 0) (|theta| / 2 - 1 / |theta| + |theta|) /
      cdf (normalLaw 0) (|theta| / 2 - 1 / |theta|))
      (𝓝[≠] 0) (𝓝 (Real.exp 1)) := by
  have hbe : 1 < Real.exp (1 : ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
  have hh := (tendsto_conditionalTailFormula_zero (b := Real.exp 1) hbe).comp
    tendsto_abs_nhdsNE_zero
  apply hh.congr'
  filter_upwards [] with theta
  simp only [Function.comp_def]
  unfold conditionalTailFormula rareCutoff
  rw [sq_abs, Real.log_exp]
  simp only [upperTail_eq_cdf_neg]
  rw [show -(1 / |theta| - |theta| / 2 - |theta|) =
    |theta| / 2 - 1 / |theta| + |theta| by ring,
    show -(1 / |theta| - |theta| / 2) = |theta| / 2 - 1 / |theta| by ring]

end Hellinger.Comparison.Examples.Normal
