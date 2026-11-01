/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.Comparison.Examples.NormalTail
public import Mathlib.Analysis.Calculus.LHopital

/-! The genuine standard-normal Mills asymptotic, obtained from the derivatives
of the already integrable upper tail and density. No Gaussian tail limit is assumed. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace Hellinger.Comparison.Examples.Normal

theorem hasDerivAt_phi (x : ℝ) : HasDerivAt phi (-x * phi x) x := by
  have hquad : HasDerivAt (fun y : ℝ ↦ -y ^ 2 / 2) (-x) x := by
    convert (((hasDerivAt_id' x).pow 2).neg.div_const 2) using 1 <;>
      first
      | (funext y; simp only [Pi.pow_apply, Pi.neg_apply, Pi.div_apply, id_eq] <;> ring)
      | ring
  have hh := hquad.exp.const_mul ((Real.sqrt (2 * Real.pi))⁻¹)
  convert hh using 1 <;>
    first
    | (funext y; simp only [phi, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero] <;> ring)
    | (simp only [phi, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero] <;> ring)

theorem tendsto_phi_atTop : Tendsto phi atTop (𝓝 0) := by
  have hquad : Tendsto (fun x : ℝ ↦ x ^ 2 / 2) atTop atTop :=
    Filter.Tendsto.atTop_div_const (by norm_num : (0 : ℝ) < 2)
      (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0))
  have hh := (Real.tendsto_exp_neg_atTop_nhds_zero.comp hquad).const_mul
    ((Real.sqrt (2 * Real.pi))⁻¹)
  have hfun : phi = fun x : ℝ ↦ (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2 / 2)) := by
    funext x
    simp only [phi, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, neg_div]
  rw [hfun]
  simpa only [Function.comp_def, mul_zero] using hh

theorem hasDerivAt_phi_div {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y ↦ phi y / y) (-phi x * (1 + 1 / x ^ 2)) x := by
  convert (hasDerivAt_phi x).div (hasDerivAt_id' x) hx using 1 <;>
    first
    | (funext y; simp only [Pi.div_apply, id_eq, div_eq_mul_inv] <;> ring)
    | (field_simp [hx] <;> ring)

theorem tendsto_phi_div_atTop : Tendsto (fun x : ℝ ↦ phi x / x) atTop (𝓝 0) :=
  tendsto_phi_atTop.div_atTop tendsto_id

noncomputable def millsRatio (z : ℝ) : ℝ := upperTail z / (phi z / z)

theorem millsRatio_pos {z : ℝ} (hz : 0 < z) : 0 < millsRatio z :=
  div_pos (upperTail_pos z) (div_pos (phi_pos z) hz)

/-- The exact asymptotic applies to the actual normalized Gaussian upper tail. -/
theorem tendsto_millsRatio_atTop : Tendsto millsRatio atTop (𝓝 1) := by
  change Tendsto (fun x : ℝ ↦ upperTail x / (phi x / x)) atTop (𝓝 1)
  refine HasDerivAt.lhopital_zero_atTop_on_Ioi (a := 0)
    (fun x _ ↦ hasDerivAt_upperTail x)
    (fun x hx ↦ hasDerivAt_phi_div (show x ≠ 0 from (show 0 < x from hx).ne'))
    (fun x _ ↦ mul_ne_zero (neg_ne_zero.mpr (phi_pos x).ne')
      (ne_of_gt (by positivity : 0 < 1 + 1 / x ^ 2)))
    tendsto_upperTail_atTop tendsto_phi_div_atTop ?_
  have hinv : Tendsto (fun x : ℝ ↦ 1 / x ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0))
  have haux : Tendsto (fun x : ℝ ↦ 1 / (1 + 1 / x ^ 2)) atTop (𝓝 1) := by
    have hone : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hh := hone.div (hone.add hinv) (by norm_num : (1 : ℝ) + 0 ≠ 0)
    change Tendsto (fun x : ℝ ↦ 1 / (1 + 1 / x ^ 2)) atTop (𝓝 ((1 : ℝ) / (1 + 0))) at hh
    simpa only [add_zero, div_one] using hh
  apply haux.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hp : phi x ≠ 0 := (phi_pos x).ne'
  have hd : 1 + 1 / x ^ 2 ≠ 0 := ne_of_gt (by positivity : 0 < 1 + 1 / x ^ 2)
  field_simp [hx.ne', hp, hd] <;> ring

/-- The positive-parameter representation is used only on `s>0` for its rare-tail limit. -/
noncomputable def rareCutoff (b s : ℝ) : ℝ := Real.log b / s - s / 2

noncomputable def conditionalTailFormula (b s : ℝ) : ℝ :=
  Real.exp (s ^ 2) * upperTail (rareCutoff b s - s) / upperTail (rareCutoff b s)

theorem conditionalRatioMean_eq_conditionalTailFormula {theta b : ℝ}
    (htheta : theta ≠ 0) (hb : 0 < b) :
    conditionalRatioMean (normalLaw 0) (normalLaw theta) b =
      ENNReal.ofReal (conditionalTailFormula b |theta|) := by
  simpa only [conditionalTailFormula, rareCutoff, ratioCutoff_eq htheta, sq_abs] using
    conditionalRatioMean_normalLaw_formula htheta hb

theorem continuousOn_conditionalTailFormula (b : ℝ) :
    ContinuousOn (conditionalTailFormula b) (Ioi 0) := by
  intro s hs
  have hsne : s ≠ 0 := (show 0 < s from hs).ne'
  have hz : ContinuousAt (rareCutoff b) s := by
    unfold rareCutoff
    exact (continuousAt_const.div continuousAt_id hsne).sub (continuousAt_id.div_const 2)
  have hE : ContinuousAt (fun u : ℝ ↦ Real.exp (u ^ 2)) s := by fun_prop
  have hN : ContinuousAt (fun u ↦ upperTail (rareCutoff b u - u)) s :=
    continuous_upperTail.continuousAt.comp (hz.sub continuousAt_id)
  have hD : ContinuousAt (fun u ↦ upperTail (rareCutoff b u)) s :=
    continuous_upperTail.continuousAt.comp hz
  exact ((hE.mul hN).div hD (upperTail_pos _).ne').continuousWithinAt

end Hellinger.Comparison.Examples.Normal
