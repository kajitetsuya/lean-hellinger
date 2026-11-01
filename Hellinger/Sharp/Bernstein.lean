/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.Sharp.Statements
public import Hellinger.BernsteinBounds
public import Hellinger.Comparison.ConditionalMoment

/-!
Sharp lower Bernstein coefficient; improved upper Bernstein and CM ⇒ NC coefficients.
The `δ > 0` range of the lower bound extends the paper's stated domain `0 < δ ≤ 1`.

* Lower: `2 (1 - c^{-δ} (1 + δ log c)) T_δ ≤ B_δ²` for every `δ > 0`.
* Upper: `B_δ² ≤ 2 δ² (1 + √c)² H² + 2 T_δ` for `0 < δ ≤ 1`.
* CM: `T_1(q) ≤ 4 M² H²` for every ordinary cutoff `q ≥ 9/4`.

The arguments are summarized in `docs/SharpConstants.md`. Auxiliary lemmas live in the
sub-namespace `Hellinger.Sharp.Bernstein`; the exported results are in `Hellinger.Sharp`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace Hellinger.Sharp

universe u

/-! ### Scalar facts -/

namespace Bernstein

/-- `e^{-u} (1 + u)` is antitone on `[0, ∞)`, in multiplied-out form. -/
theorem one_add_le_exp_sub_mul {u₀ u : ℝ} (hu₀ : 0 ≤ u₀) (hu : u₀ ≤ u) :
    1 + u ≤ Real.exp (u - u₀) * (1 + u₀) := by
  have he := Real.add_one_le_exp (u - u₀)
  nlinarith [mul_le_mul_of_nonneg_right he (by linarith : (0 : ℝ) ≤ 1 + u₀),
    mul_nonneg hu₀ (sub_nonneg.mpr hu)]

theorem rpow_neg_eq_exp {c δ : ℝ} (hc : 0 < c) :
    c ^ (-δ) = Real.exp (-(δ * Real.log c)) := by
  rw [Real.rpow_def_of_pos hc]
  congr 1
  ring

end Bernstein

open Bernstein

theorem bernsteinLowerSharpCoeff_pos {c δ : ℝ} (hc : 1 < c) (hδ : 0 < δ) :
    0 < bernsteinLowerSharpCoeff c δ := by
  have hc0 : 0 < c := lt_trans (by norm_num) hc
  have hu : 0 < δ * Real.log c := mul_pos hδ (Real.log_pos hc)
  have hlt := Real.add_one_lt_exp hu.ne'
  have hE : Real.exp (-(δ * Real.log c)) * Real.exp (δ * Real.log c) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hEpos := Real.exp_pos (-(δ * Real.log c))
  unfold bernsteinLowerSharpCoeff
  rw [rpow_neg_eq_exp hc0]
  nlinarith [mul_lt_mul_of_pos_left hlt hEpos]

namespace Bernstein

/-- The sharp lower coefficient on the strict tail `t > log c`. -/
theorem bernsteinLowerSharpCoeff_mul_exp_le_bernsteinKernel {c δ t : ℝ}
    (hc : 1 < c) (hδ : 0 < δ) (ht : Real.log c < t) :
    bernsteinLowerSharpCoeff c δ * Real.exp (δ * t) ≤ bernsteinKernel δ t := by
  have hc0 : 0 < c := lt_trans (by norm_num) hc
  have hlog : 0 < Real.log c := Real.log_pos hc
  set u₀ := δ * Real.log c with hu₀def
  set u := δ * t with hudef
  have hu₀ : 0 ≤ u₀ := (mul_pos hδ hlog).le
  have hu₀u : u₀ ≤ u := by
    rw [hu₀def, hudef]; exact mul_le_mul_of_nonneg_left ht.le hδ.le
  have hu : 0 ≤ u := hu₀.trans hu₀u
  have hmono := one_add_le_exp_sub_mul hu₀ hu₀u
  have hsplit : Real.exp (u - u₀) = Real.exp u * Real.exp (-u₀) := by
    rw [← Real.exp_add]; ring_nf
  unfold bernsteinLowerSharpCoeff bernsteinKernel
  rw [rpow_neg_eq_exp hc0, ← hu₀def, ← hudef, abs_of_nonneg hu]
  rw [hsplit] at hmono
  nlinarith

end Bernstein

/-- Sharp forward-density lower Bernstein bound, for every `δ > 0`. -/
theorem bernstein_density_lower_sharp {c δ x : ℝ} (hc : 1 < c) (hδ : 0 < δ) (hx : 0 ≤ x) :
    bernsteinLowerSharpCoeff c δ * powerTailDensityKernel c δ x ≤
      x * bernsteinKernel δ (Real.log x) := by
  by_cases htail : Real.log c < Real.log x
  · rw [powerTailDensityKernel, ite_eq_left htail]
    calc
      _ = x * (bernsteinLowerSharpCoeff c δ * Real.exp (δ * Real.log x)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (bernsteinLowerSharpCoeff_mul_exp_le_bernsteinKernel hc hδ htail) hx
  · rw [powerTailDensityKernel, ite_eq_right htail, mul_zero]
    exact mul_nonneg hx (bernsteinKernel_nonneg _ _)

namespace Bernstein

/-- `sinh (δ u) ≤ δ sinh u` for `u ≥ 0` and `0 ≤ δ ≤ 1`. -/
theorem sinh_mul_le_mul_sinh {δ u : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hu : 0 ≤ u) :
    Real.sinh (δ * u) ≤ δ * Real.sinh u := by
  let F : ℝ → ℝ := fun v ↦ δ * Real.sinh v - Real.sinh (δ * v)
  have hF : ∀ v, HasDerivAt F (δ * Real.cosh v - Real.cosh (δ * v) * δ) v := by
    intro v
    have h1 := (Real.hasDerivAt_sinh v).const_mul δ
    have h2 := (Real.hasDerivAt_sinh (δ * v)).comp v ((hasDerivAt_id v).const_mul δ)
    simp only [mul_one] at h2
    exact h1.sub h2
  have hmono : MonotoneOn F (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact (continuous_iff_continuousAt.2 fun v ↦ (hF v).continuousAt).continuousOn
    · exact fun v _ ↦ (hF v).differentiableAt.differentiableWithinAt
    · intro v hv
      rw [interior_Ici] at hv
      have hv0 : 0 < v := hv
      rw [(hF v).deriv]
      have hcosh : Real.cosh (δ * v) ≤ Real.cosh v := by
        rw [Real.cosh_le_cosh, abs_of_nonneg (mul_nonneg hδ hv0.le), abs_of_pos hv0]
        nlinarith
      nlinarith
  have h := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 hu) hu
  simp only [F, mul_zero, Real.sinh_zero, sub_zero] at h
  linarith

theorem expSymmKernel_two_mul (s : ℝ) : expSymmKernel (2 * s) = 4 * Real.sinh s ^ 2 := by
  have h1 : expSymmKernel (2 * s) = 2 * Real.cosh (2 * s) - 2 := by
    unfold expSymmKernel; rw [Real.cosh_eq]; ring
  rw [h1, Real.cosh_two_mul, Real.cosh_sq]
  ring

/-- Quadratic scaling of the even exponential kernel: `Q(δ t) ≤ δ² Q(t)` for `0 ≤ δ ≤ 1`. -/
theorem expSymmKernel_mul_le_sq_mul {δ t : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    expSymmKernel (δ * t) ≤ δ ^ 2 * expSymmKernel t := by
  set s := |t| / 2 with hs
  have hs0 : 0 ≤ s := div_nonneg (abs_nonneg _) (by norm_num)
  have ht : expSymmKernel t = 4 * Real.sinh s ^ 2 := by
    rw [← expSymmKernel_abs t, ← expSymmKernel_two_mul]; congr 1; rw [hs]; ring
  have hδt : expSymmKernel (δ * t) = 4 * Real.sinh (δ * s) ^ 2 := by
    rw [← expSymmKernel_abs (δ * t), ← expSymmKernel_two_mul]
    congr 1; rw [hs, abs_mul, abs_of_nonneg hδ]; ring
  have h0 : 0 ≤ Real.sinh (δ * s) := Real.sinh_nonneg_iff.2 (mul_nonneg hδ hs0)
  have hle := pow_le_pow_left₀ h0 (sinh_mul_le_mul_sinh hδ hδ1 hs0) 2
  rw [ht, hδt]
  nlinarith

/-- The regular-region comparison with the coefficient `2 δ² (1 + √c)²`. -/
theorem bernstein_density_regular_upper_sq {c δ x : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hx : 0 < x) (hxc : x ≤ c) :
    x * bernsteinKernel δ (Real.log x) ≤
      bernsteinUpperSqCoeff c δ * (Real.sqrt x - 1) ^ 2 := by
  have hsand := bernsteinKernel_le_two_mul_expSymmKernel δ (Real.log x)
  have hscale := expSymmKernel_mul_le_sq_mul (t := Real.log x) hδ hδ1
  have hb : bernsteinKernel δ (Real.log x) ≤ 2 * δ ^ 2 * expSymmKernel (Real.log x) := by
    nlinarith
  have hsqrt := Real.sqrt_le_sqrt hxc
  have hsquare : (Real.sqrt x + 1) ^ 2 ≤ (Real.sqrt c + 1) ^ 2 :=
    pow_le_pow_left₀ (by linarith [Real.sqrt_nonneg x]) (by linarith) 2
  calc
    _ ≤ x * (2 * δ ^ 2 * expSymmKernel (Real.log x)) := mul_le_mul_of_nonneg_left hb hx.le
    _ = (2 * δ ^ 2 * (Real.sqrt x - 1) ^ 2) * (Real.sqrt x + 1) ^ 2 := by
      calc
        _ = 2 * δ ^ 2 * (x * expSymmKernel (Real.log x)) := by ring
        _ = _ := by rw [mul_expSymmKernel_log hx, sq_sub_one_eq_sqrt_factor hx.le]; ring
    _ ≤ (2 * δ ^ 2 * (Real.sqrt x - 1) ^ 2) * (Real.sqrt c + 1) ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare
        (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _))
    _ = _ := by unfold bernsteinUpperSqCoeff; ring

theorem bernsteinUpperSqCoeff_nonneg (c δ : ℝ) : 0 ≤ bernsteinUpperSqCoeff c δ := by
  unfold bernsteinUpperSqCoeff; positivity

end Bernstein

/-- Forward-density upper Bernstein bound with the coefficient `2 δ² (1 + √c)²`. -/
theorem bernstein_density_upper_sq {c δ x : ℝ} (hc : 1 < c) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hx : 0 ≤ x) :
    x * bernsteinKernel δ (Real.log x) ≤
      bernsteinUpperSqCoeff c δ * (Real.sqrt x - 1) ^ 2 +
        2 * powerTailDensityKernel c δ x := by
  by_cases hx0 : x = 0
  · subst x
    simpa [powerTailDensityKernel] using bernsteinUpperSqCoeff_nonneg c δ
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    by_cases htail : Real.log c < Real.log x
    · have harg : 0 ≤ δ * Real.log x :=
        mul_nonneg hδ.le ((Real.log_pos hc).trans htail).le
      have hb := mul_le_mul_of_nonneg_left (bernsteinKernel_le_two_mul_exp harg) hx
      have hregular : 0 ≤ bernsteinUpperSqCoeff c δ * (Real.sqrt x - 1) ^ 2 :=
        mul_nonneg (bernsteinUpperSqCoeff_nonneg c δ) (sq_nonneg _)
      rw [powerTailDensityKernel, ite_eq_left htail]
      calc
        _ ≤ 2 * (x * Real.exp (δ * Real.log x)) := by nlinarith
        _ ≤ _ := le_add_of_nonneg_left hregular
    · have hc0 : 0 < c := lt_trans (by norm_num) hc
      have hxc : x ≤ c := (Real.log_le_log_iff hxpos hc0).mp (le_of_not_gt htail)
      simpa only [powerTailDensityKernel, ite_eq_right htail, mul_zero, add_zero] using
        bernstein_density_regular_upper_sq hδ.le hδ1 hxpos hxc

/-! ### Measure-level Bernstein bounds -/

/-- Sharp lower Bernstein bound, for every `δ > 0`, including singular measures. -/
theorem bernsteinLowerSharpCoeff_mul_tailPower_le_bernsteinSq :
    BernsteinLowerSharpStatement.{u} := by
  intro α _ μ ν _ _ c δ hc hδ
  by_cases h : μ ≪ ν
  · rw [tailPower_eq_lintegral_densityKernel h, bernsteinSq_eq_lintegral_density h]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono
    intro x
    dsimp only
    rw [← ENNReal.ofReal_mul (bernsteinLowerSharpCoeff_pos hc hδ).le]
    exact ENNReal.ofReal_le_ofReal
      (bernstein_density_lower_sharp hc hδ ENNReal.toReal_nonneg)
  · simp [tailPower_of_not_ac h, bernsteinSq_of_not_ac h]

/-- Upper Bernstein bound with the coefficient `2 δ² (1 + √c)²`. -/
theorem bernsteinSq_le_hellinger_add_tailPower_sq : BernsteinUpperSqStatement.{u} := by
  intro α _ μ ν _ _ c δ hc hδ hδ1
  by_cases h : μ ≪ ν
  · rw [bernsteinSq_eq_lintegral_density h]
    have hg : Measurable (fun x ↦ ENNReal.ofReal
        ((Real.sqrt ((μ.rnDeriv ν x).toReal) - 1) ^ 2)) := by fun_prop
    calc
      _ ≤ ∫⁻ x, ENNReal.ofReal (bernsteinUpperSqCoeff c δ) *
            ENNReal.ofReal ((Real.sqrt ((μ.rnDeriv ν x).toReal) - 1) ^ 2) +
            (2 : ℝ≥0∞) * ENNReal.ofReal
              (powerTailDensityKernel c δ ((μ.rnDeriv ν x).toReal)) ∂ν := by
        apply lintegral_mono
        intro x
        have hp := ENNReal.ofReal_le_ofReal
          (bernstein_density_upper_sq hc hδ hδ1 (x := (μ.rnDeriv ν x).toReal)
            ENNReal.toReal_nonneg)
        rwa [ENNReal.ofReal_add
          (mul_nonneg (bernsteinUpperSqCoeff_nonneg c δ) (sq_nonneg _))
          (mul_nonneg (by norm_num) (powerTailDensityKernel_nonneg ENNReal.toReal_nonneg)),
          ENNReal.ofReal_mul (bernsteinUpperSqCoeff_nonneg c δ),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat] at hp
      _ = ENNReal.ofReal (bernsteinUpperSqCoeff c δ) *
            (∫⁻ x, ENNReal.ofReal ((Real.sqrt ((μ.rnDeriv ν x).toReal) - 1) ^ 2) ∂ν) +
            2 * (∫⁻ x, ENNReal.ofReal
              (powerTailDensityKernel c δ ((μ.rnDeriv ν x).toReal)) ∂ν) := by
        calc
          _ = (∫⁻ x, ENNReal.ofReal (bernsteinUpperSqCoeff c δ) *
                ENNReal.ofReal ((Real.sqrt ((μ.rnDeriv ν x).toReal) - 1) ^ 2) ∂ν) +
              (∫⁻ x, (2 : ℝ≥0∞) * ENNReal.ofReal
                (powerTailDensityKernel c δ ((μ.rnDeriv ν x).toReal)) ∂ν) := by
            simpa only [Pi.mul_apply] using
              (lintegral_add_left (measurable_const.mul hg)
                (fun x ↦ (2 : ℝ≥0∞) * ENNReal.ofReal
                  (powerTailDensityKernel c δ ((μ.rnDeriv ν x).toReal))))
          _ = _ := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
              lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
      _ = _ := by
        rw [← hellingerSq_eq_lintegral_of_ac h, ← tailPower_eq_lintegral_densityKernel h]
  · simp [bernsteinSq_of_not_ac h, tailPower_of_not_ac h]

/-! ### CM ⇒ NC with the coefficient `4 M²` -/

namespace Bernstein

section CM

open Hellinger.Comparison

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

/-- The strict ordinary tail at any `q ≥ 9/4` is inside every native CM closed event. -/
theorem tailPower_le_closedTailMoment (hμν : μ ≪ ν) {q a : ℝ} (hq : 9 / 4 ≤ q)
    (ha : 1 ≤ a) : tailPower μ ν q 1 ≤ closedTailMoment μ ν (cmCutoff a) := by
  rw [tailPower_of_ac hμν, closedTailMoment_of_ac hμν]
  simp only [one_mul]
  apply lintegral_mono_set
  intro x hx
  have ht : cmCutoff a ≤ q := (cmCutoff_le_nine_fourths ha).trans hq
  exact (Real.log_le_log (cmCutoff_pos ha) ht).trans (le_of_lt hx)

/-- A nonnull closed ratio tail at a positive threshold `t` has conditional mean at least `t`. -/
theorem ofReal_le_conditionalRatioMean [IsFiniteMeasure μ] (hμν : μ ≪ ν) {t : ℝ}
    (ht : 0 < t) (hnull : μ (closedTailEvent μ ν t) ≠ 0) :
    ENNReal.ofReal t ≤ conditionalRatioMean μ ν t := by
  have hmass : ENNReal.ofReal t * μ (closedTailEvent μ ν t) ≤ closedTailMoment μ ν t := by
    rw [closedTailMoment_of_ac hμν]
    calc
      ENNReal.ofReal t * μ (closedTailEvent μ ν t) =
          ∫⁻ _ in closedTailEvent μ ν t, ENNReal.ofReal t ∂μ := by
        rw [setLIntegral_const]
      _ ≤ ∫⁻ x in closedTailEvent μ ν t, ENNReal.ofReal (Real.exp (llr μ ν x)) ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem (measurableSet_closedTailEvent μ ν t)] with x hx
        exact ENNReal.ofReal_le_ofReal ((mem_closedTailEvent_iff ht x).mp hx)
  rw [conditionalRatioMean_of_nonnull hμν hnull]
  exact (ENNReal.le_div_iff_mul_le (Or.inl hnull) (Or.inl (measure_ne_top μ _))).2 hmass

/-- `(2a + 1)² = 4 a² · cmCutoff a`. -/
theorem two_mul_add_one_sq_eq {a : ℝ} (ha : 1 ≤ a) :
    (2 * a + 1) ^ 2 = 4 * a ^ 2 * cmCutoff a := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  unfold cmCutoff
  field_simp
  ring

/-- Every finite native objective gives the coefficient `4 (objective)²`. -/
theorem tailPower_le_four_cmObjective_sq [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) {q a : ℝ} (hq : 9 / 4 ≤ q) (ha : 1 ≤ a)
    (hobj : cmObjective μ ν a < ∞) :
    tailPower μ ν q 1 ≤
      ENNReal.ofReal (4 * (cmObjective μ ν a).toReal ^ 2) * hellingerSq μ ν := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  let m := conditionalRatioMean μ ν (cmCutoff a)
  have hmfin : m ≠ ∞ :=
    (ENNReal.lt_top_of_mul_ne_top_right hobj.ne (ENNReal.ofReal_pos.mpr ha0).ne').ne
  have hmrep : ENNReal.ofReal m.toReal = m := ENNReal.ofReal_toReal hmfin
  have hobjreal : (cmObjective μ ν a).toReal = a * m.toReal := by
    rw [cmObjective, ENNReal.toReal_mul, ENNReal.toReal_ofReal ha0.le]
  by_cases hnull : μ (closedTailEvent μ ν (cmCutoff a)) = 0
  · have hz : closedTailMoment μ ν (cmCutoff a) = 0 := by
      rw [closedTailMoment_eq_conditionalRatioMean_mul_mass hμν, hnull, mul_zero]
    exact (tailPower_le_closedTailMoment hμν hq ha).trans (hz.le.trans zero_le)
  · have hmt : ENNReal.ofReal (cmCutoff a) ≤ m :=
      ofReal_le_conditionalRatioMean hμν (cmCutoff_pos ha) hnull
    have hmreal : cmCutoff a ≤ m.toReal := by
      have := ENNReal.toReal_mono hmfin hmt
      rwa [ENNReal.toReal_ofReal (cmCutoff_pos ha).le] at this
    have hm0 : 0 ≤ m.toReal := ENNReal.toReal_nonneg
    calc
      tailPower μ ν q 1 ≤ closedTailMoment μ ν (cmCutoff a) :=
        tailPower_le_closedTailMoment hμν hq ha
      _ = m * μ (closedTailEvent μ ν (cmCutoff a)) :=
        closedTailMoment_eq_conditionalRatioMean_mul_mass hμν _
      _ ≤ m * (ENNReal.ofReal ((2 * a + 1) ^ 2) * hellingerSq μ ν) :=
        mul_le_mul_right (cm_event_mass_le hμν ha) m
      _ = ENNReal.ofReal (m.toReal * (2 * a + 1) ^ 2) * hellingerSq μ ν := by
        calc
          m * (ENNReal.ofReal ((2 * a + 1) ^ 2) * hellingerSq μ ν) =
              (ENNReal.ofReal m.toReal * ENNReal.ofReal ((2 * a + 1) ^ 2)) *
                hellingerSq μ ν := by rw [hmrep, mul_assoc]
          _ = _ := by rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg]
      _ ≤ ENNReal.ofReal (4 * (cmObjective μ ν a).toReal ^ 2) * hellingerSq μ ν := by
        apply mul_le_mul_left
        apply ENNReal.ofReal_le_ofReal
        rw [hobjreal, two_mul_add_one_sq_eq ha]
        have h4a : 0 ≤ 4 * a ^ 2 * m.toReal := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hmreal h4a]

/-- A finite real upper bound `R` for any native objective gives the coefficient `4 R²`. -/
theorem tailPower_le_of_cmObjective_le_sharp [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) {q a R : ℝ} (hq : 9 / 4 ≤ q) (ha : 1 ≤ a)
    (hR : 0 ≤ R) (hobj : cmObjective μ ν a ≤ ENNReal.ofReal R) :
    tailPower μ ν q 1 ≤ ENNReal.ofReal (4 * R ^ 2) * hellingerSq μ ν := by
  have hobjfin : cmObjective μ ν a < ∞ := hobj.trans_lt ENNReal.ofReal_lt_top
  have hreal : (cmObjective μ ν a).toReal ≤ R := by
    simpa only [ENNReal.toReal_ofReal hR] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hobj
  apply (tailPower_le_four_cmObjective_sq hμν hq ha hobjfin).trans
  apply mul_le_mul_left
  apply ENNReal.ofReal_le_ofReal
  have := pow_le_pow_left₀ (ENNReal.toReal_nonneg : 0 ≤ (cmObjective μ ν a).toReal) hreal 2
  linarith

end CM

end Bernstein

open Bernstein

/-- CM ⇒ NC with the coefficient `4 M²`, at every ordinary cutoff `q ≥ 9/4`. -/
theorem tailPower_le_of_conditionalMoment_le_sharp : CMSharpStatement.{u} := by
  intro α _ μ ν _ _ q M hq hM hCM
  have hcmfin : Comparison.conditionalMoment μ ν < ∞ := hCM.trans_lt ENNReal.ofReal_lt_top
  have hμν := Comparison.ac_of_conditionalMoment_lt_top hcmfin
  have hcont : Continuous (fun R : ℝ ↦
      ENNReal.ofReal (4 * R ^ 2) * hellingerSq μ ν) := by
    apply (ENNReal.continuous_mul_const (hellingerSq_ne_top μ ν)).comp
    apply ENNReal.continuous_ofReal.comp
    fun_prop
  have hlim : Tendsto (fun R : ℝ ↦
      ENNReal.ofReal (4 * R ^ 2) * hellingerSq μ ν) (𝓝[>] M)
      (𝓝 (ENNReal.ofReal (4 * M ^ 2) * hellingerSq μ ν)) :=
    (hcont.tendsto M).mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with R hR
  have hMR : M < R := hR
  have hR0 : 0 ≤ R := hM.trans hMR.le
  have hCMR : Comparison.conditionalMoment μ ν < ENNReal.ofReal R := hCM.trans_lt
    ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hM).mpr hMR)
  obtain ⟨a, ha, hobj⟩ := Comparison.conditionalMoment_lt_iff.mp hCMR
  exact tailPower_le_of_cmObjective_le_sharp hμν hq ha hR0 hobj.le

/-! ### Coefficient facts -/

theorem bernsteinLowerCoeff_le_bernsteinLowerSharpCoeff {c δ : ℝ} (hc : 1 < c)
    (hδ : 0 < δ) : bernsteinLowerCoeff c δ ≤ bernsteinLowerSharpCoeff c δ := by
  have hc0 : 0 < c := lt_trans (by norm_num) hc
  set u₀ := δ * Real.log c with hu₀def
  have hu₀ : 0 ≤ u₀ := (mul_pos hδ (Real.log_pos hc)).le
  have hsinh := Real.self_le_sinh_iff.mpr hu₀
  rw [Real.sinh_eq] at hsinh
  have hE : Real.exp (-u₀) * Real.exp u₀ = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hEpos := Real.exp_pos (-u₀)
  unfold bernsteinLowerCoeff bernsteinLowerSharpCoeff
  rw [rpow_neg_eq_exp hc0, ← hu₀def]
  -- `1 - E² ≥ 2 u₀ E` with `E = e^{-u₀}`, from `sinh u₀ ≥ u₀`.
  nlinarith [mul_le_mul_of_nonneg_left hsinh hEpos.le]

theorem bernsteinUpperSqCoeff_le_bernsteinUpperCoeff {c δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    bernsteinUpperSqCoeff c δ ≤ bernsteinUpperCoeff c δ := by
  unfold bernsteinUpperSqCoeff bernsteinUpperCoeff
  have hsq : δ ^ 2 ≤ δ := by nlinarith
  have h := mul_le_mul_of_nonneg_right hsq (sq_nonneg (1 + Real.sqrt c))
  nlinarith

theorem bernsteinLowerSharpCoeff_four_one :
    bernsteinLowerSharpCoeff 4 1 = (3 - Real.log 4) / 2 := by
  unfold bernsteinLowerSharpCoeff
  rw [Real.rpow_neg (by norm_num), Real.rpow_one]
  ring

theorem bernsteinUpperSqCoeff_four_one : bernsteinUpperSqCoeff 4 1 = 18 := by
  have hs : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num [bernsteinUpperSqCoeff, hs]

theorem four_mul_sq_le_two_mul_add_one_sq {M : ℝ} (hM : 0 ≤ M) :
    4 * M ^ 2 ≤ (2 * M + 1) ^ 2 := by
  nlinarith

end Hellinger.Sharp
