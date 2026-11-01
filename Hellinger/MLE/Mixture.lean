/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.MLE.MixLog
public import Hellinger.MLE.DensityBridge

/-!
Mixture geometry for the criterion `m_p = log((p₀ + p)/(2 p₀))`:
* `h(p₀, q_p)² ≤ ½ h(p₀, p)²` and `h(p₀, p)²/16 ≤ h(p₀, q_p)²` for `q_p = (p₀ + p)/2`;
* the Bernstein size `‖m_p‖_{P₀,B} ≤ 3 h(p₀, p)`;
* the curvature `P₀ m_p ≤ -h(p₀, p)²/16`.
The lower mixture constant `1/16` replaces the paper's `(1 - 1/√2)²`; any positive constant
serves the shell argument.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Hellinger.MLE

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-! ### Pointwise inequalities -/

/-- `(√a - √((a+b)/2))² ≤ ½ (√a - √b)²`. -/
theorem sq_sqrt_sub_sqrt_mid_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a - Real.sqrt ((a + b) / 2)) ^ 2 ≤ (Real.sqrt a - Real.sqrt b) ^ 2 / 2 := by
  set x := Real.sqrt a; set y := Real.sqrt b; set f := Real.sqrt ((a + b) / 2)
  have hx : 0 ≤ x := Real.sqrt_nonneg _
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  have hf : 0 ≤ f := Real.sqrt_nonneg _
  have hf2 : f ^ 2 = (x ^ 2 + y ^ 2) / 2 := by
    rw [Real.sq_sqrt (by positivity), Real.sq_sqrt ha, Real.sq_sqrt hb]
  have hmid : x + y ≤ 2 * f := by nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 2 * f)]
  nlinarith [mul_nonneg hx (show 0 ≤ 2 * f - (x + y) by linarith)]

/-- `(√a - √b)² ≤ 16 (√a - √((a+b)/2))²`. -/
theorem sq_sqrt_sub_sqrt_le_sixteen_mid {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a - Real.sqrt b) ^ 2 ≤ 16 * (Real.sqrt a - Real.sqrt ((a + b) / 2)) ^ 2 := by
  set x := Real.sqrt a; set y := Real.sqrt b; set f := Real.sqrt ((a + b) / 2)
  have hx : 0 ≤ x := Real.sqrt_nonneg _
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  have hf : 0 ≤ f := Real.sqrt_nonneg _
  have hf2 : f ^ 2 = (x ^ 2 + y ^ 2) / 2 := by
    rw [Real.sq_sqrt (by positivity), Real.sq_sqrt ha, Real.sq_sqrt hb]
  -- `2 (x - f)(x + f) = (x - y)(x + y)` and `x + f ≤ 2 (x + y)`
  have hid : 2 * (x - f) * (x + f) = (x - y) * (x + y) := by nlinarith
  have hfle : f ≤ x + y := by nlinarith [sq_nonneg (x + y), mul_nonneg hx hy]
  rcases (add_nonneg hx hy).eq_or_lt with h0 | hpos
  · have hx0 : x = 0 := by linarith
    have hy0 : y = 0 := by linarith
    simp [hx0, hy0]; positivity
  have key : ((x - y) * (x + y)) ^ 2 ≤ (16 * (x - f) ^ 2) * (x + y) ^ 2 := by
    rw [← hid]
    have : (x + f) ^ 2 ≤ 4 * (x + y) ^ 2 := by nlinarith
    nlinarith [sq_nonneg (x - f)]
  rw [mul_pow] at key
  exact le_of_mul_le_mul_right key (by positivity)

/-- `log y ≤ 2 (√y - 1)` for `y > 0`. -/
theorem log_le_two_mul_sqrt_sub_one {y : ℝ} (hy : 0 < y) :
    Real.log y ≤ 2 * (Real.sqrt y - 1) := by
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have : Real.log y = 2 * Real.log (Real.sqrt y) := by
    rw [← Real.log_rpow hs, Real.rpow_two, Real.sq_sqrt hy.le]
  rw [this]
  linarith [Real.log_le_sub_one_of_pos hs]

/-- The Bernstein kernel of a log-ratio bounded below by `1/2`:
`2(e^{|log y|} - 1 - |log y|) ≤ 18 (√y - 1)²` for `y ≥ 1/2`. -/
theorem bernsteinKernel_log_le {y : ℝ} (hy : 1 / 2 ≤ y) :
    bernsteinKernel 1 (Real.log y) ≤ 18 * (Real.sqrt y - 1) ^ 2 := by
  have hy0 : 0 < y := by linarith
  set x := Real.sqrt y with hxdef
  have hx0 : 0 < x := Real.sqrt_pos.mpr hy0
  have hxy : x ^ 2 = y := Real.sq_sqrt hy0.le
  have hlog : Real.log y = 2 * Real.log x := by
    rw [← hxy, Real.log_pow]; push_cast; ring
  unfold bernsteinKernel
  rw [one_mul]
  rcases le_or_gt 1 x with hx1 | hx1
  · -- `y ≥ 1`: `|log y| = log y`, `e^{log y} = y`
    have hlogx : 1 - 1 / x ≤ Real.log x := by
      have := Real.one_sub_inv_le_log_of_pos hx0; simpa [one_div] using this
    have hnn : 0 ≤ Real.log y := by rw [hlog]; exact mul_nonneg (by norm_num) (Real.log_nonneg hx1)
    rw [abs_of_nonneg hnn, Real.exp_log hy0, hlog, ← hxy]
    have h1 : x ^ 2 - 1 - 2 * Real.log x ≤ (x - 1) ^ 2 * (x + 2) / x := by
      have : (x - 1) ^ 2 * (x + 2) / x = x ^ 2 - 1 - 2 * (1 - 1 / x) := by field_simp; ring
      rw [this]; linarith
    have h2 : (x - 1) ^ 2 * (x + 2) / x ≤ 3 * (x - 1) ^ 2 := by
      rw [div_le_iff₀ hx0]; nlinarith [sq_nonneg (x - 1)]
    nlinarith [sq_nonneg (x - 1)]
  · -- `1/2 ≤ y < 1`: `|log y| = -log y`, `e^{-log y} = 1/y`
    have hlogx : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos hx0
    have hneg : Real.log y < 0 := Real.log_neg hy0 (by nlinarith)
    rw [abs_of_neg hneg, Real.exp_neg, Real.exp_log hy0, hlog, ← hxy]
    have hx2 : 1 / 2 ≤ x ^ 2 := by rw [hxy]; exact hy
    have h1 : (x ^ 2)⁻¹ - 1 - -(2 * Real.log x) ≤ (x - 1) ^ 2 * (2 * x + 1) / x ^ 2 := by
      have : (x - 1) ^ 2 * (2 * x + 1) / x ^ 2 = (x ^ 2)⁻¹ - 1 + 2 * (x - 1) := by
        field_simp; ring
      rw [this]; linarith
    have h2 : (x - 1) ^ 2 * (2 * x + 1) / x ^ 2 ≤ 6 * (x - 1) ^ 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg (x - 1)]
    nlinarith [sq_nonneg (x - 1)]

/-! ### Mixture Hellinger comparisons -/

theorem measurable_mixDensity {p₀ p : 𝒳 → ℝ≥0} (hp₀ : Measurable p₀) (hp : Measurable p) :
    Measurable (mixDensity p₀ p) :=
  (hp₀.add hp).div_const 2

/-- `h(p₀, q_p)² ≤ ½ h(p₀, p)²`. -/
theorem hellingerFunSq_mix_le (μ : Measure 𝒳) (p₀ p : 𝒳 → ℝ≥0) :
    hellingerFunSq μ p₀ (mixDensity p₀ p) ≤ 2⁻¹ * hellingerFunSq μ p₀ p := by
  unfold hellingerFunSq
  rw [← lintegral_const_mul' _ _ (by simp)]
  refine lintegral_mono fun x ↦ ?_
  rw [mixDensity_coe, show (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal 2⁻¹ by
    rw [ENNReal.ofReal_inv_of_pos (by norm_num)]; simp, ← ENNReal.ofReal_mul (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  have := sq_sqrt_sub_sqrt_mid_le (p₀ x).coe_nonneg (p x).coe_nonneg
  linarith

/-- `h(p₀, p)²/16 ≤ h(p₀, q_p)²`. -/
theorem hellingerFunSq_le_sixteen_mix (μ : Measure 𝒳) (p₀ p : 𝒳 → ℝ≥0) :
    hellingerFunSq μ p₀ p ≤ 16 * hellingerFunSq μ p₀ (mixDensity p₀ p) := by
  unfold hellingerFunSq
  rw [← lintegral_const_mul' _ _ (by simp)]
  refine lintegral_mono fun x ↦ ?_
  rw [mixDensity_coe, show (16 : ℝ≥0∞) = ENNReal.ofReal 16 by simp,
    ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal
    (sq_sqrt_sub_sqrt_le_sixteen_mid (p₀ x).coe_nonneg (p x).coe_nonneg)

/-- `h(f, g)² ≤ ∫ f + ∫ g`; in particular `h ≤ √2` between probability densities. -/
theorem hellingerFunSq_le_two (μ : Measure 𝒳) {p q : 𝒳 → ℝ≥0} (hp : IsProbDensity μ p)
    (hq : IsProbDensity μ q) : hellingerFunSq μ p q ≤ 2 := by
  calc hellingerFunSq μ p q ≤ ∫⁻ x, ((p x : ℝ≥0∞) + q x) ∂μ := by
        refine lintegral_mono fun x ↦ ?_
        rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_coe_nnreal (p := q x),
          ← ENNReal.ofReal_add (p x).coe_nonneg (q x).coe_nonneg]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 := Real.sq_sqrt (p x).coe_nonneg
        have h2 := Real.sq_sqrt (q x).coe_nonneg
        nlinarith [Real.sqrt_nonneg (p x : ℝ), Real.sqrt_nonneg (q x : ℝ),
          mul_nonneg (Real.sqrt_nonneg (p x : ℝ)) (Real.sqrt_nonneg (q x : ℝ))]
    _ = 2 := by
        rw [lintegral_add_left' hp.measurable.coe_nnreal_ennreal.aemeasurable, hp.lintegral_eq_one,
          hq.lintegral_eq_one]; norm_num

theorem hellingerFunSq_ne_top (μ : Measure 𝒳) {p q : 𝒳 → ℝ≥0} (hp : IsProbDensity μ p)
    (hq : IsProbDensity μ q) : hellingerFunSq μ p q ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp) (hellingerFunSq_le_two μ hp hq)

/-! ### The Bernstein size of `m_p` -/

/-- `P₀`-integrals against the law are `μ`-integrals with the factor `p₀`. -/
theorem lintegral_law {μ : Measure 𝒳} {p₀ : 𝒳 → ℝ≥0} (hp₀ : Measurable p₀) {g : 𝒳 → ℝ≥0∞}
    (hg : Measurable g) : ∫⁻ x, g x ∂(law μ p₀) = ∫⁻ x, (p₀ x : ℝ≥0∞) * g x ∂μ :=
  lintegral_withDensity_eq_lintegral_mul μ hp₀.coe_nnreal_ennreal hg

/-- `‖m_p‖²_{P₀,B} ≤ 18 h(p₀, q_p)²`. -/
theorem bernsteinFunSq_mixLog_le_mix {μ : Measure 𝒳} {p₀ p : 𝒳 → ℝ≥0} (hp₀ : Measurable p₀)
    (hp : Measurable p) :
    bernsteinFunSq (law μ p₀) (mixLog p₀ p) ≤ 18 * hellingerFunSq μ p₀ (mixDensity p₀ p) := by
  unfold bernsteinFunSq hellingerFunSq
  have hmeas : Measurable fun x ↦ ENNReal.ofReal (bernsteinKernel 1 (mixLog p₀ p x)) := by
    refine ENNReal.measurable_ofReal.comp ?_
    unfold bernsteinKernel
    have hm := measurable_mixLog hp₀ hp
    fun_prop
  rw [lintegral_law hp₀ hmeas, ← lintegral_const_mul' _ _ (by simp)]
  refine lintegral_mono fun x ↦ ?_
  rcases eq_zero_or_pos (p₀ x) with hx | hx
  · simp [hx]
  have hpx : (0 : ℝ) < p₀ x := by exact_mod_cast hx
  set y : ℝ := ((p₀ x : ℝ) + p x) / (2 * p₀ x) with hy
  have hy2 : 1 / 2 ≤ y := by
    rw [hy, le_div_iff₀ (by positivity)]; have := (p x).coe_nonneg; nlinarith
  have hm : mixLog p₀ p x = Real.log y := mixLog_of_pos hx
  -- `p₀ (√y - 1)² = (√p₀ - √q)²`
  have hiden : (p₀ x : ℝ) * (Real.sqrt y - 1) ^ 2 =
      (Real.sqrt (p₀ x) - Real.sqrt (((p₀ x : ℝ) + p x) / 2)) ^ 2 := by
    have hyq : y = (((p₀ x : ℝ) + p x) / 2) / p₀ x := by rw [hy]; field_simp
    rw [hyq, Real.sqrt_div' _ hpx.le]
    have hs : 0 < Real.sqrt (p₀ x : ℝ) := Real.sqrt_pos.mpr hpx
    have hss := Real.sq_sqrt hpx.le
    field_simp
    rw [hss]; ring
  rw [hm, mixDensity_coe, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul hpx.le,
    show (18 : ℝ≥0∞) = ENNReal.ofReal 18 by simp, ← ENNReal.ofReal_mul (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc (p₀ x : ℝ) * bernsteinKernel 1 (Real.log y) ≤ (p₀ x : ℝ) * (18 * (Real.sqrt y - 1) ^ 2) :=
        mul_le_mul_of_nonneg_left (bernsteinKernel_log_le hy2) hpx.le
    _ = 18 * (Real.sqrt (p₀ x) - Real.sqrt (((p₀ x : ℝ) + p x) / 2)) ^ 2 := by
        rw [← hiden]; ring

/-- `‖m_p‖²_{P₀,B} ≤ 9 h(p₀, p)²`. -/
theorem bernsteinFunSq_mixLog_le {μ : Measure 𝒳} {p₀ p : 𝒳 → ℝ≥0} (hp₀ : Measurable p₀)
    (hp : Measurable p) :
    bernsteinFunSq (law μ p₀) (mixLog p₀ p) ≤ 9 * hellingerFunSq μ p₀ p :=
  (bernsteinFunSq_mixLog_le_mix hp₀ hp).trans <| by
    calc 18 * hellingerFunSq μ p₀ (mixDensity p₀ p) ≤ 18 * (2⁻¹ * hellingerFunSq μ p₀ p) := by
          gcongr; exact hellingerFunSq_mix_le μ p₀ p
      _ = 9 * hellingerFunSq μ p₀ p := by
          rw [← mul_assoc]; congr 1
          rw [show (18 : ℝ≥0∞) = 9 * 2 by norm_num, mul_assoc, ENNReal.mul_inv_cancel (by norm_num)
            (by norm_num), mul_one]

/-- `‖m_p‖_{P₀,B} ≤ 3 h(p₀, p)`. -/
theorem bernsteinFun_mixLog_le {μ : Measure 𝒳} {p₀ p : 𝒳 → ℝ≥0} (hp₀ : Measurable p₀)
    (hp : Measurable p) :
    bernsteinFun (law μ p₀) (mixLog p₀ p) ≤ 3 * hdist μ p₀ p := by
  unfold bernsteinFun hdist
  calc bernsteinFunSq (law μ p₀) (mixLog p₀ p) ^ (1 / 2 : ℝ)
      ≤ (9 * hellingerFunSq μ p₀ p) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (bernsteinFunSq_mixLog_le hp₀ hp) (by norm_num)
    _ = 3 * hellingerFunSq μ p₀ p ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
        congr 1
        rw [show (9 : ℝ≥0∞) = 3 ^ (2 : ℝ) by norm_num, ← ENNReal.rpow_mul]; norm_num

/-! ### Curvature -/

theorem mixDensity_isProbDensity {μ : Measure 𝒳} {p₀ p : 𝒳 → ℝ≥0} (hp₀ : IsProbDensity μ p₀)
    (hp : IsProbDensity μ p) : IsProbDensity μ (mixDensity p₀ p) := by
  refine ⟨measurable_mixDensity hp₀.measurable hp.measurable, ?_⟩
  have : ∀ x, ((mixDensity p₀ p x : ℝ≥0) : ℝ≥0∞) = 2⁻¹ * ((p₀ x : ℝ≥0∞) + p x) := by
    intro x; simp [mixDensity, div_eq_inv_mul, mul_comm]
  simp_rw [this]
  rw [lintegral_const_mul' _ _ (by simp),
    lintegral_add_left' hp₀.measurable.coe_nnreal_ennreal.aemeasurable, hp₀.lintegral_eq_one,
    hp.lintegral_eq_one, one_add_one_eq_two, ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]

theorem integrable_coe_of_isProbDensity {μ : Measure 𝒳} {p : 𝒳 → ℝ≥0} (hp : IsProbDensity μ p) :
    Integrable (fun x ↦ (p x : ℝ)) μ := by
  have := integrable_toReal_of_lintegral_ne_top hp.measurable.coe_nnreal_ennreal.aemeasurable
    (by rw [hp.lintegral_eq_one]; exact ENNReal.one_ne_top)
  simpa using this

theorem integral_coe_of_isProbDensity {μ : Measure 𝒳} {p : 𝒳 → ℝ≥0} (hp : IsProbDensity μ p) :
    ∫ x, (p x : ℝ) ∂μ = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x ↦ (p x).coe_nonneg)
    (measurable_coe_nnreal_real.comp hp.measurable).aestronglyMeasurable]
  simp [hp.lintegral_eq_one]

/-- `m_p` is `P₀`-integrable and `P₀ m_p ≤ -h(p₀, q_p)²`. -/
theorem integral_mixLog_le_neg_mix {μ : Measure 𝒳} {p₀ p : 𝒳 → ℝ≥0}
    (hp₀ : IsProbDensity μ p₀) (hp : IsProbDensity μ p) :
    Integrable (mixLog p₀ p) (law μ p₀) ∧
      ∫ x, mixLog p₀ p x ∂(law μ p₀) ≤ -(hellingerFunSq μ p₀ (mixDensity p₀ p)).toReal := by
  set q := mixDensity p₀ p with hqdef
  have hq : IsProbDensity μ q := mixDensity_isProbDensity hp₀ hp
  have hm := measurable_mixLog hp₀.measurable hp.measurable
  have hp₀r := measurable_coe_nnreal_real.comp hp₀.measurable
  have hqr := measurable_coe_nnreal_real.comp hq.measurable
  set g : 𝒳 → ℝ := fun x ↦ 2 * (Real.sqrt (p₀ x) * Real.sqrt (q x) - p₀ x) with hg
  set d : 𝒳 → ℝ := fun x ↦ (Real.sqrt (p₀ x) - Real.sqrt (q x)) ^ 2 with hd
  have hgd : ∀ x, g x = -d x + ((q x : ℝ) - p₀ x) := by
    intro x
    simp only [hg, hd]
    have h1 := Real.sq_sqrt (p₀ x).coe_nonneg
    have h2 := Real.sq_sqrt (q x).coe_nonneg
    nlinarith
  have hd_le : ∀ x, d x ≤ (p₀ x : ℝ) + q x := by
    intro x
    simp only [hd]
    have h1 := Real.sq_sqrt (p₀ x).coe_nonneg
    have h2 := Real.sq_sqrt (q x).coe_nonneg
    nlinarith [mul_nonneg (Real.sqrt_nonneg (p₀ x : ℝ)) (Real.sqrt_nonneg (q x : ℝ))]
  have hdm : Measurable d := by simp only [hd]; fun_prop
  have hint0 := integrable_coe_of_isProbDensity hp₀
  have hintq := integrable_coe_of_isProbDensity hq
  have hdint : Integrable d μ :=
    (hint0.add hintq).mono' hdm.aestronglyMeasurable
      (ae_of_all _ fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (by simp only [hd]; positivity)]; exact hd_le x)
  have hgint : Integrable g μ := by
    have : g = fun x ↦ -d x + ((q x : ℝ) - p₀ x) := funext hgd
    rw [this]; exact hdint.neg.add (hintq.sub hint0)
  -- pointwise `p₀ m_p ≤ g` and `p₀ m_p ≥ -log 2 · p₀`
  have hup : ∀ x, (p₀ x : ℝ) * mixLog p₀ p x ≤ g x := by
    intro x
    rcases eq_zero_or_pos (p₀ x) with hx | hx
    · simp [hg, hx]
    have hpx : (0 : ℝ) < p₀ x := by exact_mod_cast hx
    have hqx : ((q x : ℝ≥0) : ℝ) = ((p₀ x : ℝ) + p x) / 2 := mixDensity_coe p₀ p x
    have hqpos : (0 : ℝ) < q x := by rw [hqx]; have := (p x).coe_nonneg; positivity
    rw [mixLog_of_pos hx, show ((p₀ x : ℝ) + p x) / (2 * p₀ x) = (q x : ℝ) / p₀ x by
      rw [hqx]; field_simp]
    have hlog := log_le_two_mul_sqrt_sub_one (div_pos hqpos hpx)
    have hs : 0 < Real.sqrt (p₀ x : ℝ) := Real.sqrt_pos.mpr hpx
    have hiden : (p₀ x : ℝ) * Real.sqrt ((q x : ℝ) / p₀ x) =
        Real.sqrt (p₀ x) * Real.sqrt (q x) := by
      rw [Real.sqrt_div' _ hpx.le]
      field_simp
      rw [Real.sq_sqrt hpx.le]
    calc (p₀ x : ℝ) * Real.log ((q x : ℝ) / p₀ x)
        ≤ (p₀ x : ℝ) * (2 * (Real.sqrt ((q x : ℝ) / p₀ x) - 1)) :=
          mul_le_mul_of_nonneg_left hlog hpx.le
      _ = g x := by simp only [hg]; rw [← hiden]; ring
  have hlow : ∀ x, -(Real.log 2 * p₀ x) ≤ (p₀ x : ℝ) * mixLog p₀ p x := by
    intro x
    have := neg_log_two_le_mixLog p₀ p x
    nlinarith [(p₀ x).coe_nonneg]
  have hpm : Integrable (fun x ↦ (p₀ x : ℝ) * mixLog p₀ p x) μ := by
    refine (((hint0.const_mul (Real.log 2)).add (hgint.norm))).mono'
      (hp₀r.mul hm).aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
    have h1 := hlow x
    have h2 := hup x
    have h3 : 0 ≤ Real.log 2 * p₀ x :=
      mul_nonneg (Real.log_pos (by norm_num)).le (p₀ x).coe_nonneg
    have h4 : g x ≤ ‖g x‖ := Real.le_norm_self (g x)
    have h5 : 0 ≤ ‖g x‖ := norm_nonneg _
    rw [Real.norm_eq_abs, abs_le]
    dsimp only [Pi.add_apply]
    constructor <;> linarith
  have hlaw : ∀ f : 𝒳 → ℝ, ∫ x, f x ∂(law μ p₀) = ∫ x, (p₀ x : ℝ) * f x ∂μ := fun f ↦ by
    rw [law, integral_withDensity_eq_integral_smul hp₀.measurable]; rfl
  refine ⟨?_, ?_⟩
  · rw [law, integrable_withDensity_iff_integrable_smul hp₀.measurable]
    exact hpm
  · rw [hlaw]
    calc ∫ x, (p₀ x : ℝ) * mixLog p₀ p x ∂μ ≤ ∫ x, g x ∂μ := integral_mono hpm hgint hup
      _ = -∫ x, d x ∂μ + (∫ x, (q x : ℝ) ∂μ - ∫ x, (p₀ x : ℝ) ∂μ) := by
          rw [show g = fun x ↦ -d x + ((q x : ℝ) - p₀ x) from funext hgd,
            integral_add (f := fun x ↦ -d x) (g := fun x ↦ (q x : ℝ) - p₀ x) hdint.neg
              (hintq.sub hint0), integral_neg, integral_sub hintq hint0]
      _ = -(hellingerFunSq μ p₀ q).toReal := by
          rw [integral_coe_of_isProbDensity hq, integral_coe_of_isProbDensity hp₀, sub_self,
            add_zero, hellingerFunSq, ← integral_eq_lintegral_of_nonneg_ae
              (ae_of_all _ fun x ↦ by positivity) hdm.aestronglyMeasurable]

/-- The population curvature `P₀ m_p ≤ -h(p₀, p)²/16`, with `m_p` integrable. -/
theorem integral_mixLog_le {μ : Measure 𝒳} {p₀ p : 𝒳 → ℝ≥0} (hp₀ : IsProbDensity μ p₀)
    (hp : IsProbDensity μ p) :
    Integrable (mixLog p₀ p) (law μ p₀) ∧
      ∫ x, mixLog p₀ p x ∂(law μ p₀) ≤ -(16⁻¹ * (hellingerFunSq μ p₀ p).toReal) := by
  obtain ⟨hint, hle⟩ := integral_mixLog_le_neg_mix hp₀ hp
  refine ⟨hint, hle.trans (neg_le_neg ?_)⟩
  have hq := mixDensity_isProbDensity hp₀ hp
  have h16 := hellingerFunSq_le_sixteen_mix μ p₀ p
  have hfin := hellingerFunSq_ne_top μ hp₀ hq
  have h16r : (hellingerFunSq μ p₀ p).toReal ≤ 16 * (hellingerFunSq μ p₀ (mixDensity p₀ p)).toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) hfin) h16
    rwa [ENNReal.toReal_mul, show (16 : ℝ≥0∞).toReal = 16 by norm_num] at this
  linarith

end Hellinger.MLE
