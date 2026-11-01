/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.MLE.Comparator
public import Hellinger.MLE.Bracketing
public import Hellinger.MLE.WeakLawBasic
public import Hellinger.MLE.Mixture
public import Hellinger.VariationScalar
public import Hellinger.KLDensityScalar
public import Hellinger.Constants

/-!
The comparator error of the weak-law form of Theorem 8, under the weak-law truncation
condition (W).

With `P₀ = p₀ · μ`, the central part `C_n = log(p₀/p_n) 1{p₀ ≤ 4 p_n}`, the extended tail
`T_n = extTail p₀ p_n`, thresholds `L_n` and the exceptional event
`G_n = {∃ i < n, T_n(X_i) > L_n}`, the comparator error is
`Z_n = ½ (E_n + |(ℙ_n − P₀) C_n| + (P₀ C_n)_+ + ℙ_n[T_n 1{T_n ≤ L_n}])`.

* The central second moment: `P₀ C_n² ≤ 8 h(p₀, p_n)²` (`lintegral_centralLog_sq_le`).
* The central mean: `P₀ C_n ≤ 3 h(p₀, p_n)²` (`integral_centralLog_le`), without absolute
  continuity.
* The union bound `Pr(G_n) ≤ n P₀(T_n > L_n)` (`measure_exceptionalEvent_le`).
* `Z_n = O_P^*(a_n²)` under (W2) (`weakComparatorError_opStar`).
* The empirical lower bound: almost surely, off `G_n` and when `Z_n` is finite,
  `ℙ_n m_{phat_n} ≥ -Z_n` (`sampleMean_mixLog_ge_weak`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Hellinger.MLE

variable {𝒳 : Type*} [MeasurableSpace 𝒳] {μ : Measure 𝒳}
  {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} {X : ℕ → Ω → 𝒳} {p₀ : 𝒳 → ℝ≥0}
  {S : ℕ → Set (𝒳 → ℝ≥0)} {pn : ℕ → 𝒳 → ℝ≥0} {phat : ℕ → Ω → 𝒳 → ℝ≥0}
  {δ : ℕ → ℝ} {D : ℝ}

/-- The central part `C = log(p₀/q) 1{p₀ ≤ 4 q}`; it is `0` where `p₀ = 0`
(since `Real.log 0 = 0`). -/
noncomputable def centralLog (p₀ q : 𝒳 → ℝ≥0) (x : 𝒳) : ℝ :=
  if p₀ x ≤ 4 * q x then logRatio p₀ q x else 0

/-- The sample mean of an extended nonnegative function, `ℙ_n f = n⁻¹ ∑ f(X_i)` in `[0, ∞]`. -/
noncomputable def ennMean (X : ℕ → Ω → 𝒳) (n : ℕ) (f : 𝒳 → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  (n : ℝ≥0∞)⁻¹ * ∑ i : Fin n, f (X i ω)

/-- The exceptional event `G_n = {∃ i < n, T_n(X_i) > L_n}`. -/
def exceptionalEvent (X : ℕ → Ω → 𝒳) (p₀ : 𝒳 → ℝ≥0) (pn : ℕ → 𝒳 → ℝ≥0) (L : ℕ → ℝ≥0∞)
    (n : ℕ) : Set Ω :=
  {ω | ∃ i : Fin n, L n < extTail p₀ (pn n) (X i ω)}

/-- `Z_n = ½ (E_n + |(ℙ_n − P₀) C_n| + (P₀ C_n)_+ + ℙ_n[T_n 1{T_n ≤ L_n}])`. -/
noncomputable def weakComparatorError (μ : Measure 𝒳) (X : ℕ → Ω → 𝒳) (p₀ : 𝒳 → ℝ≥0)
    (pn : ℕ → 𝒳 → ℝ≥0) (phat : ℕ → Ω → 𝒳 → ℝ≥0) (L : ℕ → ℝ≥0∞) (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
  2⁻¹ * (logLikDeficit (sample X n ω) (pn n) (phat n ω) +
    ENNReal.ofReal |sampleMean X n (centralLog p₀ (pn n)) ω -
      ∫ x, centralLog p₀ (pn n) x ∂(law μ p₀)| +
    ENNReal.ofReal (∫ x, centralLog p₀ (pn n) x ∂(law μ p₀)) +
    ennMean X n (truncTail p₀ (pn n) (L n)) ω)

/-! ### Measurability -/

theorem measurable_centralLog {p₀ q : 𝒳 → ℝ≥0} (hp₀ : Measurable p₀) (hq : Measurable q) :
    Measurable (centralLog p₀ q) :=
  Measurable.ite (measurableSet_le hp₀ (hq.const_mul 4)) (measurable_logRatio hp₀ hq)
    measurable_const

theorem measurable_ennMean (hX : ∀ i, Measurable (X i)) (n : ℕ) {f : 𝒳 → ℝ≥0∞}
    (hf : Measurable f) : Measurable (ennMean X n f) :=
  (Finset.measurable_sum (f := fun (i : Fin n) ω ↦ f (X i ω)) _
    fun i _ ↦ hf.comp (hX i)).const_mul _

theorem measurableSet_exceptionalEvent (hX : ∀ i, Measurable (X i)) (hp₀ : Measurable p₀)
    {n : ℕ} (hpn : Measurable (pn n)) (L : ℕ → ℝ≥0∞) :
    MeasurableSet (exceptionalEvent X p₀ pn L n) := by
  have : exceptionalEvent X p₀ pn L n =
      ⋃ i : Fin n, X i ⁻¹' {x | L n < extTail p₀ (pn n) x} := by
    ext ω; simp [exceptionalEvent]
  rw [this]
  exact MeasurableSet.iUnion fun i ↦ (hX i)
    (measurableSet_lt measurable_const (measurable_extTail hp₀ hpn))

/-! ### Scalar inequalities -/

omit [MeasurableSpace 𝒳] in
/-- `b (√(a/b) − 1)² = (√a − √b)²` for `a ≥ 0`, `b > 0`. -/
theorem mul_sqrt_div_sub_one_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    b * (Real.sqrt (a / b) - 1) ^ 2 = (Real.sqrt a - Real.sqrt b) ^ 2 := by
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  rw [Real.sqrt_div ha]
  field_simp
  rw [Real.sq_sqrt hb.le]

omit [MeasurableSpace 𝒳] in
/-- `a log(a/b)² ≤ 8 (√a − √b)²` for `0 < a ≤ 4 b`. -/
theorem mul_log_div_sq_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≤ 4 * b) :
    a * Real.log (a / b) ^ 2 ≤ 8 * (Real.sqrt a - Real.sqrt b) ^ 2 := by
  set r := a / b with hr
  have hr0 : 0 < r := div_pos ha hb
  have hr4 : r ≤ 4 := by rw [hr, div_le_iff₀ hb]; linarith
  have hsr : Real.sqrt r ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hr4
  have h1 := mul_sq_log_le_four_sqrt_mul_hellinger hr0
  have h2 : r * Real.log r ^ 2 ≤ 8 * (Real.sqrt r - 1) ^ 2 :=
    h1.trans (by nlinarith [sq_nonneg (Real.sqrt r - 1)])
  have ha' : a = b * r := by rw [hr]; field_simp
  calc a * Real.log r ^ 2 = b * (r * Real.log r ^ 2) := by rw [ha']; ring
    _ ≤ b * (8 * (Real.sqrt r - 1) ^ 2) := by gcongr
    _ = 8 * (b * (Real.sqrt r - 1) ^ 2) := by ring
    _ = 8 * (Real.sqrt a - Real.sqrt b) ^ 2 := by rw [hr, mul_sqrt_div_sub_one_sq ha.le hb]

omit [MeasurableSpace 𝒳] in
/-- `a log(a/b) ≤ 3 (√a − √b)² + (a − b)` for `0 < a ≤ 4 b`. -/
theorem mul_log_div_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≤ 4 * b) :
    a * Real.log (a / b) ≤ 3 * (Real.sqrt a - Real.sqrt b) ^ 2 + (a - b) := by
  set r := a / b with hr
  have hr0 : 0 < r := div_pos ha hb
  have hr4 : r ≤ 4 := by rw [hr, div_le_iff₀ hb]; linarith
  have h1 := klFun_le_klUpperCoeff_mul_hellinger (by norm_num : (1 : ℝ) < 4) hr0 hr4
  rw [klUpperCoeff_four, InformationTheory.klFun_apply] at h1
  have ha' : a = b * r := by rw [hr]; field_simp
  have h2 := mul_le_mul_of_nonneg_left h1 hb.le
  rw [← mul_sqrt_div_sub_one_sq ha.le hb, ← hr]
  calc a * Real.log r = b * (r * Real.log r + 1 - r) - b + b * r := by rw [ha']; ring
    _ ≤ b * (3 * (Real.sqrt r - 1) ^ 2) - b + b * r := by linarith
    _ = 3 * (b * (Real.sqrt r - 1) ^ 2) + (a - b) := by rw [ha']; ring

/-! ### The central second moment -/

/-- The central second moment: `P₀ C² ≤ 8 h(p₀, q)²`. -/
theorem lintegral_centralLog_sq_le {q : 𝒳 → ℝ≥0} (hp₀ : IsProbDensity μ p₀)
    (hq : IsProbDensity μ q) :
    ∫⁻ x, ENNReal.ofReal (centralLog p₀ q x ^ 2) ∂(law μ p₀) ≤ 8 * hellingerFunSq μ p₀ q := by
  have hmeas : Measurable fun x ↦ ENNReal.ofReal (centralLog p₀ q x ^ 2) :=
    ((measurable_centralLog hp₀.measurable hq.measurable).pow_const 2).ennreal_ofReal
  rw [lintegral_law hp₀.measurable hmeas, hellingerFunSq, ← lintegral_const_mul' _ _ (by simp)]
  refine lintegral_mono fun x ↦ ?_
  rcases eq_zero_or_pos (p₀ x) with hx | hx
  · simp [hx]
  by_cases h4 : p₀ x ≤ 4 * q x
  · have hqx : 0 < q x := by
      by_contra h0
      rw [not_lt, nonpos_iff_eq_zero] at h0
      rw [h0, mul_zero] at h4
      exact hx.ne' (le_antisymm h4 zero_le)
    have h4' : (p₀ x : ℝ) ≤ 4 * q x := by exact_mod_cast h4
    simp only [centralLog, h4, ↓reduceIte, logRatio]
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_ofNat 8, ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal
      (mul_log_div_sq_le (by exact_mod_cast hx) (by exact_mod_cast hqx) h4')
  · simp [centralLog, h4]

/-- `C ∈ L²(P₀)`. -/
theorem memLp_centralLog {q : 𝒳 → ℝ≥0} (hp₀ : IsProbDensity μ p₀) (hq : IsProbDensity μ q) :
    MemLp (centralLog p₀ q) 2 (law μ p₀) := by
  have hm := measurable_centralLog hp₀.measurable hq.measurable
  refine (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2
    ⟨(hm.pow_const 2).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x ↦ sq_nonneg _)).2
        (lt_of_le_of_lt (lintegral_centralLog_sq_le hp₀ hq) ?_)⟩
  exact ENNReal.mul_lt_top (by simp) (hellingerFunSq_ne_top μ hp₀ hq).lt_top

theorem integral_centralLog_sq_le {q : 𝒳 → ℝ≥0} (hp₀ : IsProbDensity μ p₀)
    (hq : IsProbDensity μ q) :
    ∫ x, centralLog p₀ q x ^ 2 ∂(law μ p₀) ≤ 8 * (hellingerFunSq μ p₀ q).toReal := by
  have hm := measurable_centralLog hp₀.measurable hq.measurable
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x ↦ sq_nonneg _)
    (hm.pow_const 2).aestronglyMeasurable]
  have := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (by simp) (hellingerFunSq_ne_top μ hp₀ hq))
    (lintegral_centralLog_sq_le hp₀ hq)
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at this

/-! ### The central mean -/

/-- The central mean: `P₀ C ≤ 3 h(p₀, q)²`. No absolute continuity is needed. -/
theorem integral_centralLog_le {q : 𝒳 → ℝ≥0} (hp₀ : IsProbDensity μ p₀)
    (hq : IsProbDensity μ q) :
    ∫ x, centralLog p₀ q x ∂(law μ p₀) ≤ 3 * (hellingerFunSq μ p₀ q).toReal := by
  have := isProbabilityMeasure_law hp₀
  set Dc : Set 𝒳 := {x | p₀ x ≤ 4 * q x} with hDc
  have hDcm : MeasurableSet Dc := measurableSet_le hp₀.measurable (hq.measurable.const_mul 4)
  set H : 𝒳 → ℝ := fun x ↦ (Real.sqrt (p₀ x) - Real.sqrt (q x)) ^ 2 with hH
  have hHm : Measurable H := by
    have h1 := hp₀.measurable.coe_nnreal_real
    have h2 := hq.measurable.coe_nnreal_real
    exact ((Real.continuous_sqrt.measurable.comp h1).sub
      (Real.continuous_sqrt.measurable.comp h2)).pow_const 2
  have hHint : Integrable H μ :=
    ⟨hHm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
      (ae_of_all _ fun x ↦ sq_nonneg _)).2 (hellingerFunSq_ne_top μ hp₀ hq).lt_top⟩
  have hHval : ∫ x, H x ∂μ = (hellingerFunSq μ p₀ q).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x ↦ sq_nonneg _)
      hHm.aestronglyMeasurable]
    rfl
  have hp₀i := integrable_coe_of_isProbDensity hp₀
  have hqi := integrable_coe_of_isProbDensity hq
  have hCi : Integrable (centralLog p₀ q) (law μ p₀) :=
    (memLp_centralLog hp₀ hq).integrable one_le_two
  have hCi' : Integrable (fun x ↦ (p₀ x : ℝ) • centralLog p₀ q x) μ :=
    (integrable_withDensity_iff_integrable_smul hp₀.measurable).1 hCi
  have hgi : Integrable (fun x ↦ 3 * H x + Dc.indicator (fun x ↦ (p₀ x : ℝ) - q x) x) μ :=
    (hHint.const_mul 3).add ((hp₀i.sub hqi).indicator hDcm)
  rw [law, integral_withDensity_eq_integral_smul hp₀.measurable]
  have hpt : ∀ x, (p₀ x : ℝ) • centralLog p₀ q x ≤
      3 * H x + Dc.indicator (fun x ↦ (p₀ x : ℝ) - q x) x := by
    intro x
    rw [smul_eq_mul]
    have hH0 : 0 ≤ H x := sq_nonneg _
    by_cases h4 : p₀ x ≤ 4 * q x
    · have hxD : x ∈ Dc := h4
      simp only [centralLog, h4, ↓reduceIte, indicator_of_mem hxD, logRatio, hH]
      rcases eq_zero_or_pos (p₀ x) with hx | hx
      · rw [hx, NNReal.coe_zero, zero_mul, Real.sqrt_zero, zero_sub, neg_sq,
          Real.sq_sqrt (q x).coe_nonneg]
        have := (q x).coe_nonneg
        linarith
      have hqx : 0 < q x := by
        by_contra h0
        rw [not_lt, nonpos_iff_eq_zero] at h0
        rw [h0, mul_zero] at h4
        exact hx.ne' (le_antisymm h4 zero_le)
      exact mul_log_div_le (by exact_mod_cast hx) (by exact_mod_cast hqx) (by exact_mod_cast h4)
    · have hxD : x ∉ Dc := h4
      simp only [centralLog, h4, ↓reduceIte, indicator_of_notMem hxD, mul_zero, add_zero]
      linarith
  refine (integral_mono hCi' hgi hpt).trans ?_
  have hsub : Integrable (fun x ↦ (p₀ x : ℝ) - q x) μ := hp₀i.sub hqi
  rw [integral_add (hHint.const_mul 3) (hsub.indicator hDcm), integral_const_mul,
    hHval, integral_indicator hDcm, integral_sub hp₀i.integrableOn hqi.integrableOn]
  have hc1 := integral_add_compl hDcm hp₀i
  have hc2 := integral_add_compl hDcm hqi
  rw [integral_coe_of_isProbDensity hp₀] at hc1
  rw [integral_coe_of_isProbDensity hq] at hc2
  have hcomp : ∫ x in Dcᶜ, (q x : ℝ) ∂μ ≤ ∫ x in Dcᶜ, (p₀ x : ℝ) ∂μ := by
    refine setIntegral_mono_on hqi.integrableOn hp₀i.integrableOn hDcm.compl fun x hx ↦ ?_
    have hx' : 4 * q x < p₀ x := not_le.1 hx
    have : q x ≤ p₀ x := le_trans (by
      have := (q x).coe_nonneg
      exact_mod_cast (show (q x : ℝ) ≤ 4 * q x by linarith)) hx'.le
    exact_mod_cast this
  linarith

/-! ### From the Hellinger distance to its square -/

theorem toReal_hellingerFunSq_le_of_hdist_le {f g : 𝒳 → ℝ≥0} {D d : ℝ} (hD : 0 ≤ D)
    (hd : 0 ≤ d) (h : hdist μ f g ≤ ENNReal.ofReal (D * d)) :
    (hellingerFunSq μ f g).toReal ≤ D ^ 2 * d ^ 2 := by
  have e : hellingerFunSq μ f g = (hdist μ f g) ^ (2 : ℕ) := by
    rw [hdist, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  have : hellingerFunSq μ f g ≤ ENNReal.ofReal (D ^ 2 * d ^ 2) := by
    rw [e, show D ^ 2 * d ^ 2 = (D * d) ^ 2 by ring, ENNReal.ofReal_pow (mul_nonneg hD hd)]
    gcongr
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) this

/-! ### The union bound and Markov's bound for the truncated tail -/

/-- The union bound `Pr(G_n) ≤ n P₀(T_n > L_n)`. -/
theorem measure_exceptionalEvent_le (h : MLEBaseHypotheses μ Pr X p₀ S pn phat δ D)
    (L : ℕ → ℝ≥0∞) (n : ℕ) :
    Pr (exceptionalEvent X p₀ pn L n) ≤ n * law μ p₀ {x | L n < extTail p₀ (pn n) x} := by
  have hpn : IsProbDensity μ (pn n) := h.sieve_density n _ (h.comparator_mem n)
  have hA : MeasurableSet {x | L n < extTail p₀ (pn n) x} :=
    measurableSet_lt measurable_const (measurable_extTail h.density.measurable hpn.measurable)
  have : exceptionalEvent X p₀ pn L n =
      ⋃ i : Fin n, X i ⁻¹' {x | L n < extTail p₀ (pn n) x} := by
    ext ω; simp [exceptionalEvent]
  rw [this]
  refine (measure_iUnion_fintype_le Pr _).trans_eq ?_
  have hi : ∀ i : Fin n, Pr (X i ⁻¹' {x | L n < extTail p₀ (pn n) x}) =
      law μ p₀ {x | L n < extTail p₀ (pn n) x} := fun i ↦ by
    rw [← h.law_obs i, Measure.map_apply (h.measurable_obs i) hA]
  simp only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Linearity of expectation for the extended sample mean: `E ℙ_n f = P f` for `n ≥ 1`. -/
theorem lintegral_ennMean (hX : ∀ i, Measurable (X i)) {P : Measure 𝒳}
    (hlaw : ∀ i, Pr.map (X i) = P) {n : ℕ} (hn : n ≠ 0) {f : 𝒳 → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, ennMean X n f ω ∂Pr = ∫⁻ x, f x ∂P := by
  unfold ennMean
  rw [lintegral_const_mul _ (Finset.measurable_sum (f := fun (i : Fin n) ω ↦ f (X i ω)) _
    fun i _ ↦ hf.comp (hX i)), lintegral_finsetSum (f := fun (i : Fin n) ω ↦ f (X i ω)) _
    fun i _ ↦ hf.comp (hX i)]
  have hi : ∀ i : Fin n, ∫⁻ ω, f (X i ω) ∂Pr = ∫⁻ x, f x ∂P := fun i ↦ by
    rw [← hlaw i, lintegral_map hf (hX i)]
  simp only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast hn) (ENNReal.natCast_ne_top n),
    one_mul]

/-- Markov's bound: if `P f_n ≤ M b_n` eventually and `b_n > 0` for `n ≥ 1`, then the
extended sample mean `ℙ_n f_n` is `O_P^*(b_n)`. -/
theorem opStar_ennMean (hX : ∀ i, Measurable (X i)) {P : Measure 𝒳}
    (hlaw : ∀ i, Pr.map (X i) = P) {f : ℕ → 𝒳 → ℝ≥0∞} (hf : ∀ n, Measurable (f n))
    {b : ℕ → ℝ} (hb : ∀ n, 1 ≤ n → 0 < b n) {M : ℝ}
    (hbound : ∃ N, ∀ n ≥ N, ∫⁻ x, f n x ∂P ≤ ENNReal.ofReal (M * b n)) :
    OPStar Pr (fun n ω ↦ ennMean X n (f n) ω) b := by
  intro ε hε
  obtain ⟨N, hN⟩ := hbound
  set K : ℝ := max M 0 / ε + 1 with hK
  have hK0 : 0 < K := by positivity
  have hεK : M ≤ ε * K := by
    rw [hK, mul_add, mul_div_cancel₀ _ hε.ne', mul_one]
    linarith [le_max_left M 0]
  refine ⟨K, hK0, max N 1, fun n hn ↦ ?_⟩
  have hn1 : 1 ≤ n := le_of_max_le_right hn
  have hbn := hb n hn1
  have ht : ENNReal.ofReal (K * b n) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  calc Pr {ω | ENNReal.ofReal (K * b n) < ennMean X n (f n) ω}
      ≤ Pr {ω | ENNReal.ofReal (K * b n) ≤ ennMean X n (f n) ω} :=
        measure_mono fun ω hω ↦ by
          simp only [mem_ofPred_eq] at hω ⊢; exact hω.le
    _ ≤ (∫⁻ ω, ennMean X n (f n) ω ∂Pr) / ENNReal.ofReal (K * b n) :=
        meas_ge_le_lintegral_div (measurable_ennMean hX n (hf n)).aemeasurable ht
          ENNReal.ofReal_ne_top
    _ = (∫⁻ x, f n x ∂P) / ENNReal.ofReal (K * b n) := by
        rw [lintegral_ennMean hX hlaw (by omega) (hf n)]
    _ ≤ ENNReal.ofReal ε := by
        refine ENNReal.div_le_of_le_mul ((hN n (le_of_max_le_left hn)).trans ?_)
        rw [← ENNReal.ofReal_mul hε.le]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hεK hbn.le

/-! ### The comparator error is `O_P^*(a_n²)` -/

theorem weakComparatorError_opStar (h : MLEBaseHypotheses μ Pr X p₀ S pn phat δ D)
    (L : ℕ → ℝ≥0∞) (M : ℝ)
    (hW2 : ∃ N, ∀ n ≥ N, ∫⁻ x, truncTail p₀ (pn n) (L n) x ∂(law μ p₀) ≤
      ENNReal.ofReal (M * rate δ n ^ 2)) :
    OPStar Pr (weakComparatorError μ X p₀ pn phat L) (fun n ↦ rate δ n ^ 2) := by
  have := h.probability
  have := isProbabilityMeasure_law h.density
  have hpn : ∀ n, IsProbDensity μ (pn n) := fun n ↦ h.sieve_density n _ (h.comparator_mem n)
  obtain ⟨N, hN⟩ := h.approx
  have hH : ∀ n ≥ N, (hellingerFunSq μ p₀ (pn n)).toReal ≤ D ^ 2 * δ n ^ 2 := fun n hn ↦
    toReal_hellingerFunSq_le_of_hdist_le h.D_nonneg (h.rate_nonneg n) (hN n hn)
  have hδa : ∀ n, δ n ≤ rate δ n := fun n ↦ le_max_left _ _
  have ha : ∀ n, 0 ≤ rate δ n := fun n ↦ (h.rate_nonneg n).trans (hδa n)
  have hb : ∀ n, 0 ≤ rate δ n ^ 2 := fun n ↦ sq_nonneg _
  -- the optimization deficit
  have h₁ : OPStar Pr (fun n ω ↦ logLikDeficit (sample X n ω) (pn n) (phat n ω))
      (fun n ↦ rate δ n ^ 2) :=
    h.likelihood.rate_mono ⟨0, fun n _ ↦ pow_le_pow_left₀ (h.rate_nonneg n) (hδa n) 2⟩
  -- the central fluctuation, by Chebyshev
  have hC : 0 ≤ 8 * D ^ 2 := by positivity
  have h₂' := opStar_sampleMean h.measurable_obs h.indep h.law_obs
    (f := fun n ↦ centralLog p₀ (pn n))
    (fun n ↦ measurable_centralLog h.density.measurable (hpn n).measurable)
    (fun n ↦ memLp_centralLog h.density (hpn n))
    (b := fun n ↦ δ n / Real.sqrt n)
    (fun n ↦ div_nonneg (h.rate_nonneg n) (Real.sqrt_nonneg _)) hC
    ⟨max N 1, fun n hn ↦ by
      have hNn : N ≤ n := le_of_max_le_left hn
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
      refine (integral_centralLog_sq_le h.density (hpn n)).trans ?_
      calc 8 * (hellingerFunSq μ p₀ (pn n)).toReal ≤ 8 * (D ^ 2 * δ n ^ 2) := by
            gcongr; exact hH n hNn
        _ = 8 * D ^ 2 * n * (δ n / Real.sqrt n) ^ 2 := by
            rw [div_pow, Real.sq_sqrt (by linarith)]
            field_simp⟩
  have h₂ : OPStar Pr (fun n ω ↦ ENNReal.ofReal |sampleMean X n (centralLog p₀ (pn n)) ω -
      ∫ x, centralLog p₀ (pn n) x ∂(law μ p₀)|) (fun n ↦ rate δ n ^ 2) := by
    refine h₂'.rate_mono ⟨0, fun n _ ↦ ?_⟩
    rw [div_eq_mul_inv, sq]
    exact mul_le_mul (hδa n) (le_max_right _ _) (inv_nonneg.2 (Real.sqrt_nonneg _)) (ha n)
  -- the deterministic central mean
  have h₃ : OPStar Pr (fun n _ ↦ ENNReal.ofReal (∫ x, centralLog p₀ (pn n) x ∂(law μ p₀)))
      (fun n ↦ rate δ n ^ 2) := by
    have hc : 0 ≤ 3 * D ^ 2 := by positivity
    refine OPStar.of_le hb hc ⟨N, fun n hn _ ↦ ENNReal.ofReal_le_ofReal ?_⟩
    refine (integral_centralLog_le h.density (hpn n)).trans ?_
    calc 3 * (hellingerFunSq μ p₀ (pn n)).toReal ≤ 3 * (D ^ 2 * δ n ^ 2) := by
          gcongr; exact hH n hn
      _ ≤ 3 * D ^ 2 * rate δ n ^ 2 := by
          rw [← mul_assoc]; gcongr
          · exact h.rate_nonneg n
          · exact hδa n
  -- the truncated tail mean, by Markov
  have h₄ : OPStar Pr (fun n ω ↦ ennMean X n (truncTail p₀ (pn n) (L n)) ω)
      (fun n ↦ rate δ n ^ 2) :=
    opStar_ennMean h.measurable_obs h.law_obs
      (fun n ↦ measurable_truncTail h.density.measurable (hpn n).measurable (L n))
      (fun n hn ↦ pow_pos (rate_pos δ hn) 2) hW2
  have h₅ := (((h₁.add h₂ hb).add h₃ hb).add h₄ hb).const_mul 2⁻¹
  refine h₅.congr ⟨0, fun n _ ↦ ?_⟩
  funext ω
  simp only [weakComparatorError, Pi.add_apply]
  congr 1
  rw [ENNReal.coe_inv two_ne_zero]
  rfl

/-! ### The empirical lower bound off the exceptional event -/

omit [MeasurableSpace 𝒳] [MeasurableSpace Ω] in
/-- Midpoint concavity on a sample where `p₀` and `p` are positive and the deficit of `q`
against `p` is finite: `ℙ_n m_q ≥ -(E + ℙ_n log(p₀/p))/2`. -/
theorem neg_half_le_sampleMean_mixLog {n : ℕ} {ω : Ω} {p q : 𝒳 → ℝ≥0}
    (hω : ∀ i : Fin n, 0 < p₀ (X i ω) ∧ 0 < p (X i ω))
    (hE : logLikDeficit (sample X n ω) p q ≠ ⊤) :
    -((logLikDeficit (sample X n ω) p q).toReal + sampleMean X n (logRatio p₀ p) ω) / 2 ≤
      sampleMean X n (mixLog p₀ q) ω := by
  set x := sample X n ω with hx
  have hLp : likelihood x p ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ ↦ (hω i).2.ne'
  have hLq : likelihood x q ≠ 0 := by
    intro h0
    apply hE
    simp only [logLikDeficit, hLp, h0, ↓reduceIte]
  have hqpos : ∀ i : Fin n, 0 < q (X i ω) := fun i ↦
    pos_iff_ne_zero.2 (Finset.prod_ne_zero_iff.1 hLq i (Finset.mem_univ _))
  set d := (Real.log (likelihood x p : ℝ) - Real.log (likelihood x q : ℝ)) / n with hd
  have hdef : logLikDeficit x p q = ENNReal.ofReal d := by
    simp only [logLikDeficit, hLp, hLq, ↓reduceIte, hd]
  set a : Fin n → ℝ := fun i ↦ Real.log (p₀ (X i ω)) with ha
  set b : Fin n → ℝ := fun i ↦ Real.log (p (X i ω)) with hb
  set c : Fin n → ℝ := fun i ↦ Real.log (q (X i ω)) with hc
  have hlogp : Real.log (likelihood x p : ℝ) = ∑ i, b i := by
    simp only [likelihood, NNReal.coe_prod, hx, sample, hb]
    exact Real.log_prod fun i _ ↦ by exact_mod_cast (hω i).2.ne'
  have hlogq : Real.log (likelihood x q : ℝ) = ∑ i, c i := by
    simp only [likelihood, NNReal.coe_prod, hx, sample, hc]
    exact Real.log_prod fun i _ ↦ by exact_mod_cast (hqpos i).ne'
  have hℓ : sampleMean X n (logRatio p₀ p) ω = (n : ℝ)⁻¹ * ((∑ i, a i) - ∑ i, b i) := by
    simp only [sampleMean, logRatio, ha, hb]
    rw [← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    exact Real.log_div (by exact_mod_cast (hω i).1.ne') (by exact_mod_cast (hω i).2.ne')
  have hm : (n : ℝ)⁻¹ * (((∑ i, c i) - ∑ i, a i) / 2) ≤ sampleMean X n (mixLog p₀ q) ω := by
    simp only [sampleMean]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (Nat.cast_nonneg _))
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    have hp : (0 : ℝ) < p₀ (X i ω) := by exact_mod_cast (hω i).1
    have hqi : (0 : ℝ) < q (X i ω) := by exact_mod_cast hqpos i
    rw [mixLog_of_pos (hω i).1]
    exact half_log_sub_le_log_mix hp hqi
  have hd' : d = (n : ℝ)⁻¹ * ((∑ i, b i) - ∑ i, c i) := by
    rw [hd, hlogp, hlogq, div_eq_inv_mul]
  have key : (n : ℝ)⁻¹ * (((∑ i, c i) - ∑ i, a i) / 2) =
      (-((n : ℝ)⁻¹ * ((∑ i, b i) - ∑ i, c i)) -
        (n : ℝ)⁻¹ * ((∑ i, a i) - ∑ i, b i)) / 2 := by ring
  rw [← hd', ← hℓ] at key
  rw [hdef, ENNReal.toReal_ofReal']
  have := le_max_left d 0
  linarith

omit [MeasurableSpace Ω] in
/-- The empirical lower bound, pointwise: on a sample with `p₀(X_i) > 0`, off `G_n` and with
`Z_n` finite, `ℙ_n m_{phat_n} ≥ -Z_n`. -/
theorem neg_toReal_weakComparatorError_le {L : ℕ → ℝ≥0∞} {n : ℕ} {ω : Ω}
    (hp₀ : ∀ i : Fin n, 0 < p₀ (X i ω)) (hG : ω ∉ exceptionalEvent X p₀ pn L n)
    (hZ : weakComparatorError μ X p₀ pn phat L n ω ≠ ⊤) :
    -(weakComparatorError μ X p₀ pn phat L n ω).toReal ≤
      sampleMean X n (mixLog p₀ (phat n ω)) ω := by
  set A := logLikDeficit (sample X n ω) (pn n) (phat n ω) with hA
  set E := ∫ x, centralLog p₀ (pn n) x ∂(law μ p₀) with hE
  set F := sampleMean X n (centralLog p₀ (pn n)) ω - E with hF
  set R := ennMean X n (truncTail p₀ (pn n) (L n)) ω with hR
  have hZ' : weakComparatorError μ X p₀ pn phat L n ω =
      2⁻¹ * (A + ENNReal.ofReal |F| + ENNReal.ofReal E + R) := rfl
  have hsum : A + ENNReal.ofReal |F| + ENNReal.ofReal E + R ≠ ⊤ := by
    intro htop
    apply hZ
    rw [hZ', htop]
    exact ENNReal.mul_top (by norm_num)
  have hAt : A ≠ ⊤ := fun h' ↦ hsum (by simp [h'])
  have hRt : R ≠ ⊤ := fun h' ↦ hsum (by simp [h'])
  have hle : ∀ i : Fin n, extTail p₀ (pn n) (X i ω) ≤ L n := by
    intro i
    by_contra hlt
    exact hG ⟨i, not_le.1 hlt⟩
  have htr : ∀ i : Fin n, truncTail p₀ (pn n) (L n) (X i ω) = extTail p₀ (pn n) (X i ω) :=
    fun i ↦ by simp only [truncTail, hle i, ↓reduceIte]
  have hfin : ∀ i : Fin n, extTail p₀ (pn n) (X i ω) ≠ ⊤ := by
    intro i htop
    apply hRt
    rw [hR, ennMean, ENNReal.mul_eq_top]
    left
    refine ⟨ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top n), ?_⟩
    exact ENNReal.sum_eq_top.2 ⟨i, Finset.mem_univ _, by rw [htr, htop]⟩
  have hpn : ∀ i : Fin n, 0 < pn n (X i ω) := by
    intro i
    by_contra h0
    rw [not_lt, nonpos_iff_eq_zero] at h0
    exact hfin i (by simp [extTail, hp₀ i, h0])
  have hdec : ∀ i : Fin n, logRatio p₀ (pn n) (X i ω) =
      centralLog p₀ (pn n) (X i ω) + (extTail p₀ (pn n) (X i ω)).toReal := by
    intro i
    have hns : ¬ (0 < p₀ (X i ω) ∧ pn n (X i ω) = 0) := fun h' ↦ (hpn i).ne' h'.2
    by_cases h4 : p₀ (X i ω) ≤ 4 * pn n (X i ω)
    · simp [centralLog, extTail, h4, not_lt.2 h4, hns]
    · have h4' := not_le.1 h4
      rw [extTail_eq_ofReal_logRatio hns h4', ENNReal.toReal_ofReal]
      · simp [centralLog, h4]
      · refine Real.log_nonneg ?_
        have hq : (0 : ℝ) < pn n (X i ω) := by exact_mod_cast hpn i
        rw [le_div_iff₀ hq, one_mul]
        have h4r : (4 : ℝ) * pn n (X i ω) < p₀ (X i ω) := by exact_mod_cast h4'
        linarith
  have hRr : R.toReal = (n : ℝ)⁻¹ * ∑ i : Fin n, (extTail p₀ (pn n) (X i ω)).toReal := by
    rw [hR, ennMean, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_sum fun i _ ↦ by rw [htr]; exact hfin i]
    simp only [htr]
  have hℓ : sampleMean X n (logRatio p₀ (pn n)) ω = F + E + R.toReal := by
    rw [hF, hRr, sub_add_cancel, sampleMean, sampleMean, ← mul_add, ← Finset.sum_add_distrib]
    simp only [hdec]
  have h3 : A + ENNReal.ofReal |F| + ENNReal.ofReal E ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hAt, ENNReal.ofReal_ne_top⟩,
      ENNReal.ofReal_ne_top⟩
  have hZr : (weakComparatorError μ X p₀ pn phat L n ω).toReal =
      2⁻¹ * (A.toReal + |F| + max E 0 + R.toReal) := by
    rw [hZ', ENNReal.toReal_mul, ENNReal.toReal_add h3 hRt,
      ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hAt, ENNReal.ofReal_ne_top⟩)
        ENNReal.ofReal_ne_top,
      ENNReal.toReal_add hAt ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (abs_nonneg _),
      ENNReal.toReal_ofReal', ENNReal.toReal_inv]
    norm_num
  have hmain := neg_half_le_sampleMean_mixLog (X := X) (p := pn n) (q := phat n ω)
    (fun i ↦ ⟨hp₀ i, hpn i⟩) hAt
  rw [hℓ] at hmain
  rw [hZr]
  have := le_abs_self F
  have := le_max_left E 0
  linarith

/-- The empirical lower bound: almost surely, off the exceptional event `G_n` and when `Z_n` is
finite, `ℙ_n m_{phat_n} ≥ -Z_n`. -/
theorem sampleMean_mixLog_ge_weak (h : MLEBaseHypotheses μ Pr X p₀ S pn phat δ D)
    (L : ℕ → ℝ≥0∞) :
    ∃ N, ∀ n ≥ N, ∀ᵐ ω ∂Pr, ω ∉ exceptionalEvent X p₀ pn L n →
      weakComparatorError μ X p₀ pn phat L n ω ≠ ⊤ →
        -(weakComparatorError μ X p₀ pn phat L n ω).toReal ≤
          sampleMean X n (mixLog p₀ (phat n ω)) ω := by
  refine ⟨0, fun n _ ↦ ?_⟩
  have hpos : ∀ᵐ ω ∂Pr, ∀ i : Fin n, 0 < p₀ (X i ω) := by
    rw [ae_all_iff]
    intro i
    have h1 : ∀ᵐ y ∂(Pr.map (X i)), 0 < p₀ y := by
      rw [h.law_obs i]; exact ae_law_pos h.density.measurable
    exact ae_of_ae_map (h.measurable_obs i).aemeasurable h1
  filter_upwards [hpos] with ω hω hG hZ
  exact neg_toReal_weakComparatorError_le hω hG hZ

end Hellinger.MLE
