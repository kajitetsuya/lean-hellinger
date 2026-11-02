/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.MLE.MixLog
public import Hellinger.MLE.Bracketing

/-!
Entropy transfer for the mixture log-ratio criterion `m_f = log((p₀ + f)/(2 p₀))`.

With `P₀ = p₀ · μ`:
* every `m_f` with `∫ f dμ < ∞` has finite Bernstein "norm" (`bernsteinFun_mixLog_lt_top`);
* `‖m_u - m_l‖²_{P₀,B} ≤ 6 h²(l, u)` (`bernsteinFunSq_mixLog_sub_le`), hence
  `‖m_u - m_l‖_{P₀,B} ≤ √6 h(l, u)` (`bernsteinFun_mixLog_sub_le`);
* Hellinger `ε`-brackets of `F` map to Bernstein `3ε`-brackets of `{m_p : p ∈ F}`, so
  `J̃_[](3r, {m_p : p ∈ F}, ‖·‖_{P₀,B}) ≤ 3 J̃_[](r, F, h)`
  (`bBracketingIntegral_mixLogClass_le`).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Hellinger.MLE

/-! ### Real inequalities -/

theorem bernsteinKernel_one_neg (t : ℝ) : bernsteinKernel 1 (-t) = bernsteinKernel 1 t := by
  simp [bernsteinKernel, abs_neg]

/-- `a K(log((a + b)/(2a))) ≤ 5a + b` for `a > 0`, `b ≥ 0`, with `K = bernsteinKernel 1`. -/
theorem mul_bernsteinKernel_log_mix_le {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    a * bernsteinKernel 1 (Real.log ((a + b) / (2 * a))) ≤ 5 * a + b := by
  set t := (a + b) / (2 * a) with ht
  have htpos : 0 < t := by positivity
  have h2at : 2 * a * t = a + b := by rw [ht]; field_simp
  have htinv : t⁻¹ ≤ 2 := by
    rw [ht, inv_div, div_le_iff₀ (by positivity)]; linarith
  have hexp : Real.exp |Real.log t| ≤ t + t⁻¹ := by
    rcases le_total 0 (Real.log t) with h | h
    · rw [abs_of_nonneg h, Real.exp_log htpos]
      linarith [inv_pos.mpr htpos]
    · rw [abs_of_nonpos h, Real.exp_neg, Real.exp_log htpos]
      linarith
  have hK : bernsteinKernel 1 (Real.log t) ≤ 2 * (t + t⁻¹) := by
    simp only [bernsteinKernel, one_mul]
    linarith [abs_nonneg (Real.log t)]
  calc a * bernsteinKernel 1 (Real.log t) ≤ a * (2 * (t + t⁻¹)) :=
        mul_le_mul_of_nonneg_left hK ha.le
    _ = 2 * a * t + 2 * a * t⁻¹ := by ring
    _ ≤ (a + b) + 2 * a * 2 := by
        rw [h2at]; gcongr
    _ = 5 * a + b := by ring

/-- `√(a + u) - √(a + l) ≤ √u - √l` for `a ≥ 0` and `0 ≤ l ≤ u`. -/
theorem sqrt_add_sub_sqrt_add_le {a u l : ℝ} (ha : 0 ≤ a) (hl : 0 ≤ l) (hlu : l ≤ u) :
    Real.sqrt (a + u) - Real.sqrt (a + l) ≤ Real.sqrt u - Real.sqrt l := by
  have hu : 0 ≤ u := hl.trans hlu
  set x := Real.sqrt (a + u)
  set y := Real.sqrt (a + l)
  set s := Real.sqrt u
  set r := Real.sqrt l
  have hx : 0 ≤ x := Real.sqrt_nonneg _
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hx2 : x ^ 2 = a + u := Real.sq_sqrt (by linarith)
  have hy2 : y ^ 2 = a + l := Real.sq_sqrt (by linarith)
  have hs2 : s ^ 2 = u := Real.sq_sqrt hu
  have hr2 : r ^ 2 = l := Real.sq_sqrt hl
  have hsq : (x * r) ^ 2 ≤ (s * y) ^ 2 := by
    rw [mul_pow, mul_pow, hx2, hy2, hs2, hr2]; nlinarith
  have hxr : x * r ≤ s * y := by
    nlinarith [mul_nonneg hx hr, mul_nonneg hs hy]
  have hsq2 : (x + r) ^ 2 ≤ (s + y) ^ 2 := by nlinarith
  have : x + r ≤ s + y := by nlinarith [add_nonneg hx hr, add_nonneg hs hy]
  linarith

/-- The pointwise size bound, ordered case. -/
theorem mul_bernsteinKernel_log_ratio_le_of_le {a u l : ℝ} (ha : 0 < a) (hl : 0 ≤ l)
    (hlu : l ≤ u) :
    a * bernsteinKernel 1 (Real.log ((a + u) / (2 * a)) - Real.log ((a + l) / (2 * a))) ≤
      6 * (Real.sqrt u - Real.sqrt l) ^ 2 := by
  have hu : 0 ≤ u := hl.trans hlu
  have hA : 0 < a + u := by linarith
  have hB : 0 < a + l := by linarith
  set x := Real.sqrt (a + u) with hxdef
  set y := Real.sqrt (a + l) with hydef
  have hx : 0 < x := Real.sqrt_pos.mpr hA
  have hy : 0 < y := Real.sqrt_pos.mpr hB
  have hx2 : x ^ 2 = a + u := Real.sq_sqrt hA.le
  have hy2 : y ^ 2 = a + l := Real.sq_sqrt hB.le
  have hyx : y ≤ x := Real.sqrt_le_sqrt (by linarith)
  have hlog : Real.log ((a + u) / (2 * a)) - Real.log ((a + l) / (2 * a)) =
      2 * Real.log (x / y) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    have : (a + u) / (2 * a) / ((a + l) / (2 * a)) = (x / y) ^ 2 := by
      rw [div_pow, hx2, hy2]; field_simp
    rw [this, Real.log_pow]; push_cast; ring
  have hxy : 0 < x / y := div_pos hx hy
  have hlog0 : 0 ≤ Real.log (x / y) := Real.log_nonneg (by rw [le_div_iff₀ hy]; linarith)
  have hlogge : 1 - y / x ≤ Real.log (x / y) := by
    have := Real.one_sub_inv_le_log_of_pos hxy
    rwa [inv_div] at this
  have hexp : Real.exp (2 * Real.log (x / y)) = x ^ 2 / y ^ 2 := by
    rw [show 2 * Real.log (x / y) = Real.log ((x / y) ^ 2) by rw [Real.log_pow]; push_cast; ring,
      Real.exp_log (by positivity), div_pow]
  rw [hlog]
  have hK : bernsteinKernel 1 (2 * Real.log (x / y)) =
      2 * (x ^ 2 / y ^ 2 - 1 - 2 * Real.log (x / y)) := by
    simp only [bernsteinKernel, one_mul]
    rw [abs_of_nonneg (by linarith), hexp]
  rw [hK]
  -- the bracket `S = x²/y² - 3 + 2y/x = (x - y)²(x + 2y)/(x y²)` dominates the kernel
  set S := x ^ 2 / y ^ 2 - 3 + 2 * (y / x) with hS
  have hS_eq : y ^ 2 * S = (x - y) ^ 2 * (x + 2 * y) / x := by
    rw [hS]; field_simp; ring
  have hS0 : 0 ≤ S := by
    have h0 : y ^ 2 * 0 ≤ y ^ 2 * S := by rw [mul_zero, hS_eq]; positivity
    exact le_of_mul_le_mul_left h0 (by positivity)
  have hay : a ≤ y ^ 2 := by rw [hy2]; linarith
  have hxy3 : (x + 2 * y) / x ≤ 3 := by rw [div_le_iff₀ hx]; linarith
  have hdiff : x - y ≤ Real.sqrt u - Real.sqrt l := sqrt_add_sub_sqrt_add_le ha.le hl hlu
  calc a * (2 * (x ^ 2 / y ^ 2 - 1 - 2 * Real.log (x / y))) ≤ a * (2 * S) := by
        gcongr; rw [hS]; linarith
    _ ≤ y ^ 2 * (2 * S) := by gcongr
    _ = 2 * ((x - y) ^ 2 * ((x + 2 * y) / x)) := by rw [mul_left_comm, hS_eq]; ring
    _ ≤ 2 * ((x - y) ^ 2 * 3) := by gcongr
    _ = 6 * (x - y) ^ 2 := by ring
    _ ≤ 6 * (Real.sqrt u - Real.sqrt l) ^ 2 := by
        gcongr

/-- The pointwise size bound, both orders. -/
theorem mul_bernsteinKernel_log_ratio_le {a u l : ℝ} (ha : 0 < a) (hl : 0 ≤ l) (hu : 0 ≤ u) :
    a * bernsteinKernel 1 (Real.log ((a + u) / (2 * a)) - Real.log ((a + l) / (2 * a))) ≤
      6 * (Real.sqrt l - Real.sqrt u) ^ 2 := by
  rcases le_total l u with hlu | hul
  · rw [show (Real.sqrt l - Real.sqrt u) ^ 2 = (Real.sqrt u - Real.sqrt l) ^ 2 by ring]
    exact mul_bernsteinKernel_log_ratio_le_of_le ha hl hlu
  · rw [← bernsteinKernel_one_neg, neg_sub]
    exact mul_bernsteinKernel_log_ratio_le_of_le ha hu hul

/-! ### Bernstein "norms" of the criterion -/

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-- Integrals against `P₀ = p₀ · μ` are dominated by `∫ p₀ · (·) dμ`; no measurability of
the integrand is needed. -/
theorem lintegral_law_le (μ : Measure 𝒳) {p₀ : 𝒳 → ℝ≥0} (hp₀ : Measurable p₀)
    (g : 𝒳 → ℝ≥0∞) : ∫⁻ x, g x ∂law μ p₀ ≤ ∫⁻ x, (p₀ x : ℝ≥0∞) * g x ∂μ :=
  lintegral_withDensity_le_lintegral_mul μ hp₀.coe_nnreal_ennreal g

/-- (a) Admissibility: `‖m_f‖²_{P₀,B} ≤ 5 + ∫ f dμ`. -/
theorem bernsteinFunSq_mixLog_le_mass {μ : Measure 𝒳} {p₀ : 𝒳 → ℝ≥0} (hp₀ : IsProbDensity μ p₀)
    (f : 𝒳 → ℝ≥0) :
    bernsteinFunSq (law μ p₀) (mixLog p₀ f) ≤ 5 + ∫⁻ x, (f x : ℝ≥0∞) ∂μ := by
  unfold bernsteinFunSq
  refine (lintegral_law_le μ hp₀.measurable _).trans ?_
  have hpt : ∀ x, (p₀ x : ℝ≥0∞) * ENNReal.ofReal (bernsteinKernel 1 (mixLog p₀ f x)) ≤
      5 * (p₀ x : ℝ≥0∞) + (f x : ℝ≥0∞) := by
    intro x
    rcases eq_zero_or_pos (p₀ x) with hx | hx
    · simp [hx]
    rw [mixLog_of_pos hx, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (p₀ x).coe_nonneg]
    have hr := mul_bernsteinKernel_log_mix_le (a := (p₀ x : ℝ)) (b := (f x : ℝ))
      (by exact_mod_cast hx) (f x).coe_nonneg
    calc ENNReal.ofReal ((p₀ x : ℝ) * bernsteinKernel 1
            (Real.log (((p₀ x : ℝ) + f x) / (2 * p₀ x))))
        ≤ ENNReal.ofReal (5 * (p₀ x : ℝ) + f x) := ENNReal.ofReal_le_ofReal hr
      _ = 5 * ENNReal.ofReal (p₀ x : ℝ) + (f x : ℝ≥0∞) := by
        rw [ENNReal.ofReal_add (by positivity) (f x).coe_nonneg, ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]
  calc ∫⁻ x, (p₀ x : ℝ≥0∞) * ENNReal.ofReal (bernsteinKernel 1 (mixLog p₀ f x)) ∂μ
      ≤ ∫⁻ x, 5 * (p₀ x : ℝ≥0∞) + (f x : ℝ≥0∞) ∂μ := lintegral_mono hpt
    _ = 5 * ∫⁻ x, (p₀ x : ℝ≥0∞) ∂μ + ∫⁻ x, (f x : ℝ≥0∞) ∂μ := by
        rw [lintegral_add_left (hp₀.measurable.coe_nnreal_ennreal.const_mul _),
          lintegral_const_mul _ hp₀.measurable.coe_nnreal_ennreal]
    _ = 5 + ∫⁻ x, (f x : ℝ≥0∞) ∂μ := by rw [hp₀.lintegral_eq_one, mul_one]

/-- (a) Admissibility: `m_f` has finite Bernstein "norm" when `∫ f dμ < ∞`. -/
theorem bernsteinFun_mixLog_lt_top {μ : Measure 𝒳} {p₀ : 𝒳 → ℝ≥0} (hp₀ : IsProbDensity μ p₀)
    {f : 𝒳 → ℝ≥0} (hf : ∫⁻ x, (f x : ℝ≥0∞) ∂μ < ∞) :
    bernsteinFun (law μ p₀) (mixLog p₀ f) < ∞ := by
  unfold bernsteinFun
  refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
  exact ((bernsteinFunSq_mixLog_le_mass hp₀ f).trans_lt
    (ENNReal.add_lt_top.mpr ⟨by simp, hf⟩)).ne

/-- (b) Size: `‖m_u - m_l‖²_{P₀,B} ≤ 6 h²(l, u)`. No order, measurability or integrability of
`l, u` is needed. -/
theorem bernsteinFunSq_mixLog_sub_le {μ : Measure 𝒳} {p₀ : 𝒳 → ℝ≥0} (hp₀ : Measurable p₀)
    (l u : 𝒳 → ℝ≥0) :
    bernsteinFunSq (law μ p₀) (mixLog p₀ u - mixLog p₀ l) ≤ 6 * hellingerFunSq μ l u := by
  unfold bernsteinFunSq hellingerFunSq
  refine (lintegral_law_le μ hp₀ _).trans ?_
  rw [← lintegral_const_mul' _ _ (by simp)]
  refine lintegral_mono fun x ↦ ?_
  rcases eq_zero_or_pos (p₀ x) with hx | hx
  · simp [hx]
  rw [Pi.sub_apply, mixLog_of_pos hx, mixLog_of_pos hx, ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_mul (p₀ x).coe_nonneg, ← ENNReal.ofReal_ofNat 6,
    ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (mul_bernsteinKernel_log_ratio_le (by exact_mod_cast hx)
    (l x).coe_nonneg (u x).coe_nonneg)

/-- (d) `‖m_u - m_l‖_{P₀,B} ≤ √6 h(l, u)`. -/
theorem bernsteinFun_mixLog_sub_le {μ : Measure 𝒳} {p₀ : 𝒳 → ℝ≥0} (hp₀ : Measurable p₀)
    (l u : 𝒳 → ℝ≥0) :
    bernsteinFun (law μ p₀) (mixLog p₀ u - mixLog p₀ l) ≤
      ENNReal.ofReal (Real.sqrt 6) * hdist μ l u := by
  unfold bernsteinFun hdist
  calc bernsteinFunSq (law μ p₀) (mixLog p₀ u - mixLog p₀ l) ^ (1 / 2 : ℝ)
      ≤ (6 * hellingerFunSq μ l u) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (bernsteinFunSq_mixLog_sub_le hp₀ l u) (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt 6) * hellingerFunSq μ l u ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), Real.sqrt_eq_rpow,
          ← ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by norm_num), ENNReal.ofReal_ofNat]

/-! ### Transfer of bracketing numbers and integrals -/

/-- A Hellinger `ε`-bracket cover of `F` maps to a Bernstein `3ε`-bracket cover of
`{m_p : p ∈ F}`. -/
theorem bracketingNumber_mixLogClass_le {μ : Measure 𝒳} {p₀ : 𝒳 → ℝ≥0}
    (hp₀ : IsProbDensity μ p₀) (F : Set (𝒳 → ℝ≥0)) {ε : ℝ} (hε : 0 < ε) :
    bracketingNumber (BernsteinAdmissible (law μ p₀)) (bernsteinBracketSize (law μ p₀))
        (ENNReal.ofReal (3 * ε)) (mixLogClass p₀ F) ≤
      hBracketingNumber μ (ENNReal.ofReal ε) F := by
  have h6 : Real.sqrt 6 < 3 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  unfold hBracketingNumber
  refine le_iInf₂ fun n ⟨b, hb⟩ ↦ iInf₂_le_of_le n ?_ le_rfl
  refine ⟨fun i ↦ (mixLog p₀ (b i).1, mixLog p₀ (b i).2), fun i ↦ ⟨?_, ?_, ?_⟩, ?_⟩
  · obtain ⟨⟨hlm, hum, hli, hui⟩, -, -⟩ := hb.1 i
    exact ⟨measurable_mixLog hp₀.measurable hlm, measurable_mixLog hp₀.measurable hum,
      bernsteinFun_mixLog_lt_top hp₀ hli, bernsteinFun_mixLog_lt_top hp₀ hui⟩
  · exact mixLog_mono p₀ (hb.1 i).2.1
  · have hsize : hdist μ (b i).1 (b i).2 < ENNReal.ofReal ε := (hb.1 i).2.2
    calc bernsteinBracketSize (law μ p₀) (mixLog p₀ (b i).1) (mixLog p₀ (b i).2)
        ≤ ENNReal.ofReal (Real.sqrt 6) * hdist μ (b i).1 (b i).2 :=
          bernsteinFun_mixLog_sub_le hp₀.measurable _ _
      _ ≤ ENNReal.ofReal (Real.sqrt 6) * ENNReal.ofReal ε := by gcongr
      _ = ENNReal.ofReal (Real.sqrt 6 * ε) := (ENNReal.ofReal_mul (Real.sqrt_nonneg _)).symm
      _ < ENNReal.ofReal (3 * ε) :=
          (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by nlinarith)
  · rintro _ ⟨p, hp, rfl⟩
    obtain ⟨i, hli, hui⟩ := hb.2 p hp
    exact ⟨i, mixLog_mono p₀ hli, mixLog_mono p₀ hui⟩

/-- (c) Entropy transfer: `J̃_[](3r, {m_p : p ∈ F}, ‖·‖_{P₀,B}) ≤ 3 J̃_[](r, F, h)`. -/
theorem bBracketingIntegral_mixLogClass_le {μ : Measure 𝒳} {p₀ : 𝒳 → ℝ≥0}
    (hp₀ : IsProbDensity μ p₀) (F : Set (𝒳 → ℝ≥0)) (r : ℝ) :
    bBracketingIntegral (law μ p₀) (3 * r) (mixLogClass p₀ F) ≤
      3 * hBracketingIntegral μ r F := by
  have h := bracketingIntegral_le_of_bracketingNumber_le (adm := BernsteinAdmissible (law μ p₀))
    (size := bernsteinBracketSize (law μ p₀)) (adm₂ := HellingerAdmissible μ)
    (size₂ := hdist μ) (F₁ := mixLogClass p₀ F) (F₂ := F) (κ := 3) (by norm_num)
    (fun ε hε ↦ bracketingNumber_mixLogClass_le hp₀ F hε) r
  rwa [ENNReal.ofReal_ofNat] at h

end Hellinger.MLE
