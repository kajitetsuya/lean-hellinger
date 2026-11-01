/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.MLE.Defs
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Mgf maximal inequality for finitely many empirical processes

With `φ(x) = eˣ - 1 - x`, facts about the Bernstein functional `‖g‖²_B = 2 P φ(|g|)`:
(B1) monotonicity, (B2) `P g² ≤ ‖g‖²_B`, (B3) `φ(λx) ≤ λ² φ(x)` for `0 ≤ λ ≤ 1`, and
(B4) `eᵘ - 1 - u ≤ φ(|u|)`; Lemma G, the one-variable mgf bounds; and Lemma M*, the
log-sum-exp maximal inequality for finitely many empirical processes. These replace
Bernstein's inequality and the Orlicz-norm maximal lemma in the proof of van der Vaart and
Wellner's Theorem 2.14.18' (see `docs/Theorem8.md`).
-/

@[expose] public section

open MeasureTheory Set Finset
open scoped ENNReal NNReal Nat

namespace Hellinger.VdW

/-! ### Scalar facts -/

/-- (B3) in scaling form: `φ(λx) ≤ λ² φ(x)` for `0 ≤ λ ≤ 1`, `x ≥ 0`, `φ(x) = eˣ - 1 - x`. -/
theorem exp_mul_sub_le_sq_mul {l x : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hx : 0 ≤ x) :
    Real.exp (l * x) - 1 - l * x ≤ l ^ 2 * (Real.exp x - 1 - x) := by
  have key : ∀ y : ℝ, HasSum (fun n : ℕ ↦ y ^ (n + 2) / ((n + 2)! : ℝ))
      (Real.exp y - 1 - y) := by
    intro y
    have h := NormedSpace.expSeries_div_hasSum_exp y
    rw [← Real.exp_eq_exp_ℝ] at h
    have h2 := (hasSum_nat_add_iff' 2).mpr h
    simpa [Finset.sum_range_succ, sub_sub] using h2
  have hR := (key x).mul_left (l ^ 2)
  refine hasSum_le (fun n ↦ ?_) (key (l * x)) hR
  have hpow : l ^ n ≤ 1 := pow_le_one₀ hl0 hl1
  have hxn : 0 ≤ x ^ (n + 2) := pow_nonneg hx _
  have hf : (0 : ℝ) < ((n + 2)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
  rw [mul_pow, ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ hf.le
  have : l ^ (n + 2) = l ^ 2 * l ^ n := by ring
  rw [this]
  have hl2 : 0 ≤ l ^ 2 := sq_nonneg l
  calc l ^ 2 * l ^ n * x ^ (n + 2) ≤ l ^ 2 * 1 * x ^ (n + 2) := by gcongr
    _ = l ^ 2 * x ^ (n + 2) := by ring

/-- (B3), second consequence: `φ(x) ≤ x²` for `0 ≤ x ≤ 1`. -/
theorem exp_sub_le_sq_of_le_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x - 1 - x ≤ x ^ 2 := by
  have h := exp_mul_sub_le_sq_mul hx0 hx1 zero_le_one
  have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  rw [mul_one] at h
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  nlinarith

/-- (B4): `eᵘ - 1 - u ≤ φ(|u|)`. -/
theorem exp_sub_le_exp_abs_sub (u : ℝ) :
    Real.exp u - 1 - u ≤ Real.exp |u| - 1 - |u| := by
  rcases le_or_gt 0 u with hu | hu
  · rw [abs_of_nonneg hu]
  · rw [abs_of_neg hu]
    have hs := Real.sinh_le_self_iff.mpr hu.le
    rw [Real.sinh_eq] at hs
    linarith

/-- `φ` is monotone on `[0, ∞)`. -/
theorem exp_sub_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Real.exp a - 1 - a ≤ Real.exp b - 1 - b := by
  have h1 := Real.add_one_le_exp (b - a)
  have h2 : Real.exp b = Real.exp a * Real.exp (b - a) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : 1 ≤ Real.exp a := Real.one_le_exp ha
  nlinarith

/-- `y² ≤ 2 φ(|y|)`. -/
theorem sq_le_bernsteinKernel (y : ℝ) : y ^ 2 ≤ bernsteinKernel 1 y := by
  have h := Real.quadratic_le_exp_of_nonneg (abs_nonneg y)
  unfold bernsteinKernel
  rw [one_mul]
  have : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
  nlinarith

/-- Lemma G pointwise bound, Bernstein case: for `0 ≤ λ ≤ 1`,
`e^{λy} ≤ 1 + λy + (λ²/2) · 2(e^{|y|} - 1 - |y|)`. -/
theorem exp_le_of_bernstein {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (y : ℝ) :
    Real.exp (l * y) ≤ 1 + l * y + l ^ 2 / 2 * bernsteinKernel 1 y := by
  have h1 := exp_sub_le_exp_abs_sub (l * y)
  rw [abs_mul, abs_of_nonneg hl0] at h1
  have h2 := exp_mul_sub_le_sq_mul hl0 hl1 (abs_nonneg y)
  unfold bernsteinKernel
  rw [one_mul]
  linarith

/-- Lemma G pointwise bound, bounded case: for `|λ y| ≤ 1`, `e^{λy} ≤ 1 + λy + λ² y²`. -/
theorem exp_le_of_abs_le_one {u : ℝ} (hu : |u| ≤ 1) :
    Real.exp u ≤ 1 + u + u ^ 2 := by
  have h1 := exp_sub_le_exp_abs_sub u
  have h2 := exp_sub_le_sq_of_le_one (abs_nonneg u) hu
  rw [sq_abs] at h2
  linarith

/-! ### The Bernstein functional: (B1) and (B2) -/

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

theorem measurable_bernsteinKernel_comp {g : 𝒳 → ℝ} (hg : Measurable g) :
    Measurable fun y ↦ bernsteinKernel 1 (g y) := by
  unfold bernsteinKernel; fun_prop

/-- (B1) monotonicity of the Bernstein functional. -/
theorem bernsteinFunSq_mono (P : Measure 𝒳) {g h : 𝒳 → ℝ} (hgh : ∀ x, |g x| ≤ |h x|) :
    Hellinger.MLE.bernsteinFunSq P g ≤ Hellinger.MLE.bernsteinFunSq P h := by
  unfold Hellinger.MLE.bernsteinFunSq
  refine lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal ?_
  unfold bernsteinKernel
  simp only [one_mul]
  linarith [exp_sub_mono (abs_nonneg (g x)) (hgh x)]

/-- The Bernstein functional of `-g` equals that of `g`. -/
theorem bernsteinFunSq_neg (P : Measure 𝒳) (g : 𝒳 → ℝ) :
    Hellinger.MLE.bernsteinFunSq P (fun x ↦ -g x) = Hellinger.MLE.bernsteinFunSq P g := by
  unfold Hellinger.MLE.bernsteinFunSq bernsteinKernel
  simp only [one_mul, abs_neg]

/-- (B2), extended form: `∫⁻ g² ≤ ‖g‖²_B`. -/
theorem lintegral_sq_le_bernsteinFunSq (P : Measure 𝒳) (g : 𝒳 → ℝ) :
    ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂P ≤ Hellinger.MLE.bernsteinFunSq P g :=
  lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal (sq_le_bernsteinKernel (g x))

/-- Finite Bernstein functional gives an integrable kernel. -/
theorem integrable_bernsteinKernel_comp (P : Measure 𝒳) {g : 𝒳 → ℝ} (hg : Measurable g)
    (hfin : Hellinger.MLE.bernsteinFunSq P g < ⊤) :
    Integrable (fun y ↦ bernsteinKernel 1 (g y)) P :=
  ⟨(measurable_bernsteinKernel_comp hg).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ ↦ bernsteinKernel_nonneg _ _)).mpr hfin⟩

theorem integral_bernsteinKernel_comp (P : Measure 𝒳) {g : 𝒳 → ℝ} (hg : Measurable g) :
    ∫ y, bernsteinKernel 1 (g y) ∂P = (Hellinger.MLE.bernsteinFunSq P g).toReal :=
  integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ ↦ bernsteinKernel_nonneg _ _)
    (measurable_bernsteinKernel_comp hg).aestronglyMeasurable

/-- (B2), integrability: finite Bernstein functional implies `g ∈ L²(P)`. -/
theorem memLp_two_of_bernsteinFunSq_lt_top (P : Measure 𝒳) {g : 𝒳 → ℝ} (hg : Measurable g)
    (hfin : Hellinger.MLE.bernsteinFunSq P g < ⊤) : MemLp g 2 P := by
  rw [memLp_two_iff_integrable_sq hg.aestronglyMeasurable]
  refine (integrable_bernsteinKernel_comp P hg hfin).mono' (by fun_prop) (ae_of_all _ fun y ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_le_bernsteinKernel _

/-- (B2), real form: `∫ g² ≤ ‖g‖²_B` when the Bernstein functional is finite. -/
theorem integral_sq_le_bernsteinFunSq (P : Measure 𝒳) {g : 𝒳 → ℝ} (hg : Measurable g)
    (hfin : Hellinger.MLE.bernsteinFunSq P g < ⊤) :
    ∫ x, g x ^ 2 ∂P ≤ (Hellinger.MLE.bernsteinFunSq P g).toReal := by
  rw [← integral_bernsteinKernel_comp P hg]
  exact integral_mono ((memLp_two_iff_integrable_sq hg.aestronglyMeasurable).mp
    (memLp_two_of_bernsteinFunSq_lt_top P hg hfin))
    (integrable_bernsteinKernel_comp P hg hfin) fun y ↦ sq_le_bernsteinKernel _

/-- Finite Bernstein functional implies integrability. -/
theorem integrable_of_bernsteinFunSq_lt_top (P : Measure 𝒳) [IsFiniteMeasure P] {g : 𝒳 → ℝ}
    (hg : Measurable g) (hfin : Hellinger.MLE.bernsteinFunSq P g < ⊤) : Integrable g P :=
  (memLp_two_of_bernsteinFunSq_lt_top P hg hfin).integrable (by norm_num)

/-! ### Lemma G: one-variable mgf bounds -/

variable (P : Measure 𝒳) [IsProbabilityMeasure P]

/-- Abstract form of Lemma G: a pointwise quadratic upper bound on `e^{λ y}` gives a bound
on the centered mgf. -/
theorem mgf_le_of_pointwise {g h : 𝒳 → ℝ} (hg : Integrable g P) (hh : Integrable h P)
    {l c : ℝ} (hle : ∀ y, Real.exp (l * g y) ≤ 1 + l * g y + h y) (hc : ∫ y, h y ∂P ≤ c) :
    Integrable (fun y ↦ Real.exp (l * (g y - ∫ z, g z ∂P))) P ∧
      ∫ y, Real.exp (l * (g y - ∫ z, g z ∂P)) ∂P ≤ Real.exp c := by
  set μ := ∫ z, g z ∂P
  have h1 : Integrable (fun y ↦ 1 + l * g y) P := (integrable_const 1).add (hg.const_mul l)
  have hdom : Integrable (fun y ↦ Real.exp (-(l * μ)) * (1 + l * g y + h y)) P :=
    (h1.add hh).const_mul _
  have hpt : ∀ y, Real.exp (l * (g y - μ)) ≤ Real.exp (-(l * μ)) * (1 + l * g y + h y) := by
    intro y
    have : Real.exp (l * (g y - μ)) = Real.exp (-(l * μ)) * Real.exp (l * g y) := by
      rw [← Real.exp_add]; ring_nf
    rw [this]
    exact mul_le_mul_of_nonneg_left (hle y) (Real.exp_pos _).le
  have hm : AEStronglyMeasurable (fun y ↦ Real.exp (l * (g y - μ))) P := by
    have := hg.aestronglyMeasurable
    fun_prop
  have hI : Integrable (fun y ↦ Real.exp (l * (g y - μ))) P :=
    hdom.mono' hm (ae_of_all _ fun y ↦ by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hpt y)
  refine ⟨hI, ?_⟩
  have hint : ∫ y, Real.exp (-(l * μ)) * (1 + l * g y + h y) ∂P =
      Real.exp (-(l * μ)) * (1 + l * μ + ∫ y, h y ∂P) := by
    rw [integral_const_mul, integral_add h1 hh, integral_add (integrable_const 1) (hg.const_mul l),
      integral_const_mul]
    simp [μ]
  calc ∫ y, Real.exp (l * (g y - μ)) ∂P
      ≤ ∫ y, Real.exp (-(l * μ)) * (1 + l * g y + h y) ∂P := integral_mono hI hdom hpt
    _ = Real.exp (-(l * μ)) * (1 + l * μ + ∫ y, h y ∂P) := hint
    _ ≤ Real.exp (-(l * μ)) * Real.exp (l * μ + c) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        linarith [Real.add_one_le_exp (l * μ + c)]
    _ = Real.exp c := by rw [← Real.exp_add]; ring_nf

/-- Lemma G (a), sign `+`: if `‖g‖²_B ≤ σ²` and `0 ≤ λ ≤ 1`, then
`E e^{λ(g - Pg)} ≤ exp(λ²σ²/2)`. -/
theorem mgf_le_of_bernstein {g : 𝒳 → ℝ} (hg : Measurable g) {σ : ℝ}
    (hB : Hellinger.MLE.bernsteinFunSq P g ≤ ENNReal.ofReal (σ ^ 2)) {l : ℝ} (hl0 : 0 ≤ l)
    (hl1 : l ≤ 1) :
    Integrable (fun y ↦ Real.exp (l * (g y - ∫ z, g z ∂P))) P ∧
      ∫ y, Real.exp (l * (g y - ∫ z, g z ∂P)) ∂P ≤ Real.exp (l ^ 2 * σ ^ 2 / 2) := by
  have hfin : Hellinger.MLE.bernsteinFunSq P g < ⊤ := hB.trans_lt ENNReal.ofReal_lt_top
  have hk := integrable_bernsteinKernel_comp P hg hfin
  refine mgf_le_of_pointwise P (integrable_of_bernsteinFunSq_lt_top P hg hfin)
    (hk.const_mul (l ^ 2 / 2)) (fun y ↦ exp_le_of_bernstein hl0 hl1 (g y)) ?_
  rw [integral_const_mul, integral_bernsteinKernel_comp P hg]
  have : (Hellinger.MLE.bernsteinFunSq P g).toReal ≤ σ ^ 2 :=
    ENNReal.toReal_le_of_le_ofReal (sq_nonneg σ) hB
  have hl2 : 0 ≤ l ^ 2 / 2 := by positivity
  calc l ^ 2 / 2 * (Hellinger.MLE.bernsteinFunSq P g).toReal ≤ l ^ 2 / 2 * σ ^ 2 :=
        mul_le_mul_of_nonneg_left this hl2
    _ = l ^ 2 * σ ^ 2 / 2 := by ring

/-- Lemma G (a), sign `-`. -/
theorem mgf_neg_le_of_bernstein {g : 𝒳 → ℝ} (hg : Measurable g) {σ : ℝ}
    (hB : Hellinger.MLE.bernsteinFunSq P g ≤ ENNReal.ofReal (σ ^ 2)) {l : ℝ} (hl0 : 0 ≤ l)
    (hl1 : l ≤ 1) :
    Integrable (fun y ↦ Real.exp ((-l) * (g y - ∫ z, g z ∂P))) P ∧
      ∫ y, Real.exp ((-l) * (g y - ∫ z, g z ∂P)) ∂P ≤ Real.exp (l ^ 2 * σ ^ 2 / 2) := by
  have h := mgf_le_of_bernstein P hg.neg (g := fun y ↦ -g y)
    (by rwa [bernsteinFunSq_neg]) hl0 hl1
  have heq : (fun y ↦ Real.exp (l * (-g y - ∫ z, -g z ∂P))) =
      fun y ↦ Real.exp ((-l) * (g y - ∫ z, g z ∂P)) := by
    funext y; rw [integral_neg]; ring_nf
  rwa [heq] at h

/-- Lemma G (b), sign `+`: if `|g| ≤ K`, `P g² ≤ σ²` and `0 ≤ λ ≤ 1/K`, then
`E e^{λ(g - Pg)} ≤ exp(λ²σ²)`. -/
theorem mgf_le_of_bounded {g : 𝒳 → ℝ} (hg : Measurable g) {σ K : ℝ} (hK : 0 < K)
    (hbd : ∀ x, |g x| ≤ K) (h2 : ∫ x, g x ^ 2 ∂P ≤ σ ^ 2) {l : ℝ} (hl0 : 0 ≤ l)
    (hl1 : l ≤ 1 / K) :
    Integrable (fun y ↦ Real.exp (l * (g y - ∫ z, g z ∂P))) P ∧
      ∫ y, Real.exp (l * (g y - ∫ z, g z ∂P)) ∂P ≤ Real.exp (l ^ 2 * σ ^ 2) := by
  have hgi : Integrable g P :=
    (integrable_const K).mono' hg.aestronglyMeasurable (ae_of_all _ fun y ↦ by
      rw [Real.norm_eq_abs]; exact hbd y)
  have hg2 : Integrable (fun y ↦ g y ^ 2) P :=
    (integrable_const (K ^ 2)).mono' (by fun_prop) (ae_of_all _ fun y ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hbd y) 2)
  refine mgf_le_of_pointwise P hgi (hg2.const_mul (l ^ 2)) (fun y ↦ ?_) ?_
  · have hu : |l * g y| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg hl0]
      calc l * |g y| ≤ (1 / K) * K :=
            mul_le_mul hl1 (hbd y) (abs_nonneg _) (by positivity)
        _ = 1 := by field_simp
    have := exp_le_of_abs_le_one hu
    calc Real.exp (l * g y) ≤ 1 + l * g y + (l * g y) ^ 2 := this
      _ = 1 + l * g y + l ^ 2 * g y ^ 2 := by ring
  · rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left h2 (sq_nonneg l)

/-- Lemma G (b), sign `-`. -/
theorem mgf_neg_le_of_bounded {g : 𝒳 → ℝ} (hg : Measurable g) {σ K : ℝ} (hK : 0 < K)
    (hbd : ∀ x, |g x| ≤ K) (h2 : ∫ x, g x ^ 2 ∂P ≤ σ ^ 2) {l : ℝ} (hl0 : 0 ≤ l)
    (hl1 : l ≤ 1 / K) :
    Integrable (fun y ↦ Real.exp ((-l) * (g y - ∫ z, g z ∂P))) P ∧
      ∫ y, Real.exp ((-l) * (g y - ∫ z, g z ∂P)) ∂P ≤ Real.exp (l ^ 2 * σ ^ 2) := by
  have h := mgf_le_of_bounded P hg.neg (g := fun y ↦ -g y) hK
    (fun x ↦ by rw [abs_neg]; exact hbd x) (by simpa using h2) hl0 hl1
  have heq : (fun y ↦ Real.exp (l * (-g y - ∫ z, -g z ∂P))) =
      fun y ↦ Real.exp ((-l) * (g y - ∫ z, g z ∂P)) := by
    funext y; rw [integral_neg]; ring_nf
  rwa [heq] at h


/-! ### Product mgf of the empirical process -/

omit [IsProbabilityMeasure P] in
theorem measurable_empiricalProcess {f : 𝒳 → ℝ} (hf : Measurable f) (n : ℕ) :
    Measurable fun x : Fin n → 𝒳 ↦ Hellinger.MLE.empiricalProcess P f x := by
  unfold Hellinger.MLE.empiricalProcess
  have : ∀ i : Fin n, Measurable fun x : Fin n → 𝒳 ↦ f (x i) :=
    fun i ↦ hf.comp (measurable_pi_apply i)
  fun_prop

omit [IsProbabilityMeasure P] in
/-- `e^{s 𝔾_n f} = ∏_j e^{(s/√n)(f(X_j) - P f)}`. -/
theorem exp_mul_empiricalProcess (f : 𝒳 → ℝ) {n : ℕ} (hn : 0 < n) (s : ℝ) (x : Fin n → 𝒳) :
    Real.exp (s * Hellinger.MLE.empiricalProcess P f x) =
      ∏ j, Real.exp (s / Real.sqrt n * (f (x j) - ∫ y, f y ∂P)) := by
  rw [← Real.exp_sum]
  congr 1
  unfold Hellinger.MLE.empiricalProcess
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hn').ne'
  have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn'.le
  field_simp
  rw [hsq]

/-- Product step: a one-coordinate mgf bound `E e^{(s/√n)(f - Pf)} ≤ e^c` gives
`E e^{s 𝔾_n f} ≤ e^{n c}` under `Pⁿ`. -/
theorem lintegral_exp_empiricalProcess_le {f : 𝒳 → ℝ} {n : ℕ} (hn : 0 < n) {s c : ℝ}
    (hI : Integrable (fun y ↦ Real.exp (s / Real.sqrt n * (f y - ∫ z, f z ∂P))) P)
    (hb : ∫ y, Real.exp (s / Real.sqrt n * (f y - ∫ z, f z ∂P)) ∂P ≤ Real.exp c) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (s * Hellinger.MLE.empiricalProcess P f x))
        ∂(Measure.pi fun _ : Fin n ↦ P) ≤ ENNReal.ofReal (Real.exp (n * c)) := by
  simp_rw [exp_mul_empiricalProcess P f hn s]
  have hprod := Integrable.fintype_prod (μ := fun _ : Fin n ↦ P)
    (f := fun _ y ↦ Real.exp (s / Real.sqrt n * (f y - ∫ z, f z ∂P))) (fun _ ↦ hI)
  rw [← ofReal_integral_eq_lintegral_ofReal hprod
    (ae_of_all _ fun x ↦ Finset.prod_nonneg fun j _ ↦ (Real.exp_pos _).le),
    integral_fintype_prod_eq_pow (ι := Fin n) (μ := P)
      (fun y ↦ Real.exp (s / Real.sqrt n * (f y - ∫ z, f z ∂P))), Fintype.card_fin,
    Real.exp_nat_mul]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (integral_nonneg fun _ ↦ (Real.exp_pos _).le)
    hb n)

/-! ### Lemma M*: the abstract log-sum-exp maximal inequality -/

/-- Abstract Lemma M*: if `E e^{±t Z_i} ≤ e^{t²σ²}` for `0 < t ≤ T`, then
`E max_i |Z_i| ≤ 2σ√(log 2m) + 2 log(2m)/T`. -/
theorem lintegral_iSup_abs_le_of_mgf {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι] [Nonempty ι] (Z : ι → Ω → ℝ)
    (hZ : ∀ i, Measurable (Z i)) {σ T : ℝ} (hσ : 0 < σ) (hT : 0 < T)
    (hmgf : ∀ t, 0 < t → t ≤ T → ∀ i,
      ∫⁻ ω, ENNReal.ofReal (Real.exp (t * Z i ω)) ∂μ ≤ ENNReal.ofReal (Real.exp (t ^ 2 * σ ^ 2)) ∧
      ∫⁻ ω, ENNReal.ofReal (Real.exp ((-t) * Z i ω)) ∂μ ≤
        ENNReal.ofReal (Real.exp (t ^ 2 * σ ^ 2))) :
    ∫⁻ ω, (⨆ i, ENNReal.ofReal |Z i ω|) ∂μ ≤
      ENNReal.ofReal (2 * σ * Real.sqrt (Real.log (2 * Fintype.card ι)) +
        2 * Real.log (2 * Fintype.card ι) / T) := by
  set m : ℝ := (Fintype.card ι : ℝ) with hm
  have hm1 : (1 : ℝ) ≤ m := by
    rw [hm]; exact_mod_cast Fintype.card_pos
  set L := Real.log (2 * m) with hL
  have hLpos : 0 < L := Real.log_pos (by linarith)
  set W : Ω → ℝ := fun ω ↦ ⨆ i, |Z i ω| with hW
  have hWm : Measurable W := Measurable.iSup fun i ↦ continuous_abs.measurable.comp (hZ i)
  have hWnn : ∀ ω, 0 ≤ W ω := fun ω ↦
    (abs_nonneg _).trans (le_ciSup (Set.finite_range fun i ↦ |Z i ω|).bddAbove
      (Classical.arbitrary ι))
  -- Step 1: the sup of `ofReal |Z i|` is at most `ofReal W`.
  have hsup : ∀ ω, (⨆ i, ENNReal.ofReal |Z i ω|) ≤ ENNReal.ofReal (W ω) := fun ω ↦
    iSup_le fun i ↦ ENNReal.ofReal_le_ofReal
      (le_ciSup (Set.finite_range fun i ↦ |Z i ω|).bddAbove i)
  -- Step 2: for each admissible `t`, `E W ≤ L/t + σ² t`.
  have hstep : ∀ t, 0 < t → t ≤ T →
      Integrable W μ ∧ ∫ ω, W ω ∂μ ≤ L / t + σ ^ 2 * t := by
    intro t ht htT
    set e := Real.exp (t ^ 2 * σ ^ 2)
    have hpt : ∀ ω, Real.exp (t * W ω) ≤
        ∑ i, (Real.exp (t * Z i ω) + Real.exp ((-t) * Z i ω)) := by
      intro ω
      obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i ↦ |Z i ω|)
      have hWi : W ω = |Z i ω| := hi.symm
      rw [hWi]
      have h1 : Real.exp (t * |Z i ω|) ≤ Real.exp (t * Z i ω) + Real.exp ((-t) * Z i ω) := by
        rcases abs_choice (Z i ω) with h | h
        · rw [h]; linarith [Real.exp_pos ((-t) * Z i ω)]
        · rw [h, mul_neg, ← neg_mul]; linarith [Real.exp_pos (t * Z i ω)]
      refine h1.trans ?_
      exact Finset.single_le_sum (f := fun i ↦ Real.exp (t * Z i ω) + Real.exp ((-t) * Z i ω))
        (fun j _ ↦ by positivity) (Finset.mem_univ i)
    have hlin : ∫⁻ ω, ENNReal.ofReal (Real.exp (t * W ω)) ∂μ ≤ ENNReal.ofReal (2 * m * e) := by
      calc ∫⁻ ω, ENNReal.ofReal (Real.exp (t * W ω)) ∂μ
          ≤ ∫⁻ ω, ∑ i, (ENNReal.ofReal (Real.exp (t * Z i ω)) +
              ENNReal.ofReal (Real.exp ((-t) * Z i ω))) ∂μ := by
            refine lintegral_mono fun ω ↦ ?_
            refine (ENNReal.ofReal_le_ofReal (hpt ω)).trans (le_of_eq ?_)
            rw [ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ by positivity)]
            exact Finset.sum_congr rfl fun i _ ↦
              ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le
        _ = ∑ i, (∫⁻ ω, ENNReal.ofReal (Real.exp (t * Z i ω)) ∂μ +
              ∫⁻ ω, ENNReal.ofReal (Real.exp ((-t) * Z i ω)) ∂μ) := by
            rw [lintegral_finsetSum _ (fun i _ ↦ by
              have := hZ i
              fun_prop)]
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            exact lintegral_add_left (by have := hZ i; fun_prop) _
        _ ≤ ∑ _i : ι, (ENNReal.ofReal e + ENNReal.ofReal e) :=
            Finset.sum_le_sum fun i _ ↦ add_le_add (hmgf t ht htT i).1 (hmgf t ht htT i).2
        _ = ENNReal.ofReal (2 * m * e) := by
            have he : 0 ≤ e := (Real.exp_pos _).le
            rw [← ENNReal.ofReal_add he he,
              ← ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ by positivity)]
            congr 1
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hm]
            ring
    have hEm : Measurable fun ω ↦ Real.exp (t * W ω) := by fun_prop
    have hEI : Integrable (fun ω ↦ Real.exp (t * W ω)) μ :=
      ⟨hEm.aestronglyMeasurable,
        (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ ↦ (Real.exp_pos _).le)).mpr
          (hlin.trans_lt ENNReal.ofReal_lt_top)⟩
    have hEle : ∫ ω, Real.exp (t * W ω) ∂μ ≤ 2 * m * e := by
      have := hlin
      rw [← ofReal_integral_eq_lintegral_ofReal hEI
        (ae_of_all _ fun _ ↦ (Real.exp_pos _).le)] at this
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp this
    have hWI : Integrable W μ := by
      refine (hEI.const_mul t⁻¹).mono' hWm.aestronglyMeasurable (ae_of_all _ fun ω ↦ ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hWnn ω)]
      have h1 := Real.add_one_le_exp (t * W ω)
      rw [le_inv_mul_iff₀ ht]
      linarith
    refine ⟨hWI, ?_⟩
    set EW := ∫ ω, W ω ∂μ
    set a := t * EW
    have htan : ∀ ω, Real.exp a * (1 - a) + Real.exp a * t * W ω ≤ Real.exp (t * W ω) := by
      intro ω
      have h1 := Real.add_one_le_exp (t * W ω - a)
      have h2 : Real.exp (t * W ω) = Real.exp a * Real.exp (t * W ω - a) := by
        rw [← Real.exp_add]; ring_nf
      rw [h2]
      have := mul_le_mul_of_nonneg_left h1 (Real.exp_pos a).le
      nlinarith
    have hlow : Real.exp a ≤ ∫ ω, Real.exp (t * W ω) ∂μ := by
      have hint : ∫ ω, (Real.exp a * (1 - a) + Real.exp a * t * W ω) ∂μ ≤
          ∫ ω, Real.exp (t * W ω) ∂μ :=
        integral_mono ((integrable_const _).add (hWI.const_mul (Real.exp a * t))) hEI htan
      rw [integral_add (integrable_const _) (hWI.const_mul _), integral_const,
        integral_const_mul] at hint
      simp only [probReal_univ, smul_eq_mul, one_mul] at hint
      have : Real.exp a * (1 - a) + Real.exp a * t * EW = Real.exp a := by
        simp only [a]; ring
      linarith
    have hexp : Real.exp a ≤ Real.exp (L + t ^ 2 * σ ^ 2) := by
      rw [Real.exp_add, hL, Real.exp_log (by linarith)]
      linarith
    have ha : t * EW ≤ L + t ^ 2 * σ ^ 2 := Real.exp_le_exp.mp hexp
    rw [div_add' _ _ _ ht.ne', le_div_iff₀ ht]
    nlinarith
  -- Step 3: choice of `t`.
  have hfin : ∃ t, 0 < t ∧ t ≤ T ∧ L / t + σ ^ 2 * t ≤ 2 * σ * Real.sqrt L + 2 * L / T := by
    set t₀ := Real.sqrt L / σ
    have hsL : 0 < Real.sqrt L := Real.sqrt_pos.mpr hLpos
    have hsq : Real.sqrt L ^ 2 = L := Real.sq_sqrt hLpos.le
    have ht₀ : 0 < t₀ := div_pos hsL hσ
    rcases le_or_gt t₀ T with h | h
    · refine ⟨t₀, ht₀, h, ?_⟩
      have : L / t₀ + σ ^ 2 * t₀ = 2 * σ * Real.sqrt L := by
        simp only [t₀]
        field_simp
        nlinarith [hsq]
      rw [this]
      have : 0 ≤ 2 * L / T := by positivity
      linarith
    · refine ⟨T, hT, le_rfl, ?_⟩
      have h1 : σ * T < Real.sqrt L := by
        simp only [t₀] at h; rwa [lt_div_iff₀ hσ, mul_comm] at h
      have h2 : σ ^ 2 * T ^ 2 ≤ L := by
        rw [← hsq]; nlinarith [mul_pos hσ hT]
      have h3 : σ ^ 2 * T ≤ L / T := by
        rw [le_div_iff₀ hT]; nlinarith
      have h4 : 0 ≤ 2 * σ * Real.sqrt L := by positivity
      have : 2 * L / T = L / T + L / T := by ring
      linarith
  obtain ⟨t, ht, htT, hbound⟩ := hfin
  obtain ⟨hWI, hEW⟩ := hstep t ht htT
  calc ∫⁻ ω, (⨆ i, ENNReal.ofReal |Z i ω|) ∂μ ≤ ∫⁻ ω, ENNReal.ofReal (W ω) ∂μ :=
        lintegral_mono hsup
    _ = ENNReal.ofReal (∫ ω, W ω ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal hWI (ae_of_all _ hWnn)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (hEW.trans hbound)

/-- `log(2m) ≤ 1 + log m`. -/
theorem log_two_mul_le {m : ℝ} (hm : 0 < m) : Real.log (2 * m) ≤ 1 + Real.log m := by
  rw [Real.log_mul (by norm_num) hm.ne']
  have := Real.log_two_lt_d9
  linarith

/-- The final constant comparison. -/
theorem bound_le_of_log_two_mul {m σ T : ℝ} (hm : 1 ≤ m) (hσ : 0 < σ) (hT : 0 < T) :
    2 * σ * Real.sqrt (Real.log (2 * m)) + 2 * Real.log (2 * m) / T ≤
      2 * σ * Real.sqrt (1 + Real.log m) + 2 * (1 / T) * (1 + Real.log m) := by
  have h := log_two_mul_le (m := m) (by linarith)
  have h1 : Real.sqrt (Real.log (2 * m)) ≤ Real.sqrt (1 + Real.log m) := Real.sqrt_le_sqrt h
  have h2 : 2 * Real.log (2 * m) / T ≤ 2 * (1 / T) * (1 + Real.log m) := by
    rw [div_eq_mul_one_div, mul_comm 2 _, mul_assoc]
    have : 0 ≤ 2 * (1 / T) := by positivity
    nlinarith
  nlinarith

/-! ### Lemma M* for the empirical process -/

/-- Lemma M* (a): Bernstein-functional bound. -/
theorem lintegral_iSup_empiricalProcess_le_of_bernstein {ι : Type*} [Fintype ι] [Nonempty ι]
    (g : ι → 𝒳 → ℝ) (hg : ∀ i, Measurable (g i)) {σ : ℝ} (hσ : 0 < σ)
    (hB : ∀ i, Hellinger.MLE.bernsteinFunSq P (g i) ≤ ENNReal.ofReal (σ ^ 2)) {n : ℕ}
    (hn : 0 < n) :
    ∫⁻ x, (⨆ i, ENNReal.ofReal |Hellinger.MLE.empiricalProcess P (g i) x|)
        ∂(Measure.pi fun _ : Fin n ↦ P) ≤
      ENNReal.ofReal (2 * σ * Real.sqrt (1 + Real.log (Fintype.card ι)) +
        2 * (1 / Real.sqrt n) * (1 + Real.log (Fintype.card ι))) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn'
  have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn'.le
  have hexp : ∀ t : ℝ, Real.exp (n * ((t / Real.sqrt n) ^ 2 * σ ^ 2 / 2)) ≤
      Real.exp (t ^ 2 * σ ^ 2) := by
    intro t
    apply Real.exp_le_exp.mpr
    have : n * ((t / Real.sqrt n) ^ 2 * σ ^ 2 / 2) = t ^ 2 * σ ^ 2 / 2 := by
      rw [div_pow, hsq]; field_simp
    rw [this]
    nlinarith [sq_nonneg t, sq_nonneg σ, mul_nonneg (sq_nonneg t) (sq_nonneg σ)]
  have hm1 : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  refine (lintegral_iSup_abs_le_of_mgf (Measure.pi fun _ : Fin n ↦ P) _
    (fun i ↦ measurable_empiricalProcess P (hg i) n) hσ hsn ?_).trans
    (ENNReal.ofReal_le_ofReal (bound_le_of_log_two_mul hm1 hσ hsn))
  intro t ht htT i
  have hl0 : 0 ≤ t / Real.sqrt n := (div_pos ht hsn).le
  have hl1 : t / Real.sqrt n ≤ 1 := (div_le_one hsn).mpr htT
  constructor
  · obtain ⟨hI, hb⟩ := mgf_le_of_bernstein P (hg i) (hB i) hl0 hl1
    exact (lintegral_exp_empiricalProcess_le P hn hI hb).trans
      (ENNReal.ofReal_le_ofReal (hexp t))
  · obtain ⟨hI, hb⟩ := mgf_neg_le_of_bernstein P (hg i) (hB i) hl0 hl1
    rw [← neg_div] at hI hb
    exact (lintegral_exp_empiricalProcess_le P hn hI hb).trans
      (ENNReal.ofReal_le_ofReal (hexp t))

/-- Lemma M* (b): bounded functions with a second-moment bound. -/
theorem lintegral_iSup_empiricalProcess_le_of_bounded {ι : Type*} [Fintype ι] [Nonempty ι]
    (g : ι → 𝒳 → ℝ) (hg : ∀ i, Measurable (g i)) {σ K : ℝ} (hσ : 0 < σ) (hK : 0 < K)
    (hbd : ∀ i x, |g i x| ≤ K) (h2 : ∀ i, ∫ x, g i x ^ 2 ∂P ≤ σ ^ 2) {n : ℕ} (hn : 0 < n) :
    ∫⁻ x, (⨆ i, ENNReal.ofReal |Hellinger.MLE.empiricalProcess P (g i) x|)
        ∂(Measure.pi fun _ : Fin n ↦ P) ≤
      ENNReal.ofReal (2 * σ * Real.sqrt (1 + Real.log (Fintype.card ι)) +
        2 * (K / Real.sqrt n) * (1 + Real.log (Fintype.card ι))) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn'
  have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn'.le
  have hT : 0 < Real.sqrt n / K := div_pos hsn hK
  have hexp : ∀ t : ℝ, Real.exp (n * ((t / Real.sqrt n) ^ 2 * σ ^ 2)) =
      Real.exp (t ^ 2 * σ ^ 2) := by
    intro t
    congr 1
    rw [div_pow, hsq]; field_simp
  have hm1 : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hKT : 1 / (Real.sqrt n / K) = K / Real.sqrt n := one_div_div _ _
  have hfin := (lintegral_iSup_abs_le_of_mgf (Measure.pi fun _ : Fin n ↦ P) _
    (fun i ↦ measurable_empiricalProcess P (hg i) n) hσ hT ?_).trans
    (ENNReal.ofReal_le_ofReal (bound_le_of_log_two_mul hm1 hσ hT))
  · rwa [hKT] at hfin
  intro t ht htT i
  have hl0 : 0 ≤ t / Real.sqrt n := (div_pos ht hsn).le
  have hl1 : t / Real.sqrt n ≤ 1 / K := by
    rw [div_le_iff₀ hsn, one_div_mul_eq_div]
    exact htT
  constructor
  · obtain ⟨hI, hb⟩ := mgf_le_of_bounded P (hg i) hK (hbd i) (h2 i) hl0 hl1
    exact (lintegral_exp_empiricalProcess_le P hn hI hb).trans (le_of_eq (by rw [hexp]))
  · obtain ⟨hI, hb⟩ := mgf_neg_le_of_bounded P (hg i) hK (hbd i) (h2 i) hl0 hl1
    rw [← neg_div] at hI hb
    exact (lintegral_exp_empiricalProcess_le P hn hI hb).trans (le_of_eq (by rw [hexp]))

/-! ### The domination step -/

omit [IsProbabilityMeasure P] in
/-- The domination step: if `|g| ≤ h` pointwise with `h` integrable and `g` integrable, then
`|𝔾_n g| ≤ |𝔾_n h| + 2√n P h` at every sample point. -/
theorem abs_empiricalProcess_le_of_abs_le {g h : 𝒳 → ℝ} (hgi : Integrable g P)
    (hhi : Integrable h P) (hgh : ∀ x, |g x| ≤ h x) {n : ℕ} (x : Fin n → 𝒳) :
    |Hellinger.MLE.empiricalProcess P g x| ≤
      |Hellinger.MLE.empiricalProcess P h x| + 2 * Real.sqrt n * ∫ y, h y ∂P := by
  unfold Hellinger.MLE.empiricalProcess
  have hs : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hni : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
  have hPg : |∫ y, g y ∂P| ≤ ∫ y, h y ∂P :=
    (abs_integral_le_integral_abs).trans (integral_mono hgi.abs hhi hgh)
  have hsum : |∑ i, g (x i)| ≤ ∑ i, h (x i) :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ hgh (x i))
  have h1 : |(n : ℝ)⁻¹ * ∑ i, g (x i) - ∫ y, g y ∂P| ≤
      (n : ℝ)⁻¹ * ∑ i, h (x i) + ∫ y, h y ∂P := by
    refine (abs_sub _ _).trans (add_le_add ?_ hPg)
    rw [abs_mul, abs_of_nonneg hni]
    exact mul_le_mul_of_nonneg_left hsum hni
  rw [abs_mul, abs_of_nonneg hs]
  have h2 : Real.sqrt n * ((n : ℝ)⁻¹ * ∑ i, h (x i) - ∫ y, h y ∂P) ≤
      |Real.sqrt n * ((n : ℝ)⁻¹ * ∑ i, h (x i) - ∫ y, h y ∂P)| := le_abs_self _
  have h3 := mul_le_mul_of_nonneg_left h1 hs
  nlinarith

end Hellinger.VdW
