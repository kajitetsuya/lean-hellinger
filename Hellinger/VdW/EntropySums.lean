/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.MLE.Bracketing
public import Mathlib.Order.SuccPred.IntervalSucc

/-!
The finite entropy sums in the proof of van der Vaart and Wellner's Theorem 2.14.18'
(outlined in `docs/Theorem8.md`).

For a class `F`, a radius `δ > 0` and a finite bracketing integral `J = J̃_[](δ, F)`:
* every bracketing number `N(ε)`, `ε > 0`, is finite;
* `δ ≤ J`;
* with `ε_p = δ / 2^p`, `N_p = N(ε_p)`, `L(m) = 1 + log m` and `M_q = ∏_{p ≤ q} N_p`:
  (F1) `√L(M_q) ≤ Σ_{p ≤ q} √L(N_p)`,
  (F2) `Σ_{q ≤ Q} ε_q Σ_{p ≤ q+1} a_p ≤ 4 Σ_{p ≤ Q+1} ε_p a_p` for real sequences `a`,
  (F3) `Σ_{p ≤ Q} ε_p √L(N_p) ≤ 2 J`, (F4) `δ √L(N_0) ≤ J`,
  (F1-F3) `Σ_{q ≤ Q} ε_q √L(M_{q+1}) ≤ 8 J`, and
  (F0) `Σ_{1 ≤ q ≤ Q} ε_q √L(M_q) ≤ ½ Σ_{q ≤ Q} ε_q √L(M_{q+1})`.
Everything is generic in the bracketing structure, as in `Hellinger.MLE.Bracketing`.
No lower bound `N_p ≥ 1` is assumed: `Real.log 0 = 0`, so `L(0) = 1`.
-/

@[expose] public section

open MeasureTheory
open Set hiding range
open Finset hiding Ioc Ico Ioc_subset_Ioc Ioc_subset_Ioc_right
open scoped ENNReal NNReal

namespace Hellinger.VdW

open Hellinger.MLE

/-! ### The function `L(m) = 1 + log m` -/

/-- `L(m) = 1 + log m` on naturals, with `Real.log 0 = 0`. -/
noncomputable def entropyLog (m : ℕ) : ℝ := 1 + Real.log m

theorem one_le_entropyLog (m : ℕ) : 1 ≤ entropyLog m := by
  unfold entropyLog
  linarith [Real.log_natCast_nonneg m]

theorem entropyLog_mul_le (a b : ℕ) : entropyLog (a * b) ≤ entropyLog a + entropyLog b := by
  unfold entropyLog
  have ha := Real.log_natCast_nonneg a
  have hb := Real.log_natCast_nonneg b
  rcases Nat.eq_zero_or_pos a with rfl | ha0
  · simp only [zero_mul, Nat.cast_zero, Real.log_zero]
    linarith
  rcases Nat.eq_zero_or_pos b with rfl | hb0
  · simp only [mul_zero, Nat.cast_zero, Real.log_zero]
    linarith
  push_cast
  rw [Real.log_mul (by positivity) (by positivity)]
  linarith

theorem sqrt_entropyLog_mul_le (a b : ℕ) :
    √(entropyLog (a * b)) ≤ √(entropyLog a) + √(entropyLog b) := by
  have ha : 0 ≤ entropyLog a := zero_le_one.trans (one_le_entropyLog a)
  have hb : 0 ≤ entropyLog b := zero_le_one.trans (one_le_entropyLog b)
  rw [Real.sqrt_le_left (by positivity)]
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  nlinarith [entropyLog_mul_le a b, mul_nonneg (Real.sqrt_nonneg (entropyLog a))
    (Real.sqrt_nonneg (entropyLog b))]

/-- (F1) `√L(∏_{p ≤ q} N_p) ≤ Σ_{p ≤ q} √L(N_p)`, with no positivity assumption on `N`. -/
theorem sqrt_entropyLog_prod_le (N : ℕ → ℕ) (q : ℕ) :
    √(entropyLog (∏ p ∈ range (q + 1), N p)) ≤ ∑ p ∈ range (q + 1), √(entropyLog (N p)) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [prod_range_succ, sum_range_succ]
    exact (sqrt_entropyLog_mul_le _ _).trans (by linarith)

/-! ### Dyadic sums of real sequences -/

/-- Inductive form of (F2). -/
theorem sum_dyadic_partialSum_add_le {δ : ℝ} (hδ : 0 ≤ δ) {a : ℕ → ℝ} (ha : ∀ p, 0 ≤ a p)
    (Q : ℕ) :
    ∑ q ∈ range (Q + 1), δ / 2 ^ q * ∑ p ∈ range (q + 2), a p
        + δ / 2 ^ Q * ∑ p ∈ range (Q + 2), a p
      ≤ 4 * ∑ p ∈ range (Q + 2), δ / 2 ^ p * a p := by
  induction Q with
  | zero =>
    simp only [zero_add, range_one, sum_singleton, pow_zero, div_one, sum_range_succ,
      range_zero, sum_empty, pow_one]
    nlinarith [ha 0, ha 1]
  | succ Q ih =>
    rw [sum_range_succ (fun q ↦ δ / 2 ^ q * ∑ p ∈ range (q + 2), a p) (Q + 1),
      show Q + 1 + 2 = Q + 2 + 1 by ring, sum_range_succ a (Q + 2),
      sum_range_succ (fun p ↦ δ / 2 ^ p * a p) (Q + 2)]
    have h1 : δ / 2 ^ (Q + 1) = δ / 2 ^ Q / 2 := by rw [pow_succ, div_div]
    have h2 : δ / 2 ^ (Q + 2) = δ / 2 ^ Q / 4 := by
      rw [pow_add, div_div]; norm_num
    rw [h1, h2]
    nlinarith [ih]

/-- (F2) `Σ_{q ≤ Q} ε_q Σ_{p ≤ q+1} a_p ≤ 4 Σ_{p ≤ Q+1} ε_p a_p` for `ε_p = δ / 2^p`. -/
theorem sum_dyadic_partialSum_le {δ : ℝ} (hδ : 0 ≤ δ) {a : ℕ → ℝ} (ha : ∀ p, 0 ≤ a p)
    (Q : ℕ) :
    ∑ q ∈ range (Q + 1), δ / 2 ^ q * ∑ p ∈ range (q + 2), a p
      ≤ 4 * ∑ p ∈ range (Q + 2), δ / 2 ^ p * a p := by
  have h := sum_dyadic_partialSum_add_le hδ ha Q
  have : 0 ≤ δ / 2 ^ Q * ∑ p ∈ range (Q + 2), a p :=
    mul_nonneg (by positivity) (sum_nonneg fun p _ ↦ ha p)
  linarith

/-- (F0) for an arbitrary nonnegative sequence `b`. -/
theorem sum_Ico_dyadic_le_half {δ : ℝ} (hδ : 0 ≤ δ) {b : ℕ → ℝ} (hb : ∀ q, 0 ≤ b q)
    (Q : ℕ) :
    ∑ q ∈ Finset.Ico 1 (Q + 1), δ / 2 ^ q * b q
      ≤ 1 / 2 * ∑ q ∈ range (Q + 1), δ / 2 ^ q * b (q + 1) := by
  rw [sum_Ico_eq_sum_range, show Q + 1 - 1 = Q by omega, sum_range_succ, mul_add, mul_sum]
  have heq : ∑ k ∈ range Q, δ / 2 ^ (1 + k) * b (1 + k)
      = ∑ k ∈ range Q, 1 / 2 * (δ / 2 ^ k * b (k + 1)) := by
    refine sum_congr rfl fun k _ ↦ ?_
    rw [add_comm 1 k, pow_succ]
    field_simp
  have : 0 ≤ 1 / 2 * (δ / 2 ^ Q * b (Q + 1)) := by
    have := hb (Q + 1)
    positivity
  linarith

/-! ### Bracketing numbers along a dyadic grid -/

variable {𝒳 β : Type*} [Preorder β] {adm : (𝒳 → β) → (𝒳 → β) → Prop}
  {size : (𝒳 → β) → (𝒳 → β) → ℝ≥0∞}

/-- `N_p = N(δ / 2^p)` as a natural number (`0` if the bracketing number is infinite). -/
noncomputable def dyadicCount (adm : (𝒳 → β) → (𝒳 → β) → Prop)
    (size : (𝒳 → β) → (𝒳 → β) → ℝ≥0∞) (δ : ℝ) (F : Set (𝒳 → β)) (p : ℕ) : ℕ :=
  (bracketingNumber adm size (ENNReal.ofReal (δ / 2 ^ p)) F).toNat

/-- `M_q = ∏_{p ≤ q} N_p`. -/
noncomputable def dyadicProd (adm : (𝒳 → β) → (𝒳 → β) → Prop)
    (size : (𝒳 → β) → (𝒳 → β) → ℝ≥0∞) (δ : ℝ) (F : Set (𝒳 → β)) (q : ℕ) : ℕ :=
  ∏ p ∈ range (q + 1), dyadicCount adm size δ F p

theorem entropyIntegrand_eq_of_ne_top {N : ℕ∞} (h : N ≠ ⊤) :
    entropyIntegrand N = ENNReal.ofReal √(entropyLog N.toNat) := by
  simp [entropyIntegrand, h, entropyLog]

/-- For an antitone integrand, `(b - a) g(b) ≤ ∫_{(a, b]} g`. -/
theorem ofReal_sub_mul_le_setLIntegral_Ioc {g : ℝ → ℝ≥0∞} (hg : Antitone g) (a b : ℝ) :
    ENNReal.ofReal (b - a) * g b ≤ ∫⁻ x in Ioc a b, g x := by
  calc ENNReal.ofReal (b - a) * g b = ∫⁻ _ in Ioc a b, g b := by
        rw [setLIntegral_const, Real.volume_Ioc, mul_comm]
    _ ≤ ∫⁻ x in Ioc a b, g x := setLIntegral_mono' measurableSet_Ioc fun x hx ↦ hg hx.2

/-- A finite bracketing integral forces every bracketing number `N(ε)`, `ε > 0`, to be finite
(including `ε > δ`): otherwise the integrand is `⊤` on `(0, min(ε, δ)]`. -/
theorem bracketingNumber_ne_top_of_bracketingIntegral_ne_top {δ : ℝ} (hδ : 0 < δ)
    {F : Set (𝒳 → β)} (hJ : bracketingIntegral adm size δ F ≠ ⊤) {ε : ℝ} (hε : 0 < ε) :
    bracketingNumber adm size (ENNReal.ofReal ε) F ≠ ⊤ := by
  intro htop
  apply hJ
  refine eq_top_iff.mpr ?_
  have hm : 0 < min ε δ := lt_min hε hδ
  calc (⊤ : ℝ≥0∞) = ∫⁻ _ in Ioc 0 (min ε δ), (⊤ : ℝ≥0∞) := by
        rw [setLIntegral_const, Real.volume_Ioc,
          ENNReal.top_mul (ENNReal.ofReal_pos.mpr (by linarith)).ne']
    _ ≤ ∫⁻ t in Ioc 0 (min ε δ),
          entropyIntegrand (bracketingNumber adm size (ENNReal.ofReal t) F) := by
        refine setLIntegral_mono' measurableSet_Ioc fun t ht ↦ ?_
        have hle := bracketingNumber_antitone_radius (adm := adm) (size := size) (F := F)
          (ENNReal.ofReal_le_ofReal (ht.2.trans (min_le_left ε δ)))
        rw [htop, top_le_iff] at hle
        simp [entropyIntegrand, hle]
    _ ≤ bracketingIntegral adm size δ F :=
        lintegral_mono_set (Ioc_subset_Ioc_right (min_le_right ε δ))

/-- `δ ≤ J̃(δ, F)` in real values, for a finite bracketing integral. -/
theorem le_toReal_bracketingIntegral (δ : ℝ) {F : Set (𝒳 → β)}
    (hJ : bracketingIntegral adm size δ F ≠ ⊤) :
    δ ≤ (bracketingIntegral adm size δ F).toReal :=
  (ENNReal.ofReal_le_iff_le_toReal hJ).mp (ofReal_le_bracketingIntegral δ F)

/-- At a dyadic radius the integrand is `√L(N_p)`. -/
theorem entropyIntegrand_dyadic_eq {δ : ℝ} (hδ : 0 < δ) {F : Set (𝒳 → β)}
    (hJ : bracketingIntegral adm size δ F ≠ ⊤) (p : ℕ) :
    entropyIntegrand (bracketingNumber adm size (ENNReal.ofReal (δ / 2 ^ p)) F)
      = ENNReal.ofReal √(entropyLog (dyadicCount adm size δ F p)) :=
  entropyIntegrand_eq_of_ne_top
    (bracketingNumber_ne_top_of_bracketingIntegral_ne_top hδ hJ (by positivity))

/-- (F3, finite) `Σ_{p ≤ Q} ε_p √L(N_p) ≤ 2 J`. -/
theorem sum_dyadic_entropy_le {δ : ℝ} (hδ : 0 < δ) {F : Set (𝒳 → β)}
    (hJ : bracketingIntegral adm size δ F ≠ ⊤) (Q : ℕ) :
    ∑ p ∈ range (Q + 1), δ / 2 ^ p * √(entropyLog (dyadicCount adm size δ F p))
      ≤ 2 * (bracketingIntegral adm size δ F).toReal := by
  have hanti := antitone_entropyIntegrand_bracketingNumber (adm := adm) (size := size) F
  have he_anti : Antitone fun p : ℕ ↦ δ / 2 ^ p := fun m n h ↦
    div_le_div_of_nonneg_left hδ.le (by positivity) (pow_le_pow_right₀ one_le_two h)
  have hterm : ∀ p : ℕ,
      ENNReal.ofReal (δ / 2 ^ p * √(entropyLog (dyadicCount adm size δ F p)))
        ≤ 2 * ∫⁻ x in Ioc (δ / 2 ^ (p + 1)) (δ / 2 ^ p),
          entropyIntegrand (bracketingNumber adm size (ENNReal.ofReal x) F) := by
    intro p
    have hsub : δ / 2 ^ p - δ / 2 ^ (p + 1) = δ / 2 ^ p / 2 := by
      rw [pow_succ]; field_simp; ring
    calc ENNReal.ofReal (δ / 2 ^ p * √(entropyLog (dyadicCount adm size δ F p)))
        = 2 * (ENNReal.ofReal (δ / 2 ^ p - δ / 2 ^ (p + 1))
            * entropyIntegrand (bracketingNumber adm size (ENNReal.ofReal (δ / 2 ^ p)) F)) := by
          rw [entropyIntegrand_dyadic_eq hδ hJ p, hsub, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
          congr 1
          ring
      _ ≤ _ := by
          gcongr
          exact ofReal_sub_mul_le_setLIntegral_Ioc hanti _ _
  have hdisj : PairwiseDisjoint (↑(range (Q + 1)) : Set ℕ)
      fun p ↦ Ioc (δ / 2 ^ (p + 1)) (δ / 2 ^ p) := by
    have h := Antitone.pairwise_disjoint_on_Ioc_succ he_anti
    simp only [Order.succ_eq_add_one] at h
    exact h.set_pairwise _
  have hunion : (⋃ p ∈ range (Q + 1), Ioc (δ / 2 ^ (p + 1)) (δ / 2 ^ p)) ⊆ Ioc 0 δ := by
    refine iUnion₂_subset fun p _ ↦ Ioc_subset_Ioc (by positivity) ?_
    simpa using he_anti (Nat.zero_le p)
  have hsum : ENNReal.ofReal
      (∑ p ∈ range (Q + 1), δ / 2 ^ p * √(entropyLog (dyadicCount adm size δ F p)))
        ≤ 2 * bracketingIntegral adm size δ F := by
    rw [ENNReal.ofReal_sum_of_nonneg fun p _ ↦ by positivity]
    calc _ ≤ ∑ p ∈ range (Q + 1), 2 * ∫⁻ x in Ioc (δ / 2 ^ (p + 1)) (δ / 2 ^ p),
              entropyIntegrand (bracketingNumber adm size (ENNReal.ofReal x) F) :=
          sum_le_sum fun p _ ↦ hterm p
      _ = 2 * ∫⁻ x in ⋃ p ∈ range (Q + 1), Ioc (δ / 2 ^ (p + 1)) (δ / 2 ^ p),
              entropyIntegrand (bracketingNumber adm size (ENNReal.ofReal x) F) := by
          rw [← mul_sum, lintegral_biUnion_finset hdisj fun _ _ ↦ measurableSet_Ioc]
      _ ≤ 2 * bracketingIntegral adm size δ F := by
          gcongr
          exact lintegral_mono_set hunion
  have h2J : 2 * bracketingIntegral adm size δ F ≠ ⊤ := ENNReal.mul_ne_top (by simp) hJ
  have := (ENNReal.ofReal_le_iff_le_toReal h2J).mp hsum
  simpa [ENNReal.toReal_mul] using this

/-- (F4) `δ √L(N_0) ≤ J`. -/
theorem mul_sqrt_entropyLog_dyadicCount_zero_le {δ : ℝ} (hδ : 0 < δ) {F : Set (𝒳 → β)}
    (hJ : bracketingIntegral adm size δ F ≠ ⊤) :
    δ * √(entropyLog (dyadicCount adm size δ F 0))
      ≤ (bracketingIntegral adm size δ F).toReal := by
  have hanti := antitone_entropyIntegrand_bracketingNumber (adm := adm) (size := size) F
  have h := ofReal_sub_mul_le_setLIntegral_Ioc hanti 0 δ
  have hval := entropyIntegrand_dyadic_eq hδ hJ 0
  simp only [pow_zero, div_one] at hval
  rw [hval, sub_zero, ← ENNReal.ofReal_mul hδ.le] at h
  exact (ENNReal.ofReal_le_iff_le_toReal hJ).mp h

/-- (F1 + F2 + F3) `Σ_{q ≤ Q} ε_q √L(M_{q+1}) ≤ 8 J`. -/
theorem sum_dyadic_prod_entropy_le {δ : ℝ} (hδ : 0 < δ) {F : Set (𝒳 → β)}
    (hJ : bracketingIntegral adm size δ F ≠ ⊤) (Q : ℕ) :
    ∑ q ∈ range (Q + 1), δ / 2 ^ q * √(entropyLog (dyadicProd adm size δ F (q + 1)))
      ≤ 8 * (bracketingIntegral adm size δ F).toReal := by
  calc ∑ q ∈ range (Q + 1), δ / 2 ^ q * √(entropyLog (dyadicProd adm size δ F (q + 1)))
      ≤ ∑ q ∈ range (Q + 1), δ / 2 ^ q *
          ∑ p ∈ range (q + 2), √(entropyLog (dyadicCount adm size δ F p)) := by
        gcongr with q hq
        exact sqrt_entropyLog_prod_le _ (q + 1)
    _ ≤ 4 * ∑ p ∈ range (Q + 2), δ / 2 ^ p * √(entropyLog (dyadicCount adm size δ F p)) :=
        sum_dyadic_partialSum_le hδ.le (fun _ ↦ Real.sqrt_nonneg _) Q
    _ ≤ 4 * (2 * (bracketingIntegral adm size δ F).toReal) := by
        gcongr
        exact sum_dyadic_entropy_le hδ hJ (Q + 1)
    _ = 8 * (bracketingIntegral adm size δ F).toReal := by ring

/-- (F0) `Σ_{1 ≤ q ≤ Q} ε_q √L(M_q) ≤ ½ Σ_{q ≤ Q} ε_q √L(M_{q+1})`. -/
theorem sum_Ico_dyadic_prod_entropy_le_half {δ : ℝ} (hδ : 0 ≤ δ) (F : Set (𝒳 → β)) (Q : ℕ) :
    ∑ q ∈ Finset.Ico 1 (Q + 1), δ / 2 ^ q * √(entropyLog (dyadicProd adm size δ F q))
      ≤ 1 / 2 * ∑ q ∈ range (Q + 1),
          δ / 2 ^ q * √(entropyLog (dyadicProd adm size δ F (q + 1))) :=
  sum_Ico_dyadic_le_half hδ (b := fun q ↦ √(entropyLog (dyadicProd adm size δ F q)))
    (fun _ ↦ Real.sqrt_nonneg _) Q

end Hellinger.VdW
