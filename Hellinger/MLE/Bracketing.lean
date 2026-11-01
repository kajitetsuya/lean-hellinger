/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.MLE.Defs

/-!
Order and scaling properties of bracketing numbers and nonstandardized bracketing integrals,
in extended values. Rescaling uses a change of variables on `(0, ct]` and the antitonicity of
the integrand; no concavity is used.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Hellinger.MLE

variable {𝒳 : Type*} {β : Type*} [Preorder β]
  {adm : (𝒳 → β) → (𝒳 → β) → Prop} {size : (𝒳 → β) → (𝒳 → β) → ℝ≥0∞}

/-! ### Bracketing numbers -/

theorem bracketingNumber_mono_set {ε : ℝ≥0∞} {F G : Set (𝒳 → β)} (h : F ⊆ G) :
    bracketingNumber adm size ε F ≤ bracketingNumber adm size ε G :=
  le_iInf₂ fun n ⟨b, hb⟩ ↦ iInf₂_le_of_le n ⟨b, hb.1, fun f hf ↦ hb.2 f (h hf)⟩ le_rfl

theorem bracketingNumber_antitone_radius {ε ε' : ℝ≥0∞} {F : Set (𝒳 → β)} (h : ε ≤ ε') :
    bracketingNumber adm size ε' F ≤ bracketingNumber adm size ε F :=
  le_iInf₂ fun n ⟨b, hb⟩ ↦ iInf₂_le_of_le n
    ⟨b, fun i ↦ ⟨(hb.1 i).1, (hb.1 i).2.1, (hb.1 i).2.2.trans_le h⟩, hb.2⟩ le_rfl

/-! ### The integrand -/

theorem entropyIntegrand_mono {N N' : ℕ∞} (h : N ≤ N') :
    entropyIntegrand N ≤ entropyIntegrand N' := by
  by_cases hN' : N' = ⊤
  · simp [entropyIntegrand, hN']
  have hN : N ≠ ⊤ := ne_top_of_le_ne_top hN' h
  have hle : N.toNat ≤ N'.toNat := ENat.toNat_le_toNat h hN'
  have hlog : Real.log (N.toNat : ℝ) ≤ Real.log (N'.toNat : ℝ) := by
    rcases Nat.eq_zero_or_pos N.toNat with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]
      exact Real.log_natCast_nonneg _
    · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hle)
  simp only [entropyIntegrand, hN, hN', ite_false]
  exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (by linarith))

theorem one_le_entropyIntegrand (N : ℕ∞) : 1 ≤ entropyIntegrand N := by
  by_cases hN : N = ⊤
  · simp [entropyIntegrand, hN]
  simp only [entropyIntegrand, hN, ite_false]
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal
    (Real.one_le_sqrt.mpr (by linarith [Real.log_natCast_nonneg N.toNat]))

/-- The integrand of a bracketing integral is antitone in the radius, hence measurable. -/
theorem antitone_entropyIntegrand_bracketingNumber (F : Set (𝒳 → β)) :
    Antitone fun ε : ℝ ↦ entropyIntegrand (bracketingNumber adm size (ENNReal.ofReal ε) F) :=
  fun _ _ h ↦ entropyIntegrand_mono
    (bracketingNumber_antitone_radius (ENNReal.ofReal_le_ofReal h))

/-! ### Change of variables on `(0, ct]` -/

/-- `∫_{(0, ct]} g = c ∫_{(0, t]} g(c ·)` for `c > 0`, in extended values. -/
theorem setLIntegral_Ioc_mul (g : ℝ → ℝ≥0∞) {c : ℝ} (hc : 0 < c) (t : ℝ) :
    ∫⁻ ε in Ioc 0 (c * t), g ε = ENNReal.ofReal c * ∫⁻ s in Ioc 0 t, g (c * s) := by
  rw [← lintegral_indicator measurableSet_Ioc, ← lintegral_indicator measurableSet_Ioc]
  have hind : ∀ s, (Ioc 0 t).indicator (fun s ↦ g (c * s)) s =
      (Ioc 0 (c * t)).indicator g (c * s) := by
    intro s
    have hmem : c * s ∈ Ioc 0 (c * t) ↔ s ∈ Ioc 0 t := by
      simp only [mem_Ioc, mul_pos_iff_of_pos_left hc, mul_le_mul_iff_right₀ hc]
    by_cases hs : s ∈ Ioc 0 t
    · rw [indicator_of_mem hs, indicator_of_mem (hmem.mpr hs)]
    · rw [indicator_of_notMem hs, indicator_of_notMem (mt hmem.mp hs)]
  simp_rw [hind]
  have hmap := lintegral_map_equiv ((Ioc 0 (c * t)).indicator g)
    (MeasurableEquiv.mulLeft₀ c hc.ne') (μ := volume)
  rw [MeasurableEquiv.coe_mulLeft₀, Real.map_volume_mul_left hc.ne',
    lintegral_smul_measure] at hmap
  rw [← hmap, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul hc.le,
    abs_of_pos (inv_pos.mpr hc), mul_inv_cancel₀ hc.ne', ENNReal.ofReal_one, one_mul]

/-- For an antitone integrand and `c ≥ 1`, `∫_{(0, ct]} g ≤ c ∫_{(0, t]} g`. -/
theorem setLIntegral_Ioc_mul_le {g : ℝ → ℝ≥0∞} (hg : Antitone g) {c : ℝ} (hc : 1 ≤ c)
    (t : ℝ) : ∫⁻ ε in Ioc 0 (c * t), g ε ≤ ENNReal.ofReal c * ∫⁻ ε in Ioc 0 t, g ε := by
  have hc0 : 0 < c := one_pos.trans_le hc
  rw [setLIntegral_Ioc_mul g hc0 t]
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  exact
    setLIntegral_mono' measurableSet_Ioc fun s hs ↦ hg (le_mul_of_one_le_left hs.1.le hc)

/-! ### Bracketing integrals -/

theorem bracketingIntegral_mono_set {δ : ℝ} {F G : Set (𝒳 → β)} (h : F ⊆ G) :
    bracketingIntegral adm size δ F ≤ bracketingIntegral adm size δ G :=
  lintegral_mono fun _ ↦ entropyIntegrand_mono (bracketingNumber_mono_set h)

theorem bracketingIntegral_mono_radius {δ δ' : ℝ} (F : Set (𝒳 → β)) (h : δ ≤ δ') :
    bracketingIntegral adm size δ F ≤ bracketingIntegral adm size δ' F :=
  lintegral_mono_set (Ioc_subset_Ioc_right h)

/-- `δ ≤ J̃(δ, F)`, since the integrand is at least one. -/
theorem ofReal_le_bracketingIntegral (δ : ℝ) (F : Set (𝒳 → β)) :
    ENNReal.ofReal δ ≤ bracketingIntegral adm size δ F := by
  calc ENNReal.ofReal δ = ∫⁻ _ in Ioc (0 : ℝ) δ, 1 := by simp [Real.volume_Ioc]
    _ ≤ bracketingIntegral adm size δ F := lintegral_mono fun _ ↦ one_le_entropyIntegrand _

/-- Fixed-class rescaling: `J̃(ct, F) ≤ c J̃(t, F)` for `c ≥ 1`. The class is held fixed. -/
theorem bracketingIntegral_mul_le (F : Set (𝒳 → β)) {c : ℝ} (hc : 1 ≤ c) (t : ℝ) :
    bracketingIntegral adm size (c * t) F ≤
      ENNReal.ofReal c * bracketingIntegral adm size t F :=
  setLIntegral_Ioc_mul_le (antitone_entropyIntegrand_bracketingNumber F) hc t

/-- Comparison of bracketing integrals across two bracketing structures: if a cover of the
second class at radius `ε` yields one of the first at radius `κ ε`, then
`J̃₁(κ t, F₁) ≤ κ J̃₂(t, F₂)`. -/
theorem bracketingIntegral_le_of_bracketingNumber_le {γ : Type*} [Preorder γ]
    {adm₂ : (𝒳 → γ) → (𝒳 → γ) → Prop} {size₂ : (𝒳 → γ) → (𝒳 → γ) → ℝ≥0∞}
    {F₁ : Set (𝒳 → β)} {F₂ : Set (𝒳 → γ)} {κ : ℝ} (hκ : 0 < κ)
    (hN : ∀ ε : ℝ, 0 < ε → bracketingNumber adm size (ENNReal.ofReal (κ * ε)) F₁ ≤
      bracketingNumber adm₂ size₂ (ENNReal.ofReal ε) F₂) (t : ℝ) :
    bracketingIntegral adm size (κ * t) F₁ ≤
      ENNReal.ofReal κ * bracketingIntegral adm₂ size₂ t F₂ := by
  unfold bracketingIntegral
  rw [setLIntegral_Ioc_mul _ hκ t]
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  exact
    setLIntegral_mono' measurableSet_Ioc fun s hs ↦ entropyIntegrand_mono (hN s hs.1)

/-! ### Hellinger classes -/

variable [MeasurableSpace 𝒳]

theorem hBracketingIntegral_mono_set (μ : Measure 𝒳) {δ : ℝ} {F G : Set (𝒳 → ℝ≥0)}
    (h : F ⊆ G) : hBracketingIntegral μ δ F ≤ hBracketingIntegral μ δ G :=
  bracketingIntegral_mono_set h

theorem hBracketingIntegral_mul_le (μ : Measure 𝒳) (F : Set (𝒳 → ℝ≥0)) {c : ℝ} (hc : 1 ≤ c)
    (t : ℝ) : hBracketingIntegral μ (c * t) F ≤ ENNReal.ofReal c * hBracketingIntegral μ t F :=
  bracketingIntegral_mul_le F hc t

theorem hBall_subset (μ : Measure 𝒳) (p₀ : 𝒳 → ℝ≥0) (S : Set (𝒳 → ℝ≥0)) (r : ℝ) :
    hBall μ p₀ S r ⊆ S := fun _ hp ↦ hp.1

theorem annulus_subset_hBall (μ : Measure 𝒳) (p₀ : 𝒳 → ℝ≥0) (S : Set (𝒳 → ℝ≥0)) (s : ℝ) :
    annulus μ p₀ S s ⊆ hBall μ p₀ S (Real.sqrt 2 * s) := fun _ hp ↦ ⟨hp.1, hp.2.2⟩

/-- `K_{nj} ≤ J̃(√2 s, 𝒫_{n, √2 s}, h)`, including the empty-annulus convention. -/
theorem annulusEntropy_le (μ : Measure 𝒳) (p₀ : 𝒳 → ℝ≥0) (S : Set (𝒳 → ℝ≥0)) (s : ℝ) :
    annulusEntropy μ p₀ S s ≤
      hBracketingIntegral μ (Real.sqrt 2 * s) (hBall μ p₀ S (Real.sqrt 2 * s)) := by
  unfold annulusEntropy
  split_ifs
  · exact zero_le
  · exact hBracketingIntegral_mono_set μ (annulus_subset_hBall μ p₀ S s)

/-! ### Shell tails -/

/-- `T_n(k)` is nonincreasing in the cutoff `k`. -/
theorem shellTail_antitone (μ : Measure 𝒳) (p₀ : 𝒳 → ℝ≥0) (S : ℕ → Set (𝒳 → ℝ≥0))
    (δ : ℕ → ℝ) (n : ℕ) : Antitone (shellTail μ p₀ S δ n) := by
  intro k k' hk
  unfold shellTail
  refine ENNReal.tsum_le_tsum fun j ↦ ?_
  split_ifs with h₁ h₂
  · exact le_rfl
  · exact absurd ⟨hk.trans h₁.1, h₁.2⟩ h₂
  · exact zero_le
  · exact le_rfl

/-- (D) gives the uniform tail bound at every larger cutoff. -/
theorem AnnularTailCondition.eventually_le {μ : Measure 𝒳} {p₀ : 𝒳 → ℝ≥0}
    {S : ℕ → Set (𝒳 → ℝ≥0)} {δ : ℕ → ℝ} (hD : AnnularTailCondition μ p₀ S δ) {ε : ℝ}
    (hε : 0 < ε) : ∃ k N : ℕ, ∀ k' ≥ k, ∀ n ≥ N, shellTail μ p₀ S δ n k' ≤ ENNReal.ofReal ε := by
  obtain ⟨k, N, h⟩ := hD ε hε
  exact ⟨k, N, fun k' hk' n hn ↦ (shellTail_antitone μ p₀ S δ n hk').trans (h n hn)⟩

/-! ### Shell scales -/

theorem rate_pos (δ : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) : 0 < rate δ n :=
  lt_max_of_lt_right (inv_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hn)))

theorem shellScale_sq (a : ℝ) (j : ℕ) : shellScale a j ^ 2 = 2 ^ j * a ^ 2 := by
  rw [shellScale, mul_pow, ← pow_mul, mul_comm j 2, pow_mul, Real.sq_sqrt (by norm_num)]

theorem shellScale_succ (a : ℝ) (j : ℕ) : shellScale a (j + 1) = Real.sqrt 2 * shellScale a j := by
  rw [shellScale, shellScale, pow_succ]; ring

theorem shellScale_pos {a : ℝ} (ha : 0 < a) (j : ℕ) : 0 < shellScale a j :=
  mul_pos (pow_pos (Real.sqrt_pos.mpr (by norm_num)) j) ha

theorem le_shellScale {a : ℝ} (ha : 0 ≤ a) (j : ℕ) : a ≤ shellScale a j :=
  le_mul_of_one_le_left ha (one_le_pow₀ (by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)))

end Hellinger.MLE
