/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.MLE.Defs
public import Mathlib.Probability.Moments.Variance

/-!
Outer expectation, outer Markov, the transfer from an arbitrary probability space carrying an
i.i.d. sample to the canonical product space, the calculus of `O_P^*`, and Chebyshev's bound
for i.i.d. sample means.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Hellinger.MLE

variable {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω}

/-! ### Outer expectation -/

theorem outerLIntegral_le_lintegral {Z g : Ω → ℝ≥0∞} (hg : Measurable g) (hZg : Z ≤ g) :
    outerLIntegral Pr Z ≤ ∫⁻ ω, g ω ∂Pr :=
  iInf₂_le_of_le g hg (iInf_le_of_le hZg le_rfl)

theorem outerLIntegral_mono {Z Z' : Ω → ℝ≥0∞} (h : Z ≤ Z') :
    outerLIntegral Pr Z ≤ outerLIntegral Pr Z' :=
  le_iInf₂ fun _ hg ↦ le_iInf fun hZ' ↦ outerLIntegral_le_lintegral hg (h.trans hZ')

/-- Outer Markov: `t P^*{Z ≥ t} ≤ E^* Z`. -/
theorem mul_measure_le_outerLIntegral (Z : Ω → ℝ≥0∞) (t : ℝ≥0∞) :
    t * Pr {ω | t ≤ Z ω} ≤ outerLIntegral Pr Z :=
  le_iInf₂ fun _ hg ↦ le_iInf fun hZg ↦
    (mul_le_mul_of_nonneg_left (measure_mono fun _ hω ↦ le_trans hω (hZg _)) zero_le).trans
      (mul_meas_ge_le_lintegral₀ hg.aemeasurable t)

/-- Outer Markov in quotient form, for `0 < t < ∞`. -/
theorem measure_le_outerLIntegral_div (Z : Ω → ℝ≥0∞) {t : ℝ≥0∞} (ht : t ≠ 0) (ht' : t ≠ ⊤) :
    Pr {ω | t ≤ Z ω} ≤ outerLIntegral Pr Z / t := by
  rw [ENNReal.le_div_iff_mul_le (Or.inl ht) (Or.inl ht'), mul_comm]
  exact mul_measure_le_outerLIntegral Z t

/-! ### Transfer to the canonical space -/

section Transfer

variable {Ω' : Type*} [MeasurableSpace Ω']

/-- Composition with a measurable map can only lower the outer expectation:
`E^*_Pr[φ ∘ Y] ≤ E^*_{Y_* Pr}[φ]`. -/
theorem outerLIntegral_comp_le {Y : Ω → Ω'} (hY : Measurable Y) (φ : Ω' → ℝ≥0∞) :
    outerLIntegral Pr (φ ∘ Y) ≤ outerLIntegral (Pr.map Y) φ :=
  le_iInf₂ fun _ hg ↦ le_iInf fun hφg ↦
    (outerLIntegral_le_lintegral (hg.comp hY) fun ω ↦ hφg (Y ω)).trans_eq
      (lintegral_map hg hY).symm

/-- Outer probability of a preimage is at most the outer probability under the image law. -/
theorem measure_preimage_le_map {Y : Ω → Ω'} (hY : Measurable Y) (s : Set Ω') :
    Pr (Y ⁻¹' s) ≤ Pr.map Y s :=
  Measure.le_map_apply hY.aemeasurable s

end Transfer

section Sample

variable {𝒳 : Type*} [MeasurableSpace 𝒳] {X : ℕ → Ω → 𝒳}

theorem measurable_sample (hX : ∀ i, Measurable (X i)) (n : ℕ) : Measurable (sample X n) :=
  measurable_pi_iff.mpr fun i ↦ hX i

/-- The first `n` observations of an i.i.d. sequence have the product law. -/
theorem map_sample_eq_pi [IsProbabilityMeasure Pr] {P : Measure 𝒳} (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X Pr) (hlaw : ∀ i, Pr.map (X i) = P) (n : ℕ) :
    Pr.map (sample X n) = Measure.pi fun _ : Fin n ↦ P := by
  have h := hind.precomp (g := (Fin.val : Fin n → ℕ)) Fin.val_injective
  rw [iIndepFun_iff_map_fun_eq_pi_map fun i : Fin n ↦ (hX i).aemeasurable] at h
  have hs : sample X n = fun ω (i : Fin n) ↦ X i ω := rfl
  rw [hs]
  simpa only [hlaw] using h

/-- Outer expectation of a function of the sample is bounded by its canonical-space value. -/
theorem outerLIntegral_sample_le [IsProbabilityMeasure Pr] {P : Measure 𝒳}
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X Pr) (hlaw : ∀ i, Pr.map (X i) = P) (n : ℕ)
    (φ : (Fin n → 𝒳) → ℝ≥0∞) :
    outerLIntegral Pr (φ ∘ sample X n) ≤ outerLIntegral (Measure.pi fun _ : Fin n ↦ P) φ := by
  rw [← map_sample_eq_pi hX hind hlaw n]
  exact outerLIntegral_comp_le (measurable_sample hX n) φ

/-- Outer probability of an event of the sample is bounded by its canonical-space value. -/
theorem measure_sample_preimage_le [IsProbabilityMeasure Pr] {P : Measure 𝒳}
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X Pr) (hlaw : ∀ i, Pr.map (X i) = P) (n : ℕ)
    (s : Set (Fin n → 𝒳)) :
    Pr (sample X n ⁻¹' s) ≤ (Measure.pi fun _ : Fin n ↦ P) s := by
  rw [← map_sample_eq_pi hX hind hlaw n]
  exact measure_preimage_le_map (measurable_sample hX n) s

end Sample

/-! ### The calculus of `O_P^*` -/

section OPStar

variable {Z Z' : ℕ → Ω → ℝ≥0∞} {b b' : ℕ → ℝ}

/-- Eventual pointwise domination transfers `O_P^*`. -/
theorem OPStar.mono (h : OPStar Pr Z' b) (hle : ∃ N, ∀ n ≥ N, ∀ ω, Z n ω ≤ Z' n ω) :
    OPStar Pr Z b := by
  intro ε hε
  obtain ⟨K, hK, N, hN⟩ := h ε hε
  obtain ⟨N', hN'⟩ := hle
  refine ⟨K, hK, max N N', fun n hn ↦ ?_⟩
  refine (measure_mono fun ω hω ↦ ?_).trans (hN n (le_of_max_le_left hn))
  exact lt_of_lt_of_le hω (hN' n (le_of_max_le_right hn) ω)

/-- Finite prefixes do not matter. -/
theorem OPStar.congr (h : OPStar Pr Z b) (heq : ∃ N, ∀ n ≥ N, Z' n = Z n) : OPStar Pr Z' b :=
  h.mono (heq.imp fun _ hN n hn ω ↦ (congrFun (hN n hn) ω).le)

/-- A larger rate, eventually, preserves `O_P^*`. -/
theorem OPStar.rate_mono (h : OPStar Pr Z b) (hb : ∃ N, ∀ n ≥ N, b n ≤ b' n) :
    OPStar Pr Z b' := by
  intro ε hε
  obtain ⟨K, hK, N, hN⟩ := h ε hε
  obtain ⟨N', hN'⟩ := hb
  refine ⟨K, hK, max N N', fun n hn ↦ (measure_mono fun ω hω ↦ ?_).trans
    (hN n (le_of_max_le_left hn))⟩
  exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left (hN' n (le_of_max_le_right hn)) hK.le)) hω

/-- A deterministic bound `Z_n ≤ c b_n` gives `O_P^*(b_n)`. -/
theorem OPStar.of_le (hb : ∀ n, 0 ≤ b n) {c : ℝ} (hc : 0 ≤ c)
    (hle : ∃ N, ∀ n ≥ N, ∀ ω, Z n ω ≤ ENNReal.ofReal (c * b n)) : OPStar Pr Z b := by
  intro ε hε
  obtain ⟨N, hN⟩ := hle
  refine ⟨c + 1, by linarith, N, fun n hn ↦ ?_⟩
  have : {ω | ENNReal.ofReal ((c + 1) * b n) < Z n ω} = ∅ := by
    ext ω
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
    exact (hN n hn ω).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (by linarith) (hb n)))
  rw [this, measure_empty]
  exact zero_le

/-- Sums of `O_P^*(b_n)` terms are `O_P^*(b_n)`. -/
theorem OPStar.add (h₁ : OPStar Pr Z b) (h₂ : OPStar Pr Z' b) (hb : ∀ n, 0 ≤ b n) :
    OPStar Pr (Z + Z') b := by
  intro ε hε
  obtain ⟨K₁, hK₁, N₁, hN₁⟩ := h₁ (ε / 2) (by linarith)
  obtain ⟨K₂, hK₂, N₂, hN₂⟩ := h₂ (ε / 2) (by linarith)
  refine ⟨K₁ + K₂, by linarith, max N₁ N₂, fun n hn ↦ ?_⟩
  have hsub : {ω | ENNReal.ofReal ((K₁ + K₂) * b n) < (Z + Z') n ω} ⊆
      {ω | ENNReal.ofReal (K₁ * b n) < Z n ω} ∪ {ω | ENNReal.ofReal (K₂ * b n) < Z' n ω} := by
    intro ω hω
    by_contra hcon
    simp only [mem_union, mem_ofPred_eq, not_or, not_lt] at hcon
    simp only [mem_ofPred_eq, Pi.add_apply] at hω
    rw [add_mul, ENNReal.ofReal_add (mul_nonneg hK₁.le (hb n)) (mul_nonneg hK₂.le (hb n))] at hω
    exact absurd (add_le_add hcon.1 hcon.2) (not_le.mpr hω)
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
      add_le_add (hN₁ n (le_of_max_le_left hn)) (hN₂ n (le_of_max_le_right hn))
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; ring_nf

/-- Constant multiples of `O_P^*(b_n)` terms are `O_P^*(b_n)`. -/
theorem OPStar.const_mul (h : OPStar Pr Z b) (c : ℝ≥0) :
    OPStar Pr (fun n ω ↦ (c : ℝ≥0∞) * Z n ω) b := by
  intro ε hε
  obtain ⟨K, hK, N, hN⟩ := h ε hε
  refine ⟨(c + 1) * K, by positivity, N, fun n hn ↦ (measure_mono fun ω hω ↦ ?_).trans (hN n hn)⟩
  simp only [mem_ofPred_eq] at hω ⊢
  by_contra hcon
  rw [not_lt] at hcon
  have : (c : ℝ≥0∞) * Z n ω ≤ ENNReal.ofReal ((c + 1) * K * b n) := by
    calc (c : ℝ≥0∞) * Z n ω ≤ ENNReal.ofReal (c + 1) * ENNReal.ofReal (K * b n) := by
          gcongr
          rw [← ENNReal.ofReal_coe_nnreal]
          exact ENNReal.ofReal_le_ofReal (by simp)
      _ = ENNReal.ofReal ((c + 1) * K * b n) := by
          rw [← ENNReal.ofReal_mul (by positivity), mul_assoc]
  exact absurd hω (not_lt.mpr this)

end OPStar

/-! ### Chebyshev for i.i.d. sample means -/

section Chebyshev

variable {𝒳 : Type*} [MeasurableSpace 𝒳] {X : ℕ → Ω → 𝒳}

/-- For each `n`, the sample mean of `f` over the first `n` observations. -/
noncomputable def sampleMean (X : ℕ → Ω → 𝒳) (n : ℕ) (f : 𝒳 → ℝ) (ω : Ω) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i : Fin n, f (X i ω)

theorem variance_sampleMean_le [IsProbabilityMeasure Pr] {P : Measure 𝒳} [IsProbabilityMeasure P]
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X Pr) (hlaw : ∀ i, Pr.map (X i) = P)
    {f : 𝒳 → ℝ} (hfm : Measurable f) (hf : MemLp f 2 P) {n : ℕ} (hn : 1 ≤ n) :
    MemLp (sampleMean X n f) 2 Pr ∧ Pr[sampleMean X n f] = ∫ x, f x ∂P ∧
      variance (sampleMean X n f) Pr ≤ (n : ℝ)⁻¹ * ∫ x, f x ^ 2 ∂P := by
  set g : Fin n → Ω → ℝ := fun i ↦ f ∘ X i with hg
  have hmem : ∀ i, MemLp (g i) 2 Pr := fun i ↦
    (memLp_map_measure_iff hfm.aestronglyMeasurable (hX i).aemeasurable).mp (by rw [hlaw i]; exact hf)
  have hint : ∀ i, ∫ ω, g i ω ∂Pr = ∫ x, f x ∂P := fun i ↦ by
    rw [← hlaw i, integral_map (hX i).aemeasurable hfm.aestronglyMeasurable]; rfl
  have hvar : ∀ i, variance (g i) Pr = variance f P := fun i ↦ by
    rw [← hlaw i, variance_map hfm.aemeasurable (hX i).aemeasurable]
  have hfun : sampleMean X n f = fun ω ↦ (n : ℝ)⁻¹ * (∑ i, g i) ω := by
    ext ω; simp [sampleMean, g, Finset.sum_apply]
  have hsum : MemLp (∑ i, g i) 2 Pr := memLp_finsetSum' _ fun i _ ↦ hmem i
  have hindn : iIndepFun g Pr :=
    (hind.precomp (g := (Fin.val : Fin n → ℕ)) Fin.val_injective).comp (fun _ ↦ f) fun _ ↦ hfm
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn)
  refine ⟨?_, ?_, ?_⟩
  · rw [hfun]; exact hsum.const_mul _
  · rw [hfun, integral_const_mul]
    simp_rw [Finset.sum_apply]
    rw [integral_finsetSum _ fun i _ ↦ (hmem i).integrable one_le_two]
    simp only [hint, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  · rw [hfun, variance_const_mul,
      IndepFun.variance_sum (X := g) (s := Finset.univ) (fun i _ ↦ hmem i)
        (fun i _ j _ hij ↦ hindn.indepFun hij)]
    simp only [hvar, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hle : variance f P ≤ ∫ x, f x ^ 2 ∂P := by
      simpa using variance_le_expectation_sq hfm.aestronglyMeasurable (μ := P)
    calc (n : ℝ)⁻¹ ^ 2 * (n * variance f P) = (n : ℝ)⁻¹ * variance f P := by field_simp
      _ ≤ (n : ℝ)⁻¹ * ∫ x, f x ^ 2 ∂P := by gcongr

/-- Chebyshev for i.i.d. sample means: if `P f_n² ≤ C n b_n²` eventually, then
`Pr_n f_n - P f_n = O_P^*(b_n)`. A zero rate is allowed. -/
theorem opStar_sampleMean [IsProbabilityMeasure Pr] {P : Measure 𝒳} [IsProbabilityMeasure P]
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X Pr) (hlaw : ∀ i, Pr.map (X i) = P)
    {f : ℕ → 𝒳 → ℝ} (hfm : ∀ n, Measurable (f n)) (hf : ∀ n, MemLp (f n) 2 P)
    {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∃ N, ∀ n ≥ N, ∫ x, f n x ^ 2 ∂P ≤ C * n * b n ^ 2) :
    OPStar Pr (fun n ω ↦ ENNReal.ofReal |sampleMean X n (f n) ω - ∫ x, f n x ∂P|) b := by
  intro ε hε
  obtain ⟨N, hN⟩ := hbound
  set K : ℝ := Real.sqrt (C / ε) + 1 with hKdef
  have hK : 0 < K := by positivity
  have hK2 : C / K ^ 2 ≤ ε := by
    rw [div_le_iff₀ (by positivity)]
    have : C / ε ≤ K ^ 2 := by
      have h1 : Real.sqrt (C / ε) ≤ K := by linarith
      calc C / ε = Real.sqrt (C / ε) ^ 2 := (Real.sq_sqrt (by positivity)).symm
        _ ≤ K ^ 2 := by gcongr
    rw [div_le_iff₀ hε] at this; linarith
  refine ⟨K, hK, max N 1, fun n hn ↦ ?_⟩
  have hn1 : 1 ≤ n := le_of_max_le_right hn
  obtain ⟨hY, hmean, hvar⟩ := variance_sampleMean_le hX hind hlaw (hfm n) (hf n) hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hvarC : variance (sampleMean X n (f n)) Pr ≤ C * b n ^ 2 := by
    calc _ ≤ (n : ℝ)⁻¹ * ∫ x, f n x ^ 2 ∂P := hvar
      _ ≤ (n : ℝ)⁻¹ * (C * n * b n ^ 2) := by gcongr; exact hN n (le_of_max_le_left hn)
      _ = C * b n ^ 2 := by field_simp
  have hset : {ω | ENNReal.ofReal (K * b n) <
      ENNReal.ofReal |sampleMean X n (f n) ω - ∫ x, f n x ∂P|} ⊆
      {ω | 0 < |sampleMean X n (f n) ω - Pr[sampleMean X n (f n)]| ∧
        K * b n ≤ |sampleMean X n (f n) ω - Pr[sampleMean X n (f n)]|} := by
    intro ω hω
    simp only [mem_ofPred_eq, hmean] at hω ⊢
    have := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (mul_nonneg hK.le (hb n))).mp hω
    exact ⟨lt_of_le_of_lt (mul_nonneg hK.le (hb n)) this, this.le⟩
  rcases (hb n).eq_or_lt with hb0 | hbpos
  · -- zero rate: the variance vanishes, so the deviation is zero almost surely
    have hvar0 : variance (sampleMean X n (f n)) Pr ≤ 0 := by
      simpa [← hb0] using hvarC
    have hnull : Pr {ω | 0 < |sampleMean X n (f n) ω - Pr[sampleMean X n (f n)]|} = 0 := by
      have hU : {ω | 0 < |sampleMean X n (f n) ω - Pr[sampleMean X n (f n)]|} =
          ⋃ m : ℕ, {ω | ((m : ℝ) + 1)⁻¹ ≤ |sampleMean X n (f n) ω - Pr[sampleMean X n (f n)]|} := by
        ext ω
        simp only [mem_ofPred_eq, mem_iUnion]
        constructor
        · intro h
          obtain ⟨m, hm⟩ := exists_nat_one_div_lt h
          exact ⟨m, by rw [← one_div]; exact hm.le⟩
        · rintro ⟨m, hm⟩
          exact lt_of_lt_of_le (by positivity) hm
      rw [hU]
      refine measure_iUnion_null fun m ↦ le_antisymm ?_ zero_le
      calc _ ≤ ENNReal.ofReal (variance (sampleMean X n (f n)) Pr / (((m : ℝ) + 1)⁻¹) ^ 2) :=
            meas_ge_le_variance_div_sq hY (by positivity)
        _ = 0 := by
          rw [ENNReal.ofReal_eq_zero]
          exact div_nonpos_of_nonpos_of_nonneg hvar0 (by positivity)
    calc _ ≤ _ := measure_mono (hset.trans fun ω hω ↦ hω.1)
      _ = 0 := hnull
      _ ≤ _ := zero_le
  · calc _ ≤ _ := measure_mono (hset.trans fun ω hω ↦ hω.2)
      _ ≤ ENNReal.ofReal (variance (sampleMean X n (f n)) Pr / (K * b n) ^ 2) :=
          meas_ge_le_variance_div_sq hY (by positivity)
      _ ≤ ENNReal.ofReal ε := by
          refine ENNReal.ofReal_le_ofReal ?_
          calc variance (sampleMean X n (f n)) Pr / (K * b n) ^ 2 ≤ C * b n ^ 2 / (K * b n) ^ 2 :=
                by gcongr
            _ = C / K ^ 2 := by field_simp
            _ ≤ ε := hK2

end Chebyshev

end Hellinger.MLE
