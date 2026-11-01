/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.MLE.Statements

/-!
Non-vacuity witness for the MLE statements: on a one-point space with the trivial sieve
`{p₀}`, `pn = phat = p₀` and `δ = 0`, every hypothesis of the MLE statements holds,
including (D), (H), (G) and measurability of the Hellinger error. So none of the exported
statements is vacuous through contradictory hypotheses.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Hellinger.MLE

universe u v

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

theorem hellingerFunSq_self (μ : Measure 𝒳) (f : 𝒳 → ℝ≥0) : hellingerFunSq μ f f = 0 := by
  simp [hellingerFunSq]

@[simp] theorem hdist_self (μ : Measure 𝒳) (f : 𝒳 → ℝ≥0) : hdist μ f f = 0 := by
  rw [hdist, hellingerFunSq_self, ENNReal.zero_rpow_of_pos (by norm_num)]

theorem entropyIntegrand_le_one {N : ℕ∞} (hN : N ≤ 1) : entropyIntegrand N ≤ 1 := by
  have hne : N ≠ ⊤ := ne_top_of_le_ne_top ENat.one_ne_top hN
  have hle : N.toNat ≤ 1 := by
    have := ENat.toNat_le_toNat hN ENat.one_ne_top
    simpa using this
  have hlog : Real.log (N.toNat : ℝ) = 0 := by
    interval_cases h : N.toNat <;> simp
  simp [entropyIntegrand, hne, hlog]

/-- A class contained in a singleton `{f}` of finite mass has bracketing integral at most `r`. -/
theorem hBracketingIntegral_le_of_subset_singleton (μ : Measure 𝒳) {f : 𝒳 → ℝ≥0}
    (hf : Measurable f) (hfin : ∫⁻ x, (f x : ℝ≥0∞) ∂μ < ∞) {F : Set (𝒳 → ℝ≥0)}
    (hF : F ⊆ {f}) (r : ℝ) :
    hBracketingIntegral μ r F ≤ ENNReal.ofReal r := by
  have hN : ∀ ε ∈ Ioc (0 : ℝ) r,
      entropyIntegrand (hBracketingNumber μ (ENNReal.ofReal ε) F) ≤ 1 := by
    intro ε hε
    apply entropyIntegrand_le_one
    refine iInf₂_le_of_le 1 ⟨fun _ ↦ (f, f), ?_, ?_⟩ (by simp)
    · intro _
      refine ⟨⟨hf, hf, hfin, hfin⟩, le_rfl, ?_⟩
      rw [hdist_self]; exact ENNReal.ofReal_pos.mpr hε.1
    · intro g hg
      rw [mem_singleton_iff.mp (hF hg)]
      exact ⟨0, le_rfl, le_rfl⟩
  calc hBracketingIntegral μ r F
      ≤ ∫⁻ _ in Ioc (0 : ℝ) r, 1 := setLIntegral_mono measurable_const hN
    _ = ENNReal.ofReal r := by simp [Real.volume_Ioc]

theorem tailLogMoment_self (ν : Measure 𝒳) [SigmaFinite ν] {c : ℝ} (hc : 1 < c) (k : ℝ) :
    tailLogMoment ν ν c k = 0 := by
  have h0 : ν (tailEvent ν ν c) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [llr_self ν] with x hx
    simp [tailEvent, hx, (Real.log_pos hc).le]
  rw [tailLogMoment_of_ac (Measure.AbsolutelyContinuous.refl _),
    setLIntegral_measure_zero _ _ h0]

section Trivial

/-- The one-point reference measure. -/
noncomputable abbrev trivialRef : Measure PUnit.{u + 1} := Measure.dirac PUnit.unit

/-- The one-point probability space. -/
noncomputable abbrev trivialProb : Measure PUnit.{v + 1} := Measure.dirac PUnit.unit

/-- The unit density. -/
abbrev trivialDensity : PUnit.{u + 1} → ℝ≥0 := fun _ ↦ 1

theorem trivialDensity_isProbDensity : IsProbDensity trivialRef.{u} trivialDensity.{u} :=
  ⟨measurable_const, by simp⟩

theorem law_trivial : law trivialRef.{u} trivialDensity.{u} = trivialRef := by
  simp [law, trivialDensity]

theorem annulus_singleton_self (μ : Measure 𝒳) (f : 𝒳 → ℝ≥0) (s : ℝ) :
    annulus μ f {f} s = ∅ := by
  ext p
  simp only [annulus, mem_ofPred_eq, mem_singleton_iff, mem_empty_iff_false, iff_false]
  rintro ⟨rfl, h, -⟩
  simp at h

theorem shellTail_singleton_self (μ : Measure 𝒳) (f : 𝒳 → ℝ≥0) (δ : ℕ → ℝ) (n k : ℕ) :
    shellTail μ f (fun _ ↦ {f}) δ n k = 0 := by
  simp [shellTail, shellTerm, annulusEntropy, annulus_singleton_self]

/-- Every hypothesis of the MLE statements holds on the one-point model. -/
theorem nonvacuous :
    MLEHypotheses trivialRef.{u} trivialProb.{v} (fun _ _ ↦ PUnit.unit) trivialDensity
      (fun _ ↦ {trivialDensity}) (fun _ ↦ trivialDensity) (fun _ _ ↦ trivialDensity)
      (fun _ ↦ 0) 0 0 ∧
    AnnularTailCondition trivialRef.{u} trivialDensity (fun _ ↦ {trivialDensity}) (fun _ ↦ 0) ∧
    PowerEnvelopeCondition trivialRef.{u} trivialDensity (fun _ ↦ {trivialDensity})
      (fun _ ↦ 0) ∧
    WholeSieveCondition trivialRef.{u} (fun _ ↦ {trivialDensity}) (fun _ ↦ 0) ∧
    ∀ n, Measurable fun ω : PUnit.{v + 1} ↦
      hdist trivialRef.{u} trivialDensity ((fun (_ : ℕ) (_ : PUnit.{v + 1}) ↦ trivialDensity) n ω) := by
  have hfin : ∫⁻ x, ((trivialDensity.{u} x : ℝ≥0) : ℝ≥0∞) ∂trivialRef = 1 :=
    trivialDensity_isProbDensity.lintegral_eq_one
  have hrate : ∀ n : ℕ, 1 ≤ n → rate (fun _ ↦ 0) n = (Real.sqrt n)⁻¹ := fun n _ ↦
    max_eq_right (inv_nonneg.mpr (Real.sqrt_nonneg _))
  have hsq : ∀ n : ℕ, 1 ≤ n → Real.sqrt n * (Real.sqrt n)⁻¹ = 1 := fun n hn ↦
    mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hn))
  refine ⟨⟨inferInstance, trivialDensity_isProbDensity, fun _ ↦ measurable_const, ?_, ?_,
      ?_, fun _ ↦ rfl, fun _ _ ↦ rfl, fun _ ↦ le_rfl, le_rfl, le_rfl,
      ⟨0, fun _ _ ↦ by simp⟩, ⟨0, fun n _ ↦ ?_⟩, ?_⟩, ?_, ?_, ?_, fun _ ↦ measurable_const⟩
  · -- independence under a Dirac measure
    classical
    rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
    intro T sets _
    by_cases h : ∀ i ∈ T, PUnit.unit ∈ sets i
    · have hmem : PUnit.unit ∈ ⋂ i ∈ T, (fun _ : PUnit.{v + 1} ↦ PUnit.unit) ⁻¹' sets i := by
        simpa using h
      rw [Measure.dirac_apply_of_mem hmem]
      refine (Finset.prod_eq_one fun i hi ↦ ?_).symm
      exact Measure.dirac_apply_of_mem (by simpa using h i hi)
    · push Not at h
      obtain ⟨i, hi, hni⟩ := h
      have hpre : (fun _ : PUnit.{v + 1} ↦ PUnit.unit) ⁻¹' sets i = ∅ := by
        ext; simpa using hni
      rw [Finset.prod_eq_zero hi (by rw [hpre, measure_empty])]
      apply measure_mono_null _ (measure_empty (μ := trivialProb.{v}))
      intro x hx
      simp only [mem_iInter, mem_preimage] at hx
      exact absurd (hx i hi) (by simpa using hni)
  · intro i
    rw [law_trivial, Measure.map_const]
    simp
  · intro n p hp
    rw [mem_singleton_iff.mp hp]
    exact trivialDensity_isProbDensity
  · rw [law_trivial, tailLogMoment_self _ (by norm_num)]
    exact zero_le
  · intro ε hε
    refine ⟨1, one_pos, 0, fun n _ ↦ ?_⟩
    have : {ω : PUnit.{v + 1} | ENNReal.ofReal (1 * (0 : ℝ) ^ 2) <
        logLikDeficit (sample (fun _ _ ↦ PUnit.unit) n ω) trivialDensity trivialDensity} = ∅ := by
      ext ω
      simp [logLikDeficit, likelihood]
    rw [this, measure_empty]
    exact zero_le
  · intro ε hε
    exact ⟨0, 0, fun n _ ↦ by rw [shellTail_singleton_self]; exact zero_le⟩
  · refine ⟨1, 1, one_pos, le_rfl, by norm_num, 1, fun n hn r hr ↦ ?_⟩
    refine (hBracketingIntegral_le_of_subset_singleton _ measurable_const (by simp; exact ENNReal.coe_lt_top)
      (fun p hp ↦ hp.1) r).trans (le_of_eq ?_)
    rw [hrate n hn]
    norm_num
    rw [hsq n hn, one_mul]
  · refine ⟨1, one_pos, 1, fun n hn ↦ ?_⟩
    refine (hBracketingIntegral_le_of_subset_singleton _ measurable_const (by simp; exact ENNReal.coe_lt_top)
      subset_rfl _).trans (le_of_eq ?_)
    rw [hrate n hn, sq, ← mul_assoc, one_mul, hsq n hn, one_mul]

end Trivial

end Hellinger.MLE
