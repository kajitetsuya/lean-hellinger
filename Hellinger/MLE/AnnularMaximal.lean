/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.MLE.External
public import Hellinger.MLE.EntropyTransfer
public import Hellinger.MLE.Mixture
public import Hellinger.MLE.ProbabilityRates
public import Hellinger.MLE.DyadicPeeling

/-!
The annular maximal bound. For the transformed class of an annulus of radius `s`, the outer
probability that the empirical supremum reaches `√n s²/32` is at most `96 K₀ (u + u²)`, where
`u = K / (√n s²)` is the normalized annular entropy and `K₀` the constant of the maximal
inequality `External.VdW_2_14_18_prime`. The maximal inequality is applied on the canonical
space with the Bernstein radius `3√2 s`,
and the result is transferred to the probability space carrying the sample.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Hellinger.MLE

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-- The maximal inequality `External.VdW_2_14_18_prime`, specialized to one sample space. -/
def MaximalBound (𝒳 : Type*) [MeasurableSpace 𝒳] (K₀ : ℝ≥0) : Prop :=
  ∀ (P : Measure 𝒳) [IsProbabilityMeasure P] (F : Set (𝒳 → ℝ)) (n : ℕ) (δ : ℝ), 0 < n → 0 < δ →
    (∀ f ∈ F, Measurable f ∧ bernsteinFun P f ≤ ENNReal.ofReal δ) →
    outerLIntegral (Measure.pi fun _ : Fin n ↦ P) (empiricalSup P F) ≤
      (K₀ : ℝ≥0∞) * bBracketingIntegral P δ F *
        (1 + bBracketingIntegral P δ F / ENNReal.ofReal (δ ^ 2 * Real.sqrt n))

theorem External.VdW_2_14_18_prime.maximalBound {𝒳 : Type u} [MeasurableSpace 𝒳]
    (h : External.VdW_2_14_18_prime.{u}) : ∃ K₀, MaximalBound 𝒳 K₀ :=
  h.imp fun _ hK ↦ hK 𝒳

/-- The annular maximal bound, transferred to the sample space. -/
theorem measure_shell_le {μ : Measure 𝒳} {p₀ : 𝒳 → ℝ≥0} (hp₀ : IsProbDensity μ p₀)
    {S : Set (𝒳 → ℝ≥0)} (hS : ∀ p ∈ S, IsProbDensity μ p) {K₀ : ℝ≥0} (hK₀ : MaximalBound 𝒳 K₀)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    {X : ℕ → Ω → 𝒳} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X Pr)
    (hlaw : ∀ i, Pr.map (X i) = law μ p₀) {n : ℕ} (hn : 1 ≤ n) {s : ℝ} (hs : 0 < s) :
    Pr {ω | ENNReal.ofReal (32⁻¹ * (Real.sqrt n * s ^ 2)) ≤
        empiricalSup (law μ p₀) (mixLogClass p₀ (annulus μ p₀ S s)) (sample X n ω)} ≤
      96 * K₀ * (annulusEntropy μ p₀ S s / ENNReal.ofReal (Real.sqrt n * s ^ 2) +
        (annulusEntropy μ p₀ S s / ENNReal.ofReal (Real.sqrt n * s ^ 2)) ^ 2) := by
  classical
  have : IsProbabilityMeasure (law μ p₀) := isProbabilityMeasure_law hp₀
  set P₀ := law μ p₀
  set A := annulus μ p₀ S s with hA
  set M := mixLogClass p₀ A with hM
  have hsqn : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hα0 : 0 < Real.sqrt n * s ^ 2 := by positivity
  set α := ENNReal.ofReal (Real.sqrt n * s ^ 2) with hαdef
  have hα : α ≠ 0 := by rw [hαdef]; exact (ENNReal.ofReal_pos.mpr hα0).ne'
  have hαt : α ≠ ⊤ := ENNReal.ofReal_ne_top
  set t := ENNReal.ofReal (32⁻¹ * (Real.sqrt n * s ^ 2)) with htdef
  have ht : t = ENNReal.ofReal 32⁻¹ * α := by
    rw [htdef, hαdef, ENNReal.ofReal_mul (by norm_num)]
  have htpos : 0 < t := ENNReal.ofReal_pos.mpr (by positivity)
  -- an empty annulus gives an empty event
  by_cases hAe : A = ∅
  · have : {ω | t ≤ empiricalSup P₀ M (sample X n ω)} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
      have : empiricalSup P₀ M (sample X n ω) = 0 := by
        simp [empiricalSup, hM, mixLogClass, hAe]
      rw [this]; exact htpos
    rw [this, measure_empty]; exact zero_le
  set K := annulusEntropy μ p₀ S s with hKdef
  have hKeq : K = hBracketingIntegral μ (Real.sqrt 2 * s) A := by
    rw [hKdef, annulusEntropy, ite_eq_right_iff.mpr (absurd · hAe)]
  set u := K / α with hudef
  have hKu : K = u * α := (ENNReal.div_mul_cancel hα hαt).symm
  -- the maximal inequality on the canonical space with radius `δ = 3 √2 s`
  set r := Real.sqrt 2 * s with hr
  have hr0 : 0 < r := by positivity
  have hclass : ∀ f ∈ M, Measurable f ∧ bernsteinFun P₀ f ≤ ENNReal.ofReal (3 * r) := by
    rintro f ⟨p, hpA, rfl⟩
    have hp := hS p hpA.1
    refine ⟨measurable_mixLog hp₀.measurable hp.measurable, ?_⟩
    calc bernsteinFun P₀ (mixLog p₀ p) ≤ 3 * hdist μ p₀ p :=
          bernsteinFun_mixLog_le hp₀.measurable hp.measurable
      _ ≤ 3 * ENNReal.ofReal r := by gcongr; exact hpA.2.2
      _ = ENNReal.ofReal (3 * r) := by
        rw [ENNReal.ofReal_mul (p := (3 : ℝ)) (q := r) (by norm_num), ENNReal.ofReal_ofNat]
  have hmax := hK₀ P₀ M n (3 * r) (by omega) (by positivity) hclass
  have hJ : bBracketingIntegral P₀ (3 * r) M ≤ 3 * K := by
    rw [hKeq]; exact bBracketingIntegral_mixLogClass_le hp₀ A r
  have hden : ENNReal.ofReal ((3 * r) ^ 2 * Real.sqrt n) = 18 * α := by
    rw [hαdef, show (18 : ℝ≥0∞) = ENNReal.ofReal 18 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    rw [hr, mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]; ring
  have hfrac : bBracketingIntegral P₀ (3 * r) M / ENNReal.ofReal ((3 * r) ^ 2 * Real.sqrt n) ≤ u := by
    rw [hden]
    calc bBracketingIntegral P₀ (3 * r) M / (18 * α) ≤ 3 * K / (18 * α) := by gcongr
      _ ≤ 3 * K / (3 * α) := by gcongr; norm_num
      _ = u := by rw [hudef, ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)]
  have houter : outerLIntegral (Measure.pi fun _ : Fin n ↦ P₀) (empiricalSup P₀ M) ≤
      3 * K₀ * (u + u ^ 2) * α := by
    calc _ ≤ (K₀ : ℝ≥0∞) * bBracketingIntegral P₀ (3 * r) M *
          (1 + bBracketingIntegral P₀ (3 * r) M / ENNReal.ofReal ((3 * r) ^ 2 * Real.sqrt n)) := hmax
      _ ≤ (K₀ : ℝ≥0∞) * (3 * K) * (1 + u) := by gcongr
      _ = 3 * K₀ * (u + u ^ 2) * α := by rw [hKu]; ring
  -- Markov on the canonical space and transfer to the sample space
  have hmarkov : t * (Measure.pi fun _ : Fin n ↦ P₀) {x | t ≤ empiricalSup P₀ M x} ≤
      3 * K₀ * (u + u ^ 2) * α :=
    (mul_measure_le_outerLIntegral _ t).trans houter
  have hpre : Pr {ω | t ≤ empiricalSup P₀ M (sample X n ω)} ≤
      (Measure.pi fun _ : Fin n ↦ P₀) {x | t ≤ empiricalSup P₀ M x} :=
    measure_sample_preimage_le hX hind hlaw n {x | t ≤ empiricalSup P₀ M x}
  set Q := (Measure.pi fun _ : Fin n ↦ P₀) {x | t ≤ empiricalSup P₀ M x}
  have hQ : ENNReal.ofReal 32⁻¹ * Q ≤ 3 * K₀ * (u + u ^ 2) := by
    rw [ht, mul_comm (ENNReal.ofReal 32⁻¹) α, mul_assoc] at hmarkov
    rw [mul_comm _ α] at hmarkov
    exact (ENNReal.mul_le_mul_iff_right hα hαt).mp hmarkov
  have h32 : (32 : ℝ≥0∞) * ENNReal.ofReal 32⁻¹ = 1 := by
    rw [show (32 : ℝ≥0∞) = ENNReal.ofReal 32 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  calc Pr {ω | t ≤ empiricalSup P₀ M (sample X n ω)} ≤ Q := hpre
    _ = 32 * (ENNReal.ofReal 32⁻¹ * Q) := by rw [← mul_assoc, h32, one_mul]
    _ ≤ 32 * (3 * K₀ * (u + u ^ 2)) := by gcongr
    _ = 96 * K₀ * (u + u ^ 2) := by ring

end Hellinger.MLE
