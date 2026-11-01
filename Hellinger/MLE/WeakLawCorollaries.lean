/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.MLE.WeakLawStatements
public import Hellinger.MLE.MixLog
public import Hellinger.MLE.DensityBridge
public import Hellinger.CutoffFourMoments

/-!
Corollaries for the weak-law form of Theorem 8: under absolute continuity the extended tail
integrates to the first log-tail moment; the first-moment log tail implies the weak-law
truncation condition (W) with `L_n = ⊤`; and the paper's squared log-tail hypotheses give the
base hypotheses together with the first-moment log tail.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Hellinger.MLE

universe u v

variable {𝒳 : Type*} [MeasurableSpace 𝒳] {μ : Measure 𝒳}

/-- Under absolute continuity the extended tail integrates to the first log-tail moment. -/
theorem lintegral_extTail_eq_tailLogMoment {p₀ q : 𝒳 → ℝ≥0} (hp₀ : IsProbDensity μ p₀)
    (hq : IsProbDensity μ q) (hac : law μ p₀ ≪ law μ q) :
    ∫⁻ x, extTail p₀ q x ∂(law μ p₀) = tailLogMoment (law μ p₀) (law μ q) 4 1 := by
  rw [tailLogMoment_of_ac hac, ← lintegral_indicator (measurableSet_tailEvent _ _ _)]
  apply lintegral_congr_ae
  filter_upwards [ae_law_pos (μ := μ) hp₀.measurable, ae_law_pos_right hq.measurable hac,
    llr_law_ae_eq hp₀ hq hac] with x h0 hq0 hl
  have hns : ¬ (0 < p₀ x ∧ q x = 0) := fun h ↦ hq0.ne' h.2
  have hqr : (0 : ℝ) < q x := by exact_mod_cast hq0
  have hpr : (0 : ℝ) < p₀ x := by exact_mod_cast h0
  have key : (4 * q x < p₀ x) ↔ Real.log 4 < Real.log ((p₀ x : ℝ) / q x) := by
    rw [Real.log_lt_log_iff (by norm_num) (div_pos hpr hqr), lt_div_iff₀ hqr,
      ← NNReal.coe_lt_coe, NNReal.coe_mul]
    norm_num [mul_comm]
  simp only [Set.indicator, tailEvent, Set.mem_ofPred_eq, hl, Real.rpow_one, extTail, hns,
    ↓reduceIte]
  by_cases h4 : 4 * q x < p₀ x
  · simp only [h4, ↓reduceIte, key.1 h4]
  · simp only [h4, ↓reduceIte, mt key.2 h4]

theorem firstMoment_implies_weakLaw : FirstMomentImpliesWeakLawStatement.{u} := by
  intro 𝒳 _ μ p₀ pn δ hp₀ hpn hfm
  obtain ⟨M, N, hN⟩ := hfm
  refine ⟨fun _ ↦ ⊤, max M 0, fun ε _ ↦ ⟨0, fun n _ ↦ ?_⟩, N, fun n hn ↦ ?_⟩
  · simp
  · have ht := hN n hn
    have hac : law μ p₀ ≪ law μ (pn n) := by
      by_contra hna
      rw [tailLogMoment_of_not_ac hna] at ht
      exact ENNReal.ofReal_ne_top (top_le_iff.mp ht)
    have he : truncTail p₀ (pn n) ⊤ = extTail p₀ (pn n) :=
      funext fun x ↦ by simp [truncTail]
    simp only [he, lintegral_extTail_eq_tailLogMoment hp₀ (hpn n) hac]
    exact ht.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)))

/-- Under the paper's hypotheses, eventually `A₁ ≤ 4 D √M δ_n²`. -/
theorem MLEHypotheses.eventually_tailLogMoment_one_le
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} {X : ℕ → Ω → 𝒳} {p₀ : 𝒳 → ℝ≥0}
    {S : ℕ → Set (𝒳 → ℝ≥0)} {pn : ℕ → 𝒳 → ℝ≥0} {phat : ℕ → Ω → 𝒳 → ℝ≥0}
    {δ : ℕ → ℝ} {D M : ℝ} (h : MLEHypotheses μ Pr X p₀ S pn phat δ D M) :
    ∃ N, ∀ n ≥ N, tailLogMoment (law μ p₀) (law μ (pn n)) 4 1 ≤
      ENNReal.ofReal (4 * D * Real.sqrt M * δ n ^ 2) := by
  obtain ⟨N₁, hN₁⟩ := h.approx
  obtain ⟨N₂, hN₂⟩ := h.logTail
  refine ⟨max N₁ N₂, fun n hn ↦ ?_⟩
  have hd := hN₁ n (le_of_max_le_left hn)
  have ht := hN₂ n (le_of_max_le_right hn)
  have hp₀ := h.density
  have hpn : IsProbDensity μ (pn n) := h.sieve_density n _ (h.comparator_mem n)
  have hδ := h.rate_nonneg n
  have hD := h.D_nonneg
  have hM := h.M_nonneg
  have := isProbabilityMeasure_law hp₀
  have := isProbabilityMeasure_law hpn
  set P := law μ p₀ with hP
  set Q := law μ (pn n) with hQ
  have hH : hellingerSq P Q = hellingerFunSq μ p₀ (pn n) :=
    (hellingerFunSq_eq_hellingerSq_law_of_isProbDensity hp₀ hpn).symm
  have hHhalf : hellingerSq P Q ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (D * δ n) := by
    rw [hH]; exact hd
  have hA₂ : tailLogMoment P Q 4 2 ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (Real.sqrt M * δ n) := by
    calc tailLogMoment P Q 4 2 ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (M * δ n ^ 2) ^ (1 / 2 : ℝ) := by
          gcongr
      _ = ENNReal.ofReal (Real.sqrt M * δ n) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
            Real.sqrt_mul hM, Real.sqrt_sq hδ]
  calc tailLogMoment P Q 4 1
      ≤ 4 * hellingerSq P Q ^ (1 - (1 : ℝ) / 2) * tailLogMoment P Q 4 2 ^ ((1 : ℝ) / 2) :=
        tailLogMoment_interpolation_four one_pos one_le_two
    _ = 4 * hellingerSq P Q ^ (1 / 2 : ℝ) * tailLogMoment P Q 4 2 ^ (1 / 2 : ℝ) := by
        norm_num
    _ ≤ 4 * ENNReal.ofReal (D * δ n) * ENNReal.ofReal (Real.sqrt M * δ n) := by
        gcongr
    _ = ENNReal.ofReal (4 * D * Real.sqrt M * δ n ^ 2) := by
        rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_mul (by positivity)]
        ring_nf

theorem squaredTail_implies_firstMoment : SquaredTailImpliesFirstMomentStatement.{u, v} := by
  intro 𝒳 _ μ Ω _ ℙ X p₀ S pn phat δ D M h
  refine ⟨{ probability := h.probability
            density := h.density
            measurable_obs := h.measurable_obs
            indep := h.indep
            law_obs := h.law_obs
            sieve_density := h.sieve_density
            comparator_mem := h.comparator_mem
            estimator_mem := h.estimator_mem
            rate_nonneg := h.rate_nonneg
            D_nonneg := h.D_nonneg
            approx := h.approx
            likelihood := h.likelihood }, ?_⟩
  obtain ⟨N, hN⟩ := h.eventually_tailLogMoment_one_le
  refine ⟨4 * D * Real.sqrt M, N, fun n hn ↦ (hN n hn).trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have hc : 0 ≤ 4 * D * Real.sqrt M := by have := h.D_nonneg; positivity
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (h.rate_nonneg n) (le_max_left _ _) 2) hc

end Hellinger.MLE
