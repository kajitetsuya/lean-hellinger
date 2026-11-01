/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.MLE.AnnularMaximal
public import Hellinger.MLE.Mixture
public import Hellinger.MLE.WeakLawStatements

/-!
The finite-`n` shell bound of `Theorem8.lean` for an abstract comparator `Z_n` that bounds
`ℙ_n m_{phat_n}` from below almost surely off an exceptional event `G_n`:
`P^*{h(p₀, p̂_n) > 2^{k/2} a_n} ≤ P^*{Z_n > 2^k a_n²/32} + Pr(G_n) + 96 K₀ (T_n(k) + T_n(k)²)`.
Only the base hypotheses are used.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Hellinger.MLE

variable {𝒳 : Type*} [MeasurableSpace 𝒳] {μ : Measure 𝒳} {Ω : Type*} [MeasurableSpace Ω]
  {Pr : Measure Ω} {X : ℕ → Ω → 𝒳} {p₀ : 𝒳 → ℝ≥0} {S : ℕ → Set (𝒳 → ℝ≥0)}
  {pn : ℕ → 𝒳 → ℝ≥0} {phat : ℕ → Ω → 𝒳 → ℝ≥0} {δ : ℕ → ℝ} {D : ℝ}

/-- The finite-`n` shell bound for a comparator `Z` with exceptional events `G`. -/
theorem tail_le_shell_bound_of_lower (h : MLEBaseHypotheses μ Pr X p₀ S pn phat δ D)
    {K₀ : ℝ≥0} (hK₀ : MaximalBound 𝒳 K₀) (Z : ℕ → Ω → ℝ≥0∞) (G : ℕ → Set Ω)
    (hlow : ∃ N, ∀ n ≥ N, ∀ᵐ ω ∂Pr, ω ∉ G n → Z n ω ≠ ⊤ →
      -(Z n ω).toReal ≤ sampleMean X n (mixLog p₀ (phat n ω)) ω) :
    ∃ N, ∀ n ≥ N, ∀ k : ℕ,
      Pr {ω | ENNReal.ofReal (shellScale (rate δ n) k) < hdist μ p₀ (phat n ω)} ≤
        Pr {ω | ENNReal.ofReal (32⁻¹ * 2 ^ k * rate δ n ^ 2) < Z n ω} + Pr (G n) +
          96 * K₀ * (shellTail μ p₀ S δ n k + shellTail μ p₀ S δ n k ^ 2) := by
  classical
  have := h.probability
  have : IsProbabilityMeasure (law μ p₀) := isProbabilityMeasure_law h.density
  obtain ⟨N₀, hN₀⟩ := hlow
  refine ⟨max N₀ 1, fun n hn k ↦ ?_⟩
  have hn1 : 1 ≤ n := le_of_max_le_right hn
  set a := rate δ n with hadef
  have ha : 0 < a := rate_pos δ hn1
  set cond : ℕ → Prop := fun j ↦ k ≤ j ∧ shellScale a j < Real.sqrt 2 with hcond
  set E : ℕ → Set Ω := fun j ↦ {ω | ENNReal.ofReal (32⁻¹ * (Real.sqrt n * shellScale a j ^ 2)) ≤
      empiricalSup (law μ p₀) (mixLogClass p₀ (annulus μ p₀ (S n) (shellScale a j)))
        (sample X n ω)} with hE
  set E' : ℕ → Set Ω := fun j ↦ if cond j then E j else ∅ with hE'
  set B := {ω | ENNReal.ofReal (32⁻¹ * 2 ^ k * a ^ 2) < Z n ω} with hB
  set Gb := {ω | ¬ (ω ∉ G n → Z n ω ≠ ⊤ →
      -(Z n ω).toReal ≤ sampleMean X n (mixLog p₀ (phat n ω)) ω)} with hGb
  have hGbnull : Pr Gb = 0 := ae_iff.mp (hN₀ n (le_of_max_le_left hn))
  set u : ℕ → ℝ≥0∞ := fun j ↦ shellTerm μ p₀ (S n) n a j with hu
  -- event inclusion
  have hsub : {ω | ENNReal.ofReal (shellScale a k) < hdist μ p₀ (phat n ω)} ⊆
      B ∪ G n ∪ Gb ∪ ⋃ j, E' j := by
    intro ω hω
    simp only [mem_ofPred_eq] at hω
    by_cases hωB : ω ∈ B
    · exact Or.inl (Or.inl (Or.inl hωB))
    by_cases hωG : ω ∈ G n
    · exact Or.inl (Or.inl (Or.inr hωG))
    by_cases hωGb : ω ∈ Gb
    · exact Or.inl (Or.inr hωGb)
    refine Or.inr (mem_iUnion.mpr ?_)
    simp only [hB, mem_ofPred_eq, not_lt] at hωB
    simp only [hGb, mem_ofPred_eq, not_not] at hωGb
    have hZfin : Z n ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hωB
    have hZle : (Z n ω).toReal ≤ 32⁻¹ * 2 ^ k * a ^ 2 :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hωB
    have hlowerS := hωGb hωG hZfin
    have hp := h.sieve_density n _ (h.estimator_mem n ω)
    obtain ⟨j, hkj, hsj, hlow, hup⟩ :=
      exists_shell ha hω (hdist_le_sqrt_two μ h.density hp)
    refine ⟨j, ?_⟩
    simp only [hE', hcond, hkj, hsj, and_self, ite_true]
    have hmem : phat n ω ∈ annulus μ p₀ (S n) (shellScale a j) :=
      ⟨h.estimator_mem n ω, hlow, hup⟩
    -- curvature at the estimator
    obtain ⟨-, hcurv⟩ := integral_mixLog_le h.density hp
    have hHfin := hellingerFunSq_ne_top μ h.density hp
    have hH : shellScale a j ^ 2 < (hellingerFunSq μ p₀ (phat n ω)).toReal := by
      have hs0 : 0 ≤ shellScale a j := (shellScale_pos ha j).le
      have h2 : ENNReal.ofReal (shellScale a j) ^ (2 : ℝ) <
          (hellingerFunSq μ p₀ (phat n ω) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) :=
        ENNReal.rpow_lt_rpow hlow (by norm_num)
      rw [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one,
        ENNReal.ofReal_rpow_of_nonneg hs0 (by norm_num), Real.rpow_two] at h2
      exact (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hHfin).mp h2
    rw [shellScale_sq] at hH
    have h2kj : (2 : ℝ) ^ k ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hkj
    have hgap : 32⁻¹ * (2 ^ j * a ^ 2) ≤
        sampleMean X n (mixLog p₀ (phat n ω)) ω - ∫ x, mixLog p₀ (phat n ω) x ∂(law μ p₀) := by
      have : 32⁻¹ * 2 ^ k * a ^ 2 ≤ 32⁻¹ * 2 ^ j * a ^ 2 := by gcongr
      nlinarith
    have hsqn : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
    simp only [hE, mem_ofPred_eq]
    rw [shellScale_sq]
    refine le_trans ?_ (le_iSup₂_of_le (mixLog p₀ (phat n ω)) ⟨phat n ω, hmem, rfl⟩ le_rfl)
    refine ENNReal.ofReal_le_ofReal ((le_abs_self _).trans' ?_)
    unfold empiricalProcess
    change 32⁻¹ * (Real.sqrt n * (2 ^ j * a ^ 2)) ≤
      Real.sqrt n * (sampleMean X n (mixLog p₀ (phat n ω)) ω -
        ∫ y, mixLog p₀ (phat n ω) y ∂(law μ p₀))
    nlinarith
  -- measure bound
  have hU : Pr (⋃ j, E' j) ≤ 96 * K₀ * (shellTail μ p₀ S δ n k + shellTail μ p₀ S δ n k ^ 2) := by
    set v : ℕ → ℝ≥0∞ := fun j ↦ if cond j then u j else 0 with hv
    have hT : shellTail μ p₀ S δ n k = ∑' j, v j := rfl
    have hEj : ∀ j, Pr (E' j) ≤ 96 * K₀ * (v j + v j ^ 2) := by
      intro j
      simp only [hE', hv]
      split_ifs with hc
      · exact measure_shell_le h.density (h.sieve_density n) hK₀ h.measurable_obs h.indep
          h.law_obs hn1 (shellScale_pos ha j)
      · simp
    calc Pr (⋃ j, E' j) ≤ ∑' j, Pr (E' j) := measure_iUnion_le _
      _ ≤ ∑' j, 96 * K₀ * (v j + v j ^ 2) := ENNReal.tsum_le_tsum hEj
      _ = 96 * K₀ * ((∑' j, v j) + ∑' j, v j ^ 2) := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_add]
      _ ≤ 96 * K₀ * ((∑' j, v j) + (∑' j, v j) ^ 2) := by
          gcongr; exact tsum_sq_le_sq_tsum v
      _ = _ := by rw [hT]
  calc _ ≤ Pr (B ∪ G n ∪ Gb ∪ ⋃ j, E' j) := measure_mono hsub
    _ ≤ Pr B + Pr (G n) + Pr Gb + Pr (⋃ j, E' j) :=
        (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
          (add_le_add (measure_union_le _ _) le_rfl)) le_rfl)
    _ ≤ Pr B + Pr (G n) + 0 +
          96 * K₀ * (shellTail μ p₀ S δ n k + shellTail μ p₀ S δ n k ^ 2) := by
        rw [hGbnull]; gcongr
    _ = _ := by rw [add_zero]

end Hellinger.MLE
