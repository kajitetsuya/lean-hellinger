/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.MLE.AnnularMaximal
public import Hellinger.MLE.Comparator
public import Hellinger.MLE.EntropyCorollaries

/-!
Corrected Theorem 8, proved by the direct shell argument from the maximal inequality
`External.VdW_2_14_18_prime`, taken as a hypothesis. The decisive finite-`n` bound is
`P^*{h(p₀, p̂_n) > 2^{k/2} a_n} ≤ P^*{Z_n > 2^k a_n²/32} + 96 K₀ (T_n(k) + T_n(k)²)`,
where `Z_n` is the comparator error. Tightness of `Z_n` and condition (D) make the right side
small for a fixed large `k`, eventually in `n`.

The unconditional forms, which discharge the hypothesis with `External.vdw_2_14_18_prime`, are
in `Theorem8Unconditional.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Hellinger.MLE

universe u v

variable {𝒳 : Type*} [MeasurableSpace 𝒳] {μ : Measure 𝒳} {Ω : Type*} [MeasurableSpace Ω]
  {Pr : Measure Ω} {X : ℕ → Ω → 𝒳} {p₀ : 𝒳 → ℝ≥0} {S : ℕ → Set (𝒳 → ℝ≥0)}
  {pn : ℕ → 𝒳 → ℝ≥0} {phat : ℕ → Ω → 𝒳 → ℝ≥0} {δ : ℕ → ℝ} {D M : ℝ}

/-- The finite-`n` shell bound. -/
theorem tail_le_shell_bound (h : MLEHypotheses μ Pr X p₀ S pn phat δ D M) {K₀ : ℝ≥0}
    (hK₀ : MaximalBound 𝒳 K₀) :
    ∃ N, ∀ n ≥ N, ∀ k : ℕ,
      Pr {ω | ENNReal.ofReal (shellScale (rate δ n) k) < hdist μ p₀ (phat n ω)} ≤
        Pr {ω | ENNReal.ofReal (32⁻¹ * 2 ^ k * rate δ n ^ 2) <
            comparatorError μ X p₀ pn phat n ω} +
          96 * K₀ * (shellTail μ p₀ S δ n k + shellTail μ p₀ S δ n k ^ 2) := by
  classical
  have := h.probability
  have : IsProbabilityMeasure (law μ p₀) := isProbabilityMeasure_law h.density
  obtain ⟨N₀, hN₀⟩ := sampleMean_mixLog_ge h
  refine ⟨max N₀ 1, fun n hn k ↦ ?_⟩
  have hn1 : 1 ≤ n := le_of_max_le_right hn
  set a := rate δ n with hadef
  have ha : 0 < a := rate_pos δ hn1
  set Z := comparatorError μ X p₀ pn phat n with hZdef
  set cond : ℕ → Prop := fun j ↦ k ≤ j ∧ shellScale a j < Real.sqrt 2 with hcond
  set E : ℕ → Set Ω := fun j ↦ {ω | ENNReal.ofReal (32⁻¹ * (Real.sqrt n * shellScale a j ^ 2)) ≤
      empiricalSup (law μ p₀) (mixLogClass p₀ (annulus μ p₀ (S n) (shellScale a j)))
        (sample X n ω)} with hE
  set E' : ℕ → Set Ω := fun j ↦ if cond j then E j else ∅ with hE'
  set B := {ω | ENNReal.ofReal (32⁻¹ * 2 ^ k * a ^ 2) < Z ω} with hB
  set G := {ω | ¬ (Z ω ≠ ⊤ → -(Z ω).toReal ≤ sampleMean X n (mixLog p₀ (phat n ω)) ω)} with hG
  have hGnull : Pr G = 0 := ae_iff.mp (hN₀ n (le_of_max_le_left hn))
  set u : ℕ → ℝ≥0∞ := fun j ↦ shellTerm μ p₀ (S n) n a j with hu
  -- event inclusion
  have hsub : {ω | ENNReal.ofReal (shellScale a k) < hdist μ p₀ (phat n ω)} ⊆
      B ∪ G ∪ ⋃ j, E' j := by
    intro ω hω
    simp only [mem_ofPred_eq] at hω
    by_cases hωB : ω ∈ B
    · exact Or.inl (Or.inl hωB)
    by_cases hωG : ω ∈ G
    · exact Or.inl (Or.inr hωG)
    refine Or.inr (mem_iUnion.mpr ?_)
    simp only [hB, mem_ofPred_eq, not_lt] at hωB
    simp only [hG, mem_ofPred_eq, not_not] at hωG
    have hZfin : Z ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hωB
    have hZle : (Z ω).toReal ≤ 32⁻¹ * 2 ^ k * a ^ 2 :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hωB
    have hlowerS := hωG hZfin
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
  calc _ ≤ Pr (B ∪ G ∪ ⋃ j, E' j) := measure_mono hsub
    _ ≤ Pr B + Pr G + Pr (⋃ j, E' j) :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ Pr B + 0 + 96 * K₀ * (shellTail μ p₀ S δ n k + shellTail μ p₀ S δ n k ^ 2) := by
        rw [hGnull]; gcongr
    _ = _ := by rw [add_zero]

/-- **Corrected Theorem 8** under the annular entropy-tail condition (D), from van der Vaart
and Wellner's Theorem 2.14.18'. -/
theorem theorem8 (hvdw : External.VdW_2_14_18_prime.{u}) : Theorem8Statement.{u, v} := by
  intro 𝒳 _ μ Ω _ Pr X p₀ S pn phat δ D M h hD
  obtain ⟨K₀, hK₀⟩ := hvdw.maximalBound (𝒳 := 𝒳)
  obtain ⟨N₀, hN₀⟩ := tail_le_shell_bound h hK₀
  intro ε hε
  obtain ⟨KZ, hKZ, N₁, hN₁⟩ := comparatorError_opStar h (ε / 2) (by linarith)
  set c : ℝ := 96 * K₀ with hc
  have hc0 : 0 ≤ c := by positivity
  set η : ℝ := min 1 (ε / (4 * (c + 1))) with hη
  have hη0 : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  obtain ⟨k₁, N₂, hT⟩ := hD.eventually_le hη0
  obtain ⟨k₂, hk₂⟩ := pow_unbounded_of_one_lt (32 * KZ) (by norm_num : (1 : ℝ) < 2)
  set k := max k₁ k₂ with hk
  refine ⟨Real.sqrt 2 ^ k, by positivity, max (max N₀ N₁) N₂, fun n hn ↦ ?_⟩
  have hnN₀ : n ≥ N₀ := le_of_max_le_left (le_of_max_le_left hn)
  have hnN₁ : n ≥ N₁ := le_of_max_le_right (le_of_max_le_left hn)
  have hnN₂ : n ≥ N₂ := le_of_max_le_right hn
  have hbound := hN₀ n hnN₀ k
  have hB : {ω | ENNReal.ofReal (32⁻¹ * 2 ^ k * rate δ n ^ 2) < comparatorError μ X p₀ pn phat n ω} ⊆
      {ω | ENNReal.ofReal (KZ * rate δ n ^ 2) < comparatorError μ X p₀ pn phat n ω} := by
    intro ω hω
    refine lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ?_) hω
    have : KZ ≤ 32⁻¹ * 2 ^ k := by
      have h2 : (2 : ℝ) ^ k₂ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (le_max_right _ _)
      linarith
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  have hTn := hT k (le_max_left _ _) n hnN₂
  have hshell : 96 * (K₀ : ℝ≥0∞) * (shellTail μ p₀ S δ n k + shellTail μ p₀ S δ n k ^ 2) ≤
      ENNReal.ofReal (ε / 2) := by
    calc 96 * (K₀ : ℝ≥0∞) * (shellTail μ p₀ S δ n k + shellTail μ p₀ S δ n k ^ 2)
        ≤ ENNReal.ofReal c * (ENNReal.ofReal η + ENNReal.ofReal η ^ 2) := by
          rw [hc, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_coe_nnreal]
          gcongr
          simp
      _ = ENNReal.ofReal (c * (η + η ^ 2)) := by
          rw [← ENNReal.ofReal_pow hη0.le, ← ENNReal.ofReal_add hη0.le (by positivity),
            ← ENNReal.ofReal_mul hc0]
      _ ≤ ENNReal.ofReal (ε / 2) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hηε : η ≤ ε / (4 * (c + 1)) := min_le_right _ _
          have h1 : η + η ^ 2 ≤ 2 * η := by nlinarith
          have h2 : c * (2 * η) ≤ ε / 2 := by
            have : c * η ≤ c * (ε / (4 * (c + 1))) := mul_le_mul_of_nonneg_left hηε hc0
            have h3 : c * (ε / (4 * (c + 1))) ≤ ε / 4 := by
              rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
              nlinarith
            linarith
          calc c * (η + η ^ 2) ≤ c * (2 * η) := mul_le_mul_of_nonneg_left h1 hc0
            _ ≤ ε / 2 := h2
  calc Pr {ω | ENNReal.ofReal (Real.sqrt 2 ^ k * rate δ n) < hdist μ p₀ (phat n ω)}
      ≤ Pr {ω | ENNReal.ofReal (32⁻¹ * 2 ^ k * rate δ n ^ 2) <
            comparatorError μ X p₀ pn phat n ω} +
          96 * K₀ * (shellTail μ p₀ S δ n k + shellTail μ p₀ S δ n k ^ 2) := hbound
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
        add_le_add ((measure_mono hB).trans (hN₁ n hnN₁)) hshell
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; ring_nf

/-- The ordinary `O_P` form when the Hellinger error is measurable. -/
theorem theorem8_measurable (hvdw : External.VdW_2_14_18_prime.{u}) :
    Theorem8MeasurableStatement.{u, v} := by
  intro 𝒳 _ μ Ω _ Pr X p₀ S pn phat δ D M h hD hmeas ε hε
  obtain ⟨K, hK, N, hN⟩ := theorem8.{u, v} hvdw μ Pr X p₀ S pn phat δ D M h hD ε hε
  exact ⟨K, hK, N, fun n hn ↦ ⟨measurableSet_lt measurable_const (hmeas n), hN n hn⟩⟩

/-- The rate theorem under the power envelope (H). -/
theorem theorem8_of_powerEnvelope (hvdw : External.VdW_2_14_18_prime.{u}) :
    Theorem8PowerEnvelopeStatement.{u, v} := by
  intro 𝒳 _ μ Ω _ Pr X p₀ S pn phat δ D M h hH
  exact theorem8.{u, v} hvdw μ Pr X p₀ S pn phat δ D M h
    (annularTail_of_powerEnvelope.{u} μ p₀ S δ hH)

/-- The rate theorem under the whole-sieve bound (G). -/
theorem theorem8_of_wholeSieve (hvdw : External.VdW_2_14_18_prime.{u}) :
    Theorem8WholeSieveStatement.{u, v} := by
  intro 𝒳 _ μ Ω _ Pr X p₀ S pn phat δ D M h hG
  exact theorem8_of_powerEnvelope.{u, v} hvdw μ Pr X p₀ S pn phat δ D M h
    (powerEnvelope_of_wholeSieve.{u} μ p₀ S δ hG)

end Hellinger.MLE
