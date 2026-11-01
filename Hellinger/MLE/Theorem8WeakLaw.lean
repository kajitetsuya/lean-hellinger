/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.MLE.Theorem8
public import Hellinger.MLE.WeakLawShell
public import Hellinger.MLE.WeakLawComparator
public import Hellinger.MLE.WeakLawCorollaries
public import Hellinger.VdW.Main
public import Hellinger.MLE.WitnessNondegenerate

/-!
The weak-law form of corrected Theorem 8: Theorem 8 under the weak-law truncation condition
(W). The finite-`n` bound is
`P^*{h(p₀, p̂_n) > 2^{k/2} a_n} ≤ P^*{Z_n > 2^k a_n²/32} + Pr(G_n) + 96 K₀ (T_n(k) + T_n(k)²)`
with the comparator `Z_n = weakComparatorError` and the exceptional event
`G_n = {∃ i < n, T_n(X_i) > L_n}`; (W1) makes `Pr(G_n) ≤ n P₀(T_n > L_n)` small.

The first-moment version is the case `L_n = ⊤`, and the version with the paper's squared
log-tail hypothesis (`theorem8`) is a further corollary (`theorem8_of_weakLaw`). Each theorem
is stated with `External.VdW_2_14_18_prime` as a hypothesis and also unconditionally, through
`External.vdw_2_14_18_prime`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Hellinger.MLE

universe u v

/-- **Corrected Theorem 8, weak-law form**, under (D) and the weak-law truncation condition
(W), from van der Vaart and Wellner's Theorem 2.14.18'. -/
theorem theorem8_weakLaw (hvdw : External.VdW_2_14_18_prime.{u}) :
    Theorem8WeakLawStatement.{u, v} := by
  intro 𝒳 _ μ Ω _ Pr X p₀ S pn phat δ D h hW hD
  obtain ⟨L, M, hW1, hW2⟩ := hW
  obtain ⟨K₀, hK₀⟩ := hvdw.maximalBound (𝒳 := 𝒳)
  obtain ⟨N₀, hN₀⟩ := tail_le_shell_bound_of_lower h hK₀ (weakComparatorError μ X p₀ pn phat L)
    (exceptionalEvent X p₀ pn L) (sampleMean_mixLog_ge_weak h L)
  intro ε hε
  obtain ⟨KZ, hKZ, N₁, hN₁⟩ := weakComparatorError_opStar h L M hW2 (ε / 3) (by linarith)
  obtain ⟨N₃, hN₃⟩ := hW1 (ε / 3) (by linarith)
  set c : ℝ := 96 * K₀ with hc
  have hc0 : 0 ≤ c := by positivity
  set η : ℝ := min 1 (ε / (6 * (c + 1))) with hη
  have hη0 : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  obtain ⟨k₁, N₂, hT⟩ := hD.eventually_le hη0
  obtain ⟨k₂, hk₂⟩ := pow_unbounded_of_one_lt (32 * KZ) (by norm_num : (1 : ℝ) < 2)
  set k := max k₁ k₂ with hk
  refine ⟨Real.sqrt 2 ^ k, by positivity, max (max N₀ N₁) (max N₂ N₃), fun n hn ↦ ?_⟩
  have hnN₀ : n ≥ N₀ := le_of_max_le_left (le_of_max_le_left hn)
  have hnN₁ : n ≥ N₁ := le_of_max_le_right (le_of_max_le_left hn)
  have hnN₂ : n ≥ N₂ := le_of_max_le_left (le_of_max_le_right hn)
  have hnN₃ : n ≥ N₃ := le_of_max_le_right (le_of_max_le_right hn)
  have hbound := hN₀ n hnN₀ k
  have hB : {ω | ENNReal.ofReal (32⁻¹ * 2 ^ k * rate δ n ^ 2) <
        weakComparatorError μ X p₀ pn phat L n ω} ⊆
      {ω | ENNReal.ofReal (KZ * rate δ n ^ 2) < weakComparatorError μ X p₀ pn phat L n ω} := by
    intro ω hω
    refine lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ?_) hω
    have : KZ ≤ 32⁻¹ * 2 ^ k := by
      have h2 : (2 : ℝ) ^ k₂ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (le_max_right _ _)
      linarith
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  have hG : Pr (exceptionalEvent X p₀ pn L n) ≤ ENNReal.ofReal (ε / 3) :=
    (measure_exceptionalEvent_le h L n).trans (hN₃ n hnN₃)
  have hTn := hT k (le_max_left _ _) n hnN₂
  have hshell : 96 * (K₀ : ℝ≥0∞) * (shellTail μ p₀ S δ n k + shellTail μ p₀ S δ n k ^ 2) ≤
      ENNReal.ofReal (ε / 3) := by
    calc 96 * (K₀ : ℝ≥0∞) * (shellTail μ p₀ S δ n k + shellTail μ p₀ S δ n k ^ 2)
        ≤ ENNReal.ofReal c * (ENNReal.ofReal η + ENNReal.ofReal η ^ 2) := by
          rw [hc, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_coe_nnreal]
          gcongr
          simp
      _ = ENNReal.ofReal (c * (η + η ^ 2)) := by
          rw [← ENNReal.ofReal_pow hη0.le, ← ENNReal.ofReal_add hη0.le (by positivity),
            ← ENNReal.ofReal_mul hc0]
      _ ≤ ENNReal.ofReal (ε / 3) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hηε : η ≤ ε / (6 * (c + 1)) := min_le_right _ _
          have h1 : η + η ^ 2 ≤ 2 * η := by nlinarith
          have h2 : c * (2 * η) ≤ ε / 3 := by
            have : c * η ≤ c * (ε / (6 * (c + 1))) := mul_le_mul_of_nonneg_left hηε hc0
            have h3 : c * (ε / (6 * (c + 1))) ≤ ε / 6 := by
              rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
              nlinarith
            linarith
          calc c * (η + η ^ 2) ≤ c * (2 * η) := mul_le_mul_of_nonneg_left h1 hc0
            _ ≤ ε / 3 := h2
  calc Pr {ω | ENNReal.ofReal (Real.sqrt 2 ^ k * rate δ n) < hdist μ p₀ (phat n ω)}
      ≤ Pr {ω | ENNReal.ofReal (32⁻¹ * 2 ^ k * rate δ n ^ 2) <
            weakComparatorError μ X p₀ pn phat L n ω} + Pr (exceptionalEvent X p₀ pn L n) +
          96 * K₀ * (shellTail μ p₀ S δ n k + shellTail μ p₀ S δ n k ^ 2) := hbound
    _ ≤ ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3) :=
        add_le_add (add_le_add ((measure_mono hB).trans (hN₁ n hnN₁)) hG) hshell
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith),
          ← ENNReal.ofReal_add (by linarith) (by linarith)]
        ring_nf

/-- The ordinary `O_P` version of the weak-law form when the Hellinger error is measurable. -/
theorem theorem8_weakLaw_measurable (hvdw : External.VdW_2_14_18_prime.{u}) :
    Theorem8WeakLawMeasurableStatement.{u, v} := by
  intro 𝒳 _ μ Ω _ Pr X p₀ S pn phat δ D h hW hD hmeas ε hε
  obtain ⟨K, hK, N, hN⟩ := theorem8_weakLaw.{u, v} hvdw μ Pr X p₀ S pn phat δ D h hW hD ε hε
  exact ⟨K, hK, N, fun n hn ↦ ⟨measurableSet_lt measurable_const (hmeas n), hN n hn⟩⟩

/-- The weak-law form under the power envelope (H). -/
theorem theorem8_weakLaw_of_powerEnvelope (hvdw : External.VdW_2_14_18_prime.{u}) :
    Theorem8WeakLawPowerEnvelopeStatement.{u, v} := by
  intro 𝒳 _ μ Ω _ Pr X p₀ S pn phat δ D h hW hH
  exact theorem8_weakLaw.{u, v} hvdw μ Pr X p₀ S pn phat δ D h hW
    (annularTail_of_powerEnvelope.{u} μ p₀ S δ hH)

/-- The weak-law form under the whole-sieve bound (G). -/
theorem theorem8_weakLaw_of_wholeSieve (hvdw : External.VdW_2_14_18_prime.{u}) :
    Theorem8WeakLawWholeSieveStatement.{u, v} := by
  intro 𝒳 _ μ Ω _ Pr X p₀ S pn phat δ D h hW hG
  exact theorem8_weakLaw_of_powerEnvelope.{u, v} hvdw μ Pr X p₀ S pn phat δ D h hW
    (powerEnvelope_of_wholeSieve.{u} μ p₀ S δ hG)

/-- Corrected Theorem 8 under the first-moment log tail: the case `L_n = ⊤` of the weak-law
form. -/
theorem theorem8_firstMoment (hvdw : External.VdW_2_14_18_prime.{u}) :
    Theorem8FirstMomentStatement.{u, v} := by
  intro 𝒳 _ μ Ω _ Pr X p₀ S pn phat δ D h hF hD
  exact theorem8_weakLaw.{u, v} hvdw μ Pr X p₀ S pn phat δ D h
    (firstMoment_implies_weakLaw.{u} μ p₀ pn δ h.density
      (fun n ↦ h.sieve_density n _ (h.comparator_mem n)) hF) hD

/-- The paper's version is a corollary: the weak-law form implies corrected Theorem 8. -/
theorem theorem8_of_weakLaw (hw : Theorem8WeakLawStatement.{u, v}) :
    Theorem8Statement.{u, v} := by
  intro 𝒳 _ μ Ω _ Pr X p₀ S pn phat δ D M h hD
  obtain ⟨hb, hF⟩ := squaredTail_implies_firstMoment.{u, v} μ Pr X p₀ S pn phat δ D M h
  exact hw μ Pr X p₀ S pn phat δ D hb
    (firstMoment_implies_weakLaw.{u} μ p₀ pn δ hb.density
      (fun n ↦ hb.sieve_density n _ (hb.comparator_mem n)) hF) hD

/-! ### Unconditional forms -/

/-- **Corrected Theorem 8, weak-law form**, unconditionally. -/
theorem theorem8_weakLaw_unconditional : Theorem8WeakLawStatement.{u, v} :=
  theorem8_weakLaw External.vdw_2_14_18_prime

theorem theorem8_weakLaw_measurable_unconditional : Theorem8WeakLawMeasurableStatement.{u, v} :=
  theorem8_weakLaw_measurable External.vdw_2_14_18_prime

theorem theorem8_weakLaw_of_powerEnvelope_unconditional :
    Theorem8WeakLawPowerEnvelopeStatement.{u, v} :=
  theorem8_weakLaw_of_powerEnvelope External.vdw_2_14_18_prime

theorem theorem8_weakLaw_of_wholeSieve_unconditional :
    Theorem8WeakLawWholeSieveStatement.{u, v} :=
  theorem8_weakLaw_of_wholeSieve External.vdw_2_14_18_prime

theorem theorem8_firstMoment_unconditional : Theorem8FirstMomentStatement.{u, v} :=
  theorem8_firstMoment External.vdw_2_14_18_prime

/-- Corrected Theorem 8 obtained again, as a corollary of the weak-law form. -/
theorem theorem8_via_weakLaw : Theorem8Statement.{u, v} :=
  theorem8_of_weakLaw theorem8_weakLaw_unconditional

/-! ### Non-vacuity -/

/-- The hypotheses of the weak-law form and of its first-moment form are jointly satisfiable,
on the nondegenerate two-point witness of `WitnessNondegenerate.lean`. -/
theorem nonvacuous_weakLaw :
    MLEBaseHypotheses Measure.count (Measure.dirac PUnit.unit : Measure PUnit.{v + 1})
      (fun _ _ ↦ true) boolP₀ (fun _ ↦ {boolP₀, boolQ}) (fun _ ↦ boolP₀)
      (fun _ _ ↦ boolP₀) boolRate 0 ∧
    FirstMomentLogTail Measure.count boolP₀ (fun _ ↦ boolP₀) boolRate ∧
    WeakLawTruncation Measure.count boolP₀ (fun _ ↦ boolP₀) boolRate ∧
    AnnularTailCondition Measure.count boolP₀ (fun _ ↦ {boolP₀, boolQ}) boolRate := by
  obtain ⟨h, hD, -⟩ := nonvacuous_nondegenerate.{v}
  obtain ⟨hb, hF⟩ := squaredTail_implies_firstMoment _ _ _ _ _ _ _ _ _ _ h
  exact ⟨hb, hF, firstMoment_implies_weakLaw _ _ _ _ hb.density
    (fun n ↦ hb.sieve_density n _ (hb.comparator_mem n)) hF, hD⟩

end Hellinger.MLE
