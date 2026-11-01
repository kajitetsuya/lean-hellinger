/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.MLE.External

/-!
Exact statements of the corrected sieve MLE theorem (Theorem 8 of the paper) and its
sufficient-condition corollaries, as propositions. They are proved in `Theorem8.lean` from the
maximal inequality `External.VdW_2_14_18_prime`, and unconditionally in
`Theorem8Unconditional.lean`.

The paper's entropy assumption `J̃_[](δ_n, 𝒫_{n,δ_n}, h) ≤ δ_n² √n` does not suffice (a
counterexample is given in `docs/Theorem8.md`); it is replaced by the annular entropy-tail
condition (D).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Hellinger.MLE

universe u v

/-- The hypotheses of Theorem 8 of the paper, all but the entropy condition. Observations are
i.i.d. with law `p₀ · μ`; the sieve `S n` consists of probability densities; `pn n ∈ S n` is
deterministic; the estimator `phat n ω ∈ S n` is an arbitrary, possibly nonmeasurable, map.
Approximation and log-tail bounds hold eventually with fixed finite `D, M ≥ 0`. The sample
likelihood comparison `ℙ_n log phat ≥ ℙ_n log pn - O_P(δ_n²)` is the statement that the
optimization deficit is `O_P^*(δ_n²)`. -/
structure MLEHypotheses {𝒳 : Type u} [MeasurableSpace 𝒳] (μ : Measure 𝒳)
    {Ω : Type v} [MeasurableSpace Ω] (ℙ : Measure Ω) (X : ℕ → Ω → 𝒳) (p₀ : 𝒳 → ℝ≥0)
    (S : ℕ → Set (𝒳 → ℝ≥0)) (pn : ℕ → 𝒳 → ℝ≥0) (phat : ℕ → Ω → 𝒳 → ℝ≥0)
    (δ : ℕ → ℝ) (D M : ℝ) : Prop where
  probability : IsProbabilityMeasure ℙ
  density : IsProbDensity μ p₀
  measurable_obs : ∀ i, Measurable (X i)
  indep : iIndepFun X ℙ
  law_obs : ∀ i, ℙ.map (X i) = law μ p₀
  sieve_density : ∀ n, ∀ p ∈ S n, IsProbDensity μ p
  comparator_mem : ∀ n, pn n ∈ S n
  estimator_mem : ∀ n ω, phat n ω ∈ S n
  rate_nonneg : ∀ n, 0 ≤ δ n
  D_nonneg : 0 ≤ D
  M_nonneg : 0 ≤ M
  /-- `h(p₀, p_n) ≤ D δ_n` eventually. -/
  approx : ∃ N, ∀ n ≥ N, hdist μ p₀ (pn n) ≤ ENNReal.ofReal (D * δ n)
  /-- `P₀[(log(p₀/p_n))² 1{p₀/p_n > 4}] ≤ M δ_n²` eventually (`+∞` off absolute continuity). -/
  logTail : ∃ N, ∀ n ≥ N,
    tailLogMoment (law μ p₀) (law μ (pn n)) 4 2 ≤ ENNReal.ofReal (M * δ n ^ 2)
  /-- `ℙ_n log phat_n ≥ ℙ_n log p_n - O_P(δ_n²)`, through the nonnegative deficit. -/
  likelihood : OPStar ℙ (fun n ω ↦ logLikDeficit (sample X n ω) (pn n) (phat n ω))
    (fun n ↦ δ n ^ 2)

/-- The conclusion `h(p₀, phat_n) = O_P^*(a_n)`, `a_n = max(δ_n, n^{-1/2})`. -/
def RateConclusion {𝒳 : Type u} [MeasurableSpace 𝒳] (μ : Measure 𝒳)
    {Ω : Type v} [MeasurableSpace Ω] (ℙ : Measure Ω) (p₀ : 𝒳 → ℝ≥0)
    (phat : ℕ → Ω → 𝒳 → ℝ≥0) (δ : ℕ → ℝ) : Prop :=
  OPStar ℙ (fun n ω ↦ hdist μ p₀ (phat n ω)) (rate δ)

/-- Corrected Theorem 8 under the annular entropy-tail condition (D). -/
def Theorem8Statement : Prop :=
  ∀ {𝒳 : Type u} [MeasurableSpace 𝒳] (μ : Measure 𝒳)
    {Ω : Type v} [MeasurableSpace Ω] (ℙ : Measure Ω) (X : ℕ → Ω → 𝒳) (p₀ : 𝒳 → ℝ≥0)
    (S : ℕ → Set (𝒳 → ℝ≥0)) (pn : ℕ → 𝒳 → ℝ≥0) (phat : ℕ → Ω → 𝒳 → ℝ≥0)
    (δ : ℕ → ℝ) (D M : ℝ),
    MLEHypotheses μ ℙ X p₀ S pn phat δ D M → AnnularTailCondition μ p₀ S δ →
      RateConclusion μ ℙ p₀ phat δ

/-- The ordinary `O_P` form when the Hellinger error is measurable: the tail events are
measurable and their probabilities are eventually small. This restates `RateConclusion`;
the `MeasurableSet` conjunct follows directly from the measurability premise. -/
def Theorem8MeasurableStatement : Prop :=
  ∀ {𝒳 : Type u} [MeasurableSpace 𝒳] (μ : Measure 𝒳)
    {Ω : Type v} [MeasurableSpace Ω] (ℙ : Measure Ω) (X : ℕ → Ω → 𝒳) (p₀ : 𝒳 → ℝ≥0)
    (S : ℕ → Set (𝒳 → ℝ≥0)) (pn : ℕ → 𝒳 → ℝ≥0) (phat : ℕ → Ω → 𝒳 → ℝ≥0)
    (δ : ℕ → ℝ) (D M : ℝ),
    MLEHypotheses μ ℙ X p₀ S pn phat δ D M → AnnularTailCondition μ p₀ S δ →
    (∀ n, Measurable fun ω ↦ hdist μ p₀ (phat n ω)) →
      ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, ∀ n ≥ N,
        MeasurableSet {ω | ENNReal.ofReal (K * rate δ n) < hdist μ p₀ (phat n ω)} ∧
        ℙ {ω | ENNReal.ofReal (K * rate δ n) < hdist μ p₀ (phat n ω)} ≤ ENNReal.ofReal ε

/-- (H) implies (D). No probabilistic hypothesis is needed. -/
def PowerEnvelopeImpliesAnnularStatement : Prop :=
  ∀ {𝒳 : Type u} [MeasurableSpace 𝒳] (μ : Measure 𝒳) (p₀ : 𝒳 → ℝ≥0)
    (S : ℕ → Set (𝒳 → ℝ≥0)) (δ : ℕ → ℝ),
    PowerEnvelopeCondition μ p₀ S δ → AnnularTailCondition μ p₀ S δ

/-- (G) implies (H) with `β = 1`. -/
def WholeSieveImpliesPowerEnvelopeStatement : Prop :=
  ∀ {𝒳 : Type u} [MeasurableSpace 𝒳] (μ : Measure 𝒳) (p₀ : 𝒳 → ℝ≥0)
    (S : ℕ → Set (𝒳 → ℝ≥0)) (δ : ℕ → ℝ),
    WholeSieveCondition μ S δ → PowerEnvelopeCondition μ p₀ S δ

/-- The rate theorem under (H). -/
def Theorem8PowerEnvelopeStatement : Prop :=
  ∀ {𝒳 : Type u} [MeasurableSpace 𝒳] (μ : Measure 𝒳)
    {Ω : Type v} [MeasurableSpace Ω] (ℙ : Measure Ω) (X : ℕ → Ω → 𝒳) (p₀ : 𝒳 → ℝ≥0)
    (S : ℕ → Set (𝒳 → ℝ≥0)) (pn : ℕ → 𝒳 → ℝ≥0) (phat : ℕ → Ω → 𝒳 → ℝ≥0)
    (δ : ℕ → ℝ) (D M : ℝ),
    MLEHypotheses μ ℙ X p₀ S pn phat δ D M → PowerEnvelopeCondition μ p₀ S δ →
      RateConclusion μ ℙ p₀ phat δ

/-- The rate theorem under (G). -/
def Theorem8WholeSieveStatement : Prop :=
  ∀ {𝒳 : Type u} [MeasurableSpace 𝒳] (μ : Measure 𝒳)
    {Ω : Type v} [MeasurableSpace Ω] (ℙ : Measure Ω) (X : ℕ → Ω → 𝒳) (p₀ : 𝒳 → ℝ≥0)
    (S : ℕ → Set (𝒳 → ℝ≥0)) (pn : ℕ → 𝒳 → ℝ≥0) (phat : ℕ → Ω → 𝒳 → ℝ≥0)
    (δ : ℕ → ℝ) (D M : ℝ),
    MLEHypotheses μ ℙ X p₀ S pn phat δ D M → WholeSieveCondition μ S δ →
      RateConclusion μ ℙ p₀ phat δ

end Hellinger.MLE
