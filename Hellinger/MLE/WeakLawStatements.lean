/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.MLE.Statements

/-!
The weak-law form of corrected Theorem 8: Theorem 8 under the weak-law truncation condition
(W), which replaces the squared log-tail assumption, as suggested by a footnote in the
paper's discussion following Theorem 8. The proof is outlined in `docs/Theorem8.md`.

With `T_n = extTail p₀ p_n` the extended log tail (`⊤` on the singular set
`{p₀ > 0 = p_n}`), condition (W) asks for thresholds `L_n ∈ [0, ∞]` and a finite `M` with
`n P₀(T_n > L_n) → 0` and `P₀[T_n 1{T_n ≤ L_n}] ≤ M a_n²` eventually. No absolute continuity
is assumed. The first-moment tail condition is the special case `L_n = ⊤`, and the paper's
squared-tail assumption implies the first-moment one, so `Theorem8Statement` is a corollary.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Hellinger.MLE

universe u v

/-- The extended log tail: `⊤` where `p₀(x) > 0 = q(x)`, `log(p₀(x)/q(x))` where
`p₀(x) > 4 q(x) > 0`, and `0` otherwise (in particular where `p₀(x) = 0` or `p₀(x) ≤ 4 q(x)`).
The tail event `{p₀ > 4 q}` is written without division. -/
noncomputable def extTail {𝒳 : Type*} (p₀ q : 𝒳 → ℝ≥0) (x : 𝒳) : ℝ≥0∞ :=
  if 0 < p₀ x ∧ q x = 0 then ⊤
  else if 4 * q x < p₀ x then ENNReal.ofReal (Real.log ((p₀ x : ℝ) / q x)) else 0

/-- The truncated tail `T 1{T ≤ L}`, in `[0, ∞]`. With `L = ⊤` it is `T` itself. -/
noncomputable def truncTail {𝒳 : Type*} (p₀ q : 𝒳 → ℝ≥0) (L : ℝ≥0∞) (x : 𝒳) : ℝ≥0∞ :=
  if extTail p₀ q x ≤ L then extTail p₀ q x else 0

/-- Condition (W), the weak-law truncation of the log tail: there are thresholds
`L_n ∈ [0, ∞]` and a finite `M` such that (W1) `n P₀(T_n > L_n) → 0` and (W2), eventually,
`P₀[T_n 1{T_n ≤ L_n}] ≤ M a_n²`, where `T_n = extTail p₀ p_n`, `P₀ = p₀ · μ` and
`a_n = max(δ_n, n^{-1/2})`. A negative `M` is the same as `M = 0`. -/
def WeakLawTruncation {𝒳 : Type*} [MeasurableSpace 𝒳] (μ : Measure 𝒳) (p₀ : 𝒳 → ℝ≥0)
    (pn : ℕ → 𝒳 → ℝ≥0) (δ : ℕ → ℝ) : Prop :=
  ∃ L : ℕ → ℝ≥0∞, ∃ M : ℝ,
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      (n : ℝ≥0∞) * law μ p₀ {x | L n < extTail p₀ (pn n) x} ≤ ENNReal.ofReal ε) ∧
    ∃ N : ℕ, ∀ n ≥ N,
      ∫⁻ x, truncTail p₀ (pn n) (L n) x ∂(law μ p₀) ≤ ENNReal.ofReal (M * rate δ n ^ 2)

/-- The first-moment log tail: `P₀[log(p₀/p_n) 1{p₀/p_n > 4}] ≤ M a_n²` eventually, for some
finite `M` (`+∞` off absolute continuity), with `a_n = max(δ_n, n^{-1/2})`. The paper's
`δ_n²` scale implies this one. -/
def FirstMomentLogTail {𝒳 : Type*} [MeasurableSpace 𝒳] (μ : Measure 𝒳) (p₀ : 𝒳 → ℝ≥0)
    (pn : ℕ → 𝒳 → ℝ≥0) (δ : ℕ → ℝ) : Prop :=
  ∃ M : ℝ, ∃ N : ℕ, ∀ n ≥ N,
    tailLogMoment (law μ p₀) (law μ (pn n)) 4 1 ≤ ENNReal.ofReal (M * rate δ n ^ 2)

/-- The hypotheses of `MLEHypotheses` other than the squared log-tail bound (and its
constant `M`): i.i.d. observations with law `p₀ · μ`, a sieve of probability densities, a
deterministic `p_n ∈ S_n` with `h(p₀, p_n) ≤ D δ_n` eventually, an arbitrary estimator
`phat_n ∈ S_n`, and the likelihood comparison `ℙ_n log phat ≥ ℙ_n log p_n - O_P(δ_n²)`. -/
structure MLEBaseHypotheses {𝒳 : Type u} [MeasurableSpace 𝒳] (μ : Measure 𝒳)
    {Ω : Type v} [MeasurableSpace Ω] (Pr : Measure Ω) (X : ℕ → Ω → 𝒳) (p₀ : 𝒳 → ℝ≥0)
    (S : ℕ → Set (𝒳 → ℝ≥0)) (pn : ℕ → 𝒳 → ℝ≥0) (phat : ℕ → Ω → 𝒳 → ℝ≥0)
    (δ : ℕ → ℝ) (D : ℝ) : Prop where
  probability : IsProbabilityMeasure Pr
  density : IsProbDensity μ p₀
  measurable_obs : ∀ i, Measurable (X i)
  indep : iIndepFun X Pr
  law_obs : ∀ i, Pr.map (X i) = law μ p₀
  sieve_density : ∀ n, ∀ p ∈ S n, IsProbDensity μ p
  comparator_mem : ∀ n, pn n ∈ S n
  estimator_mem : ∀ n ω, phat n ω ∈ S n
  rate_nonneg : ∀ n, 0 ≤ δ n
  D_nonneg : 0 ≤ D
  /-- `h(p₀, p_n) ≤ D δ_n` eventually. -/
  approx : ∃ N, ∀ n ≥ N, hdist μ p₀ (pn n) ≤ ENNReal.ofReal (D * δ n)
  /-- `ℙ_n log phat_n ≥ ℙ_n log p_n - O_P(δ_n²)`, through the nonnegative deficit. -/
  likelihood : OPStar Pr (fun n ω ↦ logLikDeficit (sample X n ω) (pn n) (phat n ω))
    (fun n ↦ δ n ^ 2)

/-- **Corrected Theorem 8, weak-law form**: under (D), with the squared log-tail bound
replaced by the weak-law truncation condition (W). -/
def Theorem8WeakLawStatement : Prop :=
  ∀ {𝒳 : Type u} [MeasurableSpace 𝒳] (μ : Measure 𝒳)
    {Ω : Type v} [MeasurableSpace Ω] (Pr : Measure Ω) (X : ℕ → Ω → 𝒳) (p₀ : 𝒳 → ℝ≥0)
    (S : ℕ → Set (𝒳 → ℝ≥0)) (pn : ℕ → 𝒳 → ℝ≥0) (phat : ℕ → Ω → 𝒳 → ℝ≥0)
    (δ : ℕ → ℝ) (D : ℝ),
    MLEBaseHypotheses μ Pr X p₀ S pn phat δ D → WeakLawTruncation μ p₀ pn δ →
      AnnularTailCondition μ p₀ S δ → RateConclusion μ Pr p₀ phat δ

/-- The ordinary `O_P` version of the weak-law form when the Hellinger error is measurable. -/
def Theorem8WeakLawMeasurableStatement : Prop :=
  ∀ {𝒳 : Type u} [MeasurableSpace 𝒳] (μ : Measure 𝒳)
    {Ω : Type v} [MeasurableSpace Ω] (Pr : Measure Ω) (X : ℕ → Ω → 𝒳) (p₀ : 𝒳 → ℝ≥0)
    (S : ℕ → Set (𝒳 → ℝ≥0)) (pn : ℕ → 𝒳 → ℝ≥0) (phat : ℕ → Ω → 𝒳 → ℝ≥0)
    (δ : ℕ → ℝ) (D : ℝ),
    MLEBaseHypotheses μ Pr X p₀ S pn phat δ D → WeakLawTruncation μ p₀ pn δ →
    AnnularTailCondition μ p₀ S δ →
    (∀ n, Measurable fun ω ↦ hdist μ p₀ (phat n ω)) →
      ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, ∀ n ≥ N,
        MeasurableSet {ω | ENNReal.ofReal (K * rate δ n) < hdist μ p₀ (phat n ω)} ∧
        Pr {ω | ENNReal.ofReal (K * rate δ n) < hdist μ p₀ (phat n ω)} ≤ ENNReal.ofReal ε

/-- The weak-law form under the power envelope (H). -/
def Theorem8WeakLawPowerEnvelopeStatement : Prop :=
  ∀ {𝒳 : Type u} [MeasurableSpace 𝒳] (μ : Measure 𝒳)
    {Ω : Type v} [MeasurableSpace Ω] (Pr : Measure Ω) (X : ℕ → Ω → 𝒳) (p₀ : 𝒳 → ℝ≥0)
    (S : ℕ → Set (𝒳 → ℝ≥0)) (pn : ℕ → 𝒳 → ℝ≥0) (phat : ℕ → Ω → 𝒳 → ℝ≥0)
    (δ : ℕ → ℝ) (D : ℝ),
    MLEBaseHypotheses μ Pr X p₀ S pn phat δ D → WeakLawTruncation μ p₀ pn δ →
      PowerEnvelopeCondition μ p₀ S δ → RateConclusion μ Pr p₀ phat δ

/-- The weak-law form under the whole-sieve bound (G). -/
def Theorem8WeakLawWholeSieveStatement : Prop :=
  ∀ {𝒳 : Type u} [MeasurableSpace 𝒳] (μ : Measure 𝒳)
    {Ω : Type v} [MeasurableSpace Ω] (Pr : Measure Ω) (X : ℕ → Ω → 𝒳) (p₀ : 𝒳 → ℝ≥0)
    (S : ℕ → Set (𝒳 → ℝ≥0)) (pn : ℕ → 𝒳 → ℝ≥0) (phat : ℕ → Ω → 𝒳 → ℝ≥0)
    (δ : ℕ → ℝ) (D : ℝ),
    MLEBaseHypotheses μ Pr X p₀ S pn phat δ D → WeakLawTruncation μ p₀ pn δ →
      WholeSieveCondition μ S δ → RateConclusion μ Pr p₀ phat δ

/-- The first-moment log tail implies (W), with `L_n = ⊤`. -/
def FirstMomentImpliesWeakLawStatement : Prop :=
  ∀ {𝒳 : Type u} [MeasurableSpace 𝒳] (μ : Measure 𝒳) (p₀ : 𝒳 → ℝ≥0)
    (pn : ℕ → 𝒳 → ℝ≥0) (δ : ℕ → ℝ),
    IsProbDensity μ p₀ → (∀ n, IsProbDensity μ (pn n)) →
      FirstMomentLogTail μ p₀ pn δ → WeakLawTruncation μ p₀ pn δ

/-- Corrected Theorem 8 under (D), with the squared log-tail bound replaced by the
first-moment log tail. -/
def Theorem8FirstMomentStatement : Prop :=
  ∀ {𝒳 : Type u} [MeasurableSpace 𝒳] (μ : Measure 𝒳)
    {Ω : Type v} [MeasurableSpace Ω] (Pr : Measure Ω) (X : ℕ → Ω → 𝒳) (p₀ : 𝒳 → ℝ≥0)
    (S : ℕ → Set (𝒳 → ℝ≥0)) (pn : ℕ → 𝒳 → ℝ≥0) (phat : ℕ → Ω → 𝒳 → ℝ≥0)
    (δ : ℕ → ℝ) (D : ℝ),
    MLEBaseHypotheses μ Pr X p₀ S pn phat δ D → FirstMomentLogTail μ p₀ pn δ →
      AnnularTailCondition μ p₀ S δ → RateConclusion μ Pr p₀ phat δ

/-- The hypotheses of Theorem 8 of the paper give the base hypotheses and the first-moment log
tail (by the interpolation `A₁ ≤ 4 h A₂^{1/2}`). -/
def SquaredTailImpliesFirstMomentStatement : Prop :=
  ∀ {𝒳 : Type u} [MeasurableSpace 𝒳] (μ : Measure 𝒳)
    {Ω : Type v} [MeasurableSpace Ω] (Pr : Measure Ω) (X : ℕ → Ω → 𝒳) (p₀ : 𝒳 → ℝ≥0)
    (S : ℕ → Set (𝒳 → ℝ≥0)) (pn : ℕ → 𝒳 → ℝ≥0) (phat : ℕ → Ω → 𝒳 → ℝ≥0)
    (δ : ℕ → ℝ) (D M : ℝ),
    MLEHypotheses μ Pr X p₀ S pn phat δ D M →
      MLEBaseHypotheses μ Pr X p₀ S pn phat δ D ∧ FirstMomentLogTail μ p₀ pn δ

end Hellinger.MLE
