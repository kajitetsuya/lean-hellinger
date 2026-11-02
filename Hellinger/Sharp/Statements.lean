/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.Constants
public import Hellinger.Definitions
public import Hellinger.Comparison.Definitions

/-!
Sharpened constants: the coefficients that the paper's proofs yield before rounding, and the
bounds they give. The paper's statements keep their rounded coefficients;
`SharpCoeffsImproveStatement` shows that each sharpened coefficient is at least as good, so
every bound here implies the corresponding bound of the paper.

The Kullback–Leibler divergence upper and lower-tail, Bernstein "norm" lower and
Kullback–Leibler variation coefficients are the best pointwise constants of their kernel
inequalities on the relevant range. The others are improved but not claimed sharp: `(e δ)⁻¹`
is pointwise best only when `δ log c ≤ 1`, and the `δ²` Bernstein "norm" upper, the
interpolation and the CM coefficients are improvements. The arguments are summarized in
`docs/SharpConstants.md`. "Sharp" in a declaration name marks this module, not a sharpness
claim. With `J(c) = (1 - c^{-1/2})^{-2}` (`tailMassCoeff`):

- Kullback–Leibler divergence upper: `K(c) = J(c) (log c - 1 + 1/c)`, which is
  `4 log 4 - 3 ≈ 2.545` at `c = 4` (paper: `1 + √c`);
- Kullback–Leibler divergence tail factor: `(e δ)⁻¹` (paper: `δ⁻¹`);
- Kullback–Leibler divergence lower tail: `1 - (1 - 1/c)/log c`, about `0.459` at `c = 4`
  (paper: `min(1/3, (1-1/c)/2)`);
- Bernstein "norm" lower: `2(1 - c^{-δ}(1 + δ log c))`, for every `δ > 0`
  (paper: `(1 - c^{-δ})²`, for `δ ≤ 1`);
- Bernstein "norm" upper: `2 δ² (1 + √c)²` for `δ ≤ 1` (paper: `2 δ (1 + √c)²`);
- Kullback–Leibler variation upper: `max(J(c) (log c)^k, B_k)` with `B_k` the supremum of the
  kernel ratio on `(0, 1)`; at `k = 2` it is `J(c) (log c)²`, which is `16 (log 2)² ≈ 7.69`
  at `c = 4`;
- interpolation: `J(c)^{1 - k/k'}` (paper: `J(c)`);
- CM ⇒ NC: `4 M²` at every cutoff `q ≥ 9/4` (paper: `(2M + 1)²` at `q = 4`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Hellinger.Sharp

universe u

/-! ### Sharpened coefficients -/

/-- `K(c) = J(c) (log c - 1 + 1/c)`, the sharp Kullback–Leibler divergence upper coefficient. -/
noncomputable def klSharpCoeff (c : ℝ) : ℝ := tailMassCoeff c * (Real.log c - 1 + 1 / c)

/-- `1 - (1 - 1/c)/log c`, the sharp coefficient of the Kullback–Leibler divergence lower tail
bound. -/
noncomputable def klTailLowerSharpCoeff (c : ℝ) : ℝ := 1 - (1 - 1 / c) / Real.log c

/-- `2 (1 - c^{-δ} (1 + δ log c))`, the sharp Bernstein lower coefficient. -/
noncomputable def bernsteinLowerSharpCoeff (c δ : ℝ) : ℝ :=
  2 * (1 - c ^ (-δ) * (1 + δ * Real.log c))

/-- `2 δ² (1 + √c)²`, the Bernstein upper coefficient with the exponent `δ²`. -/
noncomputable def bernsteinUpperSqCoeff (c δ : ℝ) : ℝ := 2 * δ ^ 2 * (1 + Real.sqrt c) ^ 2

/-- `B_k = sup_{0 < r < 1} r |log r|^k / (√r - 1)²`. It is finite for `k ≥ 2`. -/
noncomputable def variationLowerSup (k : ℝ) : ℝ :=
  ⨆ r : Set.Ioo (0 : ℝ) 1, (r : ℝ) * |Real.log r| ^ k / (Real.sqrt r - 1) ^ 2

/-- `max(J(c) (log c)^k, B_k)`, the sharp Kullback–Leibler variation upper coefficient. -/
noncomputable def variationSharpCoeff (c k : ℝ) : ℝ :=
  max (tailMassCoeff c * Real.log c ^ k) (variationLowerSup k)

/-- `J(c)^{1 - k/k'}`, the improved interpolation coefficient. -/
noncomputable def interpolationSharpCoeff (c k k' : ℝ) : ℝ := tailMassCoeff c ^ (1 - k / k')

/-! ### Measure-level bounds -/

/-- Kullback–Leibler divergence upper bound with the sharp coefficient. -/
def KLUpperSharpStatement : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (c : ℝ), 1 < c →
      kl μ ν ≤ ENNReal.ofReal (klSharpCoeff c) * hellingerSq μ ν + tailLogMoment μ ν c 1

/-- The log tail is bounded by the power tail with factor `(e δ)⁻¹`. -/
def TailLogPowerSharpStatement : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ ν : Measure α) (c δ : ℝ), 0 < δ →
    tailLogMoment μ ν c 1 ≤ ENNReal.ofReal (Real.exp 1 * δ)⁻¹ * tailPower μ ν c δ

/-- Theorem 1's Kullback–Leibler divergence upper bound with `K(c)` and `(e δ)⁻¹`. -/
def KLUpperPowerSharpStatement : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (c δ : ℝ), 1 < c → 0 < δ →
      kl μ ν ≤ ENNReal.ofReal (klSharpCoeff c) * hellingerSq μ ν +
        ENNReal.ofReal (Real.exp 1 * δ)⁻¹ * tailPower μ ν c δ

/-- Kullback–Leibler divergence lower tail bound with the sharp coefficient. -/
def KLLowerTailSharpStatement : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (c : ℝ), 1 < c →
      ENNReal.ofReal (klTailLowerSharpCoeff c) * tailLogMoment μ ν c 1 ≤ kl μ ν

/-- Bernstein lower bound with the sharp coefficient, for every `δ > 0`. -/
def BernsteinLowerSharpStatement : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (c δ : ℝ), 1 < c → 0 < δ →
      ENNReal.ofReal (bernsteinLowerSharpCoeff c δ) * tailPower μ ν c δ ≤ bernsteinSq μ ν δ

/-- Bernstein upper bound with the coefficient `2 δ² (1 + √c)²`. -/
def BernsteinUpperSqStatement : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (c δ : ℝ), 1 < c → 0 < δ → δ ≤ 1 →
      bernsteinSq μ ν δ ≤ ENNReal.ofReal (bernsteinUpperSqCoeff c δ) * hellingerSq μ ν +
        2 * tailPower μ ν c δ

/-- Kullback–Leibler variation upper bound with the sharp coefficient, for every real `k ≥ 2`. -/
def VariationUpperSharpStatement : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (c k : ℝ), 1 < c → 2 ≤ k →
      logMoment μ ν k ≤ ENNReal.ofReal (variationSharpCoeff c k) * hellingerSq μ ν +
        tailLogMoment μ ν c k

/-- Log-tail interpolation with the improved coefficient, for `0 < k ≤ k'`. -/
def InterpolationSharpStatement : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (c k k' : ℝ), 1 < c → 0 < k → k ≤ k' →
      tailLogMoment μ ν c k ≤ ENNReal.ofReal (interpolationSharpCoeff c k k') *
        hellingerSq μ ν ^ (1 - k / k') * tailLogMoment μ ν c k' ^ (k / k')

/-- Power-tail interpolation with the improved coefficient, for `0 < δ ≤ δ'`. -/
def PowerInterpolationSharpStatement : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (c δ δ' : ℝ), 1 < c → 0 < δ → δ ≤ δ' →
      tailPower μ ν c δ ≤ ENNReal.ofReal (interpolationSharpCoeff c δ δ') *
        hellingerSq μ ν ^ (1 - δ / δ') * tailPower μ ν c δ' ^ (δ / δ')

/-- CM ⇒ NC with the coefficient `4 M²`, at every cutoff `q ≥ 9/4`. -/
def CMSharpStatement : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (q M : ℝ), 9 / 4 ≤ q → 0 ≤ M →
      Comparison.conditionalMoment μ ν ≤ ENNReal.ofReal M →
        tailPower μ ν q 1 ≤ ENNReal.ofReal (4 * M ^ 2) * hellingerSq μ ν

/-! ### The sharpened coefficients improve the paper's -/

/-- Every sharpened coefficient is at least as good as the paper's, so each bound here implies
the corresponding bound of the paper. -/
def SharpCoeffsImproveStatement : Prop :=
  ∀ c : ℝ, 1 < c →
    klSharpCoeff c ≤ klUpperCoeff c ∧
    klTailLowerCoeff c ≤ klTailLowerSharpCoeff c ∧
    (∀ δ : ℝ, 0 < δ → bernsteinLowerCoeff c δ ≤ bernsteinLowerSharpCoeff c δ) ∧
    (∀ δ : ℝ, 0 < δ → δ ≤ 1 → bernsteinUpperSqCoeff c δ ≤ bernsteinUpperCoeff c δ) ∧
    (∀ k : ℝ, 2 ≤ k → variationSharpCoeff c k ≤ variationUpperCoeff c k) ∧
    (∀ k k' : ℝ, 0 < k → k ≤ k' → interpolationSharpCoeff c k k' ≤ interpolationCoeff c) ∧
    (∀ δ : ℝ, 0 < δ → (Real.exp 1 * δ)⁻¹ ≤ δ⁻¹) ∧
    (∀ M : ℝ, 0 ≤ M → 4 * M ^ 2 ≤ (2 * M + 1) ^ 2)

/-- Closed forms: the values at the paper's cutoff `c = 4`, and the Kullback–Leibler variation
coefficient at `k = 2`. -/
def SharpCoeffValuesStatement : Prop :=
  klSharpCoeff 4 = 4 * Real.log 4 - 3 ∧
  klTailLowerSharpCoeff 4 = 1 - 3 / (4 * Real.log 4) ∧
  bernsteinLowerSharpCoeff 4 1 = (3 - Real.log 4) / 2 ∧
  bernsteinUpperSqCoeff 4 1 = 18 ∧
  (∀ c : ℝ, 1 < c → variationSharpCoeff c 2 = tailMassCoeff c * Real.log c ^ (2 : ℝ)) ∧
  variationSharpCoeff 4 2 = 16 * Real.log 2 ^ 2 ∧
  (∀ k k' : ℝ, interpolationSharpCoeff 4 k k' = 4 ^ (1 - k / k'))

end Hellinger.Sharp
