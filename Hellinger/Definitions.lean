/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith

/-!
Measure-level discrepancies for the Hellinger bounds. The intended measures are probability
measures on an arbitrary measurable space. All nonnegative integrals have extended values.
Density-representation identities and discrepancy bounds are established in the subsequent modules.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Hellinger

variable {α : Type*} {mα : MeasurableSpace α}

/-- A canonical dominator chosen separately for each pair of measures. -/
noncomputable def pairMeasure (μ ν : Measure α) : Measure α := μ + ν

/-- The real Radon--Nikodym density with respect to the pairwise dominator.
For probability measures this is a finite density almost everywhere. -/
noncomputable def pairDensity (μ ν : Measure α) : α → ℝ :=
  fun x ↦ (μ.rnDeriv (pairMeasure μ ν) x).toReal

/-- Squared Hellinger distance, without a factor `1/2`.
The second density uses the same dominator `μ + ν`, including mass outside `μ`'s support. -/
noncomputable def hellingerSq (μ ν : Measure α) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal
    ((Real.sqrt (pairDensity μ ν x) -
      Real.sqrt ((ν.rnDeriv (pairMeasure μ ν) x).toReal)) ^ 2) ∂(pairMeasure μ ν)

/-- The Kullback–Leibler divergence is exactly mathlib's extended nonnegative divergence. -/
noncomputable def kl (μ ν : Measure α) : ℝ≥0∞ := InformationTheory.klDiv μ ν

/-- Finiteness of the Kullback–Leibler divergence, the domain used only for the centered
Kullback–Leibler variation clause. -/
def FiniteKL (μ ν : Measure α) : Prop := kl μ ν < ∞

/-- The strictly truncated event. For `c > 1` its log-likelihood ratio is positive.
This event is used only in the absolutely-continuous branch of the tail quantities. -/
noncomputable def tailEvent (μ ν : Measure α) (c : ℝ) : Set α :=
  {x | Real.log c < llr μ ν x}

theorem measurableSet_tailEvent (μ ν : Measure α) (c : ℝ) :
    MeasurableSet (tailEvent μ ν c) :=
  measurableSet_lt measurable_const (measurable_llr μ ν)

/-- The nonnegative Bernstein kernel, including its factor `2`. -/
noncomputable def bernsteinKernel (δ l : ℝ) : ℝ :=
  2 * (Real.exp (|δ * l|) - 1 - |δ * l|)

theorem bernsteinKernel_nonneg (δ l : ℝ) : 0 ≤ bernsteinKernel δ l := by
  have h := Real.add_one_le_exp (|δ * l|)
  dsimp [bernsteinKernel]
  linarith

/-- The `k`th order Kullback–Leibler variation `E_μ|log(dμ/dν)|^k`. For the specified
positive-exponent domain, failure of absolute continuity contributes infinity rather than a
totalized logarithm. -/
noncomputable def logMoment (μ ν : Measure α) (k : ℝ) : ℝ≥0∞ := by
  classical
  exact if μ ≪ ν then ∫⁻ x, ENNReal.ofReal (|llr μ ν x| ^ k) ∂μ else ∞

/-- The squared Bernstein "norm" of `δ` times the log-likelihood ratio. Its specified
parameter domain is `0 < δ ≤ 1`; the infinite branch records positive `μ` mass where the
likelihood denominator vanishes. -/
noncomputable def bernsteinSq (μ ν : Measure α) (δ : ℝ) : ℝ≥0∞ := by
  classical
  exact if μ ≪ ν then
    ∫⁻ x, ENNReal.ofReal (bernsteinKernel δ (llr μ ν x)) ∂μ
  else ∞

/-- The power tail `E_μ[(dμ/dν)^δ; dμ/dν > c]` on the specified domain `c > 1`, `δ > 0`.
The exponential form is the positive likelihood-ratio power in the ac branch.
The power is formed only inside the truncated event. -/
noncomputable def tailPower (μ ν : Measure α) (c δ : ℝ) : ℝ≥0∞ := by
  classical
  exact if μ ≪ ν then
    ∫⁻ x in tailEvent μ ν c, ENNReal.ofReal (Real.exp (δ * llr μ ν x)) ∂μ
  else ∞

/-- The log tail `E_μ[L^k; dμ/dν > c]` on the specified domain `c > 1`, `k > 0`.
The real power is evaluated under the restricted measure, where its base is positive. -/
noncomputable def tailLogMoment (μ ν : Measure α) (c k : ℝ) : ℝ≥0∞ := by
  classical
  exact if μ ≪ ν then
    ∫⁻ x in tailEvent μ ν c, ENNReal.ofReal ((llr μ ν x) ^ k) ∂μ
  else ∞

/-- The `k`th order centered Kullback–Leibler variation on probability measures. An explicit proof
of finite Kullback–Leibler divergence is required, so converting the divergence to a real number
cannot erase an infinite mean. Finite Kullback–Leibler divergence makes the log-likelihood ratio
integrable and its mean finite. -/
noncomputable def centeredLogMoment (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (k : ℝ)
    (_hKL : FiniteKL μ ν) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (|llr μ ν x - (kl μ ν).toReal| ^ k) ∂μ

theorem finiteKL_iff (μ ν : Measure α) :
    FiniteKL μ ν ↔ μ ≪ ν ∧ Integrable (llr μ ν) μ := by
  simpa only [FiniteKL, kl, lt_top_iff_ne_top] using
    (InformationTheory.klDiv_ne_top_iff (μ := μ) (ν := ν))

theorem finiteKL_ac {μ ν : Measure α} (hKL : FiniteKL μ ν) : μ ≪ ν :=
  ((finiteKL_iff μ ν).mp hKL).1

theorem finiteKL_integrable_llr {μ ν : Measure α} (hKL : FiniteKL μ ν) :
    Integrable (llr μ ν) μ :=
  ((finiteKL_iff μ ν).mp hKL).2

theorem llr_pos_of_mem_tailEvent {μ ν : Measure α} {c : ℝ} (hc : 1 < c)
    {x : α} (hx : x ∈ tailEvent μ ν c) : 0 < llr μ ν x :=
  (Real.log_pos hc).trans hx

theorem logMoment_of_ac {μ ν : Measure α} (h : μ ≪ ν) (k : ℝ) :
    logMoment μ ν k = ∫⁻ x, ENNReal.ofReal (|llr μ ν x| ^ k) ∂μ := by
  simp [logMoment, h]

theorem bernsteinSq_of_ac {μ ν : Measure α} (h : μ ≪ ν) (δ : ℝ) :
    bernsteinSq μ ν δ = ∫⁻ x, ENNReal.ofReal (bernsteinKernel δ (llr μ ν x)) ∂μ := by
  simp [bernsteinSq, h]

theorem tailPower_of_ac {μ ν : Measure α} (h : μ ≪ ν) (c δ : ℝ) :
    tailPower μ ν c δ =
      ∫⁻ x in tailEvent μ ν c, ENNReal.ofReal (Real.exp (δ * llr μ ν x)) ∂μ := by
  simp [tailPower, h]

theorem tailLogMoment_of_ac {μ ν : Measure α} (h : μ ≪ ν) (c k : ℝ) :
    tailLogMoment μ ν c k =
      ∫⁻ x in tailEvent μ ν c, ENNReal.ofReal ((llr μ ν x) ^ k) ∂μ := by
  simp [tailLogMoment, h]

@[simp] theorem logMoment_of_not_ac {μ ν : Measure α} (h : ¬ μ ≪ ν) (k : ℝ) :
    logMoment μ ν k = ∞ := by simp [logMoment, h]

@[simp] theorem bernsteinSq_of_not_ac {μ ν : Measure α} (h : ¬ μ ≪ ν) (δ : ℝ) :
    bernsteinSq μ ν δ = ∞ := by simp [bernsteinSq, h]

@[simp] theorem tailPower_of_not_ac {μ ν : Measure α} (h : ¬ μ ≪ ν) (c δ : ℝ) :
    tailPower μ ν c δ = ∞ := by simp [tailPower, h]

@[simp] theorem tailLogMoment_of_not_ac {μ ν : Measure α} (h : ¬ μ ≪ ν) (c k : ℝ) :
    tailLogMoment μ ν c k = ∞ := by simp [tailLogMoment, h]

end Hellinger
