/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.Sharp.KL
public import Hellinger.Sharp.Bernstein
public import Hellinger.Sharp.Variation

/-!
Coefficient comparisons for the sharpened constants: every sharpened coefficient is at least
as good as the paper's, with closed forms at the paper's cutoff `c = 4` and at `k = 2`. The
`*_of_sharp` corollaries derive the exact statement of each bound of the paper from its
sharpened version, so the paper's bounds are recovered as corollaries.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Hellinger.Sharp

/-- Each sharpened coefficient is no worse than the paper's. -/
theorem sharpCoeffs_improve : SharpCoeffsImproveStatement := by
  intro c hc
  refine ⟨klSharpCoeff_le_klUpperCoeff hc, klTailLowerCoeff_le_klTailLowerSharpCoeff hc,
    fun δ hδ ↦ bernsteinLowerCoeff_le_bernsteinLowerSharpCoeff hc hδ,
    fun δ hδ hδ1 ↦ bernsteinUpperSqCoeff_le_bernsteinUpperCoeff hδ hδ1,
    fun k hk ↦ variationSharpCoeff_le_variationUpperCoeff hc hk,
    fun k k' hk hkk' ↦ interpolationSharpCoeff_le_interpolationCoeff hc hk hkk',
    fun δ hδ ↦ ?_, fun M hM ↦ four_mul_sq_le_two_mul_add_one_sq hM⟩
  have he : 1 ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  rw [inv_le_inv₀ (by positivity) hδ]
  nlinarith

/-- The closed forms at `c = 4` and at `k = 2`. -/
theorem sharpCoeff_values : SharpCoeffValuesStatement :=
  ⟨klSharpCoeff_four, klTailLowerSharpCoeff_four, bernsteinLowerSharpCoeff_four_one,
    bernsteinUpperSqCoeff_four_one, fun _ hc ↦ variationSharpCoeff_two hc,
    variationSharpCoeff_four_two, interpolationSharpCoeff_four⟩

/-! ### The paper's bounds, recovered from the sharpened ones -/

section Recovered

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α}

theorem tailLogMoment_one_le_inv_mul_tailPower_of_sharp (c : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    tailLogMoment μ ν c 1 ≤ ENNReal.ofReal δ⁻¹ * tailPower μ ν c δ := by
  have he : 1 ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  refine (tailLogMoment_one_le_tailPower_sharp μ ν c δ hδ).trans ?_
  gcongr
  nlinarith

variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]

theorem kl_le_hellinger_add_tailLogMoment_of_sharp {c : ℝ} (hc : 1 < c) :
    kl μ ν ≤ ENNReal.ofReal (klUpperCoeff c) * hellingerSq μ ν + tailLogMoment μ ν c 1 := by
  refine (kl_le_hellinger_add_tailLogMoment_sharp μ ν c hc).trans ?_
  gcongr
  exact (sharpCoeffs_improve c hc).1

theorem kl_le_hellinger_add_tailPower_of_sharp {c δ : ℝ} (hc : 1 < c) (hδ : 0 < δ) :
    kl μ ν ≤ ENNReal.ofReal (klUpperCoeff c) * hellingerSq μ ν +
      ENNReal.ofReal δ⁻¹ * tailPower μ ν c δ :=
  (kl_le_hellinger_add_tailLogMoment_of_sharp hc).trans
    (add_le_add_right (tailLogMoment_one_le_inv_mul_tailPower_of_sharp c hδ) _)

theorem klTailLowerCoeff_mul_tailLogMoment_le_kl_of_sharp {c : ℝ} (hc : 1 < c) :
    ENNReal.ofReal (klTailLowerCoeff c) * tailLogMoment μ ν c 1 ≤ kl μ ν := by
  refine le_trans ?_ (klTailLowerSharpCoeff_mul_tailLogMoment_le_kl μ ν c hc)
  gcongr
  exact (sharpCoeffs_improve c hc).2.1

theorem bernsteinLowerCoeff_mul_tailPower_le_bernsteinSq_of_sharp {c δ : ℝ}
    (hc : 1 < c) (hδ : 0 < δ) (_hδ1 : δ ≤ 1) :
    ENNReal.ofReal (bernsteinLowerCoeff c δ) * tailPower μ ν c δ ≤ bernsteinSq μ ν δ := by
  refine le_trans ?_ (bernsteinLowerSharpCoeff_mul_tailPower_le_bernsteinSq μ ν c δ hc hδ)
  gcongr
  exact (sharpCoeffs_improve c hc).2.2.1 δ hδ

theorem bernsteinSq_le_hellinger_add_tailPower_of_sharp {c δ : ℝ}
    (hc : 1 < c) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    bernsteinSq μ ν δ ≤ ENNReal.ofReal (bernsteinUpperCoeff c δ) * hellingerSq μ ν +
      2 * tailPower μ ν c δ := by
  refine (bernsteinSq_le_hellinger_add_tailPower_sq μ ν c δ hc hδ hδ1).trans ?_
  gcongr
  exact (sharpCoeffs_improve c hc).2.2.2.1 δ hδ hδ1

theorem logMoment_le_hellinger_add_tailLogMoment_of_sharp {c k : ℝ} (hc : 1 < c)
    (hk : 2 ≤ k) :
    logMoment μ ν k ≤ ENNReal.ofReal (variationUpperCoeff c k) * hellingerSq μ ν +
      tailLogMoment μ ν c k := by
  refine (logMoment_le_hellinger_add_tailLogMoment_sharp μ ν c k hc hk).trans ?_
  gcongr
  exact (sharpCoeffs_improve c hc).2.2.2.2.1 k hk

end Recovered

section RecoveredProbability

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

theorem tailLogMoment_interpolation_of_sharp {c k k' : ℝ} (hc : 1 < c) (hk : 0 < k)
    (hkk' : k ≤ k') :
    tailLogMoment μ ν c k ≤ ENNReal.ofReal (interpolationCoeff c) *
      hellingerSq μ ν ^ (1 - k / k') * tailLogMoment μ ν c k' ^ (k / k') := by
  refine (tailLogMoment_interpolation_sharp μ ν c k k' hc hk hkk').trans ?_
  gcongr
  exact (sharpCoeffs_improve c hc).2.2.2.2.2.1 k k' hk hkk'

theorem tailPower_interpolation_of_sharp {c δ δ' : ℝ} (hc : 1 < c) (hδ : 0 < δ)
    (hδδ' : δ ≤ δ') :
    tailPower μ ν c δ ≤ ENNReal.ofReal (interpolationCoeff c) *
      hellingerSq μ ν ^ (1 - δ / δ') * tailPower μ ν c δ' ^ (δ / δ') := by
  refine (tailPower_interpolation_sharp μ ν c δ δ' hc hδ hδδ').trans ?_
  gcongr
  exact (sharpCoeffs_improve c hc).2.2.2.2.2.1 δ δ' hδ hδδ'

theorem tailPower_four_le_of_conditionalMoment_le_of_sharp {M : ℝ} (hM : 0 ≤ M)
    (hCM : Comparison.conditionalMoment μ ν ≤ ENNReal.ofReal M) :
    tailPower μ ν 4 1 ≤ ENNReal.ofReal ((2 * M + 1) ^ 2) * hellingerSq μ ν := by
  refine (tailPower_le_of_conditionalMoment_le_sharp μ ν 4 M (by norm_num) hM hCM).trans ?_
  gcongr
  exact four_mul_sq_le_two_mul_add_one_sq hM

end RecoveredProbability

end Hellinger.Sharp
