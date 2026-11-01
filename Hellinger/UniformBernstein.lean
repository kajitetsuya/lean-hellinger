/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.Uniform
public import Hellinger.BernsteinBounds

/-! Uniform Bernstein control is equivalent to uniform control of a fixed power tail. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace Hellinger

variable {α : Type*} [MeasurableSpace α]

theorem uniform_bernsteinSq_iff_tailPower (μ : Measure α) [IsProbabilityMeasure μ]
    (F : Set (Measure α)) (hF : ∀ ν ∈ F, IsProbabilityMeasure ν)
    {c δ : ℝ} (hc : 1 < c) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    UniformHellingerBound μ F (fun ν ↦ bernsteinSq μ ν δ) ↔
      UniformHellingerBound μ F (fun ν ↦ tailPower μ ν c δ) := by
  let a : ℝ≥0 := Real.toNNReal (bernsteinLowerCoeff c δ)
  let b : ℝ≥0 := Real.toNNReal (bernsteinUpperCoeff c δ)
  constructor
  · intro hB
    apply hB.of_mul_le ((Real.toNNReal_pos.mpr (bernsteinLowerCoeff_pos hc hδ)).ne' : a ≠ 0)
    intro ν hν
    let : IsProbabilityMeasure ν := hF ν hν
    simpa only [a, ENNReal.ofReal] using
      (bernsteinLowerCoeff_mul_tailPower_le_bernsteinSq (μ := μ) (ν := ν) hc hδ hδ1)
  · rintro ⟨M, hM⟩
    refine ⟨b + 2 * M, ?_⟩
    intro ν hν
    let : IsProbabilityMeasure ν := hF ν hν
    calc
      bernsteinSq μ ν δ ≤ ENNReal.ofReal (bernsteinUpperCoeff c δ) * hellingerSq μ ν +
          2 * tailPower μ ν c δ := bernsteinSq_le_hellinger_add_tailPower hc hδ hδ1
      _ ≤ ENNReal.ofReal (bernsteinUpperCoeff c δ) * hellingerSq μ ν +
          2 * ((M : ℝ≥0∞) * hellingerSq μ ν) :=
        add_le_add_right (mul_le_mul_right (hM ν hν) 2) _
      _ = _ := by
        simp only [ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_ofNat, b, ENNReal.ofReal]
        rw [add_mul, mul_assoc]

end Hellinger
