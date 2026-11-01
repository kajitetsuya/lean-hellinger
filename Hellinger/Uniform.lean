/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.Definitions
import Mathlib.Tactic.NormNum

/-! Uniform finite Hellinger multipliers, with the constant quantified before the family. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace Hellinger

variable {α : Type*} [MeasurableSpace α]

/-- One finite nonnegative multiplier works for every member of the given family. -/
def UniformHellingerBound (μ : Measure α) (F : Set (Measure α))
    (d : Measure α → ℝ≥0∞) : Prop :=
  ∃ C : ℝ≥0, ∀ ν ∈ F, d ν ≤ (C : ℝ≥0∞) * hellingerSq μ ν

theorem uniformHellingerBound_iff_real (μ : Measure α) (F : Set (Measure α))
    (d : Measure α → ℝ≥0∞) :
    UniformHellingerBound μ F d ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ν ∈ F, d ν ≤ ENNReal.ofReal C * hellingerSq μ ν := by
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, C.property, by simpa using hC⟩
  · rintro ⟨C, hC, h⟩
    refine ⟨Real.toNNReal C, ?_⟩
    exact h

theorem UniformHellingerBound.mono {μ : Measure α} {F : Set (Measure α)}
    {f g : Measure α → ℝ≥0∞} (hf : UniformHellingerBound μ F f)
    (hgf : ∀ ν ∈ F, g ν ≤ f ν) : UniformHellingerBound μ F g := by
  obtain ⟨C, hC⟩ := hf
  exact ⟨C, fun ν hν ↦ (hgf ν hν).trans (hC ν hν)⟩

theorem UniformHellingerBound.of_mul_le {μ : Measure α} {F : Set (Measure α)}
    {f g : Measure α → ℝ≥0∞} {a : ℝ≥0} (hg : UniformHellingerBound μ F g)
    (ha : a ≠ 0) (hfg : ∀ ν ∈ F, (a : ℝ≥0∞) * f ν ≤ g ν) :
    UniformHellingerBound μ F f := by
  obtain ⟨C, hC⟩ := hg
  refine ⟨a⁻¹ * C, ?_⟩
  intro ν hν
  have ha0 : (a : ℝ≥0∞) ≠ 0 := by exact_mod_cast ha
  have h := mul_le_mul_right ((hfg ν hν).trans (hC ν hν)) (a : ℝ≥0∞)⁻¹
  rw [← mul_assoc, ENNReal.inv_mul_cancel ha0 ENNReal.coe_ne_top, one_mul] at h
  simpa only [ENNReal.coe_mul, ENNReal.coe_inv ha, mul_assoc] using h

/-- The two explicit comparison bounds imply equality of uniform-control conditions. -/
theorem uniformHellingerBound_iff_of_comparisons (μ : Measure α) (F : Set (Measure α))
    (f g : Measure α → ℝ≥0∞) (a b : ℝ≥0) (ha : a ≠ 0)
    (hlower : ∀ ν ∈ F, (a : ℝ≥0∞) * f ν ≤ g ν)
    (hupper : ∀ ν ∈ F, g ν ≤ (b : ℝ≥0∞) * hellingerSq μ ν + f ν) :
    UniformHellingerBound μ F g ↔ UniformHellingerBound μ F f := by
  constructor
  · intro hg
    exact hg.of_mul_le ha hlower
  · rintro ⟨M, hM⟩
    refine ⟨b + M, ?_⟩
    intro ν hν
    calc
      g ν ≤ (b : ℝ≥0∞) * hellingerSq μ ν + f ν := hupper ν hν
      _ ≤ (b : ℝ≥0∞) * hellingerSq μ ν + (M : ℝ≥0∞) * hellingerSq μ ν :=
        add_le_add_right (hM ν hν) _
      _ = ((b + M : ℝ≥0) : ℝ≥0∞) * hellingerSq μ ν := by
        rw [ENNReal.coe_add, add_mul]

end Hellinger
