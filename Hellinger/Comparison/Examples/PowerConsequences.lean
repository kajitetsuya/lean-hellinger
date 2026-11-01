/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.Comparison.Examples.Power
public import Hellinger.UniformBernstein

/-! The power example as a genuine uniform-family counterexample to FM necessity. -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Hellinger.Comparison.Examples.Power

theorem uniform_half_tail_singleton {q : ℝ} (hq : 1 < q) :
    UniformHellingerBound uniformLaw {linearLaw}
      (fun ν ↦ tailPower uniformLaw ν q (1 / 2)) := by
  obtain ⟨M, hM⟩ := exists_half_tail_multiplier hq
  refine ⟨M, ?_⟩
  intro ν hν
  have heq : ν = linearLaw := Set.mem_singleton_iff.mp hν
  subst ν
  exact hM

theorem uniform_half_bernstein_singleton {q : ℝ} (hq : 1 < q) :
    UniformHellingerBound uniformLaw {linearLaw}
      (fun ν ↦ bernsteinSq uniformLaw ν (1 / 2)) := by
  have hF : ∀ ν ∈ ({linearLaw} : Set (Measure ℝ)), IsProbabilityMeasure ν := by
    intro ν hν
    have heq : ν = linearLaw := Set.mem_singleton_iff.mp hν
    subst ν
    infer_instance
  exact (uniform_bernsteinSq_iff_tailPower uniformLaw {linearLaw} hF hq
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)).mpr
      (uniform_half_tail_singleton hq)

/-- One fixed family has uniform fractional NC and Bernstein bounds while even
memberwise finite full moments fail. -/
theorem fractional_nc_without_full_moment {q : ℝ} (hq : 1 < q) :
    UniformHellingerBound uniformLaw {linearLaw}
      (fun ν ↦ tailPower uniformLaw ν q (1 / 2)) ∧
    UniformHellingerBound uniformLaw {linearLaw}
      (fun ν ↦ bernsteinSq uniformLaw ν (1 / 2)) ∧
    ¬ (∀ ν ∈ ({linearLaw} : Set (Measure ℝ)), fullRatioMoment uniformLaw ν < ∞) := by
  refine ⟨uniform_half_tail_singleton hq, uniform_half_bernstein_singleton hq, ?_⟩
  intro hFM
  have hfin := hFM linearLaw (by simp)
  rw [fullRatioMoment_eq_top] at hfin
  exact lt_irrefl _ hfin

end Hellinger.Comparison.Examples.Power
