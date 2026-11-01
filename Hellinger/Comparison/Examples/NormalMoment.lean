/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.Comparison.Examples.Normal
public import Hellinger.Comparison.FiniteMoment

/-! Finite full moments for each actual normal pair. This supplies a singleton
UB/CM strictness witness. NormalControl proves uniform CM on bounded parameter sets. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Hellinger.Comparison.Examples.NormalMoment

open Normal

theorem integrable_exp_llr_normal (theta : ℝ) :
    Integrable (fun x ↦ Real.exp (llr (normalLaw 0) (normalLaw theta) x)) (normalLaw 0) := by
  have hi : Integrable (fun x : ℝ ↦ Real.exp (-theta * x)) (normalLaw 0) := by
    simpa only [normalLaw] using
      (integrable_exp_mul_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (-theta))
  have hs : Integrable (fun x : ℝ ↦ Real.exp (-theta * x + theta ^ 2 / 2))
      (normalLaw 0) := by
    simpa only [Real.exp_add] using hi.mul_const (Real.exp (theta ^ 2 / 2))
  apply hs.congr
  filter_upwards [llr_normalLaw_ae theta] with x hx
  exact congrArg Real.exp hx.symm

theorem fullRatioMoment_normal_lt_top (theta : ℝ) :
    fullRatioMoment (normalLaw 0) (normalLaw theta) < ∞ := by
  rw [fullRatioMoment_of_ac (normalLaw_absolutelyContinuous 0 theta)]
  have hi := integrable_exp_llr_normal theta
  exact lt_top_iff_ne_top.mpr
    ((lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x ↦ (Real.exp_pos _).le))).mpr hi)

theorem conditionalMoment_normal_lt_top (theta : ℝ) :
    conditionalMoment (normalLaw 0) (normalLaw theta) < ∞ :=
  conditionalMoment_lt_top_of_fullRatioMoment_lt_top (fullRatioMoment_normal_lt_top theta)

theorem uniform_conditionalMoment_singleton (theta : ℝ) :
    ∃ M : ℝ≥0, ∀ ν ∈ ({normalLaw theta} : Set (Measure ℝ)),
      conditionalMoment (normalLaw 0) ν ≤ (M : ℝ≥0∞) := by
  have hf := conditionalMoment_normal_lt_top theta
  refine ⟨(conditionalMoment (normalLaw 0) (normalLaw theta)).toNNReal, ?_⟩
  intro ν hν
  have heq : ν = normalLaw theta := Set.mem_singleton_iff.mp hν
  subst ν
  rw [ENNReal.coe_toNNReal hf.ne]

end Hellinger.Comparison.Examples.NormalMoment
