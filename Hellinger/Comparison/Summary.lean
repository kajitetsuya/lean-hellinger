/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.Comparison.Boundedness
public import Hellinger.Comparison.ConditionalMoment
public import Hellinger.Comparison.Cutoff
public import Hellinger.Comparison.PowerTail
public import Hellinger.Comparison.FiniteMoment
public import Hellinger.Comparison.Examples.CMSeparation
public import Hellinger.Comparison.Examples.FMSeparation
public import Hellinger.Comparison.Examples.PowerConsequences
public import Hellinger.Comparison.Examples.NormalMoment

/-! Typed family and pairwise comparisons. The normal singleton is a strictness
witness. NormalControl proves the bounded-parameter normal CM result. -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Hellinger.Comparison.Summary

variable {α : Type*} [MeasurableSpace α]

def NC (μ : Measure α) (F : Set (Measure α)) (q δ : ℝ) : Prop :=
  UniformHellingerBound μ F (fun ν ↦ tailPower μ ν q δ)

def WS (μ : Measure α) (F : Set (Measure α)) (δ : ℝ) : Prop :=
  UniformHellingerBound μ F (fun ν ↦ tailPower μ ν (Real.exp (1 / δ)) δ)

def UCM (μ : Measure α) (F : Set (Measure α)) : Prop :=
  ∃ M : ℝ≥0, ∀ ν ∈ F, conditionalMoment μ ν ≤ (M : ℝ≥0∞)

def UFM (μ : Measure α) (F : Set (Measure α)) : Prop :=
  ∃ B : ℝ≥0, ∀ ν ∈ F, fullRatioMoment μ ν ≤ (B : ℝ≥0∞)

/-- Memberwise finiteness is distinct from a uniform full-moment bound. -/
def FM (μ : Measure α) (F : Set (Measure α)) : Prop :=
  ∀ ν ∈ F, fullRatioMoment μ ν < ∞

/-- Literal pointwise boundedness for the supplied total ratio representatives. -/
def UB (F : Set (Measure α)) (r : Measure α → α → ℝ≥0∞) : Prop :=
  ∃ B : ℝ≥0, ∀ ν ∈ F, ∀ x, r ν x ≤ (B : ℝ≥0∞)

/-- All forward arrows use a constant chosen before every family member.
The dominator and ratio representative may vary with that member. -/
theorem forward_implications (μ : Measure α) [IsProbabilityMeasure μ]
    (F : Set (Measure α)) (hF : ∀ ν ∈ F, IsProbabilityMeasure ν)
    (κ : Measure α → Measure α) (hκ : ∀ ν ∈ F, SigmaFinite (κ ν))
    (hμκ : ∀ ν ∈ F, μ ≪ κ ν) (r : Measure α → α → ℝ≥0∞)
    (hr : ∀ ν ∈ F, r ν =ᵐ[μ] dominatedRatio μ ν (κ ν))
    {q δ : ℝ} (hq : 1 < q) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (UB F r → UCM μ F) ∧
    (UCM μ F → NC μ F q 1) ∧
    (NC μ F q 1 → NC μ F q δ) ∧
    (NC μ F q 1 → UFM μ F) ∧
    (UFM μ F → FM μ F) ∧
    (WS μ F δ ↔ NC μ F q δ) ∧
    (UniformHellingerBound μ F (fun ν ↦ bernsteinSq μ ν δ) ↔ NC μ F q δ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact uniform_conditionalMoment_of_uniform_ratio_representative_bound μ F hF κ hκ hμκ r hr
  · exact uniform_tailPower_of_uniform_conditionalMoment μ F hF hq zero_lt_one le_rfl
  · exact uniform_tailPower_of_larger_exponent μ F hF hq hδ hδ1
  · exact uniform_fullRatioMoment_of_uniform_tailPower_one (μ := μ) F hF hq
  · rintro ⟨B, hB⟩ ν hν
    exact (hB ν hν).trans_lt ENNReal.coe_lt_top
  · exact uniform_ws_iff_tailPower μ F hF hq hδ hδ1
  · exact uniform_bernsteinSq_iff_tailPower μ F hF hq hδ hδ1

/-- The fixed-pair finiteness equivalence does not uniformize the CM constant. -/
theorem pairwise_cm_iff_fm (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : conditionalMoment μ ν < ∞ ↔ fullRatioMoment μ ν < ∞ := by
  constructor
  · intro hCM
    have hrep : ENNReal.ofReal (conditionalMoment μ ν).toReal = conditionalMoment μ ν :=
      ENNReal.ofReal_toReal hCM.ne
    have hb := tailPower_four_le_of_conditionalMoment_le
      (μ := μ) (ν := ν) ENNReal.toReal_nonneg (le_of_eq hrep.symm)
    have htail : tailPower μ ν 4 1 < ∞ := hb.trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hellingerSq_ne_top μ ν).lt_top)
    exact (fullRatioMoment_lt_top_iff_tailPower_one_lt_top (by norm_num : (1 : ℝ) < 4)).mpr htail
  · exact conditionalMoment_lt_top_of_fullRatioMoment_lt_top

theorem pairwise_nc_one_iff_fm (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {q : ℝ} (hq : 1 < q) :
    (∃ M : ℝ≥0, tailPower μ ν q 1 ≤ (M : ℝ≥0∞) * hellingerSq μ ν) ↔
      fullRatioMoment μ ν < ∞ := by
  constructor
  · rintro ⟨M, hM⟩
    apply (fullRatioMoment_lt_top_iff_tailPower_one_lt_top hq).mpr
    exact hM.trans_lt
      (ENNReal.mul_lt_top ENNReal.coe_lt_top (hellingerSq_ne_top μ ν).lt_top)
  · intro hfull
    have hCM := conditionalMoment_lt_top_of_fullRatioMoment_lt_top hfull
    have hrep : ENNReal.ofReal (conditionalMoment μ ν).toReal = conditionalMoment μ ν :=
      ENNReal.ofReal_toReal hCM.ne
    have hb := tailPower_one_le_of_conditionalMoment_le hq ENNReal.toReal_nonneg
      (le_of_eq hrep.symm)
    refine ⟨Real.toNNReal ((2 * (conditionalMoment μ ν).toReal + 1) ^ 2 +
      4 * tailMassCoeff q), ?_⟩
    exact hb

theorem nc_one_without_uniform_cm {q : ℝ} (hq : 1 < q) :
    NC Examples.Power.uniformLaw Examples.CMSeparation.family q 1 ∧
      ¬ UCM Examples.Power.uniformLaw Examples.CMSeparation.family :=
  Examples.CMSeparation.cm_family_separation hq

theorem uniform_full_moment_without_fractional_nc {q δ : ℝ}
    (hq : 1 < q) (hδ : 0 < δ) (_hδ1 : δ < 1) :
    (∀ ν ∈ Examples.FMSeparation.modelFamily, IsProbabilityMeasure ν) ∧
    UFM Examples.Power.uniformLaw Examples.FMSeparation.modelFamily ∧
      ¬ NC Examples.Power.uniformLaw Examples.FMSeparation.modelFamily q δ :=
  ⟨Examples.FMSeparation.modelFamily_probability,
    Examples.FMSeparation.uniform_fullRatioMoment_le_two,
    Examples.FMSeparation.not_uniform_tailPower hq hδ⟩

theorem fractional_nc_without_finite_moment {q : ℝ} (hq : 1 < q) :
    NC Examples.Power.uniformLaw {Examples.Power.linearLaw} q (1 / 2) ∧
    UniformHellingerBound Examples.Power.uniformLaw {Examples.Power.linearLaw}
      (fun ν ↦ bernsteinSq Examples.Power.uniformLaw ν (1 / 2)) ∧
      ¬ FM Examples.Power.uniformLaw {Examples.Power.linearLaw} :=
  Examples.Power.fractional_nc_without_full_moment hq

/-- A genuine normal pair has finite CM but no bound even almost everywhere
on its canonical ratio. Thus a singleton already witnesses strictness. -/
theorem uniform_cm_without_ub {theta : ℝ} (htheta : theta ≠ 0) :
    UCM (Examples.Normal.normalLaw 0) {Examples.Normal.normalLaw theta} ∧
      ¬ UB {Examples.Normal.normalLaw theta}
        (fun ν ↦ dominatedRatio (Examples.Normal.normalLaw 0) ν volume) := by
  refine ⟨Examples.NormalMoment.uniform_conditionalMoment_singleton theta, ?_⟩
  rintro ⟨B, hB⟩
  apply Examples.Normal.not_ae_bounded_dominatedRatio htheta
  exact ⟨B, Filter.Eventually.of_forall
    (hB (Examples.Normal.normalLaw theta) (Set.mem_singleton _))⟩

/-- The four crossed arrows have explicit probability-family witnesses.
The fractional-NC-to-FM counterexample uses the source exponent one half;
the UFM-to-NC counterexample works for every positive fractional exponent. -/
theorem strict_separations {q δ : ℝ} (hq : 1 < q) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (UCM (Examples.Normal.normalLaw 0) {Examples.Normal.normalLaw 1} ∧
      ¬ UB {Examples.Normal.normalLaw 1}
        (fun ν ↦ dominatedRatio (Examples.Normal.normalLaw 0) ν volume)) ∧
    (NC Examples.Power.uniformLaw Examples.CMSeparation.family q 1 ∧
      ¬ UCM Examples.Power.uniformLaw Examples.CMSeparation.family) ∧
    ((∀ ν ∈ Examples.FMSeparation.modelFamily, IsProbabilityMeasure ν) ∧
      UFM Examples.Power.uniformLaw Examples.FMSeparation.modelFamily ∧
      ¬ NC Examples.Power.uniformLaw Examples.FMSeparation.modelFamily q δ) ∧
    (NC Examples.Power.uniformLaw {Examples.Power.linearLaw} q (1 / 2) ∧
      UniformHellingerBound Examples.Power.uniformLaw {Examples.Power.linearLaw}
        (fun ν ↦ bernsteinSq Examples.Power.uniformLaw ν (1 / 2)) ∧
      ¬ FM Examples.Power.uniformLaw {Examples.Power.linearLaw}) :=
  ⟨uniform_cm_without_ub one_ne_zero, nc_one_without_uniform_cm hq,
    uniform_full_moment_without_fractional_nc hq hδ hδ1,
    fractional_nc_without_finite_moment hq⟩

end Hellinger.Comparison.Summary
