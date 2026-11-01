/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.Definitions

/-!
Extended comparison quantities. The intended domain is probability measures and finite
positive ratio thresholds. The ac branch uses the log-likelihood ratio, while every
non-ac branch explicitly retains the infinite contribution from singular support.
The native CM optimizer is a real number `a >= 1`, distinct from an ordinary cutoff.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Hellinger.Comparison

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

/-- The full first likelihood-ratio moment, with its singular-support contribution. -/
noncomputable def fullRatioMoment (μ ν : Measure α) : ℝ≥0∞ := by
  classical
  exact if μ ≪ ν then
    ∫⁻ x, ENNReal.ofReal (Real.exp (llr μ ν x)) ∂μ
  else ∞

/-- The closed upper ratio event in the ac branch. For positive `t` this is
`{x | t <= exp (llr μ ν x)}`. This event alone does not encode singular support. -/
noncomputable def closedTailEvent (μ ν : Measure α) (t : ℝ) : Set α :=
  {x | Real.log t ≤ llr μ ν x}

theorem measurableSet_closedTailEvent (μ ν : Measure α) (t : ℝ) :
    MeasurableSet (closedTailEvent μ ν t) :=
  measurableSet_le measurable_const (measurable_llr μ ν)

theorem mem_closedTailEvent_iff {t : ℝ} (ht : 0 < t) (x : α) :
    x ∈ closedTailEvent μ ν t ↔ t ≤ Real.exp (llr μ ν x) := by
  exact Real.log_le_iff_le_exp ht

/-- The closed first ratio tail, infinite in the non-ac branch. -/
noncomputable def closedTailMoment (μ ν : Measure α) (t : ℝ) : ℝ≥0∞ := by
  classical
  exact if μ ≪ ν then
    ∫⁻ x in closedTailEvent μ ν t, ENNReal.ofReal (Real.exp (llr μ ν x)) ∂μ
  else ∞

/-- The conditional ratio mean. The ac null-event branch is explicitly zero;
in the non-ac branch a finite positive cutoff contains singular support, giving infinity. -/
noncomputable def conditionalRatioMean (μ ν : Measure α) (t : ℝ) : ℝ≥0∞ := by
  classical
  exact if μ ≪ ν then
    if μ (closedTailEvent μ ν t) = 0 then 0
    else closedTailMoment μ ν t / μ (closedTailEvent μ ν t)
  else ∞

/-- CM's native cutoff, without altering the ordinary cutoff used in NC. -/
noncomputable def cmCutoff (a : ℝ) : ℝ := (1 + 1 / (2 * a)) ^ 2

/-- CM's native real-parameter objective. Only `a >= 1` is used by the infimum. -/
noncomputable def cmObjective (μ ν : Measure α) (a : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal a * conditionalRatioMean μ ν (cmCutoff a)

/-- The source CM infimum, over all real parameters `a >= 1`. -/
noncomputable def conditionalMoment (μ ν : Measure α) : ℝ≥0∞ :=
  ⨅ a : {a : ℝ // 1 ≤ a}, cmObjective μ ν a.1

theorem fullRatioMoment_of_ac (h : μ ≪ ν) :
    fullRatioMoment μ ν = ∫⁻ x, ENNReal.ofReal (Real.exp (llr μ ν x)) ∂μ := by
  simp [fullRatioMoment, h]

@[simp] theorem fullRatioMoment_of_not_ac (h : ¬ μ ≪ ν) :
    fullRatioMoment μ ν = ∞ := by
  simp [fullRatioMoment, h]

theorem closedTailMoment_of_ac (h : μ ≪ ν) (t : ℝ) :
    closedTailMoment μ ν t =
      ∫⁻ x in closedTailEvent μ ν t, ENNReal.ofReal (Real.exp (llr μ ν x)) ∂μ := by
  simp [closedTailMoment, h]

@[simp] theorem closedTailMoment_of_not_ac (h : ¬ μ ≪ ν) (t : ℝ) :
    closedTailMoment μ ν t = ∞ := by
  simp [closedTailMoment, h]

theorem conditionalRatioMean_of_ac (h : μ ≪ ν) (t : ℝ) :
    conditionalRatioMean μ ν t =
      if μ (closedTailEvent μ ν t) = 0 then 0
      else closedTailMoment μ ν t / μ (closedTailEvent μ ν t) := by
  simp only [conditionalRatioMean, ite_eq_left h]

@[simp] theorem conditionalRatioMean_of_not_ac (h : ¬ μ ≪ ν) (t : ℝ) :
    conditionalRatioMean μ ν t = ∞ := by
  simp [conditionalRatioMean, h]

theorem conditionalRatioMean_of_null (h : μ ≪ ν) {t : ℝ}
    (ht : μ (closedTailEvent μ ν t) = 0) : conditionalRatioMean μ ν t = 0 := by
  simp [conditionalRatioMean, h, ht]

theorem conditionalRatioMean_of_nonnull (h : μ ≪ ν) {t : ℝ}
    (ht : μ (closedTailEvent μ ν t) ≠ 0) :
    conditionalRatioMean μ ν t = closedTailMoment μ ν t / μ (closedTailEvent μ ν t) := by
  simp [conditionalRatioMean, h, ht]

@[simp] theorem cmCutoff_one : cmCutoff 1 = (9 / 4 : ℝ) := by
  norm_num [cmCutoff]

theorem one_lt_cmCutoff {a : ℝ} (ha : 1 ≤ a) : 1 < cmCutoff a := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hdiv : 0 < 1 / (2 * a) := by positivity
  dsimp [cmCutoff]
  nlinarith [sq_nonneg (1 / (2 * a))]

theorem cmCutoff_pos {a : ℝ} (ha : 1 ≤ a) : 0 < cmCutoff a :=
  zero_lt_one.trans (one_lt_cmCutoff ha)

theorem cmCutoff_le_nine_fourths {a : ℝ} (ha : 1 ≤ a) :
    cmCutoff a ≤ (9 / 4 : ℝ) := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hdiv0 : 0 ≤ 1 / (2 * a) := by positivity
  have hdiv : 1 / (2 * a) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * a)).2
    nlinarith
  dsimp [cmCutoff]
  nlinarith [sq_nonneg (1 / (2 * a))]

theorem conditionalMoment_le (a : ℝ) (ha : 1 ≤ a) :
    conditionalMoment μ ν ≤ cmObjective μ ν a :=
  iInf_le (fun b : {a : ℝ // 1 ≤ a} ↦ cmObjective μ ν b.1) ⟨a, ha⟩

theorem le_conditionalMoment {b : ℝ≥0∞}
    (hb : ∀ a : ℝ, 1 ≤ a → b ≤ cmObjective μ ν a) :
    b ≤ conditionalMoment μ ν := by
  exact le_iInf fun a ↦ hb a.1 a.2

theorem conditionalMoment_lt_iff {b : ℝ≥0∞} :
    conditionalMoment μ ν < b ↔ ∃ a : ℝ, 1 ≤ a ∧ cmObjective μ ν a < b := by
  simp only [conditionalMoment, iInf_lt_iff, Subtype.exists, exists_prop]

/-- A finite infimum supplies some finite objective; no minimizing parameter is asserted. -/
theorem exists_cmObjective_lt_top (h : conditionalMoment μ ν < ∞) :
    ∃ a : ℝ, 1 ≤ a ∧ cmObjective μ ν a < ∞ :=
  conditionalMoment_lt_iff.mp h

@[simp] theorem cmObjective_of_not_ac (h : ¬ μ ≪ ν) {a : ℝ} (ha : 1 ≤ a) :
    cmObjective μ ν a = ∞ := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  rw [cmObjective, conditionalRatioMean_of_not_ac h,
    ENNReal.mul_top (ENNReal.ofReal_pos.mpr ha0).ne']

@[simp] theorem conditionalMoment_of_not_ac (h : ¬ μ ≪ ν) :
    conditionalMoment μ ν = ∞ := by
  apply top_unique
  exact le_conditionalMoment fun a ha ↦ by simp [cmObjective_of_not_ac h ha]

theorem ac_of_conditionalMoment_lt_top (h : conditionalMoment μ ν < ∞) : μ ≪ ν := by
  by_contra hμν
  simp [conditionalMoment_of_not_ac hμν] at h

theorem ac_of_fullRatioMoment_lt_top (h : fullRatioMoment μ ν < ∞) : μ ≪ ν := by
  by_contra hμν
  simp [fullRatioMoment_of_not_ac hμν] at h

section DensityInterpretation

variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- In the ac branch, the exponential kernel is the genuine Radon--Nikodym ratio
`μ`-almost everywhere; totalized logarithms at zero have no effect on this identity. -/
theorem exp_llr_ae_eq_rnDeriv (h : μ ≪ ν) :
    (fun x ↦ ENNReal.ofReal (Real.exp (llr μ ν x))) =ᵐ[μ] μ.rnDeriv ν := by
  filter_upwards [MeasureTheory.exp_llr_of_ac μ ν h,
    h.ae_le (Measure.rnDeriv_lt_top μ ν)] with x hx htop
  rw [hx, ENNReal.ofReal_toReal htop.ne]

/-- The finite-measure ac full moment is the first RN-ratio moment under `μ`. -/
theorem fullRatioMoment_eq_lintegral_rnDeriv (h : μ ≪ ν) :
    fullRatioMoment μ ν = ∫⁻ x, μ.rnDeriv ν x ∂μ := by
  rw [fullRatioMoment_of_ac h]
  exact lintegral_congr_ae (exp_llr_ae_eq_rnDeriv h)

/-- The closed event includes threshold atoms and agrees with the density-ratio event
in the ac finite-measure branch. The threshold is a finite positive real number. -/
theorem closedTailEvent_ae_iff (h : μ ≪ ν) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ x ∂μ, x ∈ closedTailEvent μ ν t ↔ t ≤ (μ.rnDeriv ν x).toReal := by
  filter_upwards [MeasureTheory.exp_llr_of_ac μ ν h] with x hx
  rw [mem_closedTailEvent_iff ht, hx]

/-- Restricted first RN moment on the exact closed event; no moment finiteness is used. -/
theorem closedTailMoment_eq_lintegral_rnDeriv (h : μ ≪ ν) (t : ℝ) :
    closedTailMoment μ ν t = ∫⁻ x in closedTailEvent μ ν t, μ.rnDeriv ν x ∂μ := by
  rw [closedTailMoment_of_ac h]
  exact lintegral_congr_ae (ae_restrict_of_ae (exp_llr_ae_eq_rnDeriv h))

end DensityInterpretation

end Hellinger.Comparison
