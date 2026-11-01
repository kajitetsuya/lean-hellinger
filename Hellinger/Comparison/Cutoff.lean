/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.TailMass
public import Hellinger.Uniform

/-! Changing a fixed ordinary power-tail cutoff, including singular and infinite cases. -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Hellinger

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α}

/-- The moment between two fixed cutoffs is bounded by the lower-cutoff event mass.
No absolute continuity or finite-tail assumption is imposed on the conclusion. -/
theorem tailPower_le_tailPower_add_hellingerSq [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {q a δ : ℝ} (hq : 1 < q) (ha : 1 < a) (hδ : 0 < δ) :
    tailPower μ ν q δ ≤ tailPower μ ν a δ +
      ENNReal.ofReal (a ^ δ * tailMassCoeff q) * hellingerSq μ ν := by
  classical
  by_cases hμν : μ ≪ ν
  · have ha0 : 0 < a := lt_trans (by norm_num) ha
    let f : α → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (Real.exp (δ * llr μ ν x))
    have hband : (∫⁻ x in tailEvent μ ν q \ tailEvent μ ν a, f x ∂μ) ≤
        ENNReal.ofReal (a ^ δ) * μ (tailEvent μ ν q) := by
      calc
        _ ≤ ∫⁻ x in tailEvent μ ν q \ tailEvent μ ν a,
            ENNReal.ofReal (a ^ δ) ∂μ := by
          apply setLIntegral_mono measurable_const
          intro x hx
          have hl : llr μ ν x ≤ Real.log a := le_of_not_gt hx.2
          apply ENNReal.ofReal_le_ofReal
          rw [Real.rpow_def_of_pos ha0]
          exact Real.exp_le_exp.mpr (by
            simpa only [mul_comm] using mul_le_mul_of_nonneg_left hl hδ.le)
        _ ≤ ∫⁻ x in tailEvent μ ν q, ENNReal.ofReal (a ^ δ) ∂μ :=
          lintegral_mono_set Set.sdiff_subset
        _ = _ := setLIntegral_const _ _
    rw [tailPower_of_ac hμν, tailPower_of_ac hμν]
    change (∫⁻ x in tailEvent μ ν q, f x ∂μ) ≤
      (∫⁻ x in tailEvent μ ν a, f x ∂μ) + _
    calc
      _ = (∫⁻ x in tailEvent μ ν q ∩ tailEvent μ ν a, f x ∂μ) +
          (∫⁻ x in tailEvent μ ν q \ tailEvent μ ν a, f x ∂μ) :=
        (lintegral_inter_add_sdiff f (tailEvent μ ν q)
          (measurableSet_tailEvent μ ν a)).symm
      _ ≤ (∫⁻ x in tailEvent μ ν a, f x ∂μ) +
          (∫⁻ x in tailEvent μ ν q \ tailEvent μ ν a, f x ∂μ) :=
        add_le_add (lintegral_mono_set Set.inter_subset_right) le_rfl
      _ ≤ (∫⁻ x in tailEvent μ ν a, f x ∂μ) +
          ENNReal.ofReal (a ^ δ) * μ (tailEvent μ ν q) :=
        add_le_add le_rfl hband
      _ ≤ (∫⁻ x in tailEvent μ ν a, f x ∂μ) +
          ENNReal.ofReal (a ^ δ) *
            (ENNReal.ofReal (tailMassCoeff q) * hellingerSq μ ν) :=
        add_le_add le_rfl (mul_le_mul_right
          (tailEvent_mass_le_tailMassCoeff_mul_hellingerSq hμν hq) _)
      _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_pos_of_pos ha0 δ).le]
  · simp [tailPower_of_not_ac hμν]

/-- A single finite multiplier transfers between cutoffs before every family member. -/
theorem UniformHellingerBound.tailPower_cutoff [IsFiniteMeasure μ]
    {F : Set (Measure α)} (hF : ∀ ν ∈ F, IsFiniteMeasure ν)
    {q a δ : ℝ} (hq : 1 < q) (ha : 1 < a) (hδ : 0 < δ)
    (hbound : UniformHellingerBound μ F (fun ν ↦ tailPower μ ν a δ)) :
    UniformHellingerBound μ F (fun ν ↦ tailPower μ ν q δ) := by
  let B : ℝ≥0 := Real.toNNReal (a ^ δ * tailMassCoeff q)
  obtain ⟨M, hM⟩ := hbound
  refine ⟨M + B, ?_⟩
  intro ν hν
  let : IsFiniteMeasure ν := hF ν hν
  have hcut : tailPower μ ν q δ ≤ tailPower μ ν a δ +
      (B : ℝ≥0∞) * hellingerSq μ ν := by
    simpa only [B, ENNReal.ofReal] using
      (tailPower_le_tailPower_add_hellingerSq (μ := μ) (ν := ν) hq ha hδ)
  calc
    tailPower μ ν q δ ≤ tailPower μ ν a δ +
        (B : ℝ≥0∞) * hellingerSq μ ν := hcut
    _ ≤ (M : ℝ≥0∞) * hellingerSq μ ν + (B : ℝ≥0∞) * hellingerSq μ ν :=
      add_le_add (hM ν hν) le_rfl
    _ = ((M + B : ℝ≥0) : ℝ≥0∞) * hellingerSq μ ν := by
      rw [ENNReal.coe_add, add_mul]

/-- Uniform power-tail control is independent of the fixed cutoff greater than one.
Neither a common dominating measure nor a nonempty family is required. -/
theorem uniform_tailPower_cutoff_iff (μ : Measure α) [IsFiniteMeasure μ]
    (F : Set (Measure α)) (hF : ∀ ν ∈ F, IsFiniteMeasure ν)
    {q a δ : ℝ} (hq : 1 < q) (ha : 1 < a) (hδ : 0 < δ) :
    UniformHellingerBound μ F (fun ν ↦ tailPower μ ν a δ) ↔
      UniformHellingerBound μ F (fun ν ↦ tailPower μ ν q δ) :=
  ⟨fun h ↦ h.tailPower_cutoff hF hq ha hδ,
    fun h ↦ h.tailPower_cutoff hF ha hq hδ⟩

/-- Source WS/NC equivalence, with the native WS cutoff `exp (1 / δ)` unchanged. -/
theorem uniform_ws_iff_tailPower (μ : Measure α) [IsProbabilityMeasure μ]
    (F : Set (Measure α)) (hF : ∀ ν ∈ F, IsProbabilityMeasure ν)
    {q δ : ℝ} (hq : 1 < q) (hδ : 0 < δ) (_hδ1 : δ ≤ 1) :
    UniformHellingerBound μ F (fun ν ↦ tailPower μ ν (Real.exp (1 / δ)) δ) ↔
      UniformHellingerBound μ F (fun ν ↦ tailPower μ ν q δ) := by
  apply uniform_tailPower_cutoff_iff μ F (fun ν hν ↦ ?_) hq
    (Real.one_lt_exp_iff.mpr (one_div_pos.mpr hδ)) hδ
  let : IsProbabilityMeasure ν := hF ν hν
  infer_instance

end Hellinger