/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.Definitions
public import Mathlib.Tactic.NormNum

/-! Basic properties of the canonical squared Hellinger distance. -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace Hellinger

variable {α : Type*} [MeasurableSpace α]

theorem sqrt_sub_sq_le_add {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (Real.sqrt p - Real.sqrt q) ^ 2 ≤ p + q := by
  have h := mul_nonneg (Real.sqrt_nonneg p) (Real.sqrt_nonneg q)
  nlinarith [Real.sq_sqrt hp, Real.sq_sqrt hq]

@[simp] theorem hellingerSq_self (μ : Measure α) : hellingerSq μ μ = 0 := by
  simp [hellingerSq, pairDensity]

theorem hellingerSq_symm (μ ν : Measure α) : hellingerSq μ ν = hellingerSq ν μ := by
  simp only [hellingerSq, pairDensity, pairMeasure, add_comm ν μ]
  apply lintegral_congr
  intro x
  congr 1
  ring

/-- Finiteness is proved using the entire pairwise dominator, including singular mass. -/
theorem hellingerSq_le_mass (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    hellingerSq μ ν ≤ μ univ + ν univ := by
  let ρ := pairMeasure μ ν
  let : IsFiniteMeasure ρ := by dsimp [ρ, pairMeasure]; infer_instance
  have hμ : μ ≪ ρ := (Measure.AbsolutelyContinuous.rfl : μ ≪ μ).add_right ν
  have hν : ν ≪ ρ := (Measure.AbsolutelyContinuous.rfl : ν ≪ ν).add_right' μ
  calc
    hellingerSq μ ν ≤ ∫⁻ x, μ.rnDeriv ρ x + ν.rnDeriv ρ x ∂ρ := by
      unfold hellingerSq pairDensity
      apply lintegral_mono_ae
      filter_upwards [μ.rnDeriv_lt_top ρ, ν.rnDeriv_lt_top ρ] with x hp hq
      calc
        ENNReal.ofReal
            ((Real.sqrt (μ.rnDeriv ρ x).toReal - Real.sqrt (ν.rnDeriv ρ x).toReal) ^ 2)
            ≤ ENNReal.ofReal ((μ.rnDeriv ρ x).toReal + (ν.rnDeriv ρ x).toReal) :=
          ENNReal.ofReal_le_ofReal (sqrt_sub_sq_le_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
        _ = μ.rnDeriv ρ x + ν.rnDeriv ρ x := by
          rw [ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
            ENNReal.ofReal_toReal hp.ne, ENNReal.ofReal_toReal hq.ne]
    _ = μ univ + ν univ := by
      rw [lintegral_add_left (Measure.measurable_rnDeriv μ ρ),
        Measure.lintegral_rnDeriv hμ, Measure.lintegral_rnDeriv hν]

theorem hellingerSq_le_two (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : hellingerSq μ ν ≤ 2 := by
  calc
    hellingerSq μ ν ≤ μ univ + ν univ := hellingerSq_le_mass μ ν
    _ = 2 := by norm_num

theorem hellingerSq_ne_top (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : hellingerSq μ ν ≠ ∞ :=
  ne_top_of_le_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (hellingerSq_le_two μ ν)

/-- Zero distance identifies the two finite measures; no absolute-continuity assumption. -/
theorem hellingerSq_eq_zero_iff (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] : hellingerSq μ ν = 0 ↔ μ = ν := by
  constructor
  · intro hzero
    let ρ := pairMeasure μ ν
    let : IsFiniteMeasure ρ := by dsimp [ρ, pairMeasure]; infer_instance
    have hμ : μ ≪ ρ := (Measure.AbsolutelyContinuous.rfl : μ ≪ μ).add_right ν
    have hν : ν ≪ ρ := (Measure.AbsolutelyContinuous.rfl : ν ≪ ν).add_right' μ
    have hmeas : Measurable (fun x ↦ ENNReal.ofReal
        ((Real.sqrt (μ.rnDeriv ρ x).toReal - Real.sqrt (ν.rnDeriv ρ x).toReal) ^ 2)) := by
      fun_prop
    change (∫⁻ x, ENNReal.ofReal
      ((Real.sqrt (μ.rnDeriv ρ x).toReal - Real.sqrt (ν.rnDeriv ρ x).toReal) ^ 2) ∂ρ) = 0
      at hzero
    have hpoint := (lintegral_eq_zero_iff hmeas).mp hzero
    have heq : μ.rnDeriv ρ =ᵐ[ρ] ν.rnDeriv ρ := by
      filter_upwards [hpoint, μ.rnDeriv_lt_top ρ, ν.rnDeriv_lt_top ρ] with x hx hp hq
      have hz : (Real.sqrt (μ.rnDeriv ρ x).toReal -
          Real.sqrt (ν.rnDeriv ρ x).toReal) ^ 2 = 0 :=
        le_antisymm (ENNReal.ofReal_eq_zero.mp hx) (sq_nonneg _)
      have hs : Real.sqrt (μ.rnDeriv ρ x).toReal = Real.sqrt (ν.rnDeriv ρ x).toReal :=
        sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
      apply (ENNReal.toReal_eq_toReal_iff' hp.ne hq.ne).mp
      exact (Real.sqrt_inj ENNReal.toReal_nonneg ENNReal.toReal_nonneg).mp hs
    calc
      μ = ρ.withDensity (μ.rnDeriv ρ) := (Measure.withDensity_rnDeriv_eq μ ρ hμ).symm
      _ = ρ.withDensity (ν.rnDeriv ρ) := withDensity_congr_ae heq
      _ = ν := Measure.withDensity_rnDeriv_eq ν ρ hν
  · intro h
    subst ν
    exact hellingerSq_self μ

end Hellinger
