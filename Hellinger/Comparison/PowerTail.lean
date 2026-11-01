/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.Interpolation
public import Hellinger.Uniform

/-! Comparison of positive power tails at a fixed cutoff greater than one. -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Hellinger.Comparison

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α}

/-- A larger positive exponent controls a smaller exponent on the strict tail. -/
theorem tailPower_mono_exponent {c δ δ' : ℝ} (hc : 1 < c) (_hδ : 0 < δ)
    (hδδ' : δ ≤ δ') : tailPower μ ν c δ ≤ tailPower μ ν c δ' := by
  by_cases hμν : μ ≪ ν
  · rw [tailPower_of_ac hμν, tailPower_of_ac hμν]
    apply lintegral_mono_ae
    filter_upwards [self_mem_ae_restrict (measurableSet_tailEvent μ ν c)] with x hx
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hδδ' (llr_pos_of_mem_tailEvent hc hx).le))
  · simp [tailPower_of_not_ac hμν]

/-- Extended Holder on the restricted tail measure; no finite-tail premise. -/
theorem tailPower_le_mass_rpow_mul_tailPower (hμν : μ ≪ ν) (c : ℝ)
    {δ δ' : ℝ} (hδ : 0 < δ) (hδδ' : δ < δ') :
    tailPower μ ν c δ ≤ μ (tailEvent μ ν c) ^ (1 - δ / δ') *
      tailPower μ ν c δ' ^ (δ / δ') := by
  have hδp : 0 < δ' := hδ.trans hδδ'
  have hr : 0 < δ / δ' := div_pos hδ hδp
  have hr1 : δ / δ' < 1 := (div_lt_one hδp).mpr hδδ'
  have hq : 0 < 1 - δ / δ' := sub_pos.mpr hr1
  have heq : (fun x ↦ ENNReal.ofReal (Real.exp (δ * llr μ ν x))) =
      (fun x ↦ ENNReal.ofReal (Real.exp (δ' * llr μ ν x)) ^ (δ / δ') *
        (1 : ℝ≥0∞) ^ (1 - δ / δ')) := by
    funext x
    rw [ENNReal.one_rpow, mul_one,
      ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
    congr 2
    field_simp [hδp.ne']
  have hh := ENNReal.lintegral_mul_norm_pow_le
    (μ := μ.restrict (tailEvent μ ν c))
    (f := fun x ↦ ENNReal.ofReal (Real.exp (δ' * llr μ ν x)))
    (g := fun _ ↦ (1 : ℝ≥0∞))
    (measurable_const.mul (measurable_llr μ ν)).exp.ennreal_ofReal.aemeasurable
    aemeasurable_const hr.le hq.le (by ring : δ / δ' + (1 - δ / δ') = 1)
  calc
    tailPower μ ν c δ = ∫⁻ x in tailEvent μ ν c,
        ENNReal.ofReal (Real.exp (δ * llr μ ν x)) ∂μ := tailPower_of_ac hμν c δ
    _ = ∫⁻ x in tailEvent μ ν c,
        ENNReal.ofReal (Real.exp (δ' * llr μ ν x)) ^ (δ / δ') *
          (1 : ℝ≥0∞) ^ (1 - δ / δ') ∂μ := by rw [heq]
    _ ≤ (∫⁻ x in tailEvent μ ν c, ENNReal.ofReal (Real.exp (δ' * llr μ ν x)) ∂μ) ^
          (δ / δ') * (∫⁻ _x in tailEvent μ ν c, (1 : ℝ≥0∞) ∂μ) ^ (1 - δ / δ') := hh
    _ = _ := by simp [tailPower_of_ac hμν, mul_comm]

/-- Direct equal-exponent content, also at zero or infinity. -/
theorem tailPower_le_interpolationCoeff_mul_self {c : ℝ} (hc : 1 < c) (δ : ℝ) :
    tailPower μ ν c δ ≤ ENNReal.ofReal (interpolationCoeff c) * tailPower μ ν c δ := by
  have hC : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (interpolationCoeff c) := by
    simpa using ENNReal.ofReal_le_ofReal (one_le_interpolationCoeff hc)
  simpa only [one_mul] using mul_le_mul' hC (le_refl (tailPower μ ν c δ))

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Strict interpolation for power tails, including singular measures. -/
theorem tailPower_interpolation_strict {c δ δ' : ℝ} (hc : 1 < c)
    (hδ : 0 < δ) (hδδ' : δ < δ') :
    tailPower μ ν c δ ≤ ENNReal.ofReal (interpolationCoeff c) *
      hellingerSq μ ν ^ (1 - δ / δ') * tailPower μ ν c δ' ^ (δ / δ') := by
  have hδp : 0 < δ' := hδ.trans hδδ'
  have hr : 0 < δ / δ' := div_pos hδ hδp
  have hr1 : δ / δ' < 1 := (div_lt_one hδp).mpr hδδ'
  have hq : 0 < 1 - δ / δ' := sub_pos.mpr hr1
  have hq1 : 1 - δ / δ' ≤ 1 := by linarith
  by_cases hμν : μ ≪ ν
  · have hmass := tailEvent_mass_le_tailMassCoeff_mul_hellingerSq hμν hc
    have hJ : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (tailMassCoeff c) := by
      simpa using ENNReal.ofReal_le_ofReal (one_le_tailMassCoeff hc)
    have hJpow : ENNReal.ofReal (tailMassCoeff c) ^ (1 - δ / δ') ≤
        ENNReal.ofReal (tailMassCoeff c) := by
      simpa only [ENNReal.rpow_one] using ENNReal.rpow_le_rpow_of_exponent_le hJ hq1
    calc
      tailPower μ ν c δ ≤ μ (tailEvent μ ν c) ^ (1 - δ / δ') *
          tailPower μ ν c δ' ^ (δ / δ') :=
        tailPower_le_mass_rpow_mul_tailPower hμν c hδ hδδ'
      _ ≤ (ENNReal.ofReal (tailMassCoeff c) * hellingerSq μ ν) ^ (1 - δ / δ') *
          tailPower μ ν c δ' ^ (δ / δ') :=
        mul_le_mul' (ENNReal.rpow_le_rpow hmass hq.le) le_rfl
      _ = (ENNReal.ofReal (tailMassCoeff c) ^ (1 - δ / δ') *
          hellingerSq μ ν ^ (1 - δ / δ')) * tailPower μ ν c δ' ^ (δ / δ') := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le]
      _ ≤ (ENNReal.ofReal (tailMassCoeff c) * hellingerSq μ ν ^ (1 - δ / δ')) *
          tailPower μ ν c δ' ^ (δ / δ') :=
        mul_le_mul' (mul_le_mul' hJpow le_rfl) le_rfl
      _ = _ := rfl
  · have hH : hellingerSq μ ν ≠ 0 := by
      intro hz
      have heq := (hellingerSq_eq_zero_iff μ ν).mp hz
      subst ν
      exact hμν Measure.AbsolutelyContinuous.rfl
    have hHpow : hellingerSq μ ν ^ (1 - δ / δ') ≠ 0 :=
      fun hz ↦ hH ((ENNReal.rpow_eq_zero_iff_of_pos hq).mp hz)
    have hC : ENNReal.ofReal (interpolationCoeff c) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (tailMassCoeff_pos hc)).ne'
    have hprod : ENNReal.ofReal (interpolationCoeff c) *
        hellingerSq μ ν ^ (1 - δ / δ') ≠ 0 := mul_ne_zero hC hHpow
    rw [tailPower_of_not_ac hμν, tailPower_of_not_ac hμν,
      ENNReal.top_rpow_of_pos hr, ENNReal.mul_top hprod]

/-- Every real exponent pair 0<delta<=delta', with no upper restriction on delta'. -/
theorem tailPower_interpolation {c δ δ' : ℝ} (hc : 1 < c)
    (hδ : 0 < δ) (hδδ' : δ ≤ δ') :
    tailPower μ ν c δ ≤ ENNReal.ofReal (interpolationCoeff c) *
      hellingerSq μ ν ^ (1 - δ / δ') * tailPower μ ν c δ' ^ (δ / δ') := by
  rcases eq_or_lt_of_le hδδ' with heq | hlt
  · subst δ'
    simpa only [div_self hδ.ne', sub_self, ENNReal.rpow_zero, mul_one, ENNReal.rpow_one]
      using (tailPower_le_interpolationCoeff_mul_self (μ := μ) (ν := ν) hc δ)
  · exact tailPower_interpolation_strict hc hδ hlt

theorem tailPower_interpolation_four {δ δ' : ℝ} (hδ : 0 < δ) (hδδ' : δ ≤ δ') :
    tailPower μ ν 4 δ ≤ 4 * hellingerSq μ ν ^ (1 - δ / δ') *
      tailPower μ ν 4 δ' ^ (δ / δ') := by
  simpa only [interpolationCoeff_four, ENNReal.ofReal_ofNat] using
    (tailPower_interpolation (μ := μ) (ν := ν) (c := 4) (by norm_num) hδ hδδ')

/-- Explicit growth of the smaller-exponent multiplier; the hypothesis may involve infinity. -/
theorem tailPower_le_of_le_mul_hellinger {c δ δ' : ℝ} (hc : 1 < c)
    (hδ : 0 < δ) (hδδ' : δ ≤ δ') {M : ℝ≥0∞}
    (hM : tailPower μ ν c δ' ≤ M * hellingerSq μ ν) :
    tailPower μ ν c δ ≤ ENNReal.ofReal (interpolationCoeff c) *
      M ^ (δ / δ') * hellingerSq μ ν := by
  have hδp : 0 < δ' := lt_of_lt_of_le hδ hδδ'
  have hr : 0 ≤ δ / δ' := (div_pos hδ hδp).le
  have hq : 0 ≤ 1 - δ / δ' := sub_nonneg.mpr ((div_le_one hδp).mpr hδδ')
  calc
    _ ≤ ENNReal.ofReal (interpolationCoeff c) * hellingerSq μ ν ^ (1 - δ / δ') *
        tailPower μ ν c δ' ^ (δ / δ') := tailPower_interpolation hc hδ hδδ'
    _ ≤ ENNReal.ofReal (interpolationCoeff c) * hellingerSq μ ν ^ (1 - δ / δ') *
        (M * hellingerSq μ ν) ^ (δ / δ') :=
      mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hM hr)
    _ = (ENNReal.ofReal (interpolationCoeff c) * M ^ (δ / δ')) *
        (hellingerSq μ ν ^ (1 - δ / δ') * hellingerSq μ ν ^ (δ / δ')) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hr]
      ac_rfl
    _ = _ := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ hq hr, sub_add_cancel, ENNReal.rpow_one]

/-- A single finite multiplier for the family transfers with the exact fractional growth. -/
theorem uniform_tailPower_of_larger_exponent (μ : Measure α) [IsProbabilityMeasure μ]
    (F : Set (Measure α)) (hF : ∀ ν ∈ F, IsProbabilityMeasure ν)
    {c δ δ' : ℝ} (hc : 1 < c) (hδ : 0 < δ) (hδδ' : δ ≤ δ') :
    UniformHellingerBound μ F (fun ν ↦ tailPower μ ν c δ') →
      UniformHellingerBound μ F (fun ν ↦ tailPower μ ν c δ) := by
  rintro ⟨M, hM⟩
  have hr : 0 ≤ δ / δ' := (div_pos hδ (lt_of_lt_of_le hδ hδδ')).le
  refine ⟨Real.toNNReal (interpolationCoeff c) * M ^ (δ / δ'), ?_⟩
  intro ν hν
  let : IsProbabilityMeasure ν := hF ν hν
  have h := tailPower_le_of_le_mul_hellinger hc hδ hδδ' (hM ν hν)
  simpa only [ENNReal.coe_mul, ENNReal.coe_rpow_of_nonneg _ hr, ENNReal.ofReal] using h

end Hellinger.Comparison
