/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.TailMass
public import Hellinger.HellingerBasic
public import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Tactic.FieldSimp

/-! Real-exponent tail interpolation, with separate strict and equal-exponent clauses. -/

public section

open MeasureTheory Set
open scoped ENNReal

namespace Hellinger

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α}

/-- Restricted-measure Hölder for the log tails. The integrals may be zero or infinite. -/
theorem tailLogMoment_le_mass_rpow_mul_tailLogMoment (hμν : μ ≪ ν)
    {c k k' : ℝ} (hc : 1 < c) (hk : 0 < k) (hkk' : k < k') :
    tailLogMoment μ ν c k ≤
      μ (tailEvent μ ν c) ^ (1 - k / k') * tailLogMoment μ ν c k' ^ (k / k') := by
  have hkp : 0 < k' := hk.trans hkk'
  have hr : 0 < k / k' := div_pos hk hkp
  have hr1 : k / k' < 1 := (div_lt_one hkp).mpr hkk'
  have hq : 0 < 1 - k / k' := sub_pos.mpr hr1
  have heq : (fun x ↦ ENNReal.ofReal ((llr μ ν x) ^ k)) =ᵐ[μ.restrict (tailEvent μ ν c)]
      (fun x ↦ ENNReal.ofReal ((llr μ ν x) ^ k') ^ (k / k') *
        (1 : ℝ≥0∞) ^ (1 - k / k')) := by
    filter_upwards [self_mem_ae_restrict (measurableSet_tailEvent μ ν c)] with x hx
    have hl := llr_pos_of_mem_tailEvent hc hx
    rw [ENNReal.one_rpow, mul_one,
      ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos hl k')]
    congr 1
    rw [← Real.rpow_mul hl.le]
    have hexp : k' * (k / k') = k := by field_simp [hkp.ne']
    rw [hexp]
  have hh := ENNReal.lintegral_mul_norm_pow_le
    (μ := μ.restrict (tailEvent μ ν c))
    (f := fun x ↦ ENNReal.ofReal ((llr μ ν x) ^ k')) (g := fun _ ↦ (1 : ℝ≥0∞))
    ((measurable_llr μ ν).pow_const k').ennreal_ofReal.aemeasurable aemeasurable_const
    hr.le hq.le (by ring : k / k' + (1 - k / k') = 1)
  calc
    tailLogMoment μ ν c k = ∫⁻ x in tailEvent μ ν c,
        ENNReal.ofReal ((llr μ ν x) ^ k) ∂μ := tailLogMoment_of_ac hμν c k
    _ = ∫⁻ x in tailEvent μ ν c,
        ENNReal.ofReal ((llr μ ν x) ^ k') ^ (k / k') *
          (1 : ℝ≥0∞) ^ (1 - k / k') ∂μ := lintegral_congr_ae heq
    _ ≤ (∫⁻ x in tailEvent μ ν c, ENNReal.ofReal ((llr μ ν x) ^ k') ∂μ) ^ (k / k') *
        (∫⁻ _x in tailEvent μ ν c, (1 : ℝ≥0∞) ∂μ) ^ (1 - k / k') := hh
    _ = _ := by simp [tailLogMoment_of_ac hμν, mul_comm]

/-- The equal-exponent interpolation content, proved directly in extended values. -/
theorem tailLogMoment_le_interpolationCoeff_mul_self {c : ℝ} (hc : 1 < c) (k : ℝ) :
    tailLogMoment μ ν c k ≤ ENNReal.ofReal (interpolationCoeff c) * tailLogMoment μ ν c k := by
  have hC : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (interpolationCoeff c) := by
    simpa using ENNReal.ofReal_le_ofReal (one_le_interpolationCoeff hc)
  simpa only [one_mul] using mul_le_mul' hC (le_refl (tailLogMoment μ ν c k))

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Strict interpolation with the accepted fixed-cutoff constant, including singular measures. -/
theorem tailLogMoment_interpolation_strict {c k k' : ℝ} (hc : 1 < c)
    (hk : 0 < k) (hkk' : k < k') :
    tailLogMoment μ ν c k ≤ ENNReal.ofReal (interpolationCoeff c) *
      hellingerSq μ ν ^ (1 - k / k') * tailLogMoment μ ν c k' ^ (k / k') := by
  have hkp : 0 < k' := hk.trans hkk'
  have hr : 0 < k / k' := div_pos hk hkp
  have hr1 : k / k' < 1 := (div_lt_one hkp).mpr hkk'
  have hq : 0 < 1 - k / k' := sub_pos.mpr hr1
  have hq1 : 1 - k / k' ≤ 1 := by linarith
  by_cases hμν : μ ≪ ν
  · have hmass := tailEvent_mass_le_tailMassCoeff_mul_hellingerSq hμν hc
    have hJ : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (tailMassCoeff c) := by
      simpa using ENNReal.ofReal_le_ofReal (one_le_tailMassCoeff hc)
    have hJpow : ENNReal.ofReal (tailMassCoeff c) ^ (1 - k / k') ≤
        ENNReal.ofReal (tailMassCoeff c) := by
      simpa only [ENNReal.rpow_one] using ENNReal.rpow_le_rpow_of_exponent_le hJ hq1
    calc
      tailLogMoment μ ν c k ≤ μ (tailEvent μ ν c) ^ (1 - k / k') *
          tailLogMoment μ ν c k' ^ (k / k') :=
        tailLogMoment_le_mass_rpow_mul_tailLogMoment hμν hc hk hkk'
      _ ≤ (ENNReal.ofReal (tailMassCoeff c) * hellingerSq μ ν) ^ (1 - k / k') *
          tailLogMoment μ ν c k' ^ (k / k') :=
        mul_le_mul' (ENNReal.rpow_le_rpow hmass hq.le) le_rfl
      _ = (ENNReal.ofReal (tailMassCoeff c) ^ (1 - k / k') *
          hellingerSq μ ν ^ (1 - k / k')) * tailLogMoment μ ν c k' ^ (k / k') := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le]
      _ ≤ (ENNReal.ofReal (tailMassCoeff c) * hellingerSq μ ν ^ (1 - k / k')) *
          tailLogMoment μ ν c k' ^ (k / k') :=
        mul_le_mul' (mul_le_mul' hJpow le_rfl) le_rfl
      _ = _ := rfl
  · have hH : hellingerSq μ ν ≠ 0 := by
      intro hz
      have heq := (hellingerSq_eq_zero_iff μ ν).mp hz
      subst ν
      exact hμν Measure.AbsolutelyContinuous.rfl
    have hHpow : hellingerSq μ ν ^ (1 - k / k') ≠ 0 :=
      fun hz ↦ hH ((ENNReal.rpow_eq_zero_iff_of_pos hq).mp hz)
    have hC : ENNReal.ofReal (interpolationCoeff c) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (tailMassCoeff_pos hc)).ne'
    have hprod : ENNReal.ofReal (interpolationCoeff c) *
        hellingerSq μ ν ^ (1 - k / k') ≠ 0 := mul_ne_zero hC hHpow
    rw [tailLogMoment_of_not_ac hμν, tailLogMoment_of_not_ac hμν,
      ENNReal.top_rpow_of_pos hr, ENNReal.mul_top hprod]

/-- Full Theorem 2 interpolation, with every real exponent pair `k' ≥ k > 0`.
The equal-exponent branch uses its direct extended-value theorem above. -/
theorem tailLogMoment_interpolation {c k k' : ℝ} (hc : 1 < c)
    (hk : 0 < k) (hkk' : k ≤ k') :
    tailLogMoment μ ν c k ≤ ENNReal.ofReal (interpolationCoeff c) *
      hellingerSq μ ν ^ (1 - k / k') * tailLogMoment μ ν c k' ^ (k / k') := by
  rcases eq_or_lt_of_le hkk' with heq | hlt
  · subst k'
    simpa only [div_self hk.ne', sub_self, ENNReal.rpow_zero, mul_one, ENNReal.rpow_one]
      using (tailLogMoment_le_interpolationCoeff_mul_self (μ := μ) (ν := ν) hc k)
  · exact tailLogMoment_interpolation_strict hc hk hlt

end Hellinger
