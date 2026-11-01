/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.Comparison.DensityBridge
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog

/-! Literal positive-power and positive-log tails for arbitrary common dominators.
The logarithmic kernel uses the canonical extended logarithm followed by its
nonnegative part, which agrees with the ordinary logarithm on every tail above one.
In particular, it preserves logarithmic infinity on singular support. -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Hellinger.Comparison

variable {α : Type*} [MeasurableSpace α] {μ ν κ : Measure α}

noncomputable def dominatedStrictTailEvent (μ ν κ : Measure α) (q : ℝ) : Set α :=
  {x | ENNReal.ofReal q < dominatedRatio μ ν κ x}

theorem measurableSet_dominatedStrictTailEvent (μ ν κ : Measure α) (q : ℝ) :
    MeasurableSet (dominatedStrictTailEvent μ ν κ q) :=
  measurableSet_lt measurable_const (measurable_dominatedRatio μ ν κ)

section SigmaFinite

variable [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite κ]

/-- Every strict positive-power source tail includes the infinite singular part. -/
theorem setLIntegral_dominatedRatio_rpow_eq_top_of_not_ac
    (hμκ : μ ≪ κ) (hμν : ¬ μ ≪ ν) (q : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∫⁻ x in dominatedStrictTailEvent μ ν κ q, dominatedRatio μ ν κ x ^ δ ∂μ = ∞ := by
  rw [← lintegral_indicator (measurableSet_dominatedStrictTailEvent μ ν κ q)]
  apply lintegral_eq_top_of_ae_top_singularPart hμν
  filter_upwards [dominatedRatio_ae_eq_top_singularPart (ν := ν) hμκ] with x hx
  have hmem : x ∈ dominatedStrictTailEvent μ ν κ q := by
    change ENNReal.ofReal q < dominatedRatio μ ν κ x
    rw [hx]
    exact ENNReal.ofReal_lt_top
  rw [Set.indicator_of_mem hmem, hx, ENNReal.top_rpow_of_pos hδ]

/-- Extended logarithms retain infinity before positive real powers are formed. -/
theorem setLIntegral_dominatedRatio_log_rpow_eq_top_of_not_ac
    (hμκ : μ ≪ κ) (hμν : ¬ μ ≪ ν) (q : ℝ) {k : ℝ} (hk : 0 < k) :
    ∫⁻ x in dominatedStrictTailEvent μ ν κ q,
      (ENNReal.log (dominatedRatio μ ν κ x)).toENNReal ^ k ∂μ = ∞ := by
  rw [← lintegral_indicator (measurableSet_dominatedStrictTailEvent μ ν κ q)]
  apply lintegral_eq_top_of_ae_top_singularPart hμν
  filter_upwards [dominatedRatio_ae_eq_top_singularPart (ν := ν) hμκ] with x hx
  have hmem : x ∈ dominatedStrictTailEvent μ ν κ q := by
    change ENNReal.ofReal q < dominatedRatio μ ν κ x
    rw [hx]
    exact ENNReal.ofReal_lt_top
  rw [Set.indicator_of_mem hmem, hx, ENNReal.log_top, EReal.toENNReal_top,
    ENNReal.top_rpow_of_pos hk]

end SigmaFinite

section Finite

variable [IsFiniteMeasure μ] [IsFiniteMeasure ν] [SigmaFinite κ]

theorem tailEvent_ae_eq_dominatedStrictTailEvent (hμκ : μ ≪ κ) (hμν : μ ≪ ν)
    {q : ℝ} (hq : 0 < q) :
    tailEvent μ ν q =ᵐ[μ] dominatedStrictTailEvent μ ν κ q := by
  filter_upwards [exp_llr_ae_eq_dominatedRatio hμκ hμν] with x hx
  apply propext
  change (Real.log q < llr μ ν x) ↔ ENNReal.ofReal q < dominatedRatio μ ν κ x
  rw [← hx, ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _)]
  exact Real.log_lt_iff_lt_exp hq

/-- Every real power of the positive AC likelihood ratio has the expected exponential. -/
theorem exp_mul_llr_ae_eq_dominatedRatio_rpow (hμκ : μ ≪ κ) (hμν : μ ≪ ν) (δ : ℝ) :
    (fun x ↦ ENNReal.ofReal (Real.exp (δ * llr μ ν x))) =ᵐ[μ]
      fun x ↦ dominatedRatio μ ν κ x ^ δ := by
  filter_upwards [exp_llr_ae_eq_dominatedRatio hμκ hμν] with x hx
  rw [← hx, ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul,
    mul_comm (llr μ ν x) δ]

/-- Literal positive-power source tail, including all non-AC infinite cases. -/
theorem tailPower_eq_setLIntegral_dominatedRatio_rpow (hμκ : μ ≪ κ)
    {q δ : ℝ} (hq : 1 < q) (hδ : 0 < δ) :
    tailPower μ ν q δ =
      ∫⁻ x in dominatedStrictTailEvent μ ν κ q, dominatedRatio μ ν κ x ^ δ ∂μ := by
  by_cases hμν : μ ≪ ν
  · rw [tailPower_of_ac hμν]
    calc
      _ = ∫⁻ x in tailEvent μ ν q, dominatedRatio μ ν κ x ^ δ ∂μ :=
        lintegral_congr_ae
          (ae_restrict_of_ae (exp_mul_llr_ae_eq_dominatedRatio_rpow hμκ hμν δ))
      _ = _ := setLIntegral_congr
        (tailEvent_ae_eq_dominatedStrictTailEvent hμκ hμν (zero_lt_one.trans hq))
  · rw [tailPower_of_not_ac hμν,
      setLIntegral_dominatedRatio_rpow_eq_top_of_not_ac hμκ hμν q hδ]

/-- On a tail above one the extended log's nonnegative part is the genuine log. -/
theorem log_rpow_ae_eq_dominatedRatio_log_rpow_on_tail
    (hμκ : μ ≪ κ) (hμν : μ ≪ ν) {q : ℝ} (hq : 1 < q) (k : ℝ) :
    ∀ᵐ x ∂μ, x ∈ tailEvent μ ν q →
      ENNReal.ofReal ((llr μ ν x) ^ k) =
        (ENNReal.log (dominatedRatio μ ν κ x)).toENNReal ^ k := by
  filter_upwards [exp_llr_ae_eq_dominatedRatio hμκ hμν] with x hx hmem
  rw [← hx, ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp,
    EReal.real_coe_toENNReal,
    ENNReal.ofReal_rpow_of_pos (llr_pos_of_mem_tailEvent hq hmem)]

/-- Literal positive-log source tail; no infinite ratio is converted to a real zero. -/
theorem tailLogMoment_eq_setLIntegral_dominatedRatio_log_rpow (hμκ : μ ≪ κ)
    {q k : ℝ} (hq : 1 < q) (hk : 0 < k) :
    tailLogMoment μ ν q k =
      ∫⁻ x in dominatedStrictTailEvent μ ν κ q,
        (ENNReal.log (dominatedRatio μ ν κ x)).toENNReal ^ k ∂μ := by
  by_cases hμν : μ ≪ ν
  · rw [tailLogMoment_of_ac hμν]
    calc
      _ = ∫⁻ x in tailEvent μ ν q,
          (ENNReal.log (dominatedRatio μ ν κ x)).toENNReal ^ k ∂μ :=
        setLIntegral_congr_fun_ae (measurableSet_tailEvent μ ν q)
          (log_rpow_ae_eq_dominatedRatio_log_rpow_on_tail hμκ hμν hq k)
      _ = _ := setLIntegral_congr
        (tailEvent_ae_eq_dominatedStrictTailEvent hμκ hμν (zero_lt_one.trans hq))
  · rw [tailLogMoment_of_not_ac hμν,
      setLIntegral_dominatedRatio_log_rpow_eq_top_of_not_ac hμκ hμν q hk]

end Finite

end Hellinger.Comparison
