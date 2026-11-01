/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.HellingerBridge

/-! The canonical squared Hellinger distance agrees with its density formula under
every sigma-finite reference measure dominating the two finite measures.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace Hellinger

variable {α : Type*} {mα : MeasurableSpace α} {μ ν κ : Measure α}

/-- The density representation of squared Hellinger distance under any sigma-finite
common dominator. No absolute continuity between `μ` and `ν`, or from `κ` back to
either measure, is required. The dominator may be chosen separately for each pair. -/
theorem hellingerSq_eq_lintegral_of_dominated
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [SigmaFinite κ]
    (hμκ : μ ≪ κ) (hνκ : ν ≪ κ) :
    hellingerSq μ ν =
      ∫⁻ x, ENNReal.ofReal
        ((Real.sqrt ((μ.rnDeriv κ x).toReal) -
          Real.sqrt ((ν.rnDeriv κ x).toReal)) ^ 2) ∂κ := by
  let ρ : Measure α := pairMeasure μ ν
  let : IsFiniteMeasure ρ := by
    dsimp [ρ, pairMeasure]
    infer_instance
  let f : α → ℝ≥0∞ := fun x ↦ ENNReal.ofReal
    ((Real.sqrt ((μ.rnDeriv ρ x).toReal) - Real.sqrt ((ν.rnDeriv ρ x).toReal)) ^ 2)
  have hμρ : μ ≪ ρ := Measure.AbsolutelyContinuous.rfl.add_right ν
  have hνρ : ν ≪ ρ := Measure.AbsolutelyContinuous.rfl.add_right' μ
  have hρκ : ρ ≪ κ := hμκ.add_left hνκ
  have hf : Measurable f := by
    dsimp [f]
    fun_prop
  have hμchain : μ.rnDeriv ρ * ρ.rnDeriv κ =ᵐ[κ] μ.rnDeriv κ :=
    Measure.rnDeriv_mul_rnDeriv hμρ
  have hνchain : ν.rnDeriv ρ * ρ.rnDeriv κ =ᵐ[κ] ν.rnDeriv κ :=
    Measure.rnDeriv_mul_rnDeriv hνρ
  change ∫⁻ x, f x ∂ρ = _
  rw [← lintegral_rnDeriv_mul hρκ hf.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [hμchain, hνchain, Measure.rnDeriv_lt_top ρ κ]
    with x hμ hν htop
  have hμreal : (μ.rnDeriv ρ x).toReal * (ρ.rnDeriv κ x).toReal =
      (μ.rnDeriv κ x).toReal := by
    simpa only [Pi.mul_apply, ENNReal.toReal_mul] using congrArg ENNReal.toReal hμ
  have hνreal : (ν.rnDeriv ρ x).toReal * (ρ.rnDeriv κ x).toReal =
      (ν.rnDeriv κ x).toReal := by
    simpa only [Pi.mul_apply, ENNReal.toReal_mul] using congrArg ENNReal.toReal hν
  change ρ.rnDeriv κ x * ENNReal.ofReal
    ((Real.sqrt ((μ.rnDeriv ρ x).toReal) - Real.sqrt ((ν.rnDeriv ρ x).toReal)) ^ 2) = _
  rw [← ENNReal.ofReal_toReal htop.ne, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  rw [sqrt_sub_sqrt_sq_homogeneous ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    ENNReal.toReal_nonneg, hμreal, hνreal]

end Hellinger
