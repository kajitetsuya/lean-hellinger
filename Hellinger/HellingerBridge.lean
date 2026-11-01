/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.Definitions
public import Mathlib.Tactic.FunProp

/-! An absolutely-continuous representation of the canonical squared Hellinger distance.
The reference measure remains `ν`, including its mass on the zero set of `dμ/dν`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace Hellinger

/-- Degree-one homogeneity of the squared square-root distance, including zero factors. -/
theorem sqrt_sub_sqrt_sq_homogeneous {a b t : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 ≤ t) :
    t * (Real.sqrt a - Real.sqrt b) ^ 2 =
      (Real.sqrt (a * t) - Real.sqrt (b * t)) ^ 2 := by
  rw [Real.sqrt_mul ha, Real.sqrt_mul hb, ← sub_mul, mul_pow, Real.sq_sqrt ht]
  exact mul_comm _ _

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

/-- For finite measures with `μ ≪ ν`, canonical squared Hellinger distance is the
integral of `(√(dμ/dν)-1)²` under `ν`. No reverse absolute continuity is required.
In particular, points with zero `dμ/dν` retain their `ν` contribution. -/
theorem hellingerSq_eq_lintegral_of_ac [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) :
    hellingerSq μ ν =
      ∫⁻ x, ENNReal.ofReal ((Real.sqrt ((μ.rnDeriv ν x).toReal) - 1) ^ 2) ∂ν := by
  let ρ : Measure α := pairMeasure μ ν
  let : IsFiniteMeasure ρ := by
    dsimp [ρ, pairMeasure]
    infer_instance
  let f : α → ℝ≥0∞ := fun x ↦ ENNReal.ofReal
    ((Real.sqrt ((μ.rnDeriv ρ x).toReal) - Real.sqrt ((ν.rnDeriv ρ x).toReal)) ^ 2)
  have hμρ : μ ≪ ρ := Measure.AbsolutelyContinuous.rfl.add_right ν
  have hνρ : ν ≪ ρ := Measure.AbsolutelyContinuous.rfl.add_right' μ
  have hρν : ρ ≪ ν := hμν.add_left Measure.AbsolutelyContinuous.rfl
  have hf : Measurable f := by
    dsimp [f]
    fun_prop
  have hμchain : μ.rnDeriv ρ * ρ.rnDeriv ν =ᵐ[ν] μ.rnDeriv ν :=
    Measure.rnDeriv_mul_rnDeriv hμρ
  have hνchain : ν.rnDeriv ρ * ρ.rnDeriv ν =ᵐ[ν] ν.rnDeriv ν :=
    Measure.rnDeriv_mul_rnDeriv hνρ
  change ∫⁻ x, f x ∂ρ = _
  rw [← lintegral_rnDeriv_mul hρν hf.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [hμchain, hνchain, ν.rnDeriv_self, Measure.rnDeriv_lt_top ρ ν]
    with x hμ hν hself htop
  have hμreal : (μ.rnDeriv ρ x).toReal * (ρ.rnDeriv ν x).toReal =
      (μ.rnDeriv ν x).toReal := by
    simpa only [Pi.mul_apply, ENNReal.toReal_mul] using congrArg ENNReal.toReal hμ
  have hνreal : (ν.rnDeriv ρ x).toReal * (ρ.rnDeriv ν x).toReal = 1 := by
    simpa only [Pi.mul_apply, ENNReal.toReal_mul, hself, ENNReal.toReal_one] using
      congrArg ENNReal.toReal hν
  change ρ.rnDeriv ν x * ENNReal.ofReal
    ((Real.sqrt ((μ.rnDeriv ρ x).toReal) - Real.sqrt ((ν.rnDeriv ρ x).toReal)) ^ 2) = _
  rw [← ENNReal.ofReal_toReal htop.ne, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  rw [sqrt_sub_sqrt_sq_homogeneous ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    ENNReal.toReal_nonneg, hμreal, hνreal, Real.sqrt_one]

end Hellinger
