/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.MLE.Defs

/-!
Auxiliary facts for the proof of `External.VdW_2_14_18_prime`: a finite bracketing number is
attained by a cover of exactly that size, and the Bernstein size conditions convert between
the root `bernsteinFun` and its square `bernsteinFunSq`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Hellinger.VdW

open Hellinger.MLE

variable {𝒳 : Type*} {β : Type*} [Preorder β]
  {adm : (𝒳 → β) → (𝒳 → β) → Prop} {size : (𝒳 → β) → (𝒳 → β) → ℝ≥0∞}

/-- A finite bracketing number is attained: there is a cover with exactly that many brackets. -/
theorem exists_cover_of_bracketingNumber_ne_top {ε : ℝ≥0∞} {F : Set (𝒳 → β)}
    (h : bracketingNumber adm size ε F ≠ ⊤) :
    ∃ b : Fin (bracketingNumber adm size ε F).toNat → (𝒳 → β) × (𝒳 → β),
      IsBracketCover adm size ε F b := by
  classical
  have hS : ∃ n : ℕ, ∃ b : Fin n → (𝒳 → β) × (𝒳 → β), IsBracketCover adm size ε F b := by
    by_contra hne
    push Not at hne
    apply h
    refine le_antisymm le_top (le_iInf₂ fun n hn ↦ ?_)
    obtain ⟨b, hb⟩ := hn
    exact absurd hb (hne n b)
  have heq : bracketingNumber adm size ε F = (Nat.find hS : ℕ∞) := by
    refine le_antisymm (iInf₂_le (Nat.find hS) (Nat.find_spec hS)) (le_iInf₂ fun n hn ↦ ?_)
    exact Nat.cast_le.mpr (Nat.find_min' hS hn)
  rw [heq, ENat.toNat_natCast]
  exact Nat.find_spec hS

/-- `‖f‖_B ≤ δ ↔ ‖f‖²_B ≤ δ²` for `δ ≥ 0`. -/
theorem bernsteinFun_le_ofReal_iff {𝒳 : Type*} [MeasurableSpace 𝒳] (P : Measure 𝒳) (f : 𝒳 → ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    bernsteinFun P f ≤ ENNReal.ofReal δ ↔ bernsteinFunSq P f ≤ ENNReal.ofReal (δ ^ 2) := by
  unfold bernsteinFun
  rw [show ENNReal.ofReal δ = (ENNReal.ofReal (δ ^ 2)) ^ (1 / 2 : ℝ) by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
      Real.sqrt_sq hδ]]
  exact ENNReal.rpow_le_rpow_iff (by norm_num)

/-- `‖f‖_B < ε ↔ ‖f‖²_B < ε²` for `ε ≥ 0`. -/
theorem bernsteinFun_lt_ofReal_iff {𝒳 : Type*} [MeasurableSpace 𝒳] (P : Measure 𝒳) (f : 𝒳 → ℝ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    bernsteinFun P f < ENNReal.ofReal ε ↔ bernsteinFunSq P f < ENNReal.ofReal (ε ^ 2) := by
  unfold bernsteinFun
  rw [show ENNReal.ofReal ε = (ENNReal.ofReal (ε ^ 2)) ^ (1 / 2 : ℝ) by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
      Real.sqrt_sq hε]]
  exact ENNReal.rpow_lt_rpow_iff (by norm_num)

end Hellinger.VdW
