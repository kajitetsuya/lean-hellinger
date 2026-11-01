/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.MLE.Defs

/-!
Linearity and a deterministic bound for the empirical process
`𝔾_n g = √n (ℙ_n g - P g)` at a sample point `x : Fin n → 𝒳`. Measurability is in
`MgfMaximal.measurable_empiricalProcess`.
-/

@[expose] public section

open MeasureTheory Set Finset
open scoped ENNReal NNReal

namespace Hellinger.VdW

open Hellinger.MLE

variable {𝒳 : Type*} [MeasurableSpace 𝒳] (P : Measure 𝒳) {n : ℕ}

theorem empiricalProcess_add {g h : 𝒳 → ℝ} (hg : Integrable g P) (hh : Integrable h P)
    (x : Fin n → 𝒳) :
    empiricalProcess P (g + h) x = empiricalProcess P g x + empiricalProcess P h x := by
  simp only [empiricalProcess, Pi.add_apply, Finset.sum_add_distrib, integral_add hg hh]
  ring

theorem empiricalProcess_sub {g h : 𝒳 → ℝ} (hg : Integrable g P) (hh : Integrable h P)
    (x : Fin n → 𝒳) :
    empiricalProcess P (g - h) x = empiricalProcess P g x - empiricalProcess P h x := by
  simp only [empiricalProcess, Pi.sub_apply, Finset.sum_sub_distrib, integral_sub hg hh]
  ring

theorem empiricalProcess_zero (x : Fin n → 𝒳) : empiricalProcess P (0 : 𝒳 → ℝ) x = 0 := by
  simp [empiricalProcess]

theorem empiricalProcess_finset_sum {ι : Type*} (s : Finset ι) {g : ι → 𝒳 → ℝ}
    (hg : ∀ i ∈ s, Integrable (g i) P) (x : Fin n → 𝒳) :
    empiricalProcess P (∑ i ∈ s, g i) x = ∑ i ∈ s, empiricalProcess P (g i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [empiricalProcess_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      empiricalProcess_add P (hg a (mem_insert_self a s))
        (integrable_finsetSum' s fun i hi ↦ hg i (mem_insert_of_mem hi)),
      ih fun i hi ↦ hg i (mem_insert_of_mem hi)]

/-- Equal functions have equal empirical processes. -/
theorem empiricalProcess_congr {g h : 𝒳 → ℝ} (hgh : g = h) (x : Fin n → 𝒳) :
    empiricalProcess P g x = empiricalProcess P h x := by rw [hgh]

/-- A function bounded by `c` has `|𝔾_n g| ≤ 2 √n c` at every sample point. -/
theorem abs_empiricalProcess_le_of_bounded [IsProbabilityMeasure P] {g : 𝒳 → ℝ} {c : ℝ}
    (hc : 0 ≤ c) (hgc : ∀ y, |g y| ≤ c) (x : Fin n → 𝒳) :
    |empiricalProcess P g x| ≤ 2 * Real.sqrt n * c := by
  have hmean : |(n : ℝ)⁻¹ * ∑ i, g (x i)| ≤ c := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; simpa using hc
    have hn : (0 : ℝ) < n := by exact_mod_cast hpos
    rw [abs_mul, abs_inv, Nat.abs_cast]
    calc (n : ℝ)⁻¹ * |∑ i, g (x i)| ≤ (n : ℝ)⁻¹ * ∑ _i : Fin n, c := by
          gcongr
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ hgc (x i))
      _ = c := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
  have hint : |∫ y, g y ∂P| ≤ c := by
    have := norm_integral_le_of_norm_le_const (μ := P) (f := g) (C := c)
      (Filter.Eventually.of_forall fun y ↦ by rw [Real.norm_eq_abs]; exact hgc y)
    simpa [Real.norm_eq_abs] using this
  unfold empiricalProcess
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc Real.sqrt n * |(n : ℝ)⁻¹ * ∑ i, g (x i) - ∫ y, g y ∂P|
      ≤ Real.sqrt n * (c + c) := by
        gcongr
        exact (abs_sub _ _).trans (add_le_add hmean hint)
    _ = 2 * Real.sqrt n * c := by ring

end Hellinger.VdW
