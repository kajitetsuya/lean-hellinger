/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.MLE.Bracketing
public import Hellinger.MLE.Mixture

/-!
Deterministic ingredients of the shell (peeling) argument: the Hellinger bound `h ≤ √2`, the
coverage of `{h(p₀, p) > s_k}` by the active annuli `j ≥ k` with `s_j < √2`, and
`Σ u_j² ≤ (Σ u_j)²` in extended values.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace Hellinger.MLE

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-- `h(p, q) ≤ √2` between probability densities. -/
theorem hdist_le_sqrt_two (μ : Measure 𝒳) {p q : 𝒳 → ℝ≥0} (hp : IsProbDensity μ p)
    (hq : IsProbDensity μ q) : hdist μ p q ≤ ENNReal.ofReal (Real.sqrt 2) := by
  unfold hdist
  calc hellingerFunSq μ p q ^ (1 / 2 : ℝ) ≤ (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (hellingerFunSq_le_two μ hp hq) (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt 2) := by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
          ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by norm_num), Real.sqrt_eq_rpow]

/-- Shell coverage: if `s_k < h ≤ √2` then `h` lies in an annulus `s_j < h ≤ √2 s_j` with
`j ≥ k` and `s_j < √2`. Strict lower and weak upper endpoints. -/
theorem exists_shell {a : ℝ} (ha : 0 < a) {k : ℕ} {h : ℝ≥0∞}
    (hk : ENNReal.ofReal (shellScale a k) < h) (h2 : h ≤ ENNReal.ofReal (Real.sqrt 2)) :
    ∃ j, k ≤ j ∧ shellScale a j < Real.sqrt 2 ∧ ENNReal.ofReal (shellScale a j) < h ∧
      h ≤ ENNReal.ofReal (Real.sqrt 2 * shellScale a j) := by
  classical
  have ht : 1 < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hex : ∃ j, k ≤ j ∧ h ≤ ENNReal.ofReal (Real.sqrt 2 * shellScale a j) := by
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt a⁻¹ ht
    refine ⟨max k m, le_max_left _ _, h2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    have hpow : Real.sqrt 2 ^ m ≤ Real.sqrt 2 ^ max k m :=
      pow_le_pow_right₀ ht.le (le_max_right _ _)
    have : 1 ≤ shellScale a (max k m) := by
      unfold shellScale
      have h1 : 1 < Real.sqrt 2 ^ m * a := by
        have := mul_lt_mul_of_pos_right hm ha; rwa [inv_mul_cancel₀ ha.ne'] at this
      nlinarith
    nlinarith [Real.sqrt_nonneg 2]
  obtain ⟨hkj, hjup⟩ := Nat.find_spec hex
  have hlow : ENNReal.ofReal (shellScale a (Nat.find hex)) < h := by
    rcases hkj.eq_or_lt with heq | hlt
    · rw [← heq]; exact hk
    · obtain ⟨i, hi⟩ : ∃ i, Nat.find hex = i + 1 := ⟨Nat.find hex - 1, by omega⟩
      have hmin := Nat.find_min hex (show i < Nat.find hex by omega)
      simp only [not_and, not_le] at hmin
      rw [hi, shellScale_succ]
      exact hmin (by omega)
  refine ⟨Nat.find hex, hkj, ?_, hlow, hjup⟩
  have := hlow.trans_le h2
  exact (ENNReal.ofReal_lt_ofReal_iff (Real.sqrt_pos.mpr (by norm_num))).mp this

/-- `Σ u_j² ≤ (Σ u_j)²` in `ℝ≥0∞`. -/
theorem tsum_sq_le_sq_tsum (u : ℕ → ℝ≥0∞) : ∑' j, u j ^ 2 ≤ (∑' j, u j) ^ 2 := by
  calc ∑' j, u j ^ 2 = ∑' j, u j * u j := by simp_rw [sq]
    _ ≤ ∑' j, u j * ∑' i, u i := ENNReal.tsum_le_tsum fun j ↦
        mul_le_mul_of_nonneg_left (ENNReal.le_tsum j) zero_le
    _ = (∑' j, u j) ^ 2 := by rw [ENNReal.tsum_mul_right, sq]

end Hellinger.MLE
