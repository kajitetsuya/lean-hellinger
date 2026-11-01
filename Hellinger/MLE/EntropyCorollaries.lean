/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.MLE.Statements
public import Hellinger.MLE.Bracketing
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
The sufficient entropy conditions: the power envelope (H) implies the annular tail condition
(D), and the whole-sieve bound (G) implies (H) with `β = 1`. Neither implication uses any
probabilistic hypothesis or the maximal inequality.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace Hellinger.MLE

universe u

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-- The normalized power-envelope bound on shell `j`:
`C √n a^{2-β} (√2 s_j)^β / (√n s_j²) = C (√2)^β ρ^j` with `ρ = (√2)^{β-2}`. -/
theorem powerEnvelope_shell_ratio (C β : ℝ) {a : ℝ} (ha : 0 < a) {m : ℝ} (hm : 0 < m)
    (j : ℕ) :
    C * m * a ^ (2 - β) * (Real.sqrt 2 * shellScale a j) ^ β / (m * shellScale a j ^ 2) =
      C * Real.sqrt 2 ^ β * (Real.sqrt 2 ^ (β - 2)) ^ j := by
  set t := Real.sqrt 2 with ht
  have ht0 : 0 < t := Real.sqrt_pos.mpr (by norm_num)
  have htj : 0 < t ^ j := pow_pos ht0 j
  have hs : 0 < shellScale a j := shellScale_pos ha j
  have hsq : shellScale a j ^ 2 = shellScale a j ^ (2 : ℝ) := (Real.rpow_two _).symm
  rw [Real.mul_rpow ht0.le hs.le, hsq]
  have hdiv : shellScale a j ^ β / shellScale a j ^ (2 : ℝ) = shellScale a j ^ (β - 2) :=
    (Real.rpow_sub hs β 2).symm
  have hsplit : shellScale a j ^ (β - 2) = (t ^ j) ^ (β - 2) * a ^ (β - 2) :=
    Real.mul_rpow htj.le ha.le
  have hpow : (t ^ j) ^ (β - 2) = (t ^ (β - 2)) ^ j := by
    rw [← Real.rpow_natCast_mul ht0.le, mul_comm, Real.rpow_mul_natCast ht0.le]
  have ha1 : a ^ (2 - β) * a ^ (β - 2) = 1 := by
    rw [← Real.rpow_add ha]; simp
  calc C * m * a ^ (2 - β) * (t ^ β * shellScale a j ^ β) / (m * shellScale a j ^ (2 : ℝ))
      = C * t ^ β * (a ^ (2 - β) * (shellScale a j ^ β / shellScale a j ^ (2 : ℝ))) := by
        field_simp
    _ = C * t ^ β * (t ^ (β - 2)) ^ j := by
        rw [hdiv, hsplit, hpow]
        linear_combination (C * t ^ β * (t ^ (β - 2)) ^ j) * ha1

/-- Under (H), every shell term is bounded by a geometric sequence, uniformly in `n ≥ n₀`. -/
theorem shellTerm_le_of_powerEnvelope {μ : Measure 𝒳} {p₀ : 𝒳 → ℝ≥0}
    {S : ℕ → Set (𝒳 → ℝ≥0)} {δ : ℕ → ℝ} {C β : ℝ} {n₀ : ℕ}
    (hH : ∀ n ≥ n₀, ∀ r : ℝ, rate δ n ≤ r →
      hBracketingIntegral μ r (hBall μ p₀ (S n) r) ≤
        ENNReal.ofReal (C * Real.sqrt n * rate δ n ^ (2 - β) * r ^ β))
    {n : ℕ} (hn : n ≥ max n₀ 1) (j : ℕ) :
    shellTerm μ p₀ (S n) n (rate δ n) j ≤
      ENNReal.ofReal (C * Real.sqrt 2 ^ β * (Real.sqrt 2 ^ (β - 2)) ^ j) := by
  have hn1 : 1 ≤ n := le_of_max_le_right hn
  have ha : 0 < rate δ n := rate_pos δ hn1
  have hm : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn1)
  have hs : 0 < shellScale (rate δ n) j := shellScale_pos ha j
  have hr : rate δ n ≤ Real.sqrt 2 * shellScale (rate δ n) j :=
    (le_shellScale ha.le j).trans (le_mul_of_one_le_left hs.le
      (by rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)))
  have hden : 0 < Real.sqrt n * shellScale (rate δ n) j ^ 2 := by positivity
  unfold shellTerm
  calc annulusEntropy μ p₀ (S n) (shellScale (rate δ n) j) /
        ENNReal.ofReal (Real.sqrt n * shellScale (rate δ n) j ^ 2)
      ≤ ENNReal.ofReal (C * Real.sqrt n * rate δ n ^ (2 - β) *
          (Real.sqrt 2 * shellScale (rate δ n) j) ^ β) /
        ENNReal.ofReal (Real.sqrt n * shellScale (rate δ n) j ^ 2) := by
        gcongr
        exact (annulusEntropy_le μ p₀ (S n) _).trans (hH n (le_of_max_le_left hn) _ hr)
    _ = ENNReal.ofReal (C * Real.sqrt 2 ^ β * (Real.sqrt 2 ^ (β - 2)) ^ j) := by
        rw [← ENNReal.ofReal_div_of_pos hden, powerEnvelope_shell_ratio C β ha hm j]

/-- A geometric tail in `ℝ≥0∞`: `Σ_{j ≥ k} A ρ^j ≤ A σ^k / (1 - σ)` with `σ = √ρ`. -/
theorem tsum_ite_geometric_le {A ρ : ℝ} (hA : 0 ≤ A) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (k : ℕ) :
    ∑' j, (if k ≤ j then ENNReal.ofReal (A * ρ ^ j) else 0) ≤
      ENNReal.ofReal (A * Real.sqrt ρ ^ k) * (1 - ENNReal.ofReal (Real.sqrt ρ))⁻¹ := by
  set σ := Real.sqrt ρ with hσ
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg ρ
  have hσ1 : σ ≤ 1 := by
    rw [hσ, show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hρ1.le
  have hρσ : ρ = σ ^ 2 := (Real.sq_sqrt hρ0).symm
  rw [← ENNReal.tsum_geometric, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun j ↦ ?_
  split_ifs with hkj
  · rw [← ENNReal.ofReal_pow hσ0, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hρσ, ← pow_mul, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hA
    rw [two_mul, pow_add]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hσ0 hσ1 hkj) (by positivity)
  · exact zero_le

/-- (H) implies (D). -/
theorem annularTail_of_powerEnvelope : PowerEnvelopeImpliesAnnularStatement.{u} := by
  rintro 𝒳 _ μ p₀ S δ ⟨C, β, hC, -, hβ2, n₀, hH⟩
  intro ε hε
  set ρ : ℝ := Real.sqrt 2 ^ (β - 2) with hρ
  have hρ0 : 0 ≤ ρ := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hρ1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg
    (by rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num))
    (by linarith)
  set A : ℝ := C * Real.sqrt 2 ^ β with hA
  have hA0 : 0 ≤ A := mul_nonneg hC.le (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
  set σ := Real.sqrt ρ with hσ
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg ρ
  have hσ1 : σ < 1 := by
    rw [hσ, show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt hρ0 hρ1
  -- choose `k` with `A σ^k / (1 - σ) ≤ ε`
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show 0 < ε * (1 - σ) / (A + 1) by
    have : 0 < 1 - σ := by linarith
    positivity) hσ1
  refine ⟨k, max n₀ 1, fun n hn ↦ ?_⟩
  calc shellTail μ p₀ S δ n k
      ≤ ∑' j, (if k ≤ j then ENNReal.ofReal (A * ρ ^ j) else 0) := by
        unfold shellTail
        refine ENNReal.tsum_le_tsum fun j ↦ ?_
        split_ifs with h₁ h₂
        · exact shellTerm_le_of_powerEnvelope hH hn j
        · exact absurd h₁.1 h₂
        · exact zero_le
        · exact le_rfl
    _ ≤ ENNReal.ofReal (A * σ ^ k) * (1 - ENNReal.ofReal σ)⁻¹ :=
        tsum_ite_geometric_le hA0 hρ0 hρ1 k
    _ ≤ ENNReal.ofReal ε := by
        have h1σ : 0 < 1 - σ := by linarith
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hσ0, ← ENNReal.ofReal_inv_of_pos h1σ,
          ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← div_eq_mul_inv, div_le_iff₀ h1σ]
        have hAk : A * σ ^ k ≤ (A + 1) * σ ^ k :=
          mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hσ0 k)
        calc A * σ ^ k ≤ (A + 1) * σ ^ k := hAk
          _ ≤ (A + 1) * (ε * (1 - σ) / (A + 1)) := by gcongr
          _ = ε * (1 - σ) := by field_simp

/-- (G) implies (H) with `β = 1`, by class inclusion and fixed-class rescaling at the
positive radius `a_n`. -/
theorem powerEnvelope_of_wholeSieve : WholeSieveImpliesPowerEnvelopeStatement.{u} := by
  rintro 𝒳 _ μ p₀ S δ ⟨C, hC, n₀, hG⟩
  refine ⟨C, 1, hC, le_rfl, by norm_num, max n₀ 1, fun n hn r hr ↦ ?_⟩
  have ha : 0 < rate δ n := rate_pos δ (le_of_max_le_right hn)
  have hc : 1 ≤ r / rate δ n := (one_le_div ha).mpr hr
  calc hBracketingIntegral μ r (hBall μ p₀ (S n) r)
      ≤ hBracketingIntegral μ r (S n) := hBracketingIntegral_mono_set μ (hBall_subset _ _ _ _)
    _ = hBracketingIntegral μ (r / rate δ n * rate δ n) (S n) := by
        rw [div_mul_cancel₀ _ ha.ne']
    _ ≤ ENNReal.ofReal (r / rate δ n) * hBracketingIntegral μ (rate δ n) (S n) :=
        hBracketingIntegral_mul_le μ (S n) hc _
    _ ≤ ENNReal.ofReal (r / rate δ n) *
          ENNReal.ofReal (C * Real.sqrt n * rate δ n ^ 2) := by
        gcongr; exact hG n (le_of_max_le_left hn)
    _ = ENNReal.ofReal (C * Real.sqrt n * rate δ n ^ (2 - 1 : ℝ) * r ^ (1 : ℝ)) := by
        rw [← ENNReal.ofReal_mul (div_nonneg (ha.le.trans hr) ha.le)]
        congr 1
        norm_num
        field_simp

end Hellinger.MLE
