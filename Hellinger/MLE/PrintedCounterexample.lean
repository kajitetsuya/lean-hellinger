/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.MLE.Witness
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Probability.HasLawExists

/-!
The printed entropy assumption of `thm:mle` is insufficient.

The printed theorem (source lines 1951-1970) assumes, besides the retained hypotheses, only the
one-radius bound `J̃_[](δ_n, 𝒫_{n,δ_n}, h) ≤ δ_n² √n`. `PrintedTheorem8Statement` states it with
that bound required for every `n`, and `printedTheorem8_false` refutes it.

The counterexample: `p₀` is the uniform density on `[0, 1)`, split into `2n` equal cells. For
`n` beyond a fixed threshold, the sieve contains `p₀` and every density equal to `3/2` on exactly
`n` cells and `1/2` on the other `n`. With `p_n = p₀` and `δ_n = n^{-1/2}`:

- every other sieve member is at the fixed Hellinger distance `gap` from `p₀`, where
  `gap² = 2 - √(3/2) - √(1/2)` (`gapSq_eq`);
- so the local class at radius `δ_n < gap` is `{p₀}`, whose bracketing integral is
  `δ_n = δ_n² √n`;
- the approximation and log-tail errors are zero;
- a sample of size `n` meets at most `n` cells, so the estimator that puts `3/2` on the cells
  holding observations has likelihood `(3/2)^n ≥ 1`, the likelihood of `p₀`.

The estimator is therefore an exact maximizer, yet its Hellinger error equals `gap` on every
sample point (`hdist_estimator`), so it is not `O_P^*(n^{-1/2})`. The error is constant, so the
failure does not depend on outer probability.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Hellinger.MLE

universe u v

/-- The printed `thm:mle`: the retained hypotheses and the one-radius entropy bound
`J̃_[](δ_n, 𝒫_{n,δ_n}, h) ≤ δ_n² √n` for every `n` give `h(p₀, p̂_n) = O_P^*(max(δ_n, n^{-1/2}))`.
It is false; see `printedTheorem8_false`. -/
def PrintedTheorem8Statement : Prop :=
  ∀ {𝒳 : Type u} [MeasurableSpace 𝒳] (μ : Measure 𝒳)
    {Ω : Type v} [MeasurableSpace Ω] (Pr : Measure Ω) (X : ℕ → Ω → 𝒳) (p₀ : 𝒳 → ℝ≥0)
    (S : ℕ → Set (𝒳 → ℝ≥0)) (pn : ℕ → 𝒳 → ℝ≥0) (phat : ℕ → Ω → 𝒳 → ℝ≥0)
    (δ : ℕ → ℝ) (D M : ℝ),
    MLEHypotheses μ Pr X p₀ S pn phat δ D M →
    (∀ n, hBracketingIntegral μ (δ n) (hBall μ p₀ (S n) (δ n)) ≤
      ENNReal.ofReal (δ n ^ 2 * Real.sqrt n)) →
    RateConclusion μ Pr p₀ phat δ

namespace PrintedCounterexample

/-! ### The reference measure and the cells -/

/-- Lebesgue measure on `[0, 1)`. -/
noncomputable def ref : Measure ℝ := volume.restrict (Ico 0 1)

instance : IsProbabilityMeasure ref := ⟨by simp [ref, Real.volume_Ico]⟩

/-- The uniform density `p₀`. -/
def unitDensity : ℝ → ℝ≥0 := fun _ ↦ 1

theorem unitDensity_isProbDensity : IsProbDensity ref unitDensity :=
  ⟨measurable_const, by simp [unitDensity, ref, Real.volume_Ico]⟩

theorem law_unitDensity : law ref unitDensity = ref := by
  simp [law, unitDensity]

/-- The cell index `⌊m x⌋` of `x` among `m` equal cells. -/
noncomputable def cell (m : ℕ) (x : ℝ) : ℕ := ⌊(m : ℝ) * x⌋₊

theorem measurable_cell (m : ℕ) : Measurable (cell m) :=
  Nat.measurable_floor.comp (measurable_const.mul measurable_id)

theorem mem_cellIco_iff {m : ℕ} (hm : 0 < m) (x : ℝ) (k : ℕ) :
    x ∈ Ico ((k : ℝ) / m) ((k + 1) / m) ↔ 0 ≤ x ∧ cell m x = k := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  constructor
  · rintro ⟨h1, h2⟩
    have hx : 0 ≤ x := le_trans (by positivity) h1
    refine ⟨hx, ?_⟩
    rw [cell, Nat.floor_eq_iff (by positivity)]
    constructor
    · rwa [div_le_iff₀ hm', mul_comm] at h1
    · rwa [lt_div_iff₀ hm', mul_comm] at h2
  · rintro ⟨hx, h⟩
    rw [cell, Nat.floor_eq_iff (by positivity)] at h
    constructor
    · rw [div_le_iff₀ hm', mul_comm]; exact h.1
    · rw [lt_div_iff₀ hm', mul_comm]; exact h.2

theorem Ico_eq_biUnion_cells {m : ℕ} (hm : 0 < m) :
    Ico (0 : ℝ) 1 = ⋃ k ∈ Finset.range m, Ico ((k : ℝ) / m) ((k + 1) / m) := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  ext x
  simp only [mem_iUnion, Finset.mem_range, exists_prop, mem_cellIco_iff hm]
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨cell m x, ?_, h0, rfl⟩
    rw [cell, Nat.floor_lt (by positivity)]
    calc (m : ℝ) * x < m * 1 := mul_lt_mul_of_pos_left h1 hm'
      _ = m := mul_one _
  · rintro ⟨k, hk, hx, hck⟩
    refine ⟨hx, ?_⟩
    have h2 : (m : ℝ) * x < m := by
      calc (m : ℝ) * x < (cell m x : ℝ) + 1 := Nat.lt_floor_add_one _
        _ = k + 1 := by rw [hck]
        _ ≤ m := by exact_mod_cast hk
    nlinarith

/-- A function of the cell index integrates over `[0, 1)` to the average of its values. -/
theorem lintegral_cells {m : ℕ} (hm : 0 < m) (g : ℝ → ℝ≥0∞) (f : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k)
    (hg : ∀ x ∈ Ico (0 : ℝ) 1, g x = ENNReal.ofReal (f (cell m x))) :
    ∫⁻ x in Ico (0 : ℝ) 1, g x = ENNReal.ofReal ((∑ k ∈ Finset.range m, f k) / m) := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hcell : ∀ k ∈ Finset.range m,
      ∫⁻ x in Ico ((k : ℝ) / m) ((k + 1) / m), g x = ENNReal.ofReal (f k / m) := by
    intro k hk
    rw [setLIntegral_congr_fun measurableSet_Ico (g := fun _ ↦ ENNReal.ofReal (f k)) ?_]
    · rw [setLIntegral_const, Real.volume_Ico, ← ENNReal.ofReal_mul (hf k)]
      congr 1
      field_simp
      ring
    · intro x hx
      have hmem : x ∈ Ico (0 : ℝ) 1 := by
        rw [Ico_eq_biUnion_cells hm]
        exact mem_biUnion (Finset.mem_coe.mpr hk) hx
      rw [hg x hmem, ((mem_cellIco_iff hm x k).1 hx).2]
  rw [Ico_eq_biUnion_cells hm, lintegral_biUnion_finset _ (fun _ _ ↦ measurableSet_Ico),
    Finset.sum_congr rfl hcell,
    ← ENNReal.ofReal_sum_of_nonneg (fun k _ ↦ div_nonneg (hf k) hm'.le), Finset.sum_div]
  intro i _ j _ hij
  rw [Function.onFun, Set.disjoint_left]
  intro x hi hj
  exact hij (((mem_cellIco_iff hm x i).1 hi).2.symm.trans ((mem_cellIco_iff hm x j).1 hj).2)

/-! ### The cell densities -/

/-- `3/2` on the cells in `A`, `1/2` on the others. -/
noncomputable def cellValue (A : Finset ℕ) (k : ℕ) : ℝ := if k ∈ A then 3 / 2 else 1 / 2

theorem cellValue_nonneg (A : Finset ℕ) (k : ℕ) : 0 ≤ cellValue A k := by
  unfold cellValue; split_ifs <;> norm_num

/-- The density equal to `3/2` on the cells in `A` and `1/2` on the other cells of `[0, 1)`.
It is `3/2` outside `[0, 1)`. That set is `ref`-null and observations fall there with
probability zero; the value only lets the likelihood comparison hold at every sample point
rather than almost surely. -/
noncomputable def cellDensity (m : ℕ) (A : Finset ℕ) (x : ℝ) : ℝ≥0 :=
  if x ∈ Ico (0 : ℝ) 1 then (cellValue A (cell m x)).toNNReal else (3 / 2 : ℝ).toNNReal

theorem measurable_cellDensity (m : ℕ) (A : Finset ℕ) : Measurable (cellDensity m A) :=
  Measurable.ite measurableSet_Ico
    ((measurable_from_nat (f := fun k ↦ (cellValue A k).toNNReal)).comp (measurable_cell m))
    measurable_const

/-- Summing a function of `cellValue A` over `2n` cells, `n` of them in `A`. -/
theorem sum_cellValue (φ : ℝ → ℝ) {n : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.range (2 * n))
    (hcard : A.card = n) :
    ∑ k ∈ Finset.range (2 * n), φ (cellValue A k) = n * φ (3 / 2) + n * φ (1 / 2) := by
  have hsplit : ∀ k, φ (cellValue A k) = if k ∈ A then φ (3 / 2) else φ (1 / 2) := by
    intro k; unfold cellValue; split_ifs <;> rfl
  simp_rw [hsplit]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have h1 : (Finset.range (2 * n)).filter (fun k ↦ k ∈ A) = A := by
    ext k
    simp only [Finset.mem_filter]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨hA h, h⟩⟩
  have h2 : ((Finset.range (2 * n)).filter (fun k ↦ k ∉ A)).card = n := by
    have := Finset.card_filter_add_card_filter_not
      (s := Finset.range (2 * n)) (fun k ↦ k ∈ A)
    rw [h1, hcard, Finset.card_range] at this
    omega
  rw [h1, hcard, h2]

theorem cellDensity_isProbDensity {n : ℕ} (hn : 0 < n) {A : Finset ℕ}
    (hA : A ⊆ Finset.range (2 * n)) (hcard : A.card = n) :
    IsProbDensity ref (cellDensity (2 * n) A) := by
  refine ⟨measurable_cellDensity _ _, ?_⟩
  unfold ref
  rw [lintegral_cells (m := 2 * n) (by omega) _ (cellValue A) (cellValue_nonneg A)]
  · rw [sum_cellValue (fun t ↦ t) hA hcard, ← ENNReal.ofReal_one]
    congr 1
    have hn' : (n : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  · intro x hx
    simp only [cellDensity, hx, ↓reduceIte]
    rfl

/-! ### The Hellinger gap -/

/-- `gap²`, the squared Hellinger distance from `p₀` to every other sieve member. -/
noncomputable def gapSq : ℝ := ((1 - Real.sqrt (3 / 2)) ^ 2 + (1 - Real.sqrt (1 / 2)) ^ 2) / 2

/-- The Hellinger distance from `p₀` to every other sieve member. -/
noncomputable def gap : ℝ := Real.sqrt gapSq

theorem gapSq_eq : gapSq = 2 - Real.sqrt (3 / 2) - Real.sqrt (1 / 2) := by
  have ha := Real.sq_sqrt (show (0 : ℝ) ≤ 3 / 2 by norm_num)
  have hb := Real.sq_sqrt (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  unfold gapSq
  rw [sub_sq, sub_sq, ha, hb]
  ring

theorem gapSq_pos : 0 < gapSq := by
  have hlt : Real.sqrt (1 / 2) < 1 := (Real.sqrt_lt' one_pos).mpr (by norm_num)
  have h2 : 0 < (1 - Real.sqrt (1 / 2)) ^ 2 := pow_pos (by linarith) 2
  have h1 := sq_nonneg (1 - Real.sqrt (3 / 2))
  unfold gapSq
  linarith

theorem gap_pos : 0 < gap := Real.sqrt_pos.mpr gapSq_pos

theorem hellingerFunSq_cellDensity {n : ℕ} (hn : 0 < n) {A : Finset ℕ}
    (hA : A ⊆ Finset.range (2 * n)) (hcard : A.card = n) :
    hellingerFunSq ref unitDensity (cellDensity (2 * n) A) = ENNReal.ofReal gapSq := by
  unfold hellingerFunSq ref
  rw [lintegral_cells (m := 2 * n) (by omega) _ (fun k ↦ (1 - Real.sqrt (cellValue A k)) ^ 2)
    (fun _ ↦ sq_nonneg _)]
  · rw [sum_cellValue (fun t ↦ (1 - Real.sqrt t) ^ 2) hA hcard]
    congr 1
    have hn' : (n : ℝ) ≠ 0 := by positivity
    unfold gapSq
    push_cast
    field_simp
  · intro x hx
    simp [unitDensity, cellDensity, hx, Real.coe_toNNReal _ (cellValue_nonneg _ _)]

theorem hdist_cellDensity {n : ℕ} (hn : 0 < n) {A : Finset ℕ}
    (hA : A ⊆ Finset.range (2 * n)) (hcard : A.card = n) :
    hdist ref unitDensity (cellDensity (2 * n) A) = ENNReal.ofReal gap := by
  rw [hdist, hellingerFunSq_cellDensity hn hA hcard,
    ENNReal.ofReal_rpow_of_nonneg gapSq_pos.le (by norm_num), gap, Real.sqrt_eq_rpow]

/-! ### The sieve and the estimator -/

/-- From this sample size on, `n^{-1/2} < gap`. -/
noncomputable def threshold : ℕ := ⌈gapSq⁻¹⌉₊ + 1

theorem threshold_pos : 0 < threshold := Nat.succ_pos _

theorem invSqrt_lt_gap {n : ℕ} (hn : threshold ≤ n) : (Real.sqrt n)⁻¹ < gap := by
  unfold threshold at hn
  have hlt : gapSq⁻¹ < n := by
    have h1 := Nat.le_ceil gapSq⁻¹
    have h2 : ((⌈gapSq⁻¹⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h2
    linarith
  have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (inv_nonneg.mpr gapSq_pos.le) hlt
  have hinv : (n : ℝ)⁻¹ < gapSq := by rwa [inv_lt_comm₀ hnpos gapSq_pos]
  rw [gap, Real.lt_sqrt (by positivity), inv_pow, Real.sq_sqrt hnpos.le]
  exact hinv

/-- The sieve: `{p₀}` below the threshold, and from it on `p₀` together with every density
equal to `3/2` on exactly `n` of the `2n` cells and `1/2` on the others. -/
def sieve (n : ℕ) : Set (ℝ → ℝ≥0) :=
  {p | p = unitDensity ∨ (threshold ≤ n ∧ ∃ A : Finset ℕ, A ⊆ Finset.range (2 * n) ∧
    A.card = n ∧ p = cellDensity (2 * n) A)}

theorem sieve_density (n : ℕ) : ∀ p ∈ sieve n, IsProbDensity ref p := by
  rintro p (rfl | ⟨hn, A, hA, hcard, rfl⟩)
  · exact unitDensity_isProbDensity
  · exact cellDensity_isProbDensity (threshold_pos.trans_le hn) hA hcard

/-- `n` observations meet at most `n` of the `2n` cells, so some `n` cells hold them all. -/
theorem exists_cover (n : ℕ) (x : Fin n → ℝ) :
    ∃ A : Finset ℕ, A ⊆ Finset.range (2 * n) ∧ A.card = n ∧
      ∀ i, x i ∈ Ico (0 : ℝ) 1 → cell (2 * n) (x i) ∈ A := by
  classical
  let B := (Finset.univ.filter (fun i ↦ x i ∈ Ico (0 : ℝ) 1)).image (fun i ↦ cell (2 * n) (x i))
  have hB : B ⊆ Finset.range (2 * n) := by
    intro k hk
    simp only [B, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    obtain ⟨i, hi, rfl⟩ := hk
    have hpos : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by
      have : 0 < n := Fin.pos i
      positivity
    rw [Finset.mem_range, cell, Nat.floor_lt (mul_nonneg (Nat.cast_nonneg _) hi.1)]
    calc ((2 * n : ℕ) : ℝ) * x i < ((2 * n : ℕ) : ℝ) * 1 := mul_lt_mul_of_pos_left hi.2 hpos
      _ = _ := mul_one _
  have hcardB : B.card ≤ n :=
    Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans (by simp))
  obtain ⟨A, hBA, hA, hcard⟩ := Finset.exists_subsuperset_card_eq hB hcardB (by simp; omega)
  exact ⟨A, hA, hcard, fun i hi ↦ hBA (Finset.mem_image.mpr ⟨i, by simpa using hi, rfl⟩)⟩

/-- The estimator: from the threshold on, `3/2` on `n` cells that hold every observation. -/
noncomputable def estimator {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ → ℝ≥0 :=
  if threshold ≤ n then cellDensity (2 * n) (exists_cover n (sample X n ω)).choose
  else unitDensity

theorem estimator_mem {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    estimator X n ω ∈ sieve n := by
  unfold estimator
  split_ifs with h
  · have hspec := (exists_cover n (sample X n ω)).choose_spec
    exact Or.inr ⟨h, _, hspec.1, hspec.2.1, rfl⟩
  · exact Or.inl rfl

/-- The Hellinger error of the estimator is `gap` on every sample point. -/
theorem hdist_estimator {Ω : Type*} (X : ℕ → Ω → ℝ) {n : ℕ} (hn : threshold ≤ n) (ω : Ω) :
    hdist ref unitDensity (estimator X n ω) = ENNReal.ofReal gap := by
  have hspec := (exists_cover n (sample X n ω)).choose_spec
  simp only [estimator, hn, ↓reduceIte]
  exact hdist_cellDensity (threshold_pos.trans_le hn) hspec.1 hspec.2.1

theorem cellDensity_of_cover {n : ℕ} {A : Finset ℕ} {x : Fin n → ℝ}
    (hcov : ∀ i, x i ∈ Ico (0 : ℝ) 1 → cell (2 * n) (x i) ∈ A) (i : Fin n) :
    cellDensity (2 * n) A (x i) = (3 / 2 : ℝ).toNNReal := by
  unfold cellDensity
  split_ifs with h
  · simp only [cellValue, hcov i h, ↓reduceIte]
  · rfl

/-- The estimator's likelihood is at least that of `p₀`, so its optimization deficit relative
to `p_n = p₀` is zero. -/
theorem logLikDeficit_estimator {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    logLikDeficit (sample X n ω) unitDensity (estimator X n ω) = 0 := by
  have h1 : likelihood (sample X n ω) unitDensity = 1 := by simp [likelihood, unitDensity]
  unfold estimator
  split_ifs with h
  · have hspec := (exists_cover n (sample X n ω)).choose_spec
    have hlik : likelihood (sample X n ω)
        (cellDensity (2 * n) (exists_cover n (sample X n ω)).choose) =
          (3 / 2 : ℝ).toNNReal ^ n := by
      unfold likelihood
      rw [Finset.prod_congr rfl (fun i _ ↦ cellDensity_of_cover hspec.2.2 i), Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]
    have hne : (3 / 2 : ℝ).toNNReal ^ n ≠ 0 :=
      pow_ne_zero _ (by rw [Ne, Real.toNNReal_eq_zero]; norm_num)
    rw [logLikDeficit, h1, hlik]
    simp only [one_ne_zero, hne, ↓reduceIte]
    apply ENNReal.ofReal_eq_zero.mpr
    apply div_nonpos_of_nonpos_of_nonneg _ (Nat.cast_nonneg _)
    rw [NNReal.coe_one, Real.log_one, NNReal.coe_pow,
      Real.coe_toNNReal _ (by norm_num : (0 : ℝ) ≤ 3 / 2), Real.log_pow]
    have hlog := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3 / 2)
    have := mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hlog
    linarith
  · simp [logLikDeficit, likelihood]

/-- No sieve density exceeds `3/2`. -/
theorem le_three_halves (n : ℕ) : ∀ p ∈ sieve n, ∀ x, p x ≤ (3 / 2 : ℝ).toNNReal := by
  rintro p (rfl | ⟨-, A, -, -, rfl⟩) x
  · show (1 : ℝ≥0) ≤ _
    rw [← Real.toNNReal_one]
    exact Real.toNNReal_le_toNNReal (by norm_num)
  · unfold cellDensity cellValue
    split_ifs
    · exact le_rfl
    · exact Real.toNNReal_le_toNNReal (by norm_num)
    · exact le_rfl

/-- The estimator is an exact global likelihood maximizer over the sieve, so the remark's
sufficient condition `ℙ_n log p̂_n ≥ sup_{p ∈ 𝒫_n} ℙ_n log p - O_P(δ_n²)` holds as well. -/
theorem estimator_isMLE {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    ∀ p ∈ sieve n, likelihood (sample X n ω) p ≤ likelihood (sample X n ω) (estimator X n ω) := by
  intro p hp
  unfold estimator
  split_ifs with h
  · have hspec := (exists_cover n (sample X n ω)).choose_spec
    unfold likelihood
    rw [Finset.prod_congr rfl (fun i _ ↦ cellDensity_of_cover hspec.2.2 i)]
    exact Finset.prod_le_prod (fun i _ ↦ le_three_halves n p hp _)
  · rcases hp with rfl | ⟨hn, -⟩
    · exact le_rfl
    · exact absurd hn h

/-! ### The entropy bound and the refutation -/

/-- `x⁻¹² x = x⁻¹`, including at `x = 0`. -/
theorem inv_sq_mul_self (x : ℝ) : x⁻¹ ^ 2 * x = x⁻¹ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · field_simp

theorem hBall_subset (n : ℕ) :
    hBall ref unitDensity (sieve n) (Real.sqrt n)⁻¹ ⊆ {unitDensity} := by
  rintro p ⟨hp, hd⟩
  rcases hp with rfl | ⟨hn, A, hA, hcard, rfl⟩
  · exact mem_singleton _
  · exfalso
    rw [hdist_cellDensity (threshold_pos.trans_le hn) hA hcard,
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at hd
    exact absurd hd (not_le.mpr (invSqrt_lt_gap hn))

/-- The printed entropy bound holds for every `n`, with equality for `n ≥ 1`. The local class
is contained in `{p₀}`, so the bound does not depend on whether bracket sizes are `< ε` or
`≤ ε`, nor on the factor `1/2` in the Hellinger normalization. -/
theorem printed_entropy (n : ℕ) :
    hBracketingIntegral ref (Real.sqrt n)⁻¹ (hBall ref unitDensity (sieve n) (Real.sqrt n)⁻¹) ≤
      ENNReal.ofReal ((Real.sqrt n)⁻¹ ^ 2 * Real.sqrt n) := by
  rw [inv_sq_mul_self]
  refine hBracketingIntegral_le_of_subset_singleton ref unitDensity_isProbDensity.measurable ?_
    (hBall_subset n) _
  rw [unitDensity_isProbDensity.lintegral_eq_one]
  exact ENNReal.one_lt_top

/-- All retained hypotheses of `thm:mle` hold in the counterexample, for any i.i.d. uniform
sample. -/
theorem hypotheses {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → ℝ) (hXm : ∀ i, Measurable (X i)) (hlaw : ∀ i, HasLaw (X i) ref Pr)
    (hind : iIndepFun X Pr) :
    MLEHypotheses ref Pr X unitDensity sieve (fun _ ↦ unitDensity) (estimator X)
      (fun n ↦ (Real.sqrt n)⁻¹) 0 0 where
  probability := inferInstance
  density := unitDensity_isProbDensity
  measurable_obs := hXm
  indep := hind
  law_obs i := by rw [law_unitDensity]; exact (hlaw i).map_eq
  sieve_density := sieve_density
  comparator_mem _ := Or.inl rfl
  estimator_mem := estimator_mem X
  rate_nonneg _ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  D_nonneg := le_rfl
  M_nonneg := le_rfl
  approx := ⟨0, fun n _ ↦ by simp⟩
  logTail := ⟨0, fun n _ ↦ by
    rw [law_unitDensity, tailLogMoment_self _ (by norm_num)]; exact zero_le⟩
  likelihood ε _ := ⟨1, one_pos, 0, fun n _ ↦ by simp [logLikDeficit_estimator]⟩

end PrintedCounterexample

open PrintedCounterexample in
/-- **The printed `thm:mle` is false.** In the counterexample every hypothesis holds, including
the one-radius entropy bound for every `n`, but the Hellinger error of an exact likelihood
maximizer stays at `gap > 0`. -/
theorem printedTheorem8_false : ¬ PrintedTheorem8Statement.{0, 0} := by
  intro hstmt
  obtain ⟨Ω, mΩ, Pr, X, hXm, hlaw, hind, hprob⟩ := exists_iid ℕ ref
  have hrate := hstmt ref Pr X unitDensity sieve _ (estimator X) _ 0 0
    (hypotheses Pr X hXm hlaw hind) printed_entropy
  obtain ⟨K, hK, N, hN⟩ := hrate (1 / 2) (by norm_num)
  obtain ⟨n₁, hn₁⟩ := exists_nat_gt ((K / gap) ^ 2)
  set n := max (max N threshold) n₁
  have hNn : N ≤ n := le_max_of_le_left (le_max_left _ _)
  have hTn : threshold ≤ n := le_max_of_le_left (le_max_right _ _)
  have hn₁n : n₁ ≤ n := le_max_right _ _
  have hnpos : (0 : ℝ) < n := by exact_mod_cast threshold_pos.trans_le hTn
  have hsmall : K * rate (fun n ↦ (Real.sqrt n)⁻¹) n < gap := by
    simp only [rate, max_self]
    rw [← div_eq_mul_inv, div_lt_iff₀ (Real.sqrt_pos.mpr hnpos)]
    have hK' : K / gap < Real.sqrt n := by
      rw [Real.lt_sqrt (div_nonneg hK.le gap_pos.le)]
      exact hn₁.trans_le (by exact_mod_cast hn₁n)
    rw [div_lt_iff₀ gap_pos] at hK'
    linarith
  have hall : {ω | ENNReal.ofReal (K * rate (fun n ↦ (Real.sqrt n)⁻¹) n) <
      hdist ref unitDensity (estimator X n ω)} = univ := by
    ext ω
    simp only [mem_ofPred_eq, mem_univ, iff_true]
    rw [hdist_estimator X hTn ω, ENNReal.ofReal_lt_ofReal_iff gap_pos]
    exact hsmall
  have hle : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 / 2) :=
    calc (1 : ℝ≥0∞) = Pr univ := measure_univ.symm
      _ = Pr {ω | ENNReal.ofReal (K * rate (fun n ↦ (Real.sqrt n)⁻¹) n) <
            hdist ref unitDensity (estimator X n ω)} := by rw [hall]
      _ ≤ ENNReal.ofReal (1 / 2) := hN n hNn
  rw [← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff (by norm_num)] at hle
  norm_num at hle

end Hellinger.MLE
