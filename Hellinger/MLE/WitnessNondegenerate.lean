/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.MLE.Witness
public import Hellinger.MLE.EntropyCorollaries
public import Hellinger.MLE.DensityBridge
public import Hellinger.MLE.ProbabilityRates

/-!
A non-degenerate non-vacuity witness: on the two-point space `Bool` with counting measure,
the sieve `{p₀, q}` with `p₀ = 1{true}`, `q = 1{false}` and `h(p₀, q) = √2`, rate
`δ_n = n^{-1/2}`, and `pn = phat = p₀`. Every hypothesis of the MLE statements holds, and
some annulus is nonempty, so (D) is not satisfied only through empty
shells. (D) is obtained from (H) through `annularTail_of_powerEnvelope`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Hellinger.MLE

universe v

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-! ### General facts used by the witness -/

omit [MeasurableSpace 𝒳] in
theorem logLikDeficit_self {n : ℕ} (x : Fin n → 𝒳) (p : 𝒳 → ℝ≥0) : logLikDeficit x p p = 0 := by
  unfold logLikDeficit
  split_ifs <;> simp

theorem entropyIntegrand_le_two {N : ℕ∞} (hN : N ≤ 2) : entropyIntegrand N ≤ 2 := by
  have hne : N ≠ ⊤ := ne_top_of_le_ne_top (by simp) hN
  have hle : N.toNat ≤ 2 := by simpa using ENat.toNat_le_toNat hN (by simp)
  have hlog : Real.log (N.toNat : ℝ) ≤ Real.log 2 := by
    rcases Nat.eq_zero_or_pos N.toNat with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]; exact (Real.log_pos (by norm_num)).le
    · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hle)
  have hlog2 : Real.log 2 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  simp only [entropyIntegrand, hne, ite_false]
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [show (2 : ℝ) = Real.sqrt 4 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (by linarith)

/-- A class inside a two-element set of finite-mass functions has `J̃(r) ≤ 2r`. -/
theorem hBracketingIntegral_le_of_subset_pair (μ : Measure 𝒳) {f g : 𝒳 → ℝ≥0}
    (hf : Measurable f) (hg : Measurable g) (hfin : ∫⁻ x, (f x : ℝ≥0∞) ∂μ < ∞)
    (hgin : ∫⁻ x, (g x : ℝ≥0∞) ∂μ < ∞) {F : Set (𝒳 → ℝ≥0)} (hF : F ⊆ {f, g}) (r : ℝ) :
    hBracketingIntegral μ r F ≤ ENNReal.ofReal (2 * r) := by
  have hN : ∀ ε ∈ Ioc (0 : ℝ) r,
      entropyIntegrand (hBracketingNumber μ (ENNReal.ofReal ε) F) ≤ 2 := by
    intro ε hε
    apply entropyIntegrand_le_two
    refine iInf₂_le_of_le 2 ⟨![(f, f), (g, g)], ?_, ?_⟩ (by simp)
    · intro i
      fin_cases i
      · refine ⟨⟨hf, hf, hfin, hfin⟩, le_rfl, ?_⟩
        show hdist μ f f < _
        rw [hdist_self]; exact ENNReal.ofReal_pos.mpr hε.1
      · refine ⟨⟨hg, hg, hgin, hgin⟩, le_rfl, ?_⟩
        show hdist μ g g < _
        rw [hdist_self]; exact ENNReal.ofReal_pos.mpr hε.1
    · intro h hh
      rcases hF hh with rfl | rfl
      · exact ⟨0, le_rfl, le_rfl⟩
      · exact ⟨1, le_rfl, le_rfl⟩
  calc hBracketingIntegral μ r F
      ≤ ∫⁻ _ in Ioc (0 : ℝ) r, 2 := setLIntegral_mono measurable_const hN
    _ = ENNReal.ofReal (2 * r) := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ENNReal.ofReal_mul (by norm_num)]
        simp

/-- Constant maps on the one-point probability space are independent. -/
theorem iIndepFun_const_punit {ι β : Type*} [MeasurableSpace β] (f : ι → PUnit.{v + 1} → β) :
    iIndepFun f (Measure.dirac PUnit.unit) := by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro T sets _
  have hmeas : ∀ s : Set PUnit.{v + 1}, MeasurableSet s := fun _ ↦ Subsingleton.measurableSet
  rw [Measure.dirac_apply' _ (hmeas _)]
  simp_rw [Measure.dirac_apply' _ (hmeas _)]
  by_cases h : ∀ i ∈ T, PUnit.unit ∈ f i ⁻¹' sets i
  · rw [indicator_of_mem (by simpa using h)]
    exact (Finset.prod_eq_one fun i hi ↦ indicator_of_mem (h i hi) _).symm
  · push Not at h
    obtain ⟨i, hi, hni⟩ := h
    rw [indicator_of_notMem (by simp only [mem_iInter, not_forall]; exact ⟨i, hi, hni⟩),
      Finset.prod_eq_zero hi (indicator_of_notMem hni _)]

/-! ### The two-point model -/

/-- `p₀ = 1{true}`. -/
def boolP₀ : Bool → ℝ≥0 := fun b ↦ if b then 1 else 0

/-- `q = 1{false}`. -/
def boolQ : Bool → ℝ≥0 := fun b ↦ if b then 0 else 1

/-- `δ_n = n^{-1/2}`. -/
noncomputable def boolRate : ℕ → ℝ := fun n ↦ (Real.sqrt n)⁻¹

theorem boolP₀_isProbDensity : IsProbDensity Measure.count boolP₀ :=
  ⟨measurable_of_countable _, by simp [lintegral_count, boolP₀]⟩

theorem boolQ_isProbDensity : IsProbDensity Measure.count boolQ :=
  ⟨measurable_of_countable _, by simp [lintegral_count, boolQ]⟩

theorem law_boolP₀ : law Measure.count boolP₀ = Measure.dirac true := by
  ext s hs
  rw [law_apply _ _ hs, Measure.dirac_apply' _ hs, ← lintegral_indicator hs, lintegral_count]
  by_cases ht : true ∈ s <;> simp [boolP₀, indicator, ht]

theorem hdist_boolP₀_boolQ : hdist Measure.count boolP₀ boolQ = ENNReal.ofReal (Real.sqrt 2) := by
  have h2 : hellingerFunSq Measure.count boolP₀ boolQ = ENNReal.ofReal 2 := by
    simp only [hellingerFunSq, lintegral_count, tsum_bool, boolP₀, boolQ]
    norm_num
  rw [hdist, h2, ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by norm_num), Real.sqrt_eq_rpow]

theorem rate_boolRate {n : ℕ} : rate boolRate n = (Real.sqrt n)⁻¹ := max_self _

/-- The non-degenerate witness. -/
theorem nonvacuous_nondegenerate :
    MLEHypotheses Measure.count (Measure.dirac PUnit.unit : Measure PUnit.{v + 1})
      (fun _ _ ↦ true) boolP₀ (fun _ ↦ {boolP₀, boolQ}) (fun _ ↦ boolP₀)
      (fun _ _ ↦ boolP₀) boolRate 0 0 ∧
    AnnularTailCondition Measure.count boolP₀ (fun _ ↦ {boolP₀, boolQ}) boolRate ∧
    PowerEnvelopeCondition Measure.count boolP₀ (fun _ ↦ {boolP₀, boolQ}) boolRate ∧
    WholeSieveCondition Measure.count (fun _ ↦ {boolP₀, boolQ}) boolRate ∧
    (∀ n, Measurable fun ω : PUnit.{v + 1} ↦
      hdist Measure.count boolP₀ ((fun (_ : ℕ) (_ : PUnit.{v + 1}) ↦ boolP₀) n ω)) ∧
    boolQ ∈ annulus Measure.count boolP₀ {boolP₀, boolQ} (shellScale (rate boolRate 1) 0) := by
  have hfinP : ∫⁻ x, (boolP₀ x : ℝ≥0∞) ∂Measure.count < ∞ := by
    rw [boolP₀_isProbDensity.lintegral_eq_one]; exact ENNReal.one_lt_top
  have hfinQ : ∫⁻ x, (boolQ x : ℝ≥0∞) ∂Measure.count < ∞ := by
    rw [boolQ_isProbDensity.lintegral_eq_one]; exact ENNReal.one_lt_top
  have hpair : ∀ F ⊆ ({boolP₀, boolQ} : Set (Bool → ℝ≥0)), ∀ r,
      hBracketingIntegral Measure.count r F ≤ ENNReal.ofReal (2 * r) := fun F hF r ↦
    hBracketingIntegral_le_of_subset_pair _ (measurable_of_countable _)
      (measurable_of_countable _) hfinP hfinQ hF r
  have hsq : ∀ n : ℕ, 1 ≤ n → Real.sqrt n * (Real.sqrt n)⁻¹ = 1 := fun n hn ↦
    mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hn))
  have hH : PowerEnvelopeCondition Measure.count boolP₀ (fun _ ↦ {boolP₀, boolQ}) boolRate := by
    refine ⟨2, 1, by norm_num, le_rfl, by norm_num, 1, fun n hn r _ ↦ ?_⟩
    refine (hpair _ (fun p hp ↦ hp.1) r).trans (le_of_eq ?_)
    congr 1
    rw [rate_boolRate, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_one,
      mul_assoc 2, hsq n hn, mul_one]
  refine ⟨⟨inferInstance, boolP₀_isProbDensity, fun _ ↦ measurable_const,
      iIndepFun_const_punit _, fun _ ↦ ?_, ?_, fun _ ↦ Or.inl rfl, fun _ _ ↦ Or.inl rfl,
      fun _ ↦ inv_nonneg.mpr (Real.sqrt_nonneg _), le_rfl, le_rfl,
      ⟨0, fun _ _ ↦ by simp⟩, ⟨0, fun n _ ↦ ?_⟩, ?_⟩,
    annularTail_of_powerEnvelope _ _ _ _ hH, hH, ?_, fun _ ↦ measurable_const, ?_⟩
  · rw [law_boolP₀, Measure.map_const]; simp
  · rintro n p (rfl | rfl)
    · exact boolP₀_isProbDensity
    · exact boolQ_isProbDensity
  · rw [law_boolP₀, tailLogMoment_self _ (by norm_num)]; exact zero_le
  · refine OPStar.of_le (fun n ↦ sq_nonneg _) le_rfl ⟨0, fun n _ ω ↦ ?_⟩
    rw [logLikDeficit_self]; exact zero_le
  · refine ⟨2, by norm_num, 1, fun n hn ↦ ?_⟩
    refine (hpair _ subset_rfl _).trans (le_of_eq ?_)
    rw [rate_boolRate, sq, ← mul_assoc, mul_assoc 2, hsq n hn, mul_one]
  · refine ⟨Or.inr rfl, ?_, ?_⟩ <;>
      simp only [rate_boolRate, shellScale, Nat.cast_one, Real.sqrt_one, inv_one, pow_zero,
        mul_one, hdist_boolP₀_boolQ]
    · exact (ENNReal.ofReal_lt_ofReal_iff (Real.sqrt_pos.mpr (by norm_num))).mpr
        (by rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num))
    · exact le_rfl

end Hellinger.MLE
