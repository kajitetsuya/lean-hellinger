/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.Comparison.WSScalar
public import Hellinger.Comparison.PowerTail
public import Hellinger.TailMass
public import Hellinger.KLBounds
public import Hellinger.VariationBounds

/-! WS log-tail moments for every positive real order, including the zero-multiplier coefficient
and an arbitrary fixed ordinary cutoff greater than one. -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Hellinger.Comparison

/-- The tail-mass coefficient decreases when the cutoff increases. -/
theorem tailMassCoeff_antitone {a q : ℝ} (ha : 1 < a) (haq : a ≤ q) :
    tailMassCoeff q ≤ tailMassCoeff a := by
  have hq : 1 < q := ha.trans_le haq
  have hg : cutoffGap a ≤ cutoffGap q := by
    unfold cutoffGap
    have hh := Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans ha) haq
      (by norm_num : -(1 / 2 : ℝ) ≤ 0)
    linarith
  apply (inv_le_inv₀ (sq_pos_of_pos (cutoffGap_pos hq))
    (sq_pos_of_pos (cutoffGap_pos ha))).2
  exact pow_le_pow_left₀ (cutoffGap_pos ha).le hg 2

/-- The native WS cutoff has tail-mass coefficient at most the universal source one. -/
theorem ws_native_tailMassCoeff_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    tailMassCoeff (Real.exp (1 / δ)) ≤ tailMassCoeff (Real.exp 1) := by
  apply tailMassCoeff_antitone (Real.one_lt_exp_iff.mpr zero_lt_one)
  exact Real.exp_le_exp.mpr ((one_le_div hδ).mpr hδ1)

/-- The paper's displayed universal coefficient, as the tail geometry at `e`. -/
theorem tailMassCoeff_exp_one :
    tailMassCoeff (Real.exp 1) =
      Real.exp 1 / (Real.sqrt (Real.exp 1) - 1) ^ 2 := by
  have he : 0 < Real.exp 1 := Real.exp_pos _
  have hs : 0 < Real.sqrt (Real.exp 1) := Real.sqrt_pos.mpr he
  have hsne : Real.sqrt (Real.exp 1) - 1 ≠ 0 := by
    have hsq : 1 < Real.sqrt (Real.exp 1) := by
      apply (Real.lt_sqrt (by norm_num)).mpr
      simpa only [one_pow] using (Real.one_lt_exp_iff.mpr (zero_lt_one : (0 : ℝ) < 1))
    linarith
  unfold tailMassCoeff cutoffGap
  rw [Real.rpow_neg he.le, ← Real.sqrt_eq_rpow]
  field_simp [hs.ne', hsne]
  nlinarith [Real.sq_sqrt he.le]

/-- One coefficient works for all probability pairs satisfying the same WS multiplier. -/
noncomputable def wsMomentCoeff (q δ k M : ℝ) : ℝ :=
  δ ^ (-k) * (tailMassCoeff q + tailMassCoeff (Real.exp 1) * wsLogScale k M ^ k)

theorem wsMomentCoeff_pos {q δ k M : ℝ} (hq : 1 < q) (hδ : 0 < δ)
    (hk : 0 < k) : 0 < wsMomentCoeff q δ k M := by
  unfold wsMomentCoeff
  exact mul_pos (Real.rpow_pos_of_pos hδ _) (add_pos (tailMassCoeff_pos hq)
    (mul_pos (tailMassCoeff_pos (Real.one_lt_exp_iff.mpr zero_lt_one))
      (Real.rpow_pos_of_pos (wsLogScale_pos hk) _)))

theorem wsMomentCoeff_four (δ k M : ℝ) :
    wsMomentCoeff 4 δ k M = δ ^ (-k) *
      (4 + (Real.exp 1 / (Real.sqrt (Real.exp 1) - 1) ^ 2) * wsLogScale k M ^ k) := by
  rw [wsMomentCoeff, tailMassCoeff_four, tailMassCoeff_exp_one]

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α}

/-- Polynomial moments on a positive log tail are bounded by a positive exponential
moment, including divergent integrals. -/
theorem tailLogMoment_le_scaled_tailPower (hμν : μ ≪ ν)
    {a k s : ℝ} (ha : 1 < a) (hk : 0 < k) (hs : 0 < s) :
    tailLogMoment μ ν a k ≤ ENNReal.ofReal ((k / (Real.exp 1 * s)) ^ k) *
      tailPower μ ν a s := by
  rw [tailLogMoment_of_ac hμν, tailPower_of_ac hμν]
  calc
    _ ≤ ∫⁻ x in tailEvent μ ν a,
        ENNReal.ofReal ((k / (Real.exp 1 * s)) ^ k) *
          ENNReal.ofReal (Real.exp (s * llr μ ν x)) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (measurableSet_tailEvent μ ν a)] with x hx
      rw [← ENNReal.ofReal_mul (Real.rpow_pos_of_pos
        (div_pos hk (mul_pos (Real.exp_pos 1) hs)) k).le]
      exact ENNReal.ofReal_le_ofReal
        (rpow_le_scaled_exp hk hs (llr_pos_of_mem_tailEvent ha hx).le)
    _ = _ := by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- The tail moment of the log-likelihood ratio between two cutoffs is bounded by the
ordinary-tail mass. The band is empty automatically when its endpoints are reversed. -/
theorem tailLogMoment_le_tailLogMoment_add_mass [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) {q a k : ℝ} (hq : 1 < q) (ha : 1 < a) (hk : 0 < k) :
    tailLogMoment μ ν q k ≤ tailLogMoment μ ν a k +
      ENNReal.ofReal ((Real.log a) ^ k * tailMassCoeff q) * hellingerSq μ ν := by
  let f : α → ℝ≥0∞ := fun x ↦ ENNReal.ofReal ((llr μ ν x) ^ k)
  have hband : (∫⁻ x in tailEvent μ ν q \ tailEvent μ ν a, f x ∂μ) ≤
      ENNReal.ofReal ((Real.log a) ^ k) * μ (tailEvent μ ν q) := by
    calc
      _ ≤ ∫⁻ _x in tailEvent μ ν q \ tailEvent μ ν a,
          ENNReal.ofReal ((Real.log a) ^ k) ∂μ := by
        apply setLIntegral_mono measurable_const
        intro x hx
        apply ENNReal.ofReal_le_ofReal
        exact Real.rpow_le_rpow (llr_pos_of_mem_tailEvent hq hx.1).le
          (le_of_not_gt hx.2) hk.le
      _ ≤ ∫⁻ _x in tailEvent μ ν q, ENNReal.ofReal ((Real.log a) ^ k) ∂μ :=
        lintegral_mono_set Set.sdiff_subset
      _ = _ := setLIntegral_const _ _
  rw [tailLogMoment_of_ac hμν, tailLogMoment_of_ac hμν]
  change (∫⁻ x in tailEvent μ ν q, f x ∂μ) ≤ (∫⁻ x in tailEvent μ ν a, f x ∂μ) + _
  calc
    _ = (∫⁻ x in tailEvent μ ν q ∩ tailEvent μ ν a, f x ∂μ) +
        (∫⁻ x in tailEvent μ ν q \ tailEvent μ ν a, f x ∂μ) :=
      (lintegral_inter_add_sdiff f (tailEvent μ ν q) (measurableSet_tailEvent μ ν a)).symm
    _ ≤ (∫⁻ x in tailEvent μ ν a, f x ∂μ) +
        (∫⁻ x in tailEvent μ ν q \ tailEvent μ ν a, f x ∂μ) :=
      add_le_add (lintegral_mono_set Set.inter_subset_right) le_rfl
    _ ≤ (∫⁻ x in tailEvent μ ν a, f x ∂μ) +
        ENNReal.ofReal ((Real.log a) ^ k) * μ (tailEvent μ ν q) :=
      add_le_add le_rfl hband
    _ ≤ (∫⁻ x in tailEvent μ ν a, f x ∂μ) +
        ENNReal.ofReal ((Real.log a) ^ k) *
          (ENNReal.ofReal (tailMassCoeff q) * hellingerSq μ ν) :=
      add_le_add le_rfl (mul_le_mul_right
        (tailEvent_mass_le_tailMassCoeff_mul_hellingerSq hμν hq) _)
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_pos_of_pos (Real.log_pos ha) k).le]

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Quantitative WS moment bound on its native high-log tail, for all real `k>0`. -/
theorem tailLogMoment_native_le_of_ws {δ k M : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hk : 0 < k) (hM : 0 ≤ M)
    (hWS : tailPower μ ν (Real.exp (1 / δ)) δ ≤ ENNReal.ofReal M * hellingerSq μ ν) :
    tailLogMoment μ ν (Real.exp (1 / δ)) k ≤
      ENNReal.ofReal (δ ^ (-k) * tailMassCoeff (Real.exp 1) * wsLogScale k M ^ k) *
        hellingerSq μ ν := by
  have hnative : 1 < Real.exp (1 / δ) := Real.one_lt_exp_iff.mpr (one_div_pos.mpr hδ)
  have hμν : μ ≪ ν := by
    by_contra h
    have hfin : ENNReal.ofReal M * hellingerSq μ ν < ∞ :=
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hellingerSq_ne_top μ ν)).lt_top
    simpa only [tailPower_of_not_ac h, lt_self_iff_false] using hWS.trans_lt hfin
  let r := k / wsLogScale k M
  have hr : 0 < r := (ws_exponent_pos_le_one (M := M) hk).1
  have hr1 : r ≤ 1 := (ws_exponent_pos_le_one (M := M) hk).2
  have hs : 0 < r * δ := mul_pos hr hδ
  have hsδ : r * δ ≤ δ := by nlinarith
  have hratio : r * δ / δ = r := by field_simp [hδ.ne']
  have hsmall := tailPower_le_of_le_mul_hellinger hnative hs hsδ hWS
  rw [hratio] at hsmall
  have hJ : ENNReal.ofReal (interpolationCoeff (Real.exp (1 / δ))) ≤
      ENNReal.ofReal (tailMassCoeff (Real.exp 1)) :=
    ENNReal.ofReal_le_ofReal (ws_native_tailMassCoeff_le hδ hδ1)
  have hsmall' : tailPower μ ν (Real.exp (1 / δ)) (r * δ) ≤
      ENNReal.ofReal (tailMassCoeff (Real.exp 1)) * ENNReal.ofReal (M ^ r) *
        hellingerSq μ ν := by
    rw [← ENNReal.ofReal_rpow_of_nonneg hM hr.le]
    exact hsmall.trans (mul_le_mul' (mul_le_mul' hJ le_rfl) le_rfl)
  have hscalar := ws_optimized_scalar hk hδ hM
  change (k / (Real.exp 1 * (r * δ))) ^ k * M ^ r ≤
    δ ^ (-k) * wsLogScale k M ^ k at hscalar
  have hD : 0 < tailMassCoeff (Real.exp 1) :=
    tailMassCoeff_pos (Real.one_lt_exp_iff.mpr zero_lt_one)
  have hC : 0 ≤ (k / (Real.exp 1 * (r * δ))) ^ k :=
    (Real.rpow_pos_of_pos (div_pos hk (mul_pos (Real.exp_pos 1) hs)) k).le
  calc
    _ ≤ ENNReal.ofReal ((k / (Real.exp 1 * (r * δ))) ^ k) *
        tailPower μ ν (Real.exp (1 / δ)) (r * δ) :=
      tailLogMoment_le_scaled_tailPower hμν hnative hk hs
    _ ≤ ENNReal.ofReal ((k / (Real.exp 1 * (r * δ))) ^ k) *
        (ENNReal.ofReal (tailMassCoeff (Real.exp 1)) * ENNReal.ofReal (M ^ r) *
          hellingerSq μ ν) := mul_le_mul_right hsmall' _
    _ = ENNReal.ofReal (((k / (Real.exp 1 * (r * δ))) ^ k * M ^ r) *
        tailMassCoeff (Real.exp 1)) * hellingerSq μ ν := by
      rw [ENNReal.ofReal_mul (mul_nonneg hC (Real.rpow_nonneg hM _)),
        ENNReal.ofReal_mul hC]
      ac_rfl
    _ ≤ _ := by
      apply mul_le_mul_left
      apply ENNReal.ofReal_le_ofReal
      simpa only [mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_right hscalar hD.le

/-- Exact quantitative WS log-tail bound at an arbitrary fixed ordinary cutoff.
No absolute-continuity hypothesis or finite moment of the log-likelihood ratio is added. -/
theorem tailLogMoment_le_of_ws {q δ k M : ℝ} (hq : 1 < q) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hk : 0 < k) (hM : 0 ≤ M)
    (hWS : tailPower μ ν (Real.exp (1 / δ)) δ ≤ ENNReal.ofReal M * hellingerSq μ ν) :
    tailLogMoment μ ν q k ≤ ENNReal.ofReal (wsMomentCoeff q δ k M) * hellingerSq μ ν := by
  have hnative : 1 < Real.exp (1 / δ) := Real.one_lt_exp_iff.mpr (one_div_pos.mpr hδ)
  have hμν : μ ≪ ν := by
    by_contra h
    have hfin : ENNReal.ofReal M * hellingerSq μ ν < ∞ :=
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hellingerSq_ne_top μ ν)).lt_top
    simpa only [tailPower_of_not_ac h, lt_self_iff_false] using hWS.trans_lt hfin
  have hband := tailLogMoment_le_tailLogMoment_add_mass hμν hq hnative hk
  have hinv : (1 / δ) ^ k = δ ^ (-k) := by
    rw [one_div, Real.inv_rpow hδ.le, Real.rpow_neg hδ.le]
  rw [Real.log_exp, hinv] at hband
  have hD : 0 < tailMassCoeff (Real.exp 1) :=
    tailMassCoeff_pos (Real.one_lt_exp_iff.mpr zero_lt_one)
  have hpow : 0 < δ ^ (-k) := Real.rpow_pos_of_pos hδ _
  have hscale : 0 < wsLogScale k M ^ k := Real.rpow_pos_of_pos (wsLogScale_pos hk) _
  calc
    _ ≤ tailLogMoment μ ν (Real.exp (1 / δ)) k +
        ENNReal.ofReal (δ ^ (-k) * tailMassCoeff q) * hellingerSq μ ν := hband
    _ ≤ ENNReal.ofReal (δ ^ (-k) * tailMassCoeff (Real.exp 1) * wsLogScale k M ^ k) *
        hellingerSq μ ν + ENNReal.ofReal (δ ^ (-k) * tailMassCoeff q) * hellingerSq μ ν :=
      add_le_add (tailLogMoment_native_le_of_ws hδ hδ1 hk hM hWS) le_rfl
    _ = ENNReal.ofReal (δ ^ (-k) * tailMassCoeff (Real.exp 1) * wsLogScale k M ^ k +
        δ ^ (-k) * tailMassCoeff q) * hellingerSq μ ν := by
      rw [ENNReal.ofReal_add (by positivity) (mul_pos hpow (tailMassCoeff_pos hq)).le,
        add_mul]
    _ = _ := by
      congr 2
      unfold wsMomentCoeff
      ring

/-- The printed cutoff-four constant, including the coefficient at `M=0`. -/
theorem tailLogMoment_four_le_of_ws {δ k M : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hk : 0 < k) (hM : 0 ≤ M)
    (hWS : tailPower μ ν (Real.exp (1 / δ)) δ ≤ ENNReal.ofReal M * hellingerSq μ ν) :
    tailLogMoment μ ν 4 k ≤ ENNReal.ofReal (δ ^ (-k) *
      (4 + (Real.exp 1 / (Real.sqrt (Real.exp 1) - 1) ^ 2) *
        (Real.log (max (Real.exp k) M)) ^ k)) * hellingerSq μ ν := by
  simpa only [wsMomentCoeff_four, wsLogScale] using
    (tailLogMoment_le_of_ws (μ := μ) (ν := ν) (q := 4) (by norm_num) hδ hδ1 hk hM hWS)

/-- WS implies the quantitative Kullback–Leibler divergence bound without assuming the divergence is
finite. -/
theorem kl_le_of_ws {q δ M : ℝ} (hq : 1 < q) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hM : 0 ≤ M)
    (hWS : tailPower μ ν (Real.exp (1 / δ)) δ ≤ ENNReal.ofReal M * hellingerSq μ ν) :
    kl μ ν ≤ ENNReal.ofReal (klUpperCoeff q + wsMomentCoeff q δ 1 M) * hellingerSq μ ν := by
  calc
    _ ≤ ENNReal.ofReal (klUpperCoeff q) * hellingerSq μ ν + tailLogMoment μ ν q 1 :=
      kl_le_hellinger_add_tailLogMoment hq
    _ ≤ ENNReal.ofReal (klUpperCoeff q) * hellingerSq μ ν +
        ENNReal.ofReal (wsMomentCoeff q δ 1 M) * hellingerSq μ ν :=
      add_le_add le_rfl (tailLogMoment_le_of_ws hq hδ hδ1 zero_lt_one hM hWS)
    _ = _ := by
      rw [ENNReal.ofReal_add (klUpperCoeff_pos q).le (wsMomentCoeff_pos hq hδ zero_lt_one).le,
        add_mul]

/-- WS implies every real-order Kullback–Leibler variation bound in the full source range `k>=2`. -/
theorem logMoment_le_of_ws {q δ k M : ℝ} (hq : 1 < q) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hk : 2 ≤ k) (hM : 0 ≤ M)
    (hWS : tailPower μ ν (Real.exp (1 / δ)) δ ≤ ENNReal.ofReal M * hellingerSq μ ν) :
    logMoment μ ν k ≤
      ENNReal.ofReal (variationUpperCoeff q k + wsMomentCoeff q δ k M) * hellingerSq μ ν := by
  have hk0 : 0 < k := (by norm_num : (0 : ℝ) < 2).trans_le hk
  calc
    _ ≤ ENNReal.ofReal (variationUpperCoeff q k) * hellingerSq μ ν + tailLogMoment μ ν q k :=
      logMoment_le_hellinger_add_tailLogMoment hq hk
    _ ≤ ENNReal.ofReal (variationUpperCoeff q k) * hellingerSq μ ν +
        ENNReal.ofReal (wsMomentCoeff q δ k M) * hellingerSq μ ν :=
      add_le_add le_rfl (tailLogMoment_le_of_ws hq hδ hδ1 hk0 hM hWS)
    _ = _ := by
      rw [ENNReal.ofReal_add (variationUpperCoeff_pos hq hk0).le
        (wsMomentCoeff_pos hq hδ hk0).le, add_mul]

/-- One WS multiplier chosen before the family supplies one log-tail multiplier. -/
theorem uniform_tailLogMoment_of_uniform_ws (μ : Measure α) [IsProbabilityMeasure μ]
    (F : Set (Measure α)) (hF : ∀ ν ∈ F, IsProbabilityMeasure ν)
    {q δ k : ℝ} (hq : 1 < q) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hk : 0 < k)
    (hWS : UniformHellingerBound μ F (fun ν ↦ tailPower μ ν (Real.exp (1 / δ)) δ)) :
    UniformHellingerBound μ F (fun ν ↦ tailLogMoment μ ν q k) := by
  obtain ⟨M, hM⟩ := hWS
  refine (uniformHellingerBound_iff_real μ F _).2
    ⟨wsMomentCoeff q δ k M, (wsMomentCoeff_pos hq hδ hk).le, ?_⟩
  intro ν hν
  let : IsProbabilityMeasure ν := hF ν hν
  exact tailLogMoment_le_of_ws hq hδ hδ1 hk M.property (by simpa using hM ν hν)

/-- Family WS implies one uniform Kullback–Leibler divergence multiplier, with no nonempty-family
assumption. -/
theorem uniform_kl_of_uniform_ws (μ : Measure α) [IsProbabilityMeasure μ]
    (F : Set (Measure α)) (hF : ∀ ν ∈ F, IsProbabilityMeasure ν)
    {q δ : ℝ} (hq : 1 < q) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hWS : UniformHellingerBound μ F (fun ν ↦ tailPower μ ν (Real.exp (1 / δ)) δ)) :
    UniformHellingerBound μ F (fun ν ↦ kl μ ν) := by
  obtain ⟨M, hM⟩ := hWS
  refine (uniformHellingerBound_iff_real μ F _).2
    ⟨klUpperCoeff q + wsMomentCoeff q δ 1 M,
      add_nonneg (klUpperCoeff_pos q).le (wsMomentCoeff_pos hq hδ zero_lt_one).le, ?_⟩
  intro ν hν
  let : IsProbabilityMeasure ν := hF ν hν
  exact kl_le_of_ws hq hδ hδ1 M.property (by simpa using hM ν hν)

/-- Family WS implies one uniform real-order Kullback–Leibler variation multiplier. -/
theorem uniform_logMoment_of_uniform_ws (μ : Measure α) [IsProbabilityMeasure μ]
    (F : Set (Measure α)) (hF : ∀ ν ∈ F, IsProbabilityMeasure ν)
    {q δ k : ℝ} (hq : 1 < q) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hk : 2 ≤ k)
    (hWS : UniformHellingerBound μ F (fun ν ↦ tailPower μ ν (Real.exp (1 / δ)) δ)) :
    UniformHellingerBound μ F (fun ν ↦ logMoment μ ν k) := by
  have hk0 : 0 < k := (by norm_num : (0 : ℝ) < 2).trans_le hk
  obtain ⟨M, hM⟩ := hWS
  refine (uniformHellingerBound_iff_real μ F _).2
    ⟨variationUpperCoeff q k + wsMomentCoeff q δ k M,
      add_nonneg (variationUpperCoeff_pos hq hk0).le (wsMomentCoeff_pos hq hδ hk0).le, ?_⟩
  intro ν hν
  let : IsProbabilityMeasure ν := hF ν hν
  exact logMoment_le_of_ws hq hδ hδ1 hk M.property (by simpa using hM ν hν)

/-- The joint Kullback–Leibler divergence and full real-order Kullback–Leibler variation
consequence of the same WS bound. -/
theorem kl_and_logMoment_le_of_ws {q δ M : ℝ} (hq : 1 < q) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hM : 0 ≤ M)
    (hWS : tailPower μ ν (Real.exp (1 / δ)) δ ≤ ENNReal.ofReal M * hellingerSq μ ν) :
    (kl μ ν ≤ ENNReal.ofReal (klUpperCoeff q + wsMomentCoeff q δ 1 M) * hellingerSq μ ν) ∧
    ∀ k : ℝ, 2 ≤ k → logMoment μ ν k ≤
      ENNReal.ofReal (variationUpperCoeff q k + wsMomentCoeff q δ k M) * hellingerSq μ ν :=
  ⟨kl_le_of_ws hq hδ hδ1 hM hWS,
    fun _ hk ↦ logMoment_le_of_ws hq hδ hδ1 hk hM hWS⟩

end Hellinger.Comparison
