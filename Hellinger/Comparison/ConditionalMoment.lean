/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.Comparison.Definitions
public import Hellinger.Comparison.Cutoff
public import Hellinger.Comparison.PowerTail
public import Hellinger.TailMass
public import Hellinger.HellingerBasic
public import Mathlib.Topology.Order.DenselyOrdered

/-!
Native conditional-moment comparison at the source ordinary cutoff four.
The closed conditioning event retains its threshold atoms. The final infimum argument
uses approximate objective witnesses and continuity, and does not assert attainment.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace Hellinger.Comparison

/-- Exact square-root gap at the native CM cutoff. -/
theorem cutoffGap_cmCutoff {a : ℝ} (ha : 1 ≤ a) :
    cutoffGap (cmCutoff a) = (2 * a + 1)⁻¹ := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hbase : 0 < 1 + 1 / (2 * a) := by positivity
  have hsum : 0 < 2 * a + 1 := by linarith
  unfold cutoffGap
  rw [Real.rpow_neg (cmCutoff_pos ha).le, ← Real.sqrt_eq_rpow]
  rw [cmCutoff, Real.sqrt_sq hbase.le]
  field_simp [ha0.ne', hbase.ne', hsum.ne']
  ring

/-- The general tail-mass coefficient is exactly the printed native CM constant. -/
theorem tailMassCoeff_cmCutoff {a : ℝ} (ha : 1 ≤ a) :
    tailMassCoeff (cmCutoff a) = (2 * a + 1) ^ 2 := by
  unfold tailMassCoeff
  rw [cutoffGap_cmCutoff ha, ← inv_pow, inv_inv]

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

/-- Closed-tail geometry, including atoms at the threshold. -/
theorem closedTailEvent_mass_le_tailMassCoeff_mul_hellingerSq [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν)
    {t : ℝ} (ht : 1 < t) :
    μ (closedTailEvent μ ν t) ≤ ENNReal.ofReal (tailMassCoeff t) * hellingerSq μ ν := by
  classical
  calc
    μ (closedTailEvent μ ν t) =
        ∫⁻ x in closedTailEvent μ ν t, ENNReal.ofReal (1 : ℝ) ∂μ := by simp
    _ = ∫⁻ x, (closedTailEvent μ ν t).indicator
        (fun y ↦ ENNReal.ofReal ((μ.rnDeriv ν y).toReal * (1 : ℝ))) x ∂ν :=
      setLIntegral_ofReal_eq_lintegral_density hμν measurable_const
        (measurableSet_closedTailEvent μ ν t)
    _ ≤ ∫⁻ x, ENNReal.ofReal (tailMassCoeff t) *
        ENNReal.ofReal ((Real.sqrt ((μ.rnDeriv ν x).toReal) - 1) ^ 2) ∂ν := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [Set.indicator_apply]
      split_ifs with hx
      · have hxlog : Real.log t ≤ Real.log ((μ.rnDeriv ν x).toReal) := hx
        have hr1 : 1 < (μ.rnDeriv ν x).toReal :=
          (Real.log_pos_iff ENNReal.toReal_nonneg).mp ((Real.log_pos ht).trans_le hxlog)
        have htr := (Real.log_le_log_iff (lt_trans (by norm_num) ht)
          (lt_trans (by norm_num) hr1)).mp hxlog
        rw [← ENNReal.ofReal_mul (tailMassCoeff_pos ht).le]
        simp only [mul_one]
        exact ENNReal.ofReal_le_ofReal (tail_density_mass_le_hellinger_kernel ht htr)
      · exact zero_le
    _ = ENNReal.ofReal (tailMassCoeff t) * hellingerSq μ ν := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        ← hellingerSq_eq_lintegral_of_ac hμν]

/-- Source native-cutoff mass bound, with the exact coefficient `(2a+1)^2`. -/
theorem cm_event_mass_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) {a : ℝ} (ha : 1 ≤ a) :
    μ (closedTailEvent μ ν (cmCutoff a)) ≤
      ENNReal.ofReal ((2 * a + 1) ^ 2) * hellingerSq μ ν := by
  simpa only [tailMassCoeff_cmCutoff ha] using
    (closedTailEvent_mass_le_tailMassCoeff_mul_hellingerSq hμν (one_lt_cmCutoff ha))

/-- The conditional mean times event probability is the closed tail moment.
The null-event convention is handled before any division cancellation. -/
theorem closedTailMoment_eq_conditionalRatioMean_mul_mass [IsFiniteMeasure μ] (hμν : μ ≪ ν) (t : ℝ) :
    closedTailMoment μ ν t = conditionalRatioMean μ ν t * μ (closedTailEvent μ ν t) := by
  by_cases hnull : μ (closedTailEvent μ ν t) = 0
  · rw [conditionalRatioMean_of_null hμν hnull, zero_mul,
      closedTailMoment_of_ac hμν, Measure.restrict_eq_zero.mpr hnull]
    simp
  · rw [conditionalRatioMean_of_nonnull hμν hnull,
      ENNReal.div_mul_cancel hnull (measure_ne_top μ _)]

/-- A nonnull closed ratio tail at threshold at least one has conditional mean at least one. -/
theorem one_le_conditionalRatioMean [IsFiniteMeasure μ] (hμν : μ ≪ ν) {t : ℝ} (ht : 1 ≤ t)
    (hnull : μ (closedTailEvent μ ν t) ≠ 0) :
    1 ≤ conditionalRatioMean μ ν t := by
  have hmass : μ (closedTailEvent μ ν t) ≤ closedTailMoment μ ν t := by
    rw [closedTailMoment_of_ac hμν]
    calc
      μ (closedTailEvent μ ν t) = ∫⁻ _ in closedTailEvent μ ν t, (1 : ℝ≥0∞) ∂μ := by simp
      _ ≤ ∫⁻ x in closedTailEvent μ ν t, ENNReal.ofReal (Real.exp (llr μ ν x)) ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem (measurableSet_closedTailEvent μ ν t)] with x hx
        have htx := (mem_closedTailEvent_iff (zero_lt_one.trans_le ht) x).mp hx
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (ht.trans htx)
  rw [conditionalRatioMean_of_nonnull hμν hnull]
  exact (ENNReal.le_div_iff_mul_le (Or.inl hnull) (Or.inl (measure_ne_top μ _))).2
    (by simpa using hmass)

/-- The strict ordinary tail is inside every native CM closed event. -/
theorem tailPower_four_le_closedTailMoment (hμν : μ ≪ ν) {a : ℝ} (ha : 1 ≤ a) :
    tailPower μ ν 4 1 ≤ closedTailMoment μ ν (cmCutoff a) := by
  rw [tailPower_of_ac hμν, closedTailMoment_of_ac hμν]
  simp only [one_mul]
  apply lintegral_mono_set
  intro x hx
  have ht : cmCutoff a ≤ (4 : ℝ) := (cmCutoff_le_nine_fourths ha).trans (by norm_num)
  exact (Real.log_le_log (cmCutoff_pos ha) ht).trans (le_of_lt hx)

/-- Algebra behind the witness version of the source coefficient. No optimizer is needed. -/
theorem cm_witness_coefficient_le {a m : ℝ} (ha : 1 ≤ a) (hm : 1 ≤ m) :
    m * (2 * a + 1) ^ 2 ≤ (2 * (a * m) + 1) ^ 2 := by
  have ha2 : 1 ≤ a ^ 2 := by nlinarith
  have hprod : 1 ≤ a ^ 2 * m := by
    nlinarith [mul_le_mul_of_nonneg_right ha2 (zero_le_one.trans hm)]
  have hnonneg : 0 ≤ (m - 1) * (4 * a ^ 2 * m - 1) := by
    apply mul_nonneg (sub_nonneg.mpr hm)
    nlinarith
  nlinarith

/-- Every finite native objective gives the printed coefficient with that objective
in place of the infimum. Null conditioning events give a zero ordinary tail. -/
theorem tailPower_four_le_cmObjective_coeff [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) {a : ℝ} (ha : 1 ≤ a)
    (hobj : cmObjective μ ν a < ∞) :
    tailPower μ ν 4 1 ≤
      ENNReal.ofReal ((2 * (cmObjective μ ν a).toReal + 1) ^ 2) * hellingerSq μ ν := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  let m := conditionalRatioMean μ ν (cmCutoff a)
  have hmfin : m ≠ ∞ :=
    (ENNReal.lt_top_of_mul_ne_top_right hobj.ne (ENNReal.ofReal_pos.mpr ha0).ne').ne
  have hmrep : ENNReal.ofReal m.toReal = m := ENNReal.ofReal_toReal hmfin
  have hobjreal : (cmObjective μ ν a).toReal = a * m.toReal := by
    rw [cmObjective, ENNReal.toReal_mul, ENNReal.toReal_ofReal ha0.le]
  by_cases hnull : μ (closedTailEvent μ ν (cmCutoff a)) = 0
  · have hz : closedTailMoment μ ν (cmCutoff a) = 0 := by
      rw [closedTailMoment_eq_conditionalRatioMean_mul_mass hμν, hnull, mul_zero]
    exact (tailPower_four_le_closedTailMoment hμν ha).trans (hz.le.trans zero_le)
  · have hm1 : 1 ≤ m := one_le_conditionalRatioMean hμν (one_lt_cmCutoff ha).le hnull
    have hmreal1 : 1 ≤ m.toReal := by
      simpa using (ENNReal.toReal_mono hmfin hm1)
    calc
      tailPower μ ν 4 1 ≤ closedTailMoment μ ν (cmCutoff a) :=
        tailPower_four_le_closedTailMoment hμν ha
      _ = m * μ (closedTailEvent μ ν (cmCutoff a)) :=
        closedTailMoment_eq_conditionalRatioMean_mul_mass hμν _
      _ ≤ m * (ENNReal.ofReal ((2 * a + 1) ^ 2) * hellingerSq μ ν) :=
        mul_le_mul_right (cm_event_mass_le hμν ha) m
      _ = ENNReal.ofReal (m.toReal * (2 * a + 1) ^ 2) * hellingerSq μ ν := by
        calc
          m * (ENNReal.ofReal ((2 * a + 1) ^ 2) * hellingerSq μ ν) =
              (ENNReal.ofReal m.toReal * ENNReal.ofReal ((2 * a + 1) ^ 2)) *
                hellingerSq μ ν := by rw [hmrep, mul_assoc]
          _ = _ := by rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg]
      _ ≤ ENNReal.ofReal ((2 * (cmObjective μ ν a).toReal + 1) ^ 2) *
          hellingerSq μ ν := by
        apply mul_le_mul_left
        apply ENNReal.ofReal_le_ofReal
        rw [hobjreal]
        exact cm_witness_coefficient_le ha hmreal1

/-- A finite real upper bound for any native objective supplies its source coefficient. -/
theorem tailPower_four_le_of_cmObjective_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) {a R : ℝ} (ha : 1 ≤ a)
    (hR : 0 ≤ R) (hobj : cmObjective μ ν a ≤ ENNReal.ofReal R) :
    tailPower μ ν 4 1 ≤ ENNReal.ofReal ((2 * R + 1) ^ 2) * hellingerSq μ ν := by
  have hobjfin : cmObjective μ ν a < ∞ := hobj.trans_lt ENNReal.ofReal_lt_top
  have hreal : (cmObjective μ ν a).toReal ≤ R := by
    simpa only [ENNReal.toReal_ofReal hR] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hobj
  apply (tailPower_four_le_cmObjective_coeff hμν ha hobjfin).trans
  apply mul_le_mul_left
  apply ENNReal.ofReal_le_ofReal
  exact pow_le_pow_left₀ (by positivity : 0 ≤ 2 * (cmObjective μ ν a).toReal + 1)
    (by linarith) 2

/-- Source CM coefficient at ordinary cutoff four. This proof takes approximate native
objectives and a right-hand limit. -/
theorem tailPower_four_le_of_conditionalMoment_le [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {M : ℝ} (hM : 0 ≤ M)
    (hCM : conditionalMoment μ ν ≤ ENNReal.ofReal M) :
    tailPower μ ν 4 1 ≤ ENNReal.ofReal ((2 * M + 1) ^ 2) * hellingerSq μ ν := by
  have hcmfin : conditionalMoment μ ν < ∞ := hCM.trans_lt ENNReal.ofReal_lt_top
  have hμν := ac_of_conditionalMoment_lt_top hcmfin
  have hcont : Continuous (fun R : ℝ ↦
      ENNReal.ofReal ((2 * R + 1) ^ 2) * hellingerSq μ ν) := by
    apply (ENNReal.continuous_mul_const (hellingerSq_ne_top μ ν)).comp
    apply ENNReal.continuous_ofReal.comp
    fun_prop
  have hlim : Tendsto (fun R : ℝ ↦
      ENNReal.ofReal ((2 * R + 1) ^ 2) * hellingerSq μ ν) (𝓝[>] M)
      (𝓝 (ENNReal.ofReal ((2 * M + 1) ^ 2) * hellingerSq μ ν)) :=
    (hcont.tendsto M).mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with R hR
  have hMR : M < R := hR
  have hR0 : 0 ≤ R := hM.trans hMR.le
  have hCMR : conditionalMoment μ ν < ENNReal.ofReal R := hCM.trans_lt
    ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hM).mpr hMR)
  obtain ⟨a, ha, hobj⟩ := conditionalMoment_lt_iff.mp hCMR
  exact tailPower_four_le_of_cmObjective_le hμν ha hR0 hobj.le

/-- A fixed arbitrary ordinary cutoff. The native CM cutoff remains unchanged;
cutoff transfer supplies an explicit extra term while the preceding theorem retains
its sharper exact source coefficient at four. -/
theorem tailPower_one_le_of_conditionalMoment_le [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {q M : ℝ} (hq : 1 < q) (hM : 0 ≤ M)
    (hCM : conditionalMoment μ ν ≤ ENNReal.ofReal M) :
    tailPower μ ν q 1 ≤
      ENNReal.ofReal ((2 * M + 1) ^ 2 + 4 * tailMassCoeff q) * hellingerSq μ ν := by
  have hJ : 0 < tailMassCoeff q := tailMassCoeff_pos hq
  have hcut := tailPower_le_tailPower_add_hellingerSq (μ := μ) (ν := ν)
    hq (by norm_num : (1 : ℝ) < 4) zero_lt_one
  simp only [Real.rpow_one] at hcut
  calc
    tailPower μ ν q 1 ≤ tailPower μ ν 4 1 +
        ENNReal.ofReal (4 * tailMassCoeff q) * hellingerSq μ ν := hcut
    _ ≤ ENNReal.ofReal ((2 * M + 1) ^ 2) * hellingerSq μ ν +
        ENNReal.ofReal (4 * tailMassCoeff q) * hellingerSq μ ν :=
      add_le_add (tailPower_four_le_of_conditionalMoment_le hM hCM) le_rfl
    _ = _ := by
      rw [ENNReal.ofReal_add (sq_nonneg _) (by positivity : 0 ≤ 4 * tailMassCoeff q),
        add_mul]

/-- CM supplies every NC exponent in its source range with one finite coefficient. -/
theorem tailPower_le_of_conditionalMoment_le [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {q δ M : ℝ} (hq : 1 < q) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hM : 0 ≤ M)
    (hCM : conditionalMoment μ ν ≤ ENNReal.ofReal M) :
    tailPower μ ν q δ ≤
      ENNReal.ofReal ((2 * M + 1) ^ 2 + 4 * tailMassCoeff q) * hellingerSq μ ν :=
  (tailPower_mono_exponent hq hδ hδ1).trans
    (tailPower_one_le_of_conditionalMoment_le hq hM hCM)

/-- A single finite CM bound chosen before the family yields a single finite
Hellinger multiplier, including an empty family. -/
theorem uniform_tailPower_of_uniform_conditionalMoment (μ : Measure α)
    [IsProbabilityMeasure μ] (F : Set (Measure α))
    (hF : ∀ ν ∈ F, IsProbabilityMeasure ν) {q δ : ℝ}
    (hq : 1 < q) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hCM : ∃ M : ℝ≥0, ∀ ν ∈ F, conditionalMoment μ ν ≤ (M : ℝ≥0∞)) :
    UniformHellingerBound μ F (fun ν ↦ tailPower μ ν q δ) := by
  have hJ : 0 < tailMassCoeff q := tailMassCoeff_pos hq
  obtain ⟨M, hM⟩ := hCM
  refine (uniformHellingerBound_iff_real μ F _).2
    ⟨(2 * (M : ℝ) + 1) ^ 2 + 4 * tailMassCoeff q, by positivity, ?_⟩
  intro ν hν
  let : IsProbabilityMeasure ν := hF ν hν
  exact tailPower_le_of_conditionalMoment_le hq hδ hδ1 M.property (by simpa using hM ν hν)

end Hellinger.Comparison
