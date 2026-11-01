/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.MLE.Statements
public import Hellinger.MLE.MixLog
public import Hellinger.MLE.ProbabilityRates
public import Hellinger.MLE.DensityBridge
public import Hellinger.CutoffFour
public import Hellinger.CutoffFourMoments
public import Hellinger.Centering

/-!
The comparator error of the direct proof of the corrected sieve MLE theorem.

With `P₀ = p₀ · μ` and `ℓ_n = log(p₀/p_n)`, the comparator error is
`Z_n = ½ (E_n + |(ℙ_n − P₀) ℓ_n| + (P₀ ℓ_n)_+)`, where `E_n` is the optimization deficit.
It is `O_P^*(a_n²)`, `a_n = max(δ_n, n^{-1/2})` (`comparatorError_opStar`), and almost surely
`ℙ_n m_{phat_n} ≥ -Z_n` whenever `Z_n` is finite (`sampleMean_mixLog_ge`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Hellinger.MLE

variable {𝒳 : Type*} [MeasurableSpace 𝒳] {μ : Measure 𝒳}
  {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} {X : ℕ → Ω → 𝒳} {p₀ : 𝒳 → ℝ≥0}
  {S : ℕ → Set (𝒳 → ℝ≥0)} {pn : ℕ → 𝒳 → ℝ≥0} {phat : ℕ → Ω → 𝒳 → ℝ≥0}
  {δ : ℕ → ℝ} {D M : ℝ}

/-- `Z_n = ½ (E_n + |(ℙ_n − P₀) ℓ_n| + P₀ ℓ_n)`, with `ℓ_n = log(p₀/p_n)`, `E_n` the
optimization deficit, and the last two terms embedded by `ENNReal.ofReal` (so `P₀ ℓ_n` enters
through its positive part). -/
noncomputable def comparatorError (μ : Measure 𝒳) (X : ℕ → Ω → 𝒳) (p₀ : 𝒳 → ℝ≥0)
    (pn : ℕ → 𝒳 → ℝ≥0) (phat : ℕ → Ω → 𝒳 → ℝ≥0) (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
  2⁻¹ * (logLikDeficit (sample X n ω) (pn n) (phat n ω) +
    ENNReal.ofReal |sampleMean X n (logRatio p₀ (pn n)) ω - ∫ x, logRatio p₀ (pn n) x ∂(law μ p₀)| +
    ENNReal.ofReal (∫ x, logRatio p₀ (pn n) x ∂(law μ p₀)))

/-! ### Deterministic bounds on the comparator -/

/-- The coefficient of `logMoment_upper_four` at `k = 2` is at most `8`. -/
theorem logMoment_coeff_two_le :
    4 * max (2 * Real.log 4 ^ ((2 : ℝ) - 2)) ((2 / Real.exp 1) ^ (2 : ℝ)) ≤ 8 := by
  have he : 2 < Real.exp 1 := by
    have := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0); norm_num at this; linarith
  have h1 : (2 / Real.exp 1) ^ (2 : ℝ) ≤ 2 := by
    rw [Real.rpow_two]
    have h0 : 0 ≤ 2 / Real.exp 1 := by positivity
    have h2 : 2 / Real.exp 1 ≤ 1 := by
      rw [div_le_one (by positivity)]; exact he.le
    nlinarith
  have h2 : 2 * Real.log 4 ^ ((2 : ℝ) - 2) = 2 := by norm_num
  rw [h2, max_eq_left h1]
  norm_num

/-- Eventually in `n`: `P₀ ≪ P_n`, `ℓ_n ∈ L²(P₀)`, `P₀ ℓ_n² ≤ (8D² + M) δ_n²` and
`P₀ ℓ_n ≤ (3D² + 4D√M) δ_n²`. -/
theorem MLEHypotheses.eventually_comparator_bounds
    (h : MLEHypotheses μ Pr X p₀ S pn phat δ D M) :
    ∃ N, ∀ n ≥ N, law μ p₀ ≪ law μ (pn n) ∧
      MemLp (logRatio p₀ (pn n)) 2 (law μ p₀) ∧
      ∫ x, logRatio p₀ (pn n) x ^ 2 ∂(law μ p₀) ≤ (8 * D ^ 2 + M) * δ n ^ 2 ∧
      ∫ x, logRatio p₀ (pn n) x ∂(law μ p₀) ≤ (3 * D ^ 2 + 4 * D * Real.sqrt M) * δ n ^ 2 := by
  obtain ⟨N₁, hN₁⟩ := h.approx
  obtain ⟨N₂, hN₂⟩ := h.logTail
  refine ⟨max N₁ N₂, fun n hn ↦ ?_⟩
  have hd := hN₁ n (le_of_max_le_left hn)
  have ht := hN₂ n (le_of_max_le_right hn)
  have hp₀ := h.density
  have hpn : IsProbDensity μ (pn n) := h.sieve_density n _ (h.comparator_mem n)
  have hδ := h.rate_nonneg n
  have hD := h.D_nonneg
  have hM := h.M_nonneg
  have := isProbabilityMeasure_law hp₀
  have := isProbabilityMeasure_law hpn
  set P := law μ p₀ with hP
  set Q := law μ (pn n) with hQ
  have hH : hellingerSq P Q = hellingerFunSq μ p₀ (pn n) :=
    (hellingerFunSq_eq_hellingerSq_law_of_isProbDensity hp₀ hpn).symm
  have hHhalf : hellingerSq P Q ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (D * δ n) := by
    rw [hH]; exact hd
  have hHsq : hellingerSq P Q ≤ ENNReal.ofReal (D ^ 2 * δ n ^ 2) := by
    have e : hellingerSq P Q = (hellingerSq P Q ^ (1 / 2 : ℝ)) ^ (2 : ℕ) := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
    rw [e, show D ^ 2 * δ n ^ 2 = (D * δ n) ^ 2 by ring,
      ENNReal.ofReal_pow (mul_nonneg hD hδ)]
    gcongr
  have hac : P ≪ Q := by
    by_contra hna
    rw [tailLogMoment_of_not_ac hna] at ht
    exact ENNReal.ofReal_ne_top (top_le_iff.mp ht)
  have hℓ : llr P Q =ᵐ[P] logRatio p₀ (pn n) := llr_law_ae_eq hp₀ hpn hac
  have hmeas : Measurable (logRatio p₀ (pn n)) :=
    measurable_logRatio hp₀.measurable hpn.measurable
  -- the second moment
  have hlm : logMoment P Q 2 ≤ ENNReal.ofReal ((8 * D ^ 2 + M) * δ n ^ 2) :=
    calc logMoment P Q 2
        ≤ ENNReal.ofReal (4 * max (2 * Real.log 4 ^ ((2 : ℝ) - 2))
            ((2 / Real.exp 1) ^ (2 : ℝ))) * hellingerSq P Q + tailLogMoment P Q 4 2 :=
          logMoment_upper_four le_rfl
      _ ≤ ENNReal.ofReal 8 * ENNReal.ofReal (D ^ 2 * δ n ^ 2) + ENNReal.ofReal (M * δ n ^ 2) := by
          gcongr
          exact logMoment_coeff_two_le
      _ = ENNReal.ofReal ((8 * D ^ 2 + M) * δ n ^ 2) := by
          rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity)
            (by positivity)]
          ring_nf
  rw [logMoment_of_ac hac] at hlm
  have hlint : ∫⁻ x, ENNReal.ofReal (logRatio p₀ (pn n) x ^ 2) ∂P =
      ∫⁻ x, ENNReal.ofReal (|llr P Q x| ^ (2 : ℝ)) ∂P := by
    apply lintegral_congr_ae
    filter_upwards [hℓ] with x hx
    rw [hx, Real.rpow_two, sq_abs]
  rw [← hlint] at hlm
  have hsqint : Integrable (fun x ↦ logRatio p₀ (pn n) x ^ 2) P :=
    ⟨(hmeas.pow_const 2).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x ↦ sq_nonneg _)).2
        (lt_of_le_of_lt hlm ENNReal.ofReal_lt_top)⟩
  have hmem : MemLp (logRatio p₀ (pn n)) 2 P :=
    (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2 hsqint
  have hsq : ∫ x, logRatio p₀ (pn n) x ^ 2 ∂P ≤ (8 * D ^ 2 + M) * δ n ^ 2 := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x ↦ sq_nonneg _)
      (hmeas.pow_const 2).aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hlm
  -- the first moment
  have hA₂ : tailLogMoment P Q 4 2 ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (Real.sqrt M * δ n) := by
    calc tailLogMoment P Q 4 2 ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (M * δ n ^ 2) ^ (1 / 2 : ℝ) := by
          gcongr
      _ = ENNReal.ofReal (Real.sqrt M * δ n) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
            Real.sqrt_mul hM, Real.sqrt_sq hδ]
  have hA₁ : tailLogMoment P Q 4 1 ≤ ENNReal.ofReal (4 * D * Real.sqrt M * δ n ^ 2) := by
    calc tailLogMoment P Q 4 1
        ≤ 4 * hellingerSq P Q ^ (1 - (1 : ℝ) / 2) * tailLogMoment P Q 4 2 ^ ((1 : ℝ) / 2) :=
          tailLogMoment_interpolation_four one_pos one_le_two
      _ = 4 * hellingerSq P Q ^ (1 / 2 : ℝ) * tailLogMoment P Q 4 2 ^ (1 / 2 : ℝ) := by
          norm_num
      _ ≤ 4 * ENNReal.ofReal (D * δ n) * ENNReal.ofReal (Real.sqrt M * δ n) := by
          gcongr
      _ = ENNReal.ofReal (4 * D * Real.sqrt M * δ n ^ 2) := by
          rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_mul (by positivity)]
          ring_nf
  have hkl : kl P Q ≤ ENNReal.ofReal ((3 * D ^ 2 + 4 * D * Real.sqrt M) * δ n ^ 2) :=
    calc kl P Q ≤ 3 * hellingerSq P Q + tailLogMoment P Q 4 1 := kl_upper_tailLogMoment_four
      _ ≤ ENNReal.ofReal 3 * ENNReal.ofReal (D ^ 2 * δ n ^ 2) +
            ENNReal.ofReal (4 * D * Real.sqrt M * δ n ^ 2) := by
          rw [ENNReal.ofReal_ofNat]; gcongr
      _ = _ := by
          rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity)
            (by positivity)]
          ring_nf
  have hfin : FiniteKL P Q := lt_of_le_of_lt hkl ENNReal.ofReal_lt_top
  have hmean : ∫ x, logRatio p₀ (pn n) x ∂P ≤ (3 * D ^ 2 + 4 * D * Real.sqrt M) * δ n ^ 2 := by
    rw [← integral_congr_ae hℓ, ← kl_toReal_eq_integral_llr P Q hfin]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hkl
  exact ⟨hac, hmem, hsq, hmean⟩

/-! ### The comparator error is `O_P^*(a_n²)` -/

theorem comparatorError_opStar (h : MLEHypotheses μ Pr X p₀ S pn phat δ D M) :
    OPStar Pr (comparatorError μ X p₀ pn phat) (fun n ↦ rate δ n ^ 2) := by
  classical
  have := h.probability
  have := isProbabilityMeasure_law h.density
  obtain ⟨N, hN⟩ := h.eventually_comparator_bounds
  have hδa : ∀ n, δ n ≤ rate δ n := fun n ↦ le_max_left _ _
  have ha : ∀ n, 0 ≤ rate δ n := fun n ↦ (h.rate_nonneg n).trans (hδa n)
  have hb : ∀ n, 0 ≤ rate δ n ^ 2 := fun n ↦ sq_nonneg _
  -- the optimization deficit
  have h₁ : OPStar Pr (fun n ω ↦ logLikDeficit (sample X n ω) (pn n) (phat n ω))
      (fun n ↦ rate δ n ^ 2) :=
    h.likelihood.rate_mono ⟨0, fun n _ ↦ pow_le_pow_left₀ (h.rate_nonneg n) (hδa n) 2⟩
  -- the empirical fluctuation
  set f : ℕ → 𝒳 → ℝ := fun n ↦ if N ≤ n then logRatio p₀ (pn n) else 0 with hf
  have hfm : ∀ n, Measurable (f n) := by
    intro n
    by_cases hn : N ≤ n
    · simp only [hf, hn, ↓reduceIte]
      exact measurable_logRatio h.density.measurable
        (h.sieve_density n _ (h.comparator_mem n)).measurable
    · simp only [hf, hn, ↓reduceIte]; exact measurable_const
  have hfL : ∀ n, MemLp (f n) 2 (law μ p₀) := by
    intro n
    by_cases hn : N ≤ n
    · simp only [hf, hn, ↓reduceIte]; exact (hN n hn).2.1
    · simp only [hf, hn, ↓reduceIte]; exact MemLp.zero
  have hC : 0 ≤ 8 * D ^ 2 + M := by have := h.M_nonneg; positivity
  have h₂' := opStar_sampleMean h.measurable_obs h.indep h.law_obs hfm hfL
    (b := fun n ↦ δ n / Real.sqrt n)
    (fun n ↦ div_nonneg (h.rate_nonneg n) (Real.sqrt_nonneg _)) hC
    ⟨max N 1, fun n hn ↦ by
      have hNn : N ≤ n := le_of_max_le_left hn
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
      simp only [hf, hNn, ↓reduceIte]
      refine (hN n hNn).2.2.1.trans_eq ?_
      rw [div_pow, Real.sq_sqrt (by linarith)]
      field_simp⟩
  have h₂ : OPStar Pr (fun n ω ↦ ENNReal.ofReal |sampleMean X n (logRatio p₀ (pn n)) ω -
      ∫ x, logRatio p₀ (pn n) x ∂(law μ p₀)|) (fun n ↦ rate δ n ^ 2) := by
    refine (h₂'.congr ⟨N, fun n hn ↦ ?_⟩).rate_mono ⟨0, fun n _ ↦ ?_⟩
    · simp only [hf, hn, ↓reduceIte]
    · rw [div_eq_mul_inv, sq]
      exact mul_le_mul (hδa n) (le_max_right _ _) (inv_nonneg.2 (Real.sqrt_nonneg _)) (ha n)
  -- the deterministic mean
  have h₃ : OPStar Pr (fun n _ ↦ ENNReal.ofReal (∫ x, logRatio p₀ (pn n) x ∂(law μ p₀)))
      (fun n ↦ rate δ n ^ 2) := by
    have hc : 0 ≤ 3 * D ^ 2 + 4 * D * Real.sqrt M := by have := h.D_nonneg; positivity
    refine OPStar.of_le hb hc ⟨N, fun n hn _ ↦ ENNReal.ofReal_le_ofReal ?_⟩
    refine (hN n hn).2.2.2.trans ?_
    gcongr
    · exact h.rate_nonneg n
    · exact hδa n
  have h₄ := ((h₁.add h₂ hb).add h₃ hb).const_mul 2⁻¹
  refine h₄.congr ⟨0, fun n _ ↦ ?_⟩
  funext ω
  simp only [comparatorError, Pi.add_apply]
  congr 1
  rw [ENNReal.coe_inv two_ne_zero]
  rfl

/-! ### The empirical lower bound -/

omit [MeasurableSpace 𝒳] in
/-- Midpoint concavity of `log`: `½ (log b − log a) ≤ log((a + b)/(2a))` for `a, b > 0`. -/
theorem half_log_sub_le_log_mix {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (Real.log b - Real.log a) / 2 ≤ Real.log ((a + b) / (2 * a)) := by
  have hab : Real.log (a * b) ≤ Real.log (((a + b) / 2) ^ 2) :=
    Real.log_le_log (mul_pos ha hb) (by nlinarith [sq_nonneg (a - b)])
  rw [Real.log_mul ha.ne' hb.ne', Real.log_pow] at hab
  rw [show (a + b) / (2 * a) = ((a + b) / 2) / a by field_simp,
    Real.log_div (by positivity) ha.ne']
  push_cast at hab
  linarith

omit [MeasurableSpace Ω] in
/-- The pointwise lower bound on a sample where `p₀` and `p_n` are positive. -/
theorem neg_toReal_comparatorError_le_of_pos {n : ℕ} {ω : Ω}
    (hω : ∀ i : Fin n, 0 < p₀ (X i ω) ∧ 0 < pn n (X i ω))
    (hZ : comparatorError μ X p₀ pn phat n ω ≠ ⊤) :
    -(comparatorError μ X p₀ pn phat n ω).toReal ≤
      sampleMean X n (mixLog p₀ (phat n ω)) ω := by
  set q := phat n ω with hq
  set x := sample X n ω with hx
  set E := ∫ y, logRatio p₀ (pn n) y ∂(law μ p₀) with hE
  set F := sampleMean X n (logRatio p₀ (pn n)) ω - E with hF
  have hLpn : likelihood x (pn n) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ ↦ (hω i).2.ne'
  have hLq : likelihood x q ≠ 0 := by
    intro h0
    apply hZ
    simp only [comparatorError, logLikDeficit, ← hq, ← hx, hLpn, h0, ↓reduceIte, ↓reduceIte,
      top_add]
    exact ENNReal.mul_top (by norm_num)
  have hqpos : ∀ i : Fin n, 0 < q (X i ω) := fun i ↦
    pos_iff_ne_zero.2 (Finset.prod_ne_zero_iff.1 hLq i (Finset.mem_univ _))
  set d := (Real.log (likelihood x (pn n) : ℝ) - Real.log (likelihood x q : ℝ)) / n with hd
  have hdef : logLikDeficit x (pn n) q = ENNReal.ofReal d := by
    simp only [logLikDeficit, hLpn, hLq, ↓reduceIte, hd]
  have hZr : (comparatorError μ X p₀ pn phat n ω).toReal = 2⁻¹ * (max d 0 + |F| + max E 0) := by
    simp only [comparatorError, ← hq, ← hx, ← hE, ← hF, hdef]
    rw [ENNReal.toReal_mul, ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_ofReal',
      ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_ofReal', ENNReal.toReal_inv]
    norm_num
  -- logarithms of the sample values
  set a : Fin n → ℝ := fun i ↦ Real.log (p₀ (X i ω)) with ha
  set b : Fin n → ℝ := fun i ↦ Real.log (pn n (X i ω)) with hb
  set c : Fin n → ℝ := fun i ↦ Real.log (q (X i ω)) with hc
  have hlogpn : Real.log (likelihood x (pn n) : ℝ) = ∑ i, b i := by
    simp only [likelihood, NNReal.coe_prod, hx, sample, hb]
    exact Real.log_prod fun i _ ↦ by exact_mod_cast (hω i).2.ne'
  have hlogq : Real.log (likelihood x q : ℝ) = ∑ i, c i := by
    simp only [likelihood, NNReal.coe_prod, hx, sample, hc]
    exact Real.log_prod fun i _ ↦ by exact_mod_cast (hqpos i).ne'
  have hℓ : sampleMean X n (logRatio p₀ (pn n)) ω = (n : ℝ)⁻¹ * ((∑ i, a i) - ∑ i, b i) := by
    simp only [sampleMean, logRatio, ha, hb]
    rw [← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    exact Real.log_div (by exact_mod_cast (hω i).1.ne') (by exact_mod_cast (hω i).2.ne')
  have hm : (n : ℝ)⁻¹ * (((∑ i, c i) - ∑ i, a i) / 2) ≤
      sampleMean X n (mixLog p₀ q) ω := by
    simp only [sampleMean]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (Nat.cast_nonneg _))
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    have hp : (0 : ℝ) < p₀ (X i ω) := by exact_mod_cast (hω i).1
    have hqi : (0 : ℝ) < q (X i ω) := by exact_mod_cast hqpos i
    rw [mixLog_of_pos (hω i).1]
    exact half_log_sub_le_log_mix hp hqi
  have hd' : d = (n : ℝ)⁻¹ * ((∑ i, b i) - ∑ i, c i) := by
    rw [hd, hlogpn, hlogq, div_eq_inv_mul]
  have key : (n : ℝ)⁻¹ * (((∑ i, c i) - ∑ i, a i) / 2) =
      (-((n : ℝ)⁻¹ * ((∑ i, b i) - ∑ i, c i)) -
        (n : ℝ)⁻¹ * ((∑ i, a i) - ∑ i, b i)) / 2 := by ring
  rw [← hd', ← hℓ] at key
  have hFE : sampleMean X n (logRatio p₀ (pn n)) ω = F + E := by rw [hF]; ring
  rw [hZr]
  have h1 := le_max_left d 0
  have h2 := le_abs_self F
  have h3 := le_max_left E 0
  linarith

theorem sampleMean_mixLog_ge (h : MLEHypotheses μ Pr X p₀ S pn phat δ D M) :
    ∃ N, ∀ n ≥ N, ∀ᵐ ω ∂Pr,
      comparatorError μ X p₀ pn phat n ω ≠ ⊤ →
        -(comparatorError μ X p₀ pn phat n ω).toReal ≤
          sampleMean X n (mixLog p₀ (phat n ω)) ω := by
  obtain ⟨N, hN⟩ := h.eventually_comparator_bounds
  refine ⟨max N 1, fun n hn ↦ ?_⟩
  have hac := (hN n (le_of_max_le_left hn)).1
  have hpn : IsProbDensity μ (pn n) := h.sieve_density n _ (h.comparator_mem n)
  have hpos : ∀ᵐ ω ∂Pr, ∀ i : Fin n, 0 < p₀ (X i ω) ∧ 0 < pn n (X i ω) := by
    rw [ae_all_iff]
    intro i
    have h1 : ∀ᵐ y ∂(Pr.map (X i)), 0 < p₀ y ∧ 0 < pn n y := by
      rw [h.law_obs i]
      filter_upwards [ae_law_pos h.density.measurable,
        ae_law_pos_right hpn.measurable hac] with y h1 h2 using ⟨h1, h2⟩
    exact ae_of_ae_map (h.measurable_obs i).aemeasurable h1
  filter_upwards [hpos] with ω hω hZ
  exact neg_toReal_comparatorError_le_of_pos hω hZ

end Hellinger.MLE
