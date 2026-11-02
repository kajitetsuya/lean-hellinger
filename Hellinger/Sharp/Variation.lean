/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.Sharp.Statements
public import Hellinger.Sharp.KL
public import Hellinger.VariationBounds
public import Hellinger.Interpolation
public import Hellinger.Comparison.PowerTail
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Convex.Slope
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Sharp Kullback–Leibler variation and improved interpolation coefficients.

The Kullback–Leibler variation bound uses the sharp coefficient `max(J(c) (log c)^k, B_k)`:
on `(0, 1)` the kernel ratio is at most its supremum `B_k`, on `(1, c]` the ratio is
nondecreasing and so at most its value `J(c) (log c)^k` at `r = c`, and above `c` the tail
kernel takes over. The interpolation bounds stop the Hölder proofs of the paper's
interpolation bounds before the weakening `J^{1-r} ≤ J`. The arguments are summarized in
`docs/SharpConstants.md`. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Hellinger.Sharp

universe u

/-! ### Scalar facts -/

/-- `J(c) (√c - 1)² = c`. -/
theorem tailMassCoeff_mul_sq {c : ℝ} (hc : 1 < c) :
    tailMassCoeff c * (Real.sqrt c - 1) ^ 2 = c := by
  have ht : 1 < Real.sqrt c := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) hc
  have hts : (Real.sqrt c - 1) ^ 2 ≠ 0 := pow_ne_zero 2 (by linarith)
  rw [tailMassCoeff_eq_div hc, div_mul_cancel₀ _ hts]

/-- The chord slope `s log s / (s - 1)` from `(1, 0)` is nondecreasing on `s > 1`. -/
theorem mul_log_mul_sub_one_le {s t : ℝ} (hs : 1 < s) (hst : s ≤ t) :
    s * Real.log s * (t - 1) ≤ t * Real.log t * (s - 1) := by
  have h := Real.convexOn_mul_log.secant_mono (a := 1) (x := s) (y := t)
    (Set.mem_Ici.mpr (by norm_num)) (Set.mem_Ici.mpr (by linarith))
    (Set.mem_Ici.mpr (by linarith)) (by linarith) (by linarith) hst
  simp only [Real.log_one, mul_zero, sub_zero] at h
  rwa [div_le_div_iff₀ (by linarith) (by linarith)] at h

/-- On `(1, c]` the kernel ratio is at most its value at `c`. -/
theorem variation_density_mid_sharp {c k r : ℝ} (hk : 2 ≤ k) (hr : 1 < r) (hrc : r ≤ c) :
    r * |Real.log r| ^ k ≤ tailMassCoeff c * Real.log c ^ k * (Real.sqrt r - 1) ^ 2 := by
  have hc : 1 < c := lt_of_lt_of_le hr hrc
  have hr0 : 0 < r := by linarith
  have hc0 : 0 < c := by linarith
  have hL : 0 < Real.log r := Real.log_pos hr
  have hM : 0 < Real.log c := Real.log_pos hc
  have hLM : Real.log r ≤ Real.log c := Real.log_le_log hr0 hrc
  set s := Real.sqrt r with hs_def
  set t := Real.sqrt c with ht_def
  have hs1 : 1 < s := by
    rw [hs_def, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) hr
  have hst : s ≤ t := Real.sqrt_le_sqrt hrc
  have hss : s ^ 2 = r := Real.sq_sqrt hr0.le
  have htt : t ^ 2 = c := Real.sq_sqrt hc0.le
  have hLs : Real.log r = 2 * Real.log s := by
    rw [← hss, Real.log_pow]; norm_num
  have hMt : Real.log c = 2 * Real.log t := by
    rw [← htt, Real.log_pow]; norm_num
  have hlogs : 0 < Real.log s := Real.log_pos hs1
  have hkey := mul_log_mul_sub_one_le hs1 hst
  have hX : 0 ≤ s * Real.log s * (t - 1) :=
    mul_nonneg (mul_nonneg (by linarith) hlogs.le) (by linarith)
  have hsq : (s * Real.log s * (t - 1)) ^ 2 ≤ (t * Real.log t * (s - 1)) ^ 2 :=
    pow_le_pow_left₀ hX hkey 2
  -- the `k = 2` part: `r (log r)² ≤ J(c) (log c)² (√r - 1)²`
  have htpos : 0 < (t - 1) ^ 2 := by nlinarith
  have hJ : tailMassCoeff c = t ^ 2 / (t - 1) ^ 2 := by
    rw [tailMassCoeff_eq_div hc, htt]
  have hA : r * Real.log r ^ 2 ≤ tailMassCoeff c * Real.log c ^ 2 * (s - 1) ^ 2 := by
    rw [hJ, hLs, hMt, ← hss, div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ htpos]
    nlinarith [hsq]
  -- split off the factor `(log r)^(k-2) ≤ (log c)^(k-2)`
  have hsplit : ∀ x : ℝ, 0 < x → x ^ k = x ^ 2 * x ^ (k - 2) := by
    intro x hx
    calc
      x ^ k = x ^ ((2 : ℝ) + (k - 2)) := by congr 1; ring
      _ = x ^ (2 : ℝ) * x ^ (k - 2) := Real.rpow_add hx _ _
      _ = _ := by rw [Real.rpow_two]
  have hpow : Real.log r ^ (k - 2) ≤ Real.log c ^ (k - 2) :=
    Real.rpow_le_rpow hL.le hLM (by linarith)
  have hcp : 0 ≤ Real.log c ^ (k - 2) := Real.rpow_nonneg hM.le _
  rw [abs_of_pos hL, hsplit _ hL, hsplit _ hM]
  calc
    r * (Real.log r ^ 2 * Real.log r ^ (k - 2)) =
        (r * Real.log r ^ 2) * Real.log r ^ (k - 2) := by ring
    _ ≤ (r * Real.log r ^ 2) * Real.log c ^ (k - 2) :=
      mul_le_mul_of_nonneg_left hpow (mul_nonneg hr0.le (sq_nonneg _))
    _ ≤ (tailMassCoeff c * Real.log c ^ 2 * (s - 1) ^ 2) * Real.log c ^ (k - 2) :=
      mul_le_mul_of_nonneg_right hA hcp
    _ = _ := by ring

/-- On `(0, 1)` the pointwise Kullback–Leibler variation bound `variation_density_upper` at any
cutoff `c > 1` bounds the kernel ratio. -/
theorem variationRatio_le_variationUpperCoeff {c k r : ℝ} (hc : 1 < c) (hk : 2 ≤ k)
    (hr0 : 0 < r) (hr1 : r < 1) :
    r * |Real.log r| ^ k / (Real.sqrt r - 1) ^ 2 ≤ variationUpperCoeff c k := by
  have h := variation_density_upper hc hk hr0.le
  have hker : logMomentTailDensityKernel c k r = 0 := by
    have : ¬ Real.log c < Real.log r := by
      have := Real.log_neg hr0 hr1
      have := Real.log_pos hc
      linarith
    simp [logMomentTailDensityKernel, this]
  rw [hker, add_zero] at h
  have hs : Real.sqrt r < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt hr0.le hr1
  rw [div_le_iff₀ (by nlinarith)]
  exact h

/-! ### The supremum on `(0, 1)` -/

theorem bddAbove_variationRatio {k : ℝ} (hk : 2 ≤ k) :
    BddAbove (Set.range fun r : Set.Ioo (0 : ℝ) 1 =>
      (r : ℝ) * |Real.log r| ^ k / (Real.sqrt r - 1) ^ 2) := by
  refine ⟨variationUpperCoeff 2 k, ?_⟩
  rintro _ ⟨r, rfl⟩
  exact variationRatio_le_variationUpperCoeff (by norm_num) hk r.2.1 r.2.2

theorem variationRatio_le_variationLowerSup {k r : ℝ} (hk : 2 ≤ k) (hr0 : 0 < r)
    (hr1 : r < 1) :
    r * |Real.log r| ^ k ≤ variationLowerSup k * (Real.sqrt r - 1) ^ 2 := by
  have h := le_ciSup (bddAbove_variationRatio hk) (⟨r, hr0, hr1⟩ : Set.Ioo (0 : ℝ) 1)
  have hs : Real.sqrt r < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt hr0.le hr1
  rw [div_le_iff₀ (by nlinarith)] at h
  exact h

/-! ### The sharp pointwise split -/

theorem variation_density_upper_sharp {c k r : ℝ} (hc : 1 < c) (hk : 2 ≤ k) (hr : 0 ≤ r) :
    r * |Real.log r| ^ k ≤ variationSharpCoeff c k * (Real.sqrt r - 1) ^ 2 +
      logMomentTailDensityKernel c k r := by
  have hc0 : 0 < c := lt_trans (by norm_num) hc
  have hker0 := logMomentTailDensityKernel_nonneg (k := k) hc hr
  have hV0 : 0 ≤ variationSharpCoeff c k :=
    (mul_nonneg (tailMassCoeff_pos hc).le (Real.rpow_nonneg (Real.log_pos hc).le _)).trans
      (le_max_left _ _)
  rcases eq_or_lt_of_le hr with hr0 | hrpos
  · subst r
    simp only [zero_mul]
    exact add_nonneg (mul_nonneg hV0 (sq_nonneg _)) hker0
  by_cases ht : Real.log c < Real.log r
  · rw [logMomentTailDensityKernel, ite_eq_left ht, abs_of_pos ((Real.log_pos hc).trans ht)]
    exact le_add_of_nonneg_left (mul_nonneg hV0 (sq_nonneg _))
  · have hrc : r ≤ c := (Real.log_le_log_iff hrpos hc0).mp (le_of_not_gt ht)
    rw [logMomentTailDensityKernel, ite_eq_right ht, add_zero]
    rcases lt_trichotomy r 1 with hr1 | hr1 | hr1
    · exact (variationRatio_le_variationLowerSup hk hrpos hr1).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))
    · subst r
      simp [Real.zero_rpow (by linarith : k ≠ 0)]
    · exact (variation_density_mid_sharp hk hr1 hrc).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))

/-! ### The sharp measure-level Kullback–Leibler variation bound -/

theorem logMoment_le_hellinger_add_tailLogMoment_sharp : VariationUpperSharpStatement.{u} := by
  intro α _ μ ν _ _ c k hc hk
  have hV0 : 0 ≤ variationSharpCoeff c k :=
    (mul_nonneg (tailMassCoeff_pos hc).le (Real.rpow_nonneg (Real.log_pos hc).le _)).trans
      (le_max_left _ _)
  by_cases h : μ ≪ ν
  · rw [logMoment_eq_lintegral_density h]
    have hg : Measurable (fun x ↦ ENNReal.ofReal
        ((Real.sqrt ((μ.rnDeriv ν x).toReal) - 1) ^ 2)) := by fun_prop
    calc
      _ ≤ ∫⁻ x, ENNReal.ofReal (variationSharpCoeff c k) *
            ENNReal.ofReal ((Real.sqrt ((μ.rnDeriv ν x).toReal) - 1) ^ 2) +
            ENNReal.ofReal (logMomentTailDensityKernel c k ((μ.rnDeriv ν x).toReal)) ∂ν := by
        apply lintegral_mono
        intro x
        have hp := ENNReal.ofReal_le_ofReal
          (variation_density_upper_sharp hc hk (r := (μ.rnDeriv ν x).toReal)
            ENNReal.toReal_nonneg)
        rw [ENNReal.ofReal_add (mul_nonneg hV0 (sq_nonneg _))
          (logMomentTailDensityKernel_nonneg hc ENNReal.toReal_nonneg),
          ENNReal.ofReal_mul hV0] at hp
        simpa only [llr] using hp
      _ = ENNReal.ofReal (variationSharpCoeff c k) *
            (∫⁻ x, ENNReal.ofReal ((Real.sqrt ((μ.rnDeriv ν x).toReal) - 1) ^ 2) ∂ν) +
            (∫⁻ x, ENNReal.ofReal
              (logMomentTailDensityKernel c k ((μ.rnDeriv ν x).toReal)) ∂ν) := by
        calc
          _ = (∫⁻ x, ENNReal.ofReal (variationSharpCoeff c k) *
                ENNReal.ofReal ((Real.sqrt ((μ.rnDeriv ν x).toReal) - 1) ^ 2) ∂ν) +
              (∫⁻ x, ENNReal.ofReal
                (logMomentTailDensityKernel c k ((μ.rnDeriv ν x).toReal)) ∂ν) := by
            simpa only [Pi.mul_apply] using
              (lintegral_add_left (measurable_const.mul hg)
                (fun x ↦ ENNReal.ofReal
                  (logMomentTailDensityKernel c k ((μ.rnDeriv ν x).toReal))))
          _ = _ := by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ = _ := by
        rw [← hellingerSq_eq_lintegral_of_ac h, ← tailLogMoment_eq_lintegral_densityKernel h]
  · simp [logMoment_of_not_ac h, tailLogMoment_of_not_ac h]

/-! ### Improved interpolation -/

theorem tailLogMoment_interpolation_sharp : InterpolationSharpStatement.{u} := by
  intro α _ μ ν _ _ c k k' hc hk hkk'
  rcases eq_or_lt_of_le hkk' with heq | hlt
  · subst k'
    simp [interpolationSharpCoeff, div_self hk.ne']
  have hkp : 0 < k' := hk.trans hlt
  have hr : 0 < k / k' := div_pos hk hkp
  have hr1 : k / k' < 1 := (div_lt_one hkp).mpr hlt
  have hq : 0 < 1 - k / k' := sub_pos.mpr hr1
  have hJ0 := tailMassCoeff_pos hc
  have hcoef : ENNReal.ofReal (interpolationSharpCoeff c k k') =
      ENNReal.ofReal (tailMassCoeff c) ^ (1 - k / k') :=
    (ENNReal.ofReal_rpow_of_nonneg hJ0.le hq.le).symm
  by_cases hμν : μ ≪ ν
  · have hmass := tailEvent_mass_le_tailMassCoeff_mul_hellingerSq hμν hc
    calc
      tailLogMoment μ ν c k ≤ μ (tailEvent μ ν c) ^ (1 - k / k') *
          tailLogMoment μ ν c k' ^ (k / k') :=
        tailLogMoment_le_mass_rpow_mul_tailLogMoment hμν hc hk hlt
      _ ≤ (ENNReal.ofReal (tailMassCoeff c) * hellingerSq μ ν) ^ (1 - k / k') *
          tailLogMoment μ ν c k' ^ (k / k') :=
        mul_le_mul' (ENNReal.rpow_le_rpow hmass hq.le) le_rfl
      _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le, hcoef]
  · have hH : hellingerSq μ ν ≠ 0 := by
      intro hz
      have heq := (hellingerSq_eq_zero_iff μ ν).mp hz
      subst ν
      exact hμν Measure.AbsolutelyContinuous.rfl
    have hHpow : hellingerSq μ ν ^ (1 - k / k') ≠ 0 :=
      fun hz ↦ hH ((ENNReal.rpow_eq_zero_iff_of_pos hq).mp hz)
    have hC : ENNReal.ofReal (interpolationSharpCoeff c k k') ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hJ0 _)).ne'
    have hprod : ENNReal.ofReal (interpolationSharpCoeff c k k') *
        hellingerSq μ ν ^ (1 - k / k') ≠ 0 := mul_ne_zero hC hHpow
    rw [tailLogMoment_of_not_ac hμν, tailLogMoment_of_not_ac hμν,
      ENNReal.top_rpow_of_pos hr, ENNReal.mul_top hprod]

theorem tailPower_interpolation_sharp : PowerInterpolationSharpStatement.{u} := by
  intro α _ μ ν _ _ c δ δ' hc hδ hδδ'
  rcases eq_or_lt_of_le hδδ' with heq | hlt
  · subst δ'
    simp [interpolationSharpCoeff, div_self hδ.ne']
  have hδp : 0 < δ' := hδ.trans hlt
  have hr : 0 < δ / δ' := div_pos hδ hδp
  have hr1 : δ / δ' < 1 := (div_lt_one hδp).mpr hlt
  have hq : 0 < 1 - δ / δ' := sub_pos.mpr hr1
  have hJ0 := tailMassCoeff_pos hc
  have hcoef : ENNReal.ofReal (interpolationSharpCoeff c δ δ') =
      ENNReal.ofReal (tailMassCoeff c) ^ (1 - δ / δ') :=
    (ENNReal.ofReal_rpow_of_nonneg hJ0.le hq.le).symm
  by_cases hμν : μ ≪ ν
  · have hmass := tailEvent_mass_le_tailMassCoeff_mul_hellingerSq hμν hc
    calc
      tailPower μ ν c δ ≤ μ (tailEvent μ ν c) ^ (1 - δ / δ') *
          tailPower μ ν c δ' ^ (δ / δ') :=
        Comparison.tailPower_le_mass_rpow_mul_tailPower hμν c hδ hlt
      _ ≤ (ENNReal.ofReal (tailMassCoeff c) * hellingerSq μ ν) ^ (1 - δ / δ') *
          tailPower μ ν c δ' ^ (δ / δ') :=
        mul_le_mul' (ENNReal.rpow_le_rpow hmass hq.le) le_rfl
      _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le, hcoef]
  · have hH : hellingerSq μ ν ≠ 0 := by
      intro hz
      have heq := (hellingerSq_eq_zero_iff μ ν).mp hz
      subst ν
      exact hμν Measure.AbsolutelyContinuous.rfl
    have hHpow : hellingerSq μ ν ^ (1 - δ / δ') ≠ 0 :=
      fun hz ↦ hH ((ENNReal.rpow_eq_zero_iff_of_pos hq).mp hz)
    have hC : ENNReal.ofReal (interpolationSharpCoeff c δ δ') ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hJ0 _)).ne'
    have hprod : ENNReal.ofReal (interpolationSharpCoeff c δ δ') *
        hellingerSq μ ν ^ (1 - δ / δ') ≠ 0 := mul_ne_zero hC hHpow
    rw [tailPower_of_not_ac hμν, tailPower_of_not_ac hμν,
      ENNReal.top_rpow_of_pos hr, ENNReal.mul_top hprod]

/-! ### Coefficient facts -/

theorem variationSharpCoeff_le_variationUpperCoeff {c k : ℝ} (hc : 1 < c) (hk : 2 ≤ k) :
    variationSharpCoeff c k ≤ variationUpperCoeff c k := by
  apply max_le
  · have h := variation_density_upper hc hk (lt_trans (by norm_num) hc).le
    have hker : logMomentTailDensityKernel c k c = 0 := by
      simp [logMomentTailDensityKernel]
    rw [hker, add_zero, abs_of_pos (Real.log_pos hc)] at h
    have hJ := tailMassCoeff_mul_sq hc
    have ht : 1 < Real.sqrt c := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_lt_sqrt (by norm_num) hc
    have hpos : 0 < (Real.sqrt c - 1) ^ 2 := by nlinarith
    have h' : (tailMassCoeff c * Real.log c ^ k) * (Real.sqrt c - 1) ^ 2 ≤
        variationUpperCoeff c k * (Real.sqrt c - 1) ^ 2 := by
      calc
        _ = (tailMassCoeff c * (Real.sqrt c - 1) ^ 2) * Real.log c ^ k := by ring
        _ = c * Real.log c ^ k := by rw [hJ]
        _ ≤ _ := h
    exact le_of_mul_le_mul_right h' hpos
  · have : Nonempty (Set.Ioo (0 : ℝ) 1) := Set.nonempty_Ioo_subtype (by norm_num)
    exact ciSup_le fun r ↦ variationRatio_le_variationUpperCoeff hc hk r.2.1 r.2.2

theorem interpolationSharpCoeff_le_interpolationCoeff {c k k' : ℝ} (hc : 1 < c)
    (hk : 0 < k) (hkk' : k ≤ k') : interpolationSharpCoeff c k k' ≤ interpolationCoeff c := by
  have hkp : 0 < k' := lt_of_lt_of_le hk hkk'
  have hr : 0 ≤ k / k' := (div_pos hk hkp).le
  unfold interpolationSharpCoeff interpolationCoeff
  calc
    tailMassCoeff c ^ (1 - k / k') ≤ tailMassCoeff c ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (one_le_tailMassCoeff hc) (by linarith)
    _ = _ := Real.rpow_one _

/-- `B_2 ≤ 4`: for `0 < r < 1`, `r (log r)² ≤ 4 √r (√r - 1)² ≤ 4 (√r - 1)²`. -/
theorem variationLowerSup_two_le_four : variationLowerSup 2 ≤ 4 := by
  have : Nonempty (Set.Ioo (0 : ℝ) 1) := Set.nonempty_Ioo_subtype (by norm_num)
  apply ciSup_le
  rintro ⟨r, hr0, hr1⟩
  have hs : Real.sqrt r < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt hr0.le hr1
  have hs0 := Real.sqrt_nonneg r
  have hpos : 0 < (Real.sqrt r - 1) ^ 2 := by nlinarith
  rw [div_le_iff₀ hpos]
  have h := mul_sq_log_le_four_sqrt_mul_hellinger hr0
  rw [Real.rpow_two, sq_abs]
  nlinarith [sq_nonneg (Real.sqrt r - 1)]

/-- `4 ≤ J(c) (log c)²` for every `c > 1`. -/
theorem four_le_tailMassCoeff_mul_log_sq {c : ℝ} (hc : 1 < c) :
    4 ≤ tailMassCoeff c * Real.log c ^ 2 := by
  have hc0 : 0 < c := lt_trans (by norm_num) hc
  set t := Real.sqrt c with ht_def
  have ht1 : 1 < t := by
    rw [ht_def, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) hc
  have htt : t ^ 2 = c := Real.sq_sqrt hc0.le
  have hMt : Real.log c = 2 * Real.log t := by
    rw [← htt, Real.log_pow]; norm_num
  have hkey : t - 1 ≤ t * Real.log t := Real.self_sub_one_le_mul_log (by linarith)
  have hsq : (t - 1) ^ 2 ≤ (t * Real.log t) ^ 2 := pow_le_pow_left₀ (by linarith) hkey 2
  have htpos : 0 < (t - 1) ^ 2 := by nlinarith
  rw [tailMassCoeff_eq_div hc, ← ht_def, hMt, ← htt, div_mul_eq_mul_div, le_div_iff₀ htpos]
  nlinarith [hsq]

theorem variationSharpCoeff_two {c : ℝ} (hc : 1 < c) :
    variationSharpCoeff c 2 = tailMassCoeff c * Real.log c ^ (2 : ℝ) := by
  unfold variationSharpCoeff
  apply max_eq_left
  rw [Real.rpow_two]
  exact variationLowerSup_two_le_four.trans (four_le_tailMassCoeff_mul_log_sq hc)

theorem variationSharpCoeff_four_two : variationSharpCoeff 4 2 = 16 * Real.log 2 ^ 2 := by
  rw [variationSharpCoeff_two (by norm_num), tailMassCoeff_four, Real.rpow_two,
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast
  ring

theorem interpolationSharpCoeff_four (k k' : ℝ) :
    interpolationSharpCoeff 4 k k' = 4 ^ (1 - k / k') := by
  simp [interpolationSharpCoeff]

end Hellinger.Sharp
