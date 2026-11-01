/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.Sharp.Statements
public import Hellinger.KLPower
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
Sharpened KL constants: the KL upper bound with `K(c) = J(c) (log c - 1 + 1/c)`, the
log-to-power tail factor `(e δ)⁻¹`, and the KL lower tail bound with `1 - (1 - 1/c)/log c`.
The KL upper and lower-tail coefficients are pointwise sharp; `(e δ)⁻¹` improves the paper's
`δ⁻¹`. The arguments are summarized in `docs/SharpConstants.md`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Hellinger.Sharp

universe u

/-! ### Coefficient identities -/

theorem one_lt_sqrt_of_one_lt {c : ℝ} (hc : 1 < c) : 1 < Real.sqrt c := by
  have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hc
  rwa [Real.sqrt_one] at h

/-- `J(c) = c / (√c - 1)²`. -/
theorem tailMassCoeff_eq_div {c : ℝ} (hc : 1 < c) :
    tailMassCoeff c = c / (Real.sqrt c - 1) ^ 2 := by
  have hc0 : 0 < c := lt_trans (by norm_num) hc
  have hs := one_lt_sqrt_of_one_lt hc
  have hgap : cutoffGap c = 1 - (Real.sqrt c)⁻¹ := by
    unfold cutoffGap
    rw [Real.rpow_neg hc0.le, ← Real.sqrt_eq_rpow]
  have hsq := Real.sq_sqrt hc0.le
  unfold tailMassCoeff
  rw [hgap]
  set s := Real.sqrt c
  have hs0 : s ≠ 0 := by positivity
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hs)
  rw [← hsq]
  field_simp

/-- `K(c) (√c - 1)² = klFun c`. -/
theorem klSharpCoeff_mul_sq {c : ℝ} (hc : 1 < c) :
    klSharpCoeff c * (Real.sqrt c - 1) ^ 2 = InformationTheory.klFun c := by
  have hc0 : 0 < c := lt_trans (by norm_num) hc
  have hs1 : Real.sqrt c - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt (one_lt_sqrt_of_one_lt hc))
  unfold klSharpCoeff
  rw [tailMassCoeff_eq_div hc, InformationTheory.klFun]
  field_simp
  ring

/-- `z + z²/2 ≤ -log (1 - z)` on `[0, 1)`, from the logarithmic series. -/
theorem add_sq_div_two_le_neg_log_one_sub {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    z + z ^ 2 / 2 ≤ -Real.log (1 - z) := by
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one (x := z) (by rwa [abs_of_nonneg hz0])
  have h := sum_le_hasSum (Finset.range 2) (fun i _ ↦ by positivity) hs
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem two_mul_sq_sub_one_le_klFun {c : ℝ} (hc : 1 < c) :
    2 * (Real.sqrt c - 1) ^ 2 ≤ InformationTheory.klFun c := by
  have hc0 : 0 < c := lt_trans (by norm_num) hc
  have hs := one_lt_sqrt_of_one_lt hc
  have hsq := Real.sq_sqrt hc0.le
  have hlog : Real.log c = 2 * Real.log (Real.sqrt c) := by
    rw [Real.log_sqrt hc0.le]; ring
  set s := Real.sqrt c
  have hs0 : 0 < s := by linarith
  set z := 1 - s⁻¹ with hz
  have hz0 : 0 ≤ z := by
    have : s⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs.le
    linarith
  have hz1 : z < 1 := by
    have : 0 < s⁻¹ := inv_pos.mpr hs0
    linarith
  have hser := add_sq_div_two_le_neg_log_one_sub hz0 hz1
  have h1z : 1 - z = s⁻¹ := by rw [hz]; ring
  rw [h1z, Real.log_inv, neg_neg] at hser
  have hsz : s * z = s - 1 := by rw [hz]; field_simp
  have hmul := mul_le_mul_of_nonneg_left hser (by positivity : (0 : ℝ) ≤ 2 * s ^ 2)
  have hexp : 2 * s ^ 2 * (z + z ^ 2 / 2) = 2 * s * (s * z) + (s * z) ^ 2 := by ring
  rw [hexp, hsz] at hmul
  rw [InformationTheory.klFun, hlog, ← hsq]
  nlinarith

/-- `K(c) ≥ 2`. -/
theorem two_le_klSharpCoeff {c : ℝ} (hc : 1 < c) : 2 ≤ klSharpCoeff c := by
  have hs1 : 0 < (Real.sqrt c - 1) ^ 2 :=
    pow_pos (sub_pos.mpr (one_lt_sqrt_of_one_lt hc)) 2
  have h := two_mul_sq_sub_one_le_klFun hc
  rw [← klSharpCoeff_mul_sq hc] at h
  exact le_of_mul_le_mul_right h hs1

theorem klSharpCoeff_pos {c : ℝ} (hc : 1 < c) : 0 < klSharpCoeff c :=
  lt_of_lt_of_le (by norm_num) (two_le_klSharpCoeff hc)

/-- The sharp KL upper coefficient is no larger than the paper's `1 + √c`. -/
theorem klSharpCoeff_le_klUpperCoeff {c : ℝ} (hc : 1 < c) :
    klSharpCoeff c ≤ klUpperCoeff c := by
  have hc0 : 0 < c := lt_trans (by norm_num) hc
  have hs1 : 0 < (Real.sqrt c - 1) ^ 2 :=
    pow_pos (sub_pos.mpr (one_lt_sqrt_of_one_lt hc)) 2
  have h := klFun_le_klUpperCoeff_mul_hellinger hc hc0 le_rfl
  rw [← klSharpCoeff_mul_sq hc] at h
  exact le_of_mul_le_mul_right h hs1

/-- The paper's lower-tail coefficient is no larger than the sharp one. -/
theorem klTailLowerCoeff_le_klTailLowerSharpCoeff {c : ℝ} (hc : 1 < c) :
    klTailLowerCoeff c ≤ klTailLowerSharpCoeff c := by
  have hc0 : 0 < c := lt_trans (by norm_num) hc
  have hw0 : 0 < 1 / c := one_div_pos.mpr hc0
  have hw1 : 1 / c ≤ 1 := ((div_lt_one hc0).mpr hc).le
  have hL : 0 < Real.log c := Real.log_pos hc
  have hlog := Hellinger.two_mul_one_sub_div_le_neg_log hw0 hw1
  rw [one_div, Real.log_inv, neg_neg, ← one_div] at hlog
  have hcross : 2 * (1 - 1 / c) ≤ Real.log c * (1 + 1 / c) :=
    (div_le_iff₀ (by linarith : (0 : ℝ) < 1 + 1 / c)).mp hlog
  have key : (1 - 1 / c) / Real.log c ≤ (1 + 1 / c) / 2 := by
    rw [div_le_iff₀ hL]
    nlinarith
  calc
    klTailLowerCoeff c ≤ (1 - 1 / c) / 2 := min_le_right _ _
    _ ≤ klTailLowerSharpCoeff c := by
      unfold klTailLowerSharpCoeff
      linarith

theorem klTailLowerSharpCoeff_pos {c : ℝ} (hc : 1 < c) : 0 < klTailLowerSharpCoeff c :=
  lt_of_lt_of_le (klTailLowerCoeff_pos hc) (klTailLowerCoeff_le_klTailLowerSharpCoeff hc)

theorem klSharpCoeff_four : klSharpCoeff 4 = 4 * Real.log 4 - 3 := by
  simp only [klSharpCoeff, tailMassCoeff, cutoffGap_four]
  ring

theorem klTailLowerSharpCoeff_four :
    klTailLowerSharpCoeff 4 = 1 - 3 / (4 * Real.log 4) := by
  unfold klTailLowerSharpCoeff
  rw [show (1 - 1 / 4 : ℝ) = 3 / 4 by norm_num, div_div]

/-! ### The KL upper kernel -/

/-- The upper comparison in square-root coordinates on `[t₀, ∞)`, given at `t₀`. -/
theorem reverseKL_sq_le_mul_sq_sub_one_of_ge {a t₀ u : ℝ} (ha : 1 ≤ a) (ht₀ : 0 < t₀)
    (hD : t₀ ^ 2 - 1 - 2 * Real.log t₀ ≤ (1 + a) * (t₀ - 1) ^ 2) (hu : t₀ ≤ u) :
    u ^ 2 - 1 - 2 * Real.log u ≤ (1 + a) * (u - 1) ^ 2 := by
  have hu0 : 0 < u := lt_of_lt_of_le ht₀ hu
  by_cases hau : 1 ≤ a * u
  · exact reverseKL_sq_le_mul_sq_sub_one ha hu0 hau
  · replace hau := not_le.mp hau
    let D : ℝ → ℝ := fun v ↦ (1 + a) * (v - 1) ^ 2 - (v ^ 2 - 1 - 2 * Real.log v)
    have hd (v : ℝ) (hv : 0 < v) : HasDerivAt D (2 * (a * v - 1) * (v - 1) / v) v :=
      hasDerivAt_klUpper_gap a hv
    have ha0 : 0 ≤ a := le_trans (by norm_num) ha
    have hu1 : u < 1 := by nlinarith
    have hmono : MonotoneOn D (Set.Icc t₀ u) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc t₀ u)
        (fun v hv ↦ (hd v (lt_of_lt_of_le ht₀ hv.1)).continuousAt.continuousWithinAt)
        (fun v hv ↦ (hd v (lt_of_lt_of_le ht₀ (interior_subset hv).1)).hasDerivWithinAt)
      intro v hv
      have hvI := interior_subset hv
      have hv0 : 0 < v := lt_of_lt_of_le ht₀ hvI.1
      have hav : a * v - 1 ≤ 0 := by
        have := mul_le_mul_of_nonneg_left hvI.2 ha0
        linarith
      have hv1 : v - 1 ≤ 0 := by linarith [hvI.2]
      exact div_nonneg (by nlinarith) hv0.le
    have h := hmono (show t₀ ∈ Set.Icc t₀ u from ⟨le_rfl, hu⟩)
      (show u ∈ Set.Icc t₀ u from ⟨hu, le_rfl⟩) hu
    simp only [D] at h
    linarith

/-- On `[1/c, ∞)`, the reverse-density KL kernel is bounded with the sharp coefficient. -/
theorem reverseKL_le_klSharpCoeff {c y : ℝ} (hc : 1 < c) (hy : 1 / c ≤ y) :
    y - 1 - Real.log y ≤ klSharpCoeff c * (Real.sqrt y - 1) ^ 2 := by
  have hc0 : 0 < c := lt_trans (by norm_num) hc
  have hy0 : 0 < y := lt_of_lt_of_le (one_div_pos.mpr hc0) hy
  have hs := one_lt_sqrt_of_one_lt hc
  have hs0 : 0 < Real.sqrt c := by linarith
  have ha : 1 ≤ klSharpCoeff c - 1 := by linarith [two_le_klSharpCoeff hc]
  have hu : (Real.sqrt c)⁻¹ ≤ Real.sqrt y := by
    have h := Real.sqrt_le_sqrt hy
    rwa [one_div, Real.sqrt_inv] at h
  have hD : ((Real.sqrt c)⁻¹) ^ 2 - 1 - 2 * Real.log ((Real.sqrt c)⁻¹) ≤
      (1 + (klSharpCoeff c - 1)) * ((Real.sqrt c)⁻¹ - 1) ^ 2 := by
    apply le_of_eq
    have hsq := Real.sq_sqrt hc0.le
    have hlog : Real.log c = 2 * Real.log (Real.sqrt c) := by
      rw [Real.log_sqrt hc0.le]; ring
    unfold klSharpCoeff
    rw [tailMassCoeff_eq_div hc, Real.log_inv, hlog]
    set s := Real.sqrt c
    have hs0' : s ≠ 0 := ne_of_gt hs0
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hs)
    rw [← hsq]
    field_simp
    ring
  have h := reverseKL_sq_le_mul_sq_sub_one_of_ge ha (inv_pos.mpr hs0) hD hu
  rw [Real.sq_sqrt hy0.le, Real.log_sqrt hy0.le, add_sub_cancel] at h
  linarith

/-- The sharp pointwise KL upper kernel on `[0, c]`. -/
theorem klFun_le_klSharpCoeff_mul_hellinger {c x : ℝ} (hc : 1 < c) (hx : 0 ≤ x)
    (hxc : x ≤ c) :
    InformationTheory.klFun x ≤ klSharpCoeff c * (Real.sqrt x - 1) ^ 2 := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · simp only [InformationTheory.klFun, Real.sqrt_zero]
    norm_num
    linarith [two_le_klSharpCoeff hc]
  · have hinv : 1 / c ≤ x⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hx hxc
    have h := reverseKL_le_klSharpCoeff hc hinv
    calc
      InformationTheory.klFun x = x * (x⁻¹ - 1 - Real.log x⁻¹) := klFun_eq_mul_reverseKL hx
      _ ≤ x * (klSharpCoeff c * (Real.sqrt x⁻¹ - 1) ^ 2) :=
        mul_le_mul_of_nonneg_left h hx.le
      _ = klSharpCoeff c * (x * (Real.sqrt x⁻¹ - 1) ^ 2) := by ring
      _ = klSharpCoeff c * (Real.sqrt x - 1) ^ 2 := by rw [mul_inverse_hellinger_kernel hx]

/-- The sharp pointwise KL upper kernel with the log tail, on `[0, ∞)`. -/
theorem klFun_le_klSharp_hellinger_add_logTail {c x : ℝ} (hc : 1 < c) (hx : 0 ≤ x) :
    InformationTheory.klFun x ≤
      klSharpCoeff c * (Real.sqrt x - 1) ^ 2 + logTailDensityKernel c x := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · have h := klFun_le_klSharpCoeff_mul_hellinger hc le_rfl (by linarith : (0 : ℝ) ≤ c)
    have h0 : logTailDensityKernel c 0 = 0 := by
      simp only [logTailDensityKernel, Real.log_zero, not_lt.mpr (Real.log_pos hc).le,
        ↓reduceIte]
    rw [h0, add_zero]
    exact h
  · by_cases ht : Real.log c < Real.log x
    · have hcx : c < x := (Real.log_lt_log_iff (by linarith : 0 < c) hx).mp ht
      have hnonneg := mul_nonneg (klSharpCoeff_pos hc).le (sq_nonneg (Real.sqrt x - 1))
      simp only [logTailDensityKernel, ht, ↓reduceIte]
      unfold InformationTheory.klFun
      linarith
    · have hxc : x ≤ c := (Real.log_le_log_iff hx (by linarith : 0 < c)).mp (not_lt.mp ht)
      simpa only [logTailDensityKernel, ht, ↓reduceIte, add_zero] using
        klFun_le_klSharpCoeff_mul_hellinger hc hx.le hxc

/-! ### The KL lower tail kernel -/

/-- `(1 - 1/x) log c ≤ (1 - 1/c) log x` for `1 < c ≤ x`. -/
theorem one_sub_inv_mul_log_le {c x : ℝ} (hc : 1 < c) (hcx : c ≤ x) :
    (1 - 1 / x) * Real.log c ≤ (1 - 1 / c) * Real.log x := by
  have hc0 : 0 < c := lt_trans (by norm_num) hc
  let φ : ℝ → ℝ := fun v ↦ (1 - 1 / c) * Real.log v - (1 - v⁻¹) * Real.log c
  have hd (v : ℝ) (hv : 0 < v) :
      HasDerivAt φ (((1 - 1 / c) * v - Real.log c) / v ^ 2) v := by
    have h := ((Real.hasDerivAt_log hv.ne').const_mul (1 - 1 / c)).sub
      (((hasDerivAt_inv hv.ne').const_sub 1).mul_const (Real.log c))
    convert h using 1
    field_simp
  have hmono : MonotoneOn φ (Set.Icc c x) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc c x)
      (fun v hv ↦ (hd v (lt_of_lt_of_le hc0 hv.1)).continuousAt.continuousWithinAt)
      (fun v hv ↦ (hd v (lt_of_lt_of_le hc0 (interior_subset hv).1)).hasDerivWithinAt)
    intro v hv
    have hvI := interior_subset hv
    have hv0 : 0 < v := lt_of_lt_of_le hc0 hvI.1
    have hw : 0 ≤ 1 - 1 / c := by
      have : 1 / c ≤ 1 := ((div_lt_one hc0).mpr hc).le
      linarith
    have h1 : (1 - 1 / c) * c ≤ (1 - 1 / c) * v := mul_le_mul_of_nonneg_left hvI.1 hw
    have h2 : (1 - 1 / c) * c = c - 1 := by field_simp
    have h3 := Real.log_le_sub_one_of_pos hc0
    exact div_nonneg (by linarith) (sq_nonneg v)
  have h := hmono (show c ∈ Set.Icc c x from ⟨le_rfl, hcx⟩)
    (show x ∈ Set.Icc c x from ⟨hcx, le_rfl⟩) hcx
  simp only [φ] at h
  simp only [one_div] at h ⊢
  linarith

/-- The sharp pointwise KL lower tail kernel on `[0, ∞)`. -/
theorem klTailLowerSharpCoeff_mul_logTail_le_klFun {c x : ℝ} (hc : 1 < c) (hx : 0 ≤ x) :
    klTailLowerSharpCoeff c * logTailDensityKernel c x ≤ InformationTheory.klFun x := by
  by_cases ht : Real.log c < Real.log x
  · have hc0 : 0 < c := lt_trans (by norm_num) hc
    have hx0 : 0 < x := by
      rcases eq_or_lt_of_le hx with rfl | h
      · rw [Real.log_zero] at ht
        exact absurd ht (not_lt.mpr (Real.log_pos hc).le)
      · exact h
    have hcx : c < x := (Real.log_lt_log_iff hc0 hx0).mp ht
    have hL : 0 < Real.log c := Real.log_pos hc
    have hm := one_sub_inv_mul_log_le hc hcx.le
    have hxm : x * ((1 - 1 / x) * Real.log c) ≤ x * ((1 - 1 / c) * Real.log x) :=
      mul_le_mul_of_nonneg_left hm hx0.le
    have hx1 : x * (1 - 1 / x) = x - 1 := by field_simp
    have hr : (1 - 1 / c) / Real.log c * Real.log c = 1 - 1 / c :=
      div_mul_cancel₀ _ hL.ne'
    have key : (x - 1) * Real.log c ≤
        ((1 - 1 / c) / Real.log c * (x * Real.log x)) * Real.log c := by
      calc
        (x - 1) * Real.log c = x * ((1 - 1 / x) * Real.log c) := by rw [← hx1]; ring
        _ ≤ x * ((1 - 1 / c) * Real.log x) := hxm
        _ = ((1 - 1 / c) / Real.log c * Real.log c) * (x * Real.log x) := by rw [hr]; ring
        _ = _ := by ring
    have key' := le_of_mul_le_mul_right key hL
    simp only [logTailDensityKernel, ht, ↓reduceIte]
    unfold klTailLowerSharpCoeff InformationTheory.klFun
    linarith
  · simpa only [logTailDensityKernel, ht, ↓reduceIte, mul_zero] using
      InformationTheory.klFun_nonneg hx

/-! ### Measure-level bounds -/

/-- KL is bounded by `K(c)` times squared Hellinger distance plus the strict log tail. -/
theorem kl_le_hellinger_add_tailLogMoment_sharp : KLUpperSharpStatement.{u} := by
  intro α _ μ ν _ _ c hc
  by_cases h : μ ≪ ν
  · unfold kl
    rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac h]
    have hg : Measurable (fun x ↦ ENNReal.ofReal
        ((Real.sqrt ((μ.rnDeriv ν x).toReal) - 1) ^ 2)) := by fun_prop
    calc
      (∫⁻ x, ENNReal.ofReal (InformationTheory.klFun ((μ.rnDeriv ν x).toReal)) ∂ν)
          ≤ ∫⁻ x, ENNReal.ofReal (klSharpCoeff c) *
              ENNReal.ofReal ((Real.sqrt ((μ.rnDeriv ν x).toReal) - 1) ^ 2) +
              ENNReal.ofReal (logTailDensityKernel c ((μ.rnDeriv ν x).toReal)) ∂ν := by
        apply lintegral_mono
        intro x
        have hp := ENNReal.ofReal_le_ofReal
          (klFun_le_klSharp_hellinger_add_logTail hc (x := (μ.rnDeriv ν x).toReal)
            ENNReal.toReal_nonneg)
        rwa [ENNReal.ofReal_add
          (mul_nonneg (klSharpCoeff_pos hc).le (sq_nonneg _))
          (logTailDensityKernel_nonneg hc ENNReal.toReal_nonneg),
          ENNReal.ofReal_mul (klSharpCoeff_pos hc).le] at hp
      _ = ENNReal.ofReal (klSharpCoeff c) *
            (∫⁻ x, ENNReal.ofReal ((Real.sqrt ((μ.rnDeriv ν x).toReal) - 1) ^ 2) ∂ν) +
            (∫⁻ x, ENNReal.ofReal (logTailDensityKernel c ((μ.rnDeriv ν x).toReal)) ∂ν) := by
        calc
          _ = (∫⁻ x, ENNReal.ofReal (klSharpCoeff c) *
                ENNReal.ofReal ((Real.sqrt ((μ.rnDeriv ν x).toReal) - 1) ^ 2) ∂ν) +
                (∫⁻ x, ENNReal.ofReal
                  (logTailDensityKernel c ((μ.rnDeriv ν x).toReal)) ∂ν) := by
            simpa only [Pi.mul_apply] using
              (lintegral_add_left (measurable_const.mul hg)
                (fun x ↦ ENNReal.ofReal (logTailDensityKernel c ((μ.rnDeriv ν x).toReal))))
          _ = _ := by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ = ENNReal.ofReal (klSharpCoeff c) * hellingerSq μ ν + tailLogMoment μ ν c 1 := by
        rw [← hellingerSq_eq_lintegral_of_ac h, ← tailLogMoment_one_eq_densityKernel h]
  · simp [kl, InformationTheory.klDiv_of_not_ac h, tailLogMoment_of_not_ac h]

/-- `L ≤ (e δ)⁻¹ exp (δ L)` for every real `L` and `δ > 0`. -/
theorem le_inv_exp_one_mul_mul_exp {δ : ℝ} (hδ : 0 < δ) (L : ℝ) :
    L ≤ (Real.exp 1 * δ)⁻¹ * Real.exp (δ * L) := by
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have h1 := Real.add_one_le_exp (δ * L - 1)
  rw [Real.exp_sub, sub_add_cancel, le_div_iff₀ he] at h1
  rw [← div_eq_inv_mul, le_div_iff₀ (mul_pos he hδ)]
  linarith [show L * (Real.exp 1 * δ) = δ * L * Real.exp 1 by ring]

/-- The log tail is bounded by the power tail with factor `(e δ)⁻¹`, including infinity. -/
theorem tailLogMoment_one_le_tailPower_sharp : TailLogPowerSharpStatement.{u} := by
  intro α _ μ ν c δ hδ
  classical
  have hpos : 0 < (Real.exp 1 * δ)⁻¹ := inv_pos.mpr (mul_pos (Real.exp_pos 1) hδ)
  by_cases h : μ ≪ ν
  · rw [tailLogMoment_of_ac h, tailPower_of_ac h]
    calc
      (∫⁻ x in tailEvent μ ν c, ENNReal.ofReal (llr μ ν x ^ (1 : ℝ)) ∂μ) ≤
          ∫⁻ x in tailEvent μ ν c, ENNReal.ofReal (Real.exp 1 * δ)⁻¹ *
            ENNReal.ofReal (Real.exp (δ * llr μ ν x)) ∂μ := by
        apply lintegral_mono
        intro x
        dsimp only
        rw [Real.rpow_one, ← ENNReal.ofReal_mul hpos.le]
        exact ENNReal.ofReal_le_ofReal (le_inv_exp_one_mul_mul_exp hδ _)
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  · rw [tailLogMoment_of_not_ac h, tailPower_of_not_ac h]
    rw [ENNReal.mul_top (ENNReal.ofReal_pos.mpr hpos).ne']

/-- Theorem 1's KL upper bound with `K(c)` and `(e δ)⁻¹`. -/
theorem kl_le_hellinger_add_tailPower_sharp : KLUpperPowerSharpStatement.{u} := by
  intro α _ μ ν _ _ c δ hc hδ
  exact (kl_le_hellinger_add_tailLogMoment_sharp μ ν c hc).trans
    (add_le_add_right (tailLogMoment_one_le_tailPower_sharp μ ν c δ hδ) _)

/-- The cutoff log tail is controlled by KL with the sharp coefficient. -/
theorem klTailLowerSharpCoeff_mul_tailLogMoment_le_kl : KLLowerTailSharpStatement.{u} := by
  intro α _ μ ν _ _ c hc
  by_cases h : μ ≪ ν
  · rw [tailLogMoment_one_eq_densityKernel h]
    unfold kl
    rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac h]
    calc
      ENNReal.ofReal (klTailLowerSharpCoeff c) *
          (∫⁻ x, ENNReal.ofReal (logTailDensityKernel c ((μ.rnDeriv ν x).toReal)) ∂ν)
          = ∫⁻ x, ENNReal.ofReal (klTailLowerSharpCoeff c) *
              ENNReal.ofReal (logTailDensityKernel c ((μ.rnDeriv ν x).toReal)) ∂ν :=
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ x, ENNReal.ofReal (InformationTheory.klFun ((μ.rnDeriv ν x).toReal)) ∂ν := by
        apply lintegral_mono
        intro x
        dsimp only
        rw [← ENNReal.ofReal_mul (klTailLowerSharpCoeff_pos hc).le]
        exact ENNReal.ofReal_le_ofReal
          (klTailLowerSharpCoeff_mul_logTail_le_klFun hc ENNReal.toReal_nonneg)
  · simp [kl, InformationTheory.klDiv_of_not_ac h]

end Hellinger.Sharp
