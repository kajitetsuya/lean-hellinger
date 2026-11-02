/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.MLE.Defs
public import Hellinger.HellingerBridge

/-!
Bridges from pointwise densities to the measure-level objects, for an arbitrary reference
measure `μ` (no σ-finiteness). Every Radon--Nikodym computation is carried out relative to
the finite measure `(p + q) · μ`, which dominates both laws; `μ` itself never enters a
Radon--Nikodym derivative.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Hellinger.MLE

variable {𝒳 : Type*} [MeasurableSpace 𝒳] {μ : Measure 𝒳} {p q r : 𝒳 → ℝ≥0}

/-! ### Elementary facts about laws -/

theorem law_apply (μ : Measure 𝒳) (p : 𝒳 → ℝ≥0) {s : Set 𝒳} (hs : MeasurableSet s) :
    law μ p s = ∫⁻ x in s, (p x : ℝ≥0∞) ∂μ :=
  withDensity_apply _ hs

theorem law_univ (μ : Measure 𝒳) (p : 𝒳 → ℝ≥0) :
    law μ p univ = ∫⁻ x, (p x : ℝ≥0∞) ∂μ := by
  rw [law_apply μ p MeasurableSet.univ, Measure.restrict_univ]

theorem isProbabilityMeasure_law (h : IsProbDensity μ p) : IsProbabilityMeasure (law μ p) :=
  ⟨by rw [law_univ, h.lintegral_eq_one]⟩

theorem isFiniteMeasure_law (hfin : ∫⁻ x, (p x : ℝ≥0∞) ∂μ ≠ ∞) : IsFiniteMeasure (law μ p) :=
  isFiniteMeasure_withDensity hfin

theorem law_add (hp : Measurable p) (q : 𝒳 → ℝ≥0) : law μ (p + q) = law μ p + law μ q := by
  unfold law
  rw [← withDensity_add_left hp.coe_nnreal_ennreal]
  congr 1

theorem lintegral_add_ne_top (hp : Measurable p) (hpf : ∫⁻ x, (p x : ℝ≥0∞) ∂μ ≠ ∞)
    (hqf : ∫⁻ x, (q x : ℝ≥0∞) ∂μ ≠ ∞) : ∫⁻ x, ((p + q) x : ℝ≥0∞) ∂μ ≠ ∞ := by
  simp only [Pi.add_apply, ENNReal.coe_add]
  rw [lintegral_add_left hp.coe_nnreal_ennreal]
  exact ENNReal.add_ne_top.2 ⟨hpf, hqf⟩

/-- `law μ p`-almost every point has positive density. -/
theorem ae_law_pos (hp : Measurable p) : ∀ᵐ x ∂law μ p, 0 < p x := by
  unfold law
  rw [ae_withDensity_iff hp.coe_nnreal_ennreal]
  exact Filter.Eventually.of_forall fun x hx ↦ pos_iff_ne_zero.2 (by exact_mod_cast hx)

/-- The ratio `a / b` recovers `a` after multiplying by `b`, whenever `b = 0` forces `a = 0`. -/
theorem div_mul_cancel_of_imp {a b : ℝ≥0} (h : b = 0 → a = 0) : a / b * b = a := by
  rcases eq_or_ne b 0 with hb | hb
  · simp [h hb, hb]
  · exact div_mul_cancel₀ a hb

/-- Re-expressing a law relative to a dominating law. -/
theorem law_eq_withDensity_div (hp : Measurable p) (hr : Measurable r)
    (h : ∀ x, r x = 0 → p x = 0) :
    law μ p = (law μ r).withDensity fun x ↦ ((p x / r x : ℝ≥0) : ℝ≥0∞) := by
  unfold law
  have hm : Measurable fun x ↦ ((p x / r x : ℝ≥0) : ℝ≥0∞) := (hp.div hr).coe_nnreal_ennreal
  rw [← withDensity_mul μ hr.coe_nnreal_ennreal hm]
  congr 1
  funext x
  simp only [Pi.mul_apply]
  rw [← ENNReal.coe_mul, mul_comm, div_mul_cancel_of_imp (h x)]

/-! ### Absolute continuity -/

theorem law_ac_law_iff (hp : Measurable p) (hq : Measurable q) :
    law μ p ≪ law μ q ↔ μ {x | 0 < p x ∧ q x = 0} = 0 := by
  have hA : MeasurableSet {x | 0 < p x ∧ q x = 0} :=
    (measurableSet_lt measurable_const hp).inter (measurableSet_eq_fun hq measurable_const)
  constructor
  · intro h
    have hQ : law μ q {x | 0 < p x ∧ q x = 0} = 0 := by
      rw [law_apply μ q hA, setLIntegral_eq_zero_iff hA hq.coe_nnreal_ennreal]
      exact Filter.Eventually.of_forall fun x hx ↦ by simp [hx.2]
    have hP := h hQ
    rw [law_apply μ p hA, setLIntegral_eq_zero_iff hA hp.coe_nnreal_ennreal] at hP
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hP] with x hx hxA
    have : p x = 0 := by exact_mod_cast hx hxA
    exact hxA.1.ne' this
  · intro h
    refine Measure.AbsolutelyContinuous.mk fun s hs hQs ↦ ?_
    rw [law_apply μ q hs, setLIntegral_eq_zero_iff hs hq.coe_nnreal_ennreal] at hQs
    rw [law_apply μ p hs, setLIntegral_eq_zero_iff hs hp.coe_nnreal_ennreal]
    filter_upwards [hQs, measure_eq_zero_iff_ae_notMem.1 h] with x hx hxA hxs
    by_contra hne
    exact hxA ⟨pos_iff_ne_zero.2 (by exact_mod_cast hne), by exact_mod_cast hx hxs⟩

/-- Under `law μ p ≪ law μ q`, `law μ p`-almost every point has positive `q`-density. -/
theorem ae_law_pos_right (hq : Measurable q) (hac : law μ p ≪ law μ q) :
    ∀ᵐ x ∂law μ p, 0 < q x :=
  hac.ae_le (ae_law_pos hq)

/-! ### Squared Hellinger distance -/

theorem hellingerFunSq_eq_hellingerSq_law (hp : Measurable p) (hq : Measurable q)
    (hpf : ∫⁻ x, (p x : ℝ≥0∞) ∂μ ≠ ∞) (hqf : ∫⁻ x, (q x : ℝ≥0∞) ∂μ ≠ ∞) :
    hellingerFunSq μ p q = hellingerSq (law μ p) (law μ q) := by
  have hrm : Measurable (p + q) := hp.add hq
  have : IsFiniteMeasure (law μ (p + q)) := isFiniteMeasure_law (lintegral_add_ne_top hp hpf hqf)
  have hP : law μ p = (law μ (p + q)).withDensity fun x ↦ ((p x / (p + q) x : ℝ≥0) : ℝ≥0∞) :=
    law_eq_withDensity_div hp hrm fun x hx ↦ (add_eq_zero.1 hx).1
  have hQ : law μ q = (law μ (p + q)).withDensity fun x ↦ ((q x / (p + q) x : ℝ≥0) : ℝ≥0∞) :=
    law_eq_withDensity_div hq hrm fun x hx ↦ (add_eq_zero.1 hx).2
  have hPd : (law μ p).rnDeriv (law μ (p + q)) =ᵐ[law μ (p + q)]
      fun x ↦ ((p x / (p + q) x : ℝ≥0) : ℝ≥0∞) := by
    conv_lhs => rw [hP]
    exact Measure.rnDeriv_withDensity _ (hp.div hrm).coe_nnreal_ennreal
  have hQd : (law μ q).rnDeriv (law μ (p + q)) =ᵐ[law μ (p + q)]
      fun x ↦ ((q x / (p + q) x : ℝ≥0) : ℝ≥0∞) := by
    conv_lhs => rw [hQ]
    exact Measure.rnDeriv_withDensity _ (hq.div hrm).coe_nnreal_ennreal
  have hpair : pairMeasure (law μ p) (law μ q) = law μ (p + q) := (law_add hp q).symm
  unfold hellingerSq pairDensity
  rw [hpair, eq_comm]
  calc
    _ = ∫⁻ x, ENNReal.ofReal ((Real.sqrt ((p x / (p + q) x : ℝ≥0) : ℝ) -
          Real.sqrt ((q x / (p + q) x : ℝ≥0) : ℝ)) ^ 2) ∂law μ (p + q) := by
      apply lintegral_congr_ae
      filter_upwards [hPd, hQd] with x h1 h2
      rw [h1, h2, ENNReal.coe_toReal, ENNReal.coe_toReal]
    _ = ∫⁻ x, ((p + q) x : ℝ≥0∞) * ENNReal.ofReal ((Real.sqrt ((p x / (p + q) x : ℝ≥0) : ℝ) -
          Real.sqrt ((q x / (p + q) x : ℝ≥0) : ℝ)) ^ 2) ∂μ :=
      lintegral_withDensity_eq_lintegral_mul μ hrm.coe_nnreal_ennreal (by fun_prop)
    _ = _ := by
      unfold hellingerFunSq
      apply lintegral_congr
      intro x
      have h1 : ((p x / (p + q) x : ℝ≥0) : ℝ) * ((p + q) x : ℝ) = p x := by
        rw [← NNReal.coe_mul, div_mul_cancel_of_imp (a := p x) (b := (p + q) x)
          fun hx ↦ (add_eq_zero.1 hx).1]
      have h2 : ((q x / (p + q) x : ℝ≥0) : ℝ) * ((p + q) x : ℝ) = q x := by
        rw [← NNReal.coe_mul, div_mul_cancel_of_imp (a := q x) (b := (p + q) x)
          fun hx ↦ (add_eq_zero.1 hx).2]
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _),
        Hellinger.sqrt_sub_sqrt_sq_homogeneous (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
          (NNReal.coe_nonneg _), h1, h2]

theorem hellingerFunSq_eq_hellingerSq_law_of_isProbDensity (hp : IsProbDensity μ p)
    (hq : IsProbDensity μ q) :
    hellingerFunSq μ p q = hellingerSq (law μ p) (law μ q) :=
  hellingerFunSq_eq_hellingerSq_law hp.measurable hq.measurable
    (by rw [hp.lintegral_eq_one]; exact ENNReal.one_ne_top)
    (by rw [hq.lintegral_eq_one]; exact ENNReal.one_ne_top)

/-! ### Radon--Nikodym derivative and log-likelihood ratio -/

/-- For two densities relative to a σ-finite measure `ρ`, the Radon--Nikodym derivative is
the ratio of the densities, almost everywhere for the second measure. -/
theorem rnDeriv_withDensity_withDensity_ae (ρ : Measure 𝒳) [SigmaFinite ρ] {f g : 𝒳 → ℝ≥0}
    (hf : Measurable f) (hg : Measurable g)
    [SigmaFinite (ρ.withDensity fun x ↦ (f x : ℝ≥0∞))]
    [SigmaFinite (ρ.withDensity fun x ↦ (g x : ℝ≥0∞))] :
    (ρ.withDensity fun x ↦ (f x : ℝ≥0∞)).rnDeriv (ρ.withDensity fun x ↦ (g x : ℝ≥0∞))
      =ᵐ[ρ.withDensity fun x ↦ (g x : ℝ≥0∞)] fun x ↦ (f x : ℝ≥0∞) / g x := by
  set P := ρ.withDensity fun x ↦ (f x : ℝ≥0∞)
  set Q := ρ.withDensity fun x ↦ (g x : ℝ≥0∞)
  have hQρ : Q ≪ ρ := withDensity_absolutelyContinuous _ _
  have hchain : P.rnDeriv Q * Q.rnDeriv ρ =ᵐ[Q] P.rnDeriv ρ :=
    Measure.rnDeriv_mul_rnDeriv' hQρ
  have hPρ : P.rnDeriv ρ =ᵐ[ρ] fun x ↦ (f x : ℝ≥0∞) :=
    Measure.rnDeriv_withDensity _ hf.coe_nnreal_ennreal
  have hQρ' : Q.rnDeriv ρ =ᵐ[ρ] fun x ↦ (g x : ℝ≥0∞) :=
    Measure.rnDeriv_withDensity _ hg.coe_nnreal_ennreal
  have hgpos : ∀ᵐ x ∂Q, (g x : ℝ≥0∞) ≠ 0 :=
    (ae_withDensity_iff hg.coe_nnreal_ennreal).2 (Filter.Eventually.of_forall fun _ h ↦ h)
  filter_upwards [hchain, hQρ.ae_le hPρ, hQρ.ae_le hQρ', hgpos] with x hc h1 h2 hg0
  simp only [Pi.mul_apply, h1, h2] at hc
  exact (ENNReal.eq_div_iff hg0 ENNReal.coe_ne_top).2 (by rw [mul_comm]; exact hc)

/-- The Radon--Nikodym derivative of one law with respect to another is the density ratio,
`law μ q`-almost everywhere. No absolute continuity and no σ-finiteness of `μ` is needed. -/
theorem rnDeriv_law_law_ae_right (hp : Measurable p) (hq : Measurable q)
    (hpf : ∫⁻ x, (p x : ℝ≥0∞) ∂μ ≠ ∞) (hqf : ∫⁻ x, (q x : ℝ≥0∞) ∂μ ≠ ∞) :
    (law μ p).rnDeriv (law μ q) =ᵐ[law μ q] fun x ↦ ((p x / q x : ℝ≥0) : ℝ≥0∞) := by
  have hrm : Measurable (p + q) := hp.add hq
  have : IsFiniteMeasure (law μ (p + q)) := isFiniteMeasure_law (lintegral_add_ne_top hp hpf hqf)
  have : IsFiniteMeasure (law μ p) := isFiniteMeasure_law hpf
  have : IsFiniteMeasure (law μ q) := isFiniteMeasure_law hqf
  have hP : law μ p = (law μ (p + q)).withDensity fun x ↦ ((p x / (p + q) x : ℝ≥0) : ℝ≥0∞) :=
    law_eq_withDensity_div hp hrm fun x hx ↦ (add_eq_zero.1 hx).1
  have hQ : law μ q = (law μ (p + q)).withDensity fun x ↦ ((q x / (p + q) x : ℝ≥0) : ℝ≥0∞) :=
    law_eq_withDensity_div hq hrm fun x hx ↦ (add_eq_zero.1 hx).2
  have key := rnDeriv_withDensity_withDensity_ae (law μ (p + q)) (hp.div hrm) (hq.div hrm)
    (f := fun x ↦ p x / (p + q) x) (g := fun x ↦ q x / (p + q) x)
  rw [← hP, ← hQ] at key
  filter_upwards [key, ae_law_pos hq] with x hx hqx
  rw [hx]
  have hr0 : (p + q) x ≠ 0 := by
    simp only [Pi.add_apply]
    exact (lt_of_lt_of_le hqx le_add_self).ne'
  have hd : q x / (p + q) x ≠ 0 := div_ne_zero hqx.ne' hr0
  rw [← ENNReal.coe_div hd, div_div_div_cancel_right₀ hr0]

theorem rnDeriv_law_law_ae (hp : Measurable p) (hq : Measurable q)
    (hpf : ∫⁻ x, (p x : ℝ≥0∞) ∂μ ≠ ∞) (hqf : ∫⁻ x, (q x : ℝ≥0∞) ∂μ ≠ ∞)
    (hac : law μ p ≪ law μ q) :
    (law μ p).rnDeriv (law μ q) =ᵐ[law μ p] fun x ↦ ((p x / q x : ℝ≥0) : ℝ≥0∞) :=
  hac.ae_le (rnDeriv_law_law_ae_right hp hq hpf hqf)

/-- The log-likelihood ratio of two laws is the pointwise log density ratio, `law μ p`-a.e.
On this a.e. set both densities are positive (`ae_law_pos`, `ae_law_pos_right`). -/
theorem llr_law_ae_eq_of_finite (hp : Measurable p) (hq : Measurable q)
    (hpf : ∫⁻ x, (p x : ℝ≥0∞) ∂μ ≠ ∞) (hqf : ∫⁻ x, (q x : ℝ≥0∞) ∂μ ≠ ∞)
    (hac : law μ p ≪ law μ q) :
    llr (law μ p) (law μ q) =ᵐ[law μ p] fun x ↦ Real.log ((p x : ℝ) / q x) := by
  filter_upwards [rnDeriv_law_law_ae hp hq hpf hqf hac] with x hx
  rw [llr, hx, ENNReal.coe_toReal, NNReal.coe_div]

theorem llr_law_ae_eq (hp : IsProbDensity μ p) (hq : IsProbDensity μ q)
    (hac : law μ p ≪ law μ q) :
    llr (law μ p) (law μ q) =ᵐ[law μ p] fun x ↦ Real.log ((p x : ℝ) / q x) :=
  llr_law_ae_eq_of_finite hp.measurable hq.measurable
    (by rw [hp.lintegral_eq_one]; exact ENNReal.one_ne_top)
    (by rw [hq.lintegral_eq_one]; exact ENNReal.one_ne_top) hac

/-! ### Kullback–Leibler divergence -/

/-- Integrability of the log-likelihood ratio under `law μ p`, in density form. -/
theorem integrable_llr_law_iff (hp : IsProbDensity μ p) (hq : IsProbDensity μ q)
    (hac : law μ p ≪ law μ q) :
    Integrable (llr (law μ p) (law μ q)) (law μ p) ↔
      Integrable (fun x ↦ (p x : ℝ) * Real.log ((p x : ℝ) / q x)) μ := by
  rw [integrable_congr (llr_law_ae_eq hp hq hac), law,
    integrable_withDensity_iff_integrable_smul hp.measurable]
  simp only [NNReal.smul_def, smul_eq_mul]

/-- The Kullback–Leibler divergence between two laws, in density form, on the finite branch. -/
theorem kl_law_eq (hp : IsProbDensity μ p) (hq : IsProbDensity μ q)
    (hac : law μ p ≪ law μ q)
    (hint : Integrable (fun x ↦ (p x : ℝ) * Real.log ((p x : ℝ) / q x)) μ) :
    kl (law μ p) (law μ q) =
      ENNReal.ofReal (∫ x, (p x : ℝ) * Real.log ((p x : ℝ) / q x) ∂μ) := by
  have : IsProbabilityMeasure (law μ p) := isProbabilityMeasure_law hp
  have : IsProbabilityMeasure (law μ q) := isProbabilityMeasure_law hq
  rw [kl, InformationTheory.klDiv_of_ac_of_integrable hac
    ((integrable_llr_law_iff hp hq hac).2 hint), probReal_univ, probReal_univ,
    add_sub_cancel_right, integral_congr_ae (llr_law_ae_eq hp hq hac), law,
    integral_withDensity_eq_integral_smul hp.measurable]
  simp only [NNReal.smul_def, smul_eq_mul]

end Hellinger.MLE
