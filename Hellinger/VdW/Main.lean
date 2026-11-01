/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.MLE.External
public import Hellinger.MLE.ProbabilityRates
public import Hellinger.VdW.MgfMaximal
public import Hellinger.VdW.Chaining
public import Hellinger.VdW.EntropySums
public import Hellinger.VdW.Covers
public import Hellinger.VdW.EmpiricalLinear

/-!
Final assembly of the proof of van der Vaart and Wellner (2023), Theorem 2.14.18', in the
package formulation `Hellinger.MLE.External.VdW_2_14_18_prime`, with the universal constant
`K₀ = 80`. The proof is outlined in `docs/Theorem8.md`.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal NNReal

namespace Hellinger.VdW

open Hellinger.MLE

namespace BracketChain

variable {𝒳 : Type*} {F : Set (𝒳 → ℝ)} (C : BracketChain F) (t : ℕ → ℝ)

open Classical in
/-- The `B`-majorant family, the zero function off realized tuples. -/
noncomputable def gB (q : ℕ) (k : Tup C.N q) : 𝒳 → ℝ :=
  if C.Realized q k then C.termB t q k else 0

open Classical in
/-- The link family, the zero function off realized tuples. -/
noncomputable def gL (q : ℕ) (k : Tup C.N q) : 𝒳 → ℝ :=
  if C.Realized q k then C.link t q k else 0

theorem gB_idx (q : ℕ) (f : F) : C.gB t q (C.idx q f) = C.termB t q (C.idx q f) := by
  unfold gB; exact ite_eq_left ⟨f, rfl⟩

theorem gL_idx (q : ℕ) (f : F) : C.gL t q (C.idx q f) = C.link t q (C.idx q f) := by
  unfold gL; exact ite_eq_left ⟨f, rfl⟩

theorem termB_idx_nonneg (q : ℕ) (f : F) (x : 𝒳) : 0 ≤ C.termB t q (C.idx q f) x :=
  mul_nonneg (C.width_idx_nonneg q f x) (C.indB_nonneg t q _ x)

theorem termB_idx_le (q : ℕ) (f : F) (x : 𝒳) :
    C.termB t q (C.idx q f) x ≤ C.u q (C.cell q f) x - C.l q (C.cell q f) x :=
  (mul_le_of_le_one_right (C.width_idx_nonneg q f x) (C.indB_le_one t q _ x)).trans
    (C.width_idx_le q f x)

theorem abs_link_idx_le (q : ℕ) (f : F) (x : 𝒳) :
    |C.link t q (C.idx q f) x| ≤
      C.u (q - 1) (C.cell (q - 1) f) x - C.l (q - 1) (C.cell (q - 1) f) x :=
  (C.abs_link_le t q f x).trans
    ((mul_le_of_le_one_right (C.width_idx_nonneg _ f x) (C.indA_le_one t _ _ x)).trans
      (C.width_idx_le _ f x))

/-- `termB ≤ width² / t` pointwise. -/
theorem termB_le_sq_div {q : ℕ} (ht : 0 < t q) (k : Tup C.N q) (x : 𝒳) :
    C.termB t q k x ≤ C.width q k x ^ 2 / t q := by
  unfold termB indB
  split_ifs with h1 h2
  · rw [mul_one, mul_one, le_div_iff₀ ht]; nlinarith
  · simp only [mul_zero]; positivity
  · simp only [zero_mul, mul_zero]; positivity
  · simp only [mul_zero]; positivity

/-! ### Measure-theoretic bounds on the families -/

variable [MeasurableSpace 𝒳] (P : Measure 𝒳) [IsProbabilityMeasure P]

theorem bernsteinFunSq_zero : bernsteinFunSq P (0 : 𝒳 → ℝ) = 0 := by
  simp [bernsteinFunSq, bernsteinKernel]

variable {P C} {δ : ℝ}

section Bounds

variable (hF : ∀ f ∈ F, Measurable f ∧ bernsteinFunSq P f ≤ ENNReal.ofReal (δ ^ 2))
  (hm : ∀ q i, Measurable (C.l q i) ∧ Measurable (C.u q i))
  (hs : ∀ q i, bernsteinFunSq P (C.u q i - C.l q i) < ENNReal.ofReal ((δ / 2 ^ q) ^ 2))

include hF in
theorem bernsteinFunSq_rep_le (q : ℕ) (k : Tup C.N q) :
    bernsteinFunSq P (C.rep q k) ≤ ENNReal.ofReal (δ ^ 2) := by
  by_cases h : C.Realized q k
  · exact (hF _ (C.rep_mem h)).2
  · rw [C.rep_of_not_realized h, bernsteinFunSq_zero]; exact bot_le

include hs in
theorem bernsteinFunSq_gB_lt (hδ : 0 < δ) (q : ℕ) (k : Tup C.N q) :
    bernsteinFunSq P (C.gB t q k) < ENNReal.ofReal ((δ / 2 ^ q) ^ 2) := by
  unfold gB
  split_ifs with h
  · obtain ⟨f, rfl⟩ := h
    refine lt_of_le_of_lt (bernsteinFunSq_mono P fun x => ?_) (hs q (C.cell q f))
    rw [abs_of_nonneg (C.termB_idx_nonneg t q f x)]
    exact (C.termB_idx_le t q f x).trans (le_abs_self _)
  · rw [bernsteinFunSq_zero]; exact ENNReal.ofReal_pos.2 (by positivity)

include hs in
theorem bernsteinFunSq_gL_lt (hδ : 0 < δ) (q : ℕ) (k : Tup C.N q) :
    bernsteinFunSq P (C.gL t q k) < ENNReal.ofReal ((δ / 2 ^ (q - 1)) ^ 2) := by
  unfold gL
  split_ifs with h
  · obtain ⟨f, rfl⟩ := h
    refine lt_of_le_of_lt (bernsteinFunSq_mono P fun x => ?_) (hs (q - 1) (C.cell (q - 1) f))
    exact (C.abs_link_idx_le t q f x).trans (le_abs_self _)
  · rw [bernsteinFunSq_zero]; exact ENNReal.ofReal_pos.2 (by positivity)

omit [IsProbabilityMeasure P] in
include hm in
theorem measurable_gB (q : ℕ) (k : Tup C.N q) : Measurable (C.gB t q k) := by
  unfold gB
  split_ifs
  · exact measurable_termB t hm q k
  · exact measurable_const

omit [IsProbabilityMeasure P] in
include hF hm in
theorem measurable_gL (q : ℕ) (k : Tup C.N q) : Measurable (C.gL t q k) := by
  unfold gL
  split_ifs
  · exact measurable_link t (fun g hg => (hF g hg).1) hm q k
  · exact measurable_const

omit [MeasurableSpace 𝒳] [IsProbabilityMeasure P] in
theorem abs_gB_le {q : ℕ} (hq : 1 ≤ q) (ht : 0 ≤ t (q - 1)) (k : Tup C.N q) (x : 𝒳) :
    |C.gB t q k x| ≤ t (q - 1) := by
  unfold gB
  split_ifs with h
  · obtain ⟨f, rfl⟩ := h
    rw [abs_of_nonneg (C.termB_idx_nonneg t q f x)]
    exact C.width_mul_indB_le t hq ht f x
  · simpa using ht

omit [MeasurableSpace 𝒳] [IsProbabilityMeasure P] in
theorem abs_gL_le {q : ℕ} (ht : 0 ≤ t (q - 1)) (k : Tup C.N q) (x : 𝒳) :
    |C.gL t q k x| ≤ t (q - 1) := by
  unfold gL
  split_ifs with h
  · obtain ⟨f, rfl⟩ := h
    exact C.abs_link_le_of_nonneg t q ht f x
  · simpa using ht

include hm hs in
theorem integral_sq_gB_le (hδ : 0 < δ) (q : ℕ) (k : Tup C.N q) :
    ∫ x, C.gB t q k x ^ 2 ∂P ≤ (δ / 2 ^ q) ^ 2 :=
  (integral_sq_le_bernsteinFunSq P (measurable_gB t hm q k)
    ((bernsteinFunSq_gB_lt t hs hδ q k).trans ENNReal.ofReal_lt_top)).trans
    (ENNReal.toReal_le_of_le_ofReal (sq_nonneg _) (bernsteinFunSq_gB_lt t hs hδ q k).le)

include hF hm hs in
theorem integral_sq_gL_le (hδ : 0 < δ) (q : ℕ) (k : Tup C.N q) :
    ∫ x, C.gL t q k x ^ 2 ∂P ≤ (δ / 2 ^ (q - 1)) ^ 2 :=
  (integral_sq_le_bernsteinFunSq P (measurable_gL t hF hm q k)
    ((bernsteinFunSq_gL_lt t hs hδ q k).trans ENNReal.ofReal_lt_top)).trans
    (ENNReal.toReal_le_of_le_ofReal (sq_nonneg _) (bernsteinFunSq_gL_lt t hs hδ q k).le)

include hm hs in
theorem integrable_termB_idx (q : ℕ) (f : F) : Integrable (C.termB t q (C.idx q f)) P := by
  have hD : Measurable (C.u q (C.cell q f) - C.l q (C.cell q f)) :=
    (hm q _).2.sub (hm q _).1
  refine Integrable.mono' (integrable_of_bernsteinFunSq_lt_top P hD
    ((hs q _).trans ENNReal.ofReal_lt_top)) (measurable_termB t hm q _).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (C.termB_idx_nonneg t q f x)]
  exact C.termB_idx_le t q f x

include hm hs in
theorem integral_termB_idx_le {q : ℕ} (ht : 0 < t q) (f : F) :
    ∫ x, C.termB t q (C.idx q f) x ∂P ≤ (δ / 2 ^ q) ^ 2 / t q := by
  have hD : Measurable (C.u q (C.cell q f) - C.l q (C.cell q f)) :=
    (hm q _).2.sub (hm q _).1
  have hDf := (hs q (C.cell q f)).trans ENNReal.ofReal_lt_top
  have hD2 : Integrable (fun x => (C.u q (C.cell q f) - C.l q (C.cell q f)) x ^ 2) P :=
    (memLp_two_of_bernsteinFunSq_lt_top P hD hDf).integrable_sq
  calc ∫ x, C.termB t q (C.idx q f) x ∂P
      ≤ ∫ x, (C.u q (C.cell q f) - C.l q (C.cell q f)) x ^ 2 / t q ∂P := by
        refine integral_mono (integrable_termB_idx t hm hs q f) (hD2.div_const _) fun x => ?_
        refine (C.termB_le_sq_div t ht _ x).trans ?_
        gcongr
        · exact C.width_idx_nonneg q f x
        · exact C.width_idx_le q f x
    _ = (∫ x, (C.u q (C.cell q f) - C.l q (C.cell q f)) x ^ 2 ∂P) / t q := integral_div _ _
    _ ≤ (δ / 2 ^ q) ^ 2 / t q := by
        gcongr
        exact (integral_sq_le_bernsteinFunSq P hD hDf).trans
          (ENNReal.toReal_le_of_le_ofReal (sq_nonneg _) (hs q _).le)

/-! ### Expectations of the maxima (Lemma M* of `MgfMaximal.lean`) -/

section Expectations

variable {n : ℕ} (hn : 0 < n) (hδ : 0 < δ)
include hn hδ

include hF in
/-- The root term: the maximum over level-`0` representatives, by `lintegral_iSup_empiricalProcess_le_of_bernstein`. -/
theorem lintegral_iSup_rep_le [Nonempty (Tup C.N 0)] :
    ∫⁻ x, (⨆ k : Tup C.N 0, ENNReal.ofReal |empiricalProcess P (C.rep 0 k) x|)
        ∂(Measure.pi fun _ : Fin n ↦ P) ≤
      ENNReal.ofReal (2 * δ * Real.sqrt (1 + Real.log (Fintype.card (Tup C.N 0))) +
        2 * (1 / Real.sqrt n) * (1 + Real.log (Fintype.card (Tup C.N 0)))) :=
  lintegral_iSup_empiricalProcess_le_of_bernstein P (C.rep 0)
    (fun k => measurable_rep (fun g hg => (hF g hg).1) 0 k) hδ
    (fun k => bernsteinFunSq_rep_le hF 0 k) hn

include hm hs in
/-- The `B`-pieces at level `q = 0`, by `lintegral_iSup_empiricalProcess_le_of_bernstein`. -/
theorem lintegral_iSup_gB_zero_le [Nonempty (Tup C.N 0)] :
    ∫⁻ x, (⨆ k : Tup C.N 0, ENNReal.ofReal |empiricalProcess P (C.gB t 0 k) x|)
        ∂(Measure.pi fun _ : Fin n ↦ P) ≤
      ENNReal.ofReal (2 * δ * Real.sqrt (1 + Real.log (Fintype.card (Tup C.N 0))) +
        2 * (1 / Real.sqrt n) * (1 + Real.log (Fintype.card (Tup C.N 0)))) :=
  lintegral_iSup_empiricalProcess_le_of_bernstein P (C.gB t 0)
    (fun k => measurable_gB t hm 0 k) hδ
    (fun k => by simpa using (bernsteinFunSq_gB_lt t hs hδ 0 k).le) hn

include hm hs in
/-- The `B`-pieces at levels `q ≥ 1`, by `lintegral_iSup_empiricalProcess_le_of_bounded`. -/
theorem lintegral_iSup_gB_le {q : ℕ} (hq : 1 ≤ q) (ht : 0 < t (q - 1))
    [Nonempty (Tup C.N q)] :
    ∫⁻ x, (⨆ k : Tup C.N q, ENNReal.ofReal |empiricalProcess P (C.gB t q k) x|)
        ∂(Measure.pi fun _ : Fin n ↦ P) ≤
      ENNReal.ofReal (2 * (δ / 2 ^ q) * Real.sqrt (1 + Real.log (Fintype.card (Tup C.N q))) +
        2 * (t (q - 1) / Real.sqrt n) * (1 + Real.log (Fintype.card (Tup C.N q)))) :=
  lintegral_iSup_empiricalProcess_le_of_bounded P (C.gB t q)
    (fun k => measurable_gB t hm q k) (by positivity) ht
    (fun k x => abs_gB_le t hq ht.le k x) (fun k => integral_sq_gB_le t hm hs hδ q k) hn

include hF hm hs in
/-- The links, by `lintegral_iSup_empiricalProcess_le_of_bounded`. -/
theorem lintegral_iSup_gL_le {q : ℕ} (ht : 0 < t (q - 1)) [Nonempty (Tup C.N q)] :
    ∫⁻ x, (⨆ k : Tup C.N q, ENNReal.ofReal |empiricalProcess P (C.gL t q k) x|)
        ∂(Measure.pi fun _ : Fin n ↦ P) ≤
      ENNReal.ofReal (2 * (δ / 2 ^ (q - 1)) *
          Real.sqrt (1 + Real.log (Fintype.card (Tup C.N q))) +
        2 * (t (q - 1) / Real.sqrt n) * (1 + Real.log (Fintype.card (Tup C.N q)))) :=
  lintegral_iSup_empiricalProcess_le_of_bounded P (C.gL t q)
    (fun k => measurable_gL t hF hm q k) (by positivity) ht
    (fun k x => abs_gL_le t ht.le k x) (fun k => integral_sq_gL_le t hF hm hs hδ q k) hn

end Expectations

/-! ### The pointwise chaining bound -/

omit [IsProbabilityMeasure P] in
theorem integrable_mul_ind {g ind : 𝒳 → ℝ} (hg : Integrable g P) (hind : Measurable ind)
    (h0 : ∀ y, 0 ≤ ind y) (h1 : ∀ y, ind y ≤ 1) : Integrable (fun y => g y * ind y) P := by
  refine hg.mono (hg.aestronglyMeasurable.mul hind.aestronglyMeasurable)
    (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg (h0 y)]
  exact mul_le_of_le_one_right (abs_nonneg _) (h1 y)

theorem abs_add_four_le (a b c d : ℝ) : |a + (b + c + d)| ≤ |a| + |b| + |c| + |d| := by
  have h1 := abs_add_le a (b + c + d)
  have h2 := abs_add_le (b + c) d
  have h3 := abs_add_le b c
  linarith

include hF hm hs in
/-- The chain decomposition (`BracketChain.sub_proj_zero_eq`), linearity and the bounds on the root term, the `B`-pieces, the links and the
remainder, pointwise in the sample. -/
theorem abs_empiricalProcess_le_chain (ht : ∀ q, 0 < t q) (Q : ℕ) (f : F) {n : ℕ}
    (x : Fin n → 𝒳) :
    |empiricalProcess P (f : 𝒳 → ℝ) x| ≤
      |empiricalProcess P (C.rep 0 (C.idx 0 f)) x|
      + ∑ q ∈ range (Q + 1), |empiricalProcess P (C.gB t q (C.idx q f)) x|
      + ∑ q ∈ Ico 1 (Q + 1), |empiricalProcess P (C.gL t q (C.idx q f)) x|
      + (∑ q ∈ range (Q + 1), 2 * Real.sqrt n * ((δ / 2 ^ q) ^ 2 / t q)
          + 2 * Real.sqrt n * t Q) := by
  have hint : ∀ g ∈ F, Integrable g P := fun g hg =>
    integrable_of_bernsteinFunSq_lt_top P (hF g hg).1 ((hF g hg).2.trans_lt ENNReal.ofReal_lt_top)
  have hf := hint f f.2
  have hp : ∀ q, Integrable (C.proj q f) P := fun q => hint _ (C.proj_mem q f)
  have hpB : ∀ q, Integrable (fun y => ((f : 𝒳 → ℝ) y - C.proj q f y) *
      C.indB t q (C.idx q f) y) P := fun q =>
    integrable_mul_ind (hf.sub (hp q)) (measurable_indB t hm _ _)
      (C.indB_nonneg t q _) (C.indB_le_one t q _)
  have hpL : ∀ q, Integrable (fun y => (C.proj q f y - C.proj (q - 1) f y) *
      C.indA t (q - 1) (C.idx (q - 1) f) y) P := fun q =>
    integrable_mul_ind ((hp q).sub (hp (q - 1))) (measurable_indA t hm _ _)
      (C.indA_nonneg t _ _) (C.indA_le_one t _ _)
  have hrem : Integrable (fun y => ((f : 𝒳 → ℝ) y - C.proj Q f y) *
      C.indA t Q (C.idx Q f) y) P :=
    integrable_mul_ind (hf.sub (hp Q)) (measurable_indA t hm _ _)
      (C.indA_nonneg t _ _) (C.indA_le_one t _ _)
  have hdecomp : (f : 𝒳 → ℝ) = C.proj 0 f +
      ((∑ q ∈ range (Q + 1), fun y => ((f : 𝒳 → ℝ) y - C.proj q f y) *
          C.indB t q (C.idx q f) y)
        + (∑ q ∈ Ico 1 (Q + 1), fun y => (C.proj q f y - C.proj (q - 1) f y) *
          C.indA t (q - 1) (C.idx (q - 1) f) y)
        + fun y => ((f : 𝒳 → ℝ) y - C.proj Q f y) * C.indA t Q (C.idx Q f) y) := by
    funext y
    simp only [Pi.add_apply, Finset.sum_apply]
    linarith [C.sub_proj_zero_eq t f Q y]
  have hSB := integrable_finsetSum' (range (Q + 1)) fun q _ => hpB q
  have hSL := integrable_finsetSum' (Ico 1 (Q + 1)) fun q _ => hpL q
  rw [empiricalProcess_congr P hdecomp x,
    empiricalProcess_add P (hp 0) ((hSB.add hSL).add hrem),
    empiricalProcess_add P (hSB.add hSL) hrem, empiricalProcess_add P hSB hSL,
    empiricalProcess_finset_sum P _ (fun q _ => hpB q),
    empiricalProcess_finset_sum P _ (fun q _ => hpL q)]
  have hB : ∀ q, |empiricalProcess P (fun y => ((f : 𝒳 → ℝ) y - C.proj q f y) *
      C.indB t q (C.idx q f) y) x| ≤
      |empiricalProcess P (C.gB t q (C.idx q f)) x| +
        2 * Real.sqrt n * ((δ / 2 ^ q) ^ 2 / t q) := by
    intro q
    refine (abs_empiricalProcess_le_of_abs_le P (hpB q) (integrable_termB_idx t hm hs q f)
      (fun y => C.abs_sub_proj_mul_indB_le t q f y) x).trans ?_
    rw [gB_idx]
    gcongr
    exact integral_termB_idx_le t hm hs (ht q) f
  have hL : ∀ q, empiricalProcess P (fun y => (C.proj q f y - C.proj (q - 1) f y) *
      C.indA t (q - 1) (C.idx (q - 1) f) y) x =
      empiricalProcess P (C.gL t q (C.idx q f)) x := by
    intro q
    rw [gL_idx]
    rfl
  have hR : |empiricalProcess P (fun y => ((f : 𝒳 → ℝ) y - C.proj Q f y) *
      C.indA t Q (C.idx Q f) y) x| ≤ 2 * Real.sqrt n * t Q :=
    abs_empiricalProcess_le_of_bounded P (ht Q).le
      (fun y => C.abs_sub_proj_mul_indA_le_of_nonneg t (ht Q).le f y) x
  have h1 := Finset.abs_sum_le_sum_abs (fun q => empiricalProcess P (fun y =>
    ((f : 𝒳 → ℝ) y - C.proj q f y) * C.indB t q (C.idx q f) y) x) (range (Q + 1))
  have h2 := Finset.abs_sum_le_sum_abs (fun q => empiricalProcess P (fun y =>
    (C.proj q f y - C.proj (q - 1) f y) * C.indA t (q - 1) (C.idx (q - 1) f) y) x)
    (Ico 1 (Q + 1))
  have h3 := Finset.sum_le_sum fun q (_ : q ∈ range (Q + 1)) => hB q
  rw [Finset.sum_add_distrib] at h3
  simp only [hL] at h2 ⊢
  have h4 : empiricalProcess P (C.proj 0 f) x =
      empiricalProcess P (C.rep 0 (C.idx 0 f)) x := rfl
  rw [h4]
  have habs := abs_add_four_le (empiricalProcess P (C.rep 0 (C.idx 0 f)) x)
    (∑ q ∈ range (Q + 1), empiricalProcess P (fun y =>
      ((f : 𝒳 → ℝ) y - C.proj q f y) * C.indB t q (C.idx q f) y) x)
    (∑ q ∈ Ico 1 (Q + 1), empiricalProcess P (C.gL t q (C.idx q f)) x)
    (empiricalProcess P (fun y => ((f : 𝒳 → ℝ) y - C.proj Q f y) *
      C.indA t Q (C.idx Q f) y) x)
  linarith

/-! ### The measurable majorant -/

omit [IsProbabilityMeasure P] in
theorem measurable_iSup_abs_empiricalProcess {ι : Type*} [Countable ι] (g : ι → 𝒳 → ℝ)
    (hg : ∀ i, Measurable (g i)) (n : ℕ) :
    Measurable fun x : Fin n → 𝒳 => ⨆ i, ENNReal.ofReal |empiricalProcess P (g i) x| :=
  Measurable.iSup fun i =>
    (continuous_abs.measurable.comp (measurable_empiricalProcess P (hg i) n)).ennreal_ofReal

include hF hm hs in
/-- The empirical supremum is dominated pointwise by the majorant `Φ`. -/
theorem empiricalSup_le_majorant (ht : ∀ q, 0 < t q) (Q : ℕ) {n : ℕ} (x : Fin n → 𝒳) :
    empiricalSup P F x ≤
      (⨆ k : Tup C.N 0, ENNReal.ofReal |empiricalProcess P (C.rep 0 k) x|)
      + ∑ q ∈ range (Q + 1), (⨆ k : Tup C.N q, ENNReal.ofReal |empiricalProcess P (C.gB t q k) x|)
      + ∑ q ∈ Ico 1 (Q + 1), (⨆ k : Tup C.N q, ENNReal.ofReal |empiricalProcess P (C.gL t q k) x|)
      + ENNReal.ofReal (∑ q ∈ range (Q + 1), 2 * Real.sqrt n * ((δ / 2 ^ q) ^ 2 / t q)
          + 2 * Real.sqrt n * t Q) := by
  unfold empiricalSup
  refine iSup₂_le fun g hg => ?_
  have h := abs_empiricalProcess_le_chain t hF hm hs ht Q ⟨g, hg⟩ x
  have hc : 0 ≤ ∑ q ∈ range (Q + 1), 2 * Real.sqrt n * ((δ / 2 ^ q) ^ 2 / t q)
      + 2 * Real.sqrt n * t Q := by
    have := ht Q
    refine add_nonneg (Finset.sum_nonneg fun q _ => ?_) (by positivity)
    have := ht q
    positivity
  refine (ENNReal.ofReal_le_ofReal h).trans ?_
  rw [ENNReal.ofReal_add (by positivity) hc,
    ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg fun _ _ => abs_nonneg _),
    ENNReal.ofReal_add (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _),
    ENNReal.ofReal_sum_of_nonneg fun _ _ => abs_nonneg _,
    ENNReal.ofReal_sum_of_nonneg fun _ _ => abs_nonneg _]
  gcongr with q hq q hq
  · exact le_iSup (fun k => ENNReal.ofReal |empiricalProcess P (C.rep 0 k) x|) _
  · exact le_iSup (fun k => ENNReal.ofReal |empiricalProcess P (C.gB t q k) x|) _
  · exact le_iSup (fun k => ENNReal.ofReal |empiricalProcess P (C.gL t q k) x|) _

include hF hm hs in
/-- The outer expectation of the empirical supremum, bounded term by term. -/
theorem outerLIntegral_empiricalSup_le_chain {n : ℕ} (hn : 0 < n) (hδ : 0 < δ)
    (ht : ∀ q, 0 < t q) (hne : ∀ q, Nonempty (Tup C.N q)) (Q : ℕ) :
    outerLIntegral (Measure.pi fun _ : Fin n ↦ P) (empiricalSup P F) ≤
      ENNReal.ofReal (2 * δ * Real.sqrt (1 + Real.log (Fintype.card (Tup C.N 0))) +
        2 * (1 / Real.sqrt n) * (1 + Real.log (Fintype.card (Tup C.N 0))))
      + (ENNReal.ofReal (2 * δ * Real.sqrt (1 + Real.log (Fintype.card (Tup C.N 0))) +
        2 * (1 / Real.sqrt n) * (1 + Real.log (Fintype.card (Tup C.N 0))))
        + ∑ q ∈ Ico 1 (Q + 1), ENNReal.ofReal (2 * (δ / 2 ^ q) *
            Real.sqrt (1 + Real.log (Fintype.card (Tup C.N q))) +
          2 * (t (q - 1) / Real.sqrt n) * (1 + Real.log (Fintype.card (Tup C.N q)))))
      + ∑ q ∈ Ico 1 (Q + 1), ENNReal.ofReal (2 * (δ / 2 ^ (q - 1)) *
            Real.sqrt (1 + Real.log (Fintype.card (Tup C.N q))) +
          2 * (t (q - 1) / Real.sqrt n) * (1 + Real.log (Fintype.card (Tup C.N q))))
      + ENNReal.ofReal (∑ q ∈ range (Q + 1), 2 * Real.sqrt n * ((δ / 2 ^ q) ^ 2 / t q)
          + 2 * Real.sqrt n * t Q) := by
  have hFm : ∀ g ∈ F, Measurable g := fun g hg => (hF g hg).1
  have m0 := measurable_iSup_abs_empiricalProcess (P := P) (C.rep 0) (measurable_rep hFm 0) n
  have mB : ∀ q, Measurable fun x : Fin n → 𝒳 =>
      ⨆ k : Tup C.N q, ENNReal.ofReal |empiricalProcess P (C.gB t q k) x| := fun q =>
    measurable_iSup_abs_empiricalProcess (P := P) (C.gB t q) (measurable_gB t hm q) n
  have mL : ∀ q, Measurable fun x : Fin n → 𝒳 =>
      ⨆ k : Tup C.N q, ENNReal.ofReal |empiricalProcess P (C.gL t q k) x| := fun q =>
    measurable_iSup_abs_empiricalProcess (P := P) (C.gL t q) (measurable_gL t hF hm q) n
  have mSB := Finset.measurable_sum (range (Q + 1)) fun q _ => mB q
  have mSL := Finset.measurable_sum (Ico 1 (Q + 1)) fun q _ => mL q
  refine (outerLIntegral_le_lintegral (((m0.add mSB).add mSL).add measurable_const)
    fun x => empiricalSup_le_majorant t hF hm hs ht Q x).trans ?_
  simp only [Pi.add_apply]
  rw [lintegral_add_right _ measurable_const, lintegral_add_right _ mSL,
    lintegral_add_right _ mSB, lintegral_finsetSum _ fun q _ => mB q,
    lintegral_finsetSum _ fun q _ => mL q, lintegral_const, measure_univ, mul_one]
  have hsplit : ∑ q ∈ range (Q + 1), ∫⁻ x, (⨆ k : Tup C.N q,
        ENNReal.ofReal |empiricalProcess P (C.gB t q k) x|) ∂(Measure.pi fun _ : Fin n ↦ P) =
      ∫⁻ x, (⨆ k : Tup C.N 0, ENNReal.ofReal |empiricalProcess P (C.gB t 0 k) x|)
          ∂(Measure.pi fun _ : Fin n ↦ P)
        + ∑ q ∈ Ico 1 (Q + 1), ∫⁻ x, (⨆ k : Tup C.N q,
          ENNReal.ofReal |empiricalProcess P (C.gB t q k) x|) ∂(Measure.pi fun _ : Fin n ↦ P) := by
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega)]
  rw [hsplit]
  have := hne 0
  gcongr with q hq q hq
  · exact lintegral_iSup_rep_le hF hn hδ
  · exact lintegral_iSup_gB_zero_le t hm hs hn hδ
  · have := hne q
    exact lintegral_iSup_gB_le t hm hs hn hδ (Finset.mem_Ico.1 hq).1 (ht _)
  · have := hne q
    exact lintegral_iSup_gL_le t hF hm hs hn hδ (ht _)

end Bounds

end BracketChain

/-! ### Arithmetic of the thresholds -/

theorem two_mul_sq_div_thr {e s r : ℝ} (he : 0 < e) (hs : 0 < s) (hr : 0 < r) :
    2 * r * (e ^ 2 / (r * (e / s))) = 2 * (e * s) := by
  field_simp

theorem two_mul_thr_div_mul {e L r : ℝ} (hL : 1 ≤ L) (hr : 0 < r) :
    2 * (r * (e / √L) / r) * L = 2 * (e * √L) := by
  have hs : √L ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
  calc 2 * (r * (e / √L) / r) * L = 2 * (e * (L / √L)) := by field_simp
    _ = 2 * (e * √L) := by rw [Real.div_sqrt]

theorem two_mul_sqrt_mul_thr_le {n : ℕ} {δ s : ℝ} (hδ : 0 < δ) (hs : 1 ≤ s) :
    2 * Real.sqrt n * (Real.sqrt n * (δ / 2 ^ (n + 1) / s)) ≤ δ := by
  have hn2 : ((2 * n : ℕ) : ℝ) ≤ ((2 ^ (n + 1) : ℕ) : ℝ) := by
    have : n < 2 ^ n := Nat.lt_two_pow_self
    exact_mod_cast (by rw [pow_succ]; omega : 2 * n ≤ 2 ^ (n + 1))
  push_cast at hn2
  have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
  have hp : (0 : ℝ) < 2 ^ (n + 1) := by positivity
  have h1 : δ / 2 ^ (n + 1) / s ≤ δ / 2 ^ (n + 1) := div_le_self (by positivity) hs
  calc 2 * Real.sqrt n * (Real.sqrt n * (δ / 2 ^ (n + 1) / s))
      = 2 * (Real.sqrt n * Real.sqrt n) * (δ / 2 ^ (n + 1) / s) := by ring
    _ = 2 * n * (δ / 2 ^ (n + 1) / s) := by rw [hsq]
    _ ≤ 2 * n * (δ / 2 ^ (n + 1)) := by gcongr
    _ = δ * (2 * n / 2 ^ (n + 1)) := by ring
    _ ≤ δ * 1 := by
        gcongr
        rw [div_le_one hp]; exact hn2
    _ = δ := mul_one δ

/-! ### The main case: a nonempty class with finite bracketing integral -/

theorem outerLIntegral_empiricalSup_le_of_ne_top {𝒳 : Type*} [MeasurableSpace 𝒳]
    (P : Measure 𝒳) [IsProbabilityMeasure P] {F : Set (𝒳 → ℝ)} {n : ℕ} {δ : ℝ}
    (hn : 0 < n) (hδ : 0 < δ)
    (hF : ∀ f ∈ F, Measurable f ∧ bernsteinFun P f ≤ ENNReal.ofReal δ)
    (hJ : bBracketingIntegral P δ F ≠ ⊤) (hFne : F.Nonempty) :
    outerLIntegral (Measure.pi fun _ : Fin n ↦ P) (empiricalSup P F) ≤
      ENNReal.ofReal (77 * (bBracketingIntegral P δ F).toReal +
        4 * (bBracketingIntegral P δ F).toReal ^ 2 / (δ ^ 2 * Real.sqrt n)) := by
  obtain ⟨f₀, hf₀⟩ := hFne
  have hFsq : ∀ f ∈ F, Measurable f ∧ bernsteinFunSq P f ≤ ENNReal.ofReal (δ ^ 2) :=
    fun f hf => ⟨(hF f hf).1, (bernsteinFun_le_ofReal_iff P f hδ.le).1 (hF f hf).2⟩
  have hJ' : bracketingIntegral (BernsteinAdmissible P) (bernsteinBracketSize P) δ F ≠ ⊤ := hJ
  let N : ℕ → ℕ := dyadicCount (BernsteinAdmissible P) (bernsteinBracketSize P) δ F
  have hcov : ∀ q, ∃ b : Fin (N q) → (𝒳 → ℝ) × (𝒳 → ℝ),
      IsBracketCover (BernsteinAdmissible P) (bernsteinBracketSize P)
        (ENNReal.ofReal (δ / 2 ^ q)) F b := fun q =>
    exists_cover_of_bracketingNumber_ne_top
      (bracketingNumber_ne_top_of_bracketingIntegral_ne_top hδ hJ' (by positivity))
  choose b hb using hcov
  let C : BracketChain F :=
    ⟨N, fun q i => (b q i).1, fun q i => (b q i).2, fun q f hf => (hb q).2 f hf⟩
  have hm : ∀ q i, Measurable (C.l q i) ∧ Measurable (C.u q i) := fun q i =>
    ⟨((hb q).1 i).1.1, ((hb q).1 i).1.2.1⟩
  have hs : ∀ q i, bernsteinFunSq P (C.u q i - C.l q i) < ENNReal.ofReal ((δ / 2 ^ q) ^ 2) :=
    fun q i => (bernsteinFun_lt_ofReal_iff P _ (by positivity)).1 ((hb q).1 i).2.2
  have hne : ∀ q, Nonempty (Tup C.N q) := fun q => ⟨C.idx q ⟨f₀, hf₀⟩⟩
  have hcard : ∀ q, Fintype.card (Tup C.N q) =
      dyadicProd (BernsteinAdmissible P) (bernsteinBracketSize P) δ F q := fun q => by
    rw [Tup.card]; exact Fin.prod_univ_eq_prod_range N (q + 1)
  set M := dyadicProd (BernsteinAdmissible P) (bernsteinBracketSize P) δ F with hM
  set J := (bBracketingIntegral P δ F).toReal with hJdef
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hL1 : ∀ q, 1 ≤ entropyLog (M q) := fun q => one_le_entropyLog _
  have hsL1 : ∀ q, 1 ≤ √(entropyLog (M q)) := fun q => by
    rw [Real.one_le_sqrt]; exact hL1 q
  have hsL : ∀ q, 0 < √(entropyLog (M q)) := fun q => zero_lt_one.trans_le (hsL1 q)
  let t : ℕ → ℝ := fun q => Real.sqrt n * ((δ / 2 ^ q) / √(entropyLog (M (q + 1))))
  have ht : ∀ q, 0 < t q := fun q => by
    have := hsL (q + 1)
    show 0 < Real.sqrt n * ((δ / 2 ^ q) / √(entropyLog (M (q + 1))))
    positivity
  have hmain := C.outerLIntegral_empiricalSup_le_chain t hFsq hm hs hn hδ ht hne (n + 1)
  have hE : ∀ m : ℕ, 1 + Real.log (m : ℝ) = entropyLog m := fun m => rfl
  simp only [hcard, hE] at hmain
  refine hmain.trans ?_
  -- termwise real bounds
  have hB : ∀ q ∈ Ico 1 (n + 1 + 1), 2 * (δ / 2 ^ q) * √(entropyLog (M q)) +
      2 * (t (q - 1) / Real.sqrt n) * entropyLog (M q) ≤ 6 * (δ / 2 ^ q * √(entropyLog (M q))) := by
    intro q hq
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by have := (Finset.mem_Ico.1 hq).1; omega⟩
    show 2 * (δ / 2 ^ (r + 1)) * √(entropyLog (M (r + 1))) +
      2 * (Real.sqrt n * ((δ / 2 ^ (r + 1 - 1)) / √(entropyLog (M (r + 1 - 1 + 1)))) /
        Real.sqrt n) * entropyLog (M (r + 1)) ≤ _
    simp only [Nat.add_sub_cancel]
    rw [two_mul_thr_div_mul (hL1 _) hsn]
    have h2 : δ / 2 ^ r = 2 * (δ / 2 ^ (r + 1)) := by rw [pow_succ]; field_simp
    rw [h2]
    linarith
  have hL : ∀ q ∈ Ico 1 (n + 1 + 1), 2 * (δ / 2 ^ (q - 1)) * √(entropyLog (M q)) +
      2 * (t (q - 1) / Real.sqrt n) * entropyLog (M q) ≤ 8 * (δ / 2 ^ q * √(entropyLog (M q))) := by
    intro q hq
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by have := (Finset.mem_Ico.1 hq).1; omega⟩
    show 2 * (δ / 2 ^ (r + 1 - 1)) * √(entropyLog (M (r + 1))) +
      2 * (Real.sqrt n * ((δ / 2 ^ (r + 1 - 1)) / √(entropyLog (M (r + 1 - 1 + 1)))) /
        Real.sqrt n) * entropyLog (M (r + 1)) ≤ _
    simp only [Nat.add_sub_cancel]
    rw [two_mul_thr_div_mul (hL1 _) hsn]
    have h2 : δ / 2 ^ r = 2 * (δ / 2 ^ (r + 1)) := by rw [pow_succ]; field_simp
    rw [h2]
    linarith
  have hc : ∑ q ∈ range (n + 1 + 1), 2 * Real.sqrt n * ((δ / 2 ^ q) ^ 2 / t q)
      + 2 * Real.sqrt n * t (n + 1) ≤
      2 * ∑ q ∈ range (n + 1 + 1), δ / 2 ^ q * √(entropyLog (M (q + 1))) + δ := by
    have h1 : ∑ q ∈ range (n + 1 + 1), 2 * Real.sqrt n * ((δ / 2 ^ q) ^ 2 / t q) =
        2 * ∑ q ∈ range (n + 1 + 1), δ / 2 ^ q * √(entropyLog (M (q + 1))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      exact two_mul_sq_div_thr (by positivity) (hsL _) hsn
    rw [h1]
    have h2 := two_mul_sqrt_mul_thr_le (n := n) hδ (hsL1 (n + 1 + 1))
    have h3 : 2 * Real.sqrt n * t (n + 1) =
        2 * Real.sqrt n * (Real.sqrt n * (δ / 2 ^ (n + 1) / √(entropyLog (M (n + 1 + 1))))) := rfl
    linarith
  calc _ ≤ ENNReal.ofReal (2 * δ * √(entropyLog (M 0)) +
          2 * (1 / Real.sqrt n) * entropyLog (M 0)) +
        (ENNReal.ofReal (2 * δ * √(entropyLog (M 0)) +
          2 * (1 / Real.sqrt n) * entropyLog (M 0)) +
          ∑ q ∈ Ico 1 (n + 1 + 1), ENNReal.ofReal (6 * (δ / 2 ^ q * √(entropyLog (M q))))) +
        ∑ q ∈ Ico 1 (n + 1 + 1), ENNReal.ofReal (8 * (δ / 2 ^ q * √(entropyLog (M q)))) +
        ENNReal.ofReal (2 * ∑ q ∈ range (n + 1 + 1), δ / 2 ^ q * √(entropyLog (M (q + 1)))
          + δ) := by
        gcongr with q hq q hq
        · exact hB q hq
        · exact hL q hq
    _ = ENNReal.ofReal ((2 * δ * √(entropyLog (M 0)) +
          2 * (1 / Real.sqrt n) * entropyLog (M 0)) +
        ((2 * δ * √(entropyLog (M 0)) + 2 * (1 / Real.sqrt n) * entropyLog (M 0)) +
          6 * ∑ q ∈ Ico 1 (n + 1 + 1), δ / 2 ^ q * √(entropyLog (M q))) +
        8 * ∑ q ∈ Ico 1 (n + 1 + 1), δ / 2 ^ q * √(entropyLog (M q)) +
        (2 * ∑ q ∈ range (n + 1 + 1), δ / 2 ^ q * √(entropyLog (M (q + 1))) + δ)) := by
        have hl0 := hL1 0
        rw [Finset.mul_sum _ _ (6 : ℝ), Finset.mul_sum _ _ (8 : ℝ),
          ← ENNReal.ofReal_sum_of_nonneg (fun q _ => by positivity),
          ← ENNReal.ofReal_sum_of_nonneg (fun q _ => by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have hS := sum_dyadic_prod_entropy_le hδ hJ' (n + 1)
        have hS' := sum_Ico_dyadic_prod_entropy_le_half (adm := BernsteinAdmissible P)
          (size := bernsteinBracketSize P) hδ.le F (n + 1)
        have hF4 := mul_sqrt_entropyLog_dyadicCount_zero_le hδ hJ'
        have hδJ := le_toReal_bracketingIntegral (adm := BernsteinAdmissible P)
          (size := bernsteinBracketSize P) δ hJ'
        have hM0 : M 0 = dyadicCount (BernsteinAdmissible P) (bernsteinBracketSize P) δ F 0 := by
          simp [hM, dyadicProd]
        rw [← hM0] at hF4
        rw [← hM] at hS hS'
        change _ ≤ J at hF4 hδJ
        change _ ≤ 8 * J at hS
        have hl0 : 0 ≤ entropyLog (M 0) := zero_le_one.trans (hL1 0)
        have hsq : √(entropyLog (M 0)) ^ 2 = entropyLog (M 0) := Real.sq_sqrt hl0
        have hds : 0 ≤ δ * √(entropyLog (M 0)) := by positivity
        have hL0 : 2 * (1 / Real.sqrt n) * entropyLog (M 0) ≤
            2 * (J ^ 2 / (δ ^ 2 * Real.sqrt n)) := by
          have hsq' : (δ * √(entropyLog (M 0))) ^ 2 ≤ J ^ 2 := pow_le_pow_left₀ hds hF4 2
          rw [mul_pow, hsq] at hsq'
          rw [show 2 * (1 / Real.sqrt n) * entropyLog (M 0) =
            2 * ((δ ^ 2 * entropyLog (M 0)) / (δ ^ 2 * Real.sqrt n)) by field_simp]
          gcongr
        rw [show 4 * J ^ 2 / (δ ^ 2 * Real.sqrt n) = 4 * (J ^ 2 / (δ ^ 2 * Real.sqrt n)) by ring]
        linarith

end Hellinger.VdW

namespace Hellinger.MLE.External

/-- **van der Vaart and Wellner (2023), Theorem 2.14.18'**, in the package formulation, with
`K₀ = 80`. -/
theorem vdw_2_14_18_prime : VdW_2_14_18_prime := by
  refine ⟨80, fun 𝒳 _ P _ F n δ hn hδ hF => ?_⟩
  by_cases hJ : bBracketingIntegral P δ F = ⊤
  · rw [hJ, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top, add_top,
      ENNReal.mul_top (by norm_num)]
    exact le_top
  rcases Set.eq_empty_or_nonempty F with rfl | hFne
  · refine (outerLIntegral_le_lintegral (g := fun _ => 0) measurable_const fun x => ?_).trans ?_
    · simp [empiricalSup]
    · simp
  refine (Hellinger.VdW.outerLIntegral_empiricalSup_le_of_ne_top P hn hδ hF hJ hFne).trans ?_
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hD : 0 < δ ^ 2 * Real.sqrt n := by positivity
  have hJr : 0 ≤ (bBracketingIntegral P δ F).toReal := ENNReal.toReal_nonneg
  have key : ((80 : ℝ≥0) : ℝ≥0∞) * bBracketingIntegral P δ F *
      (1 + bBracketingIntegral P δ F / ENNReal.ofReal (δ ^ 2 * Real.sqrt n)) =
      ENNReal.ofReal (80 * (bBracketingIntegral P δ F).toReal *
        (1 + (bBracketingIntegral P δ F).toReal / (δ ^ 2 * Real.sqrt n))) := by
    have e1 : ENNReal.ofReal (80 * (bBracketingIntegral P δ F).toReal *
        (1 + (bBracketingIntegral P δ F).toReal / (δ ^ 2 * Real.sqrt n))) =
        ENNReal.ofReal (80 * (bBracketingIntegral P δ F).toReal) *
          ENNReal.ofReal (1 + (bBracketingIntegral P δ F).toReal / (δ ^ 2 * Real.sqrt n)) :=
      ENNReal.ofReal_mul (by positivity)
    have e2 : ENNReal.ofReal (80 * (bBracketingIntegral P δ F).toReal) =
        ENNReal.ofReal 80 * ENNReal.ofReal (bBracketingIntegral P δ F).toReal :=
      ENNReal.ofReal_mul (by norm_num)
    have e3 : ENNReal.ofReal (1 + (bBracketingIntegral P δ F).toReal / (δ ^ 2 * Real.sqrt n)) =
        1 + ENNReal.ofReal (bBracketingIntegral P δ F).toReal /
          ENNReal.ofReal (δ ^ 2 * Real.sqrt n) := by
      rw [ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one,
        ENNReal.ofReal_div_of_pos hD]
    rw [e1, e2, e3, ENNReal.ofReal_toReal hJ]
    norm_num
  rw [key]
  apply ENNReal.ofReal_le_ofReal
  have h0 : 0 ≤ (bBracketingIntegral P δ F).toReal ^ 2 / (δ ^ 2 * Real.sqrt n) := by positivity
  rw [mul_add, mul_one,
    show 80 * (bBracketingIntegral P δ F).toReal *
        ((bBracketingIntegral P δ F).toReal / (δ ^ 2 * Real.sqrt n)) =
      80 * ((bBracketingIntegral P δ F).toReal ^ 2 / (δ ^ 2 * Real.sqrt n)) by ring,
    show 4 * (bBracketingIntegral P δ F).toReal ^ 2 / (δ ^ 2 * Real.sqrt n) =
      4 * ((bBracketingIntegral P δ F).toReal ^ 2 / (δ ^ 2 * Real.sqrt n)) by ring]
  linarith

end Hellinger.MLE.External
