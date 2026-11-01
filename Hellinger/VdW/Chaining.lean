/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Order.Lattice
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.LinearCombination

/-!
Deterministic chaining combinatorics for the proof of van der Vaart and Wellner's
Theorem 2.14.18' (outlined in `docs/Theorem8.md`).

* `Tup N q = Π_{p ≤ q} Fin (N p)`: index tuples (cells), with restriction maps;
* `BracketChain F`: bracket covers `[l q i, u q i]`, `i : Fin (N q)`, of a class `F` at each
  level `q`;
* `idx q f`: the cell of `f ∈ F` at level `q` (a fixed bracket choice at each level);
* `lowerB`, `upperB`, `width`: intersection brackets `max_{p ≤ q} l`, `min_{p ≤ q} u` and their
  width, for every tuple;
* `rep`, `proj`: representatives of realized tuples and the projection `π_q f`;
* the chaining bounds: (C1) `f` and `π_q f` lie in the intersection bracket of the cell of
  `f`, so `|f − π_q f| ≤ Δ_q f`; (C2) `Δ_q f` is at most the width of the level-`q` bracket
  of `f`; (C3) `Δ_q f ≤ Δ_{q−1} f` and `|π_q f − π_{q−1} f| ≤ Δ_{q−1} f`;
* the truncation indicators `indA`, `indB`, the telescoping decomposition of `f − π_0 f`
  (Lemma D, `sub_proj_zero_eq`) and the pointwise bounds on each piece;
* measurability of everything from measurable bracket endpoints.

Everything is deterministic: no measure is involved.
-/

@[expose] public section

open Finset

namespace Hellinger.VdW

/-! ### Index tuples -/

/-- Index tuples at level `q`: one bracket index at each level `p ≤ q`. -/
abbrev Tup (N : ℕ → ℕ) (q : ℕ) : Type := (p : Fin (q + 1)) → Fin (N p)

namespace Tup

variable {N : ℕ → ℕ}

theorem card (q : ℕ) : Fintype.card (Tup N q) = ∏ p : Fin (q + 1), N p := by
  simp [Tup]

/-- Restriction of a level-`q` tuple to the levels `≤ p`. -/
def restrict {p q : ℕ} (h : p ≤ q) (k : Tup N q) : Tup N p :=
  fun r => k ⟨r.1, Nat.lt_of_lt_of_le r.2 (Nat.succ_le_succ h)⟩

@[simp] theorem restrict_apply {p q : ℕ} (h : p ≤ q) (k : Tup N q) (r : Fin (p + 1)) :
    restrict h k r = k ⟨r.1, Nat.lt_of_lt_of_le r.2 (Nat.succ_le_succ h)⟩ := rfl

@[simp] theorem restrict_refl {q : ℕ} (h : q ≤ q) (k : Tup N q) : restrict h k = k := rfl

@[simp] theorem restrict_restrict {p q r : ℕ} (h₁ : p ≤ q) (h₂ : q ≤ r) (k : Tup N r) :
    restrict h₁ (restrict h₂ k) = restrict (h₁.trans h₂) k := rfl

end Tup

/-! ### Bracket chains -/

/-- Bracket covers of `F` at every level `q`: `N q` brackets `[l q i, u q i]`, and every
`f ∈ F` lies in one of them. -/
structure BracketChain {𝒳 : Type*} (F : Set (𝒳 → ℝ)) where
  /-- Number of brackets at level `q`. -/
  N : ℕ → ℕ
  /-- Lower bracket endpoints. -/
  l : (q : ℕ) → Fin (N q) → 𝒳 → ℝ
  /-- Upper bracket endpoints. -/
  u : (q : ℕ) → Fin (N q) → 𝒳 → ℝ
  /-- The cover property. -/
  cover : ∀ q, ∀ f ∈ F, ∃ i, l q i ≤ f ∧ f ≤ u q i

namespace BracketChain

variable {𝒳 : Type*} {F : Set (𝒳 → ℝ)} (C : BracketChain F)

/-! ### Cells -/

/-- The chosen bracket of `f ∈ F` at level `q`. -/
noncomputable def cell (q : ℕ) (f : F) : Fin (C.N q) :=
  Classical.choose (C.cover q f.1 f.2)

theorem l_cell_le (q : ℕ) (f : F) : C.l q (C.cell q f) ≤ f :=
  (Classical.choose_spec (C.cover q f.1 f.2)).1

theorem le_u_cell (q : ℕ) (f : F) : (f : 𝒳 → ℝ) ≤ C.u q (C.cell q f) :=
  (Classical.choose_spec (C.cover q f.1 f.2)).2

/-- The cell `k_q(f) = (c_p(f))_{p ≤ q}` of `f` at level `q`. -/
noncomputable def idx (q : ℕ) (f : F) : Tup C.N q := fun p => C.cell p f

@[simp] theorem idx_apply (q : ℕ) (f : F) (p : Fin (q + 1)) : C.idx q f p = C.cell p f := rfl

theorem idx_last (q : ℕ) (f : F) : C.idx q f (Fin.last q) = C.cell q f := rfl

/-- `idx` is restriction-compatible. -/
@[simp] theorem restrict_idx {p q : ℕ} (h : p ≤ q) (f : F) :
    Tup.restrict h (C.idx q f) = C.idx p f := rfl

/-! ### Intersection brackets -/

/-- `L_q(k) = max_{p ≤ q} l_{p, k_p}`. -/
noncomputable def lowerB (q : ℕ) (k : Tup C.N q) : 𝒳 → ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun p : Fin (q + 1) => C.l p (k p)

/-- `U_q(k) = min_{p ≤ q} u_{p, k_p}`. -/
noncomputable def upperB (q : ℕ) (k : Tup C.N q) : 𝒳 → ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun p : Fin (q + 1) => C.u p (k p)

/-- `Δ_q(k) = U_q(k) − L_q(k)`. -/
noncomputable def width (q : ℕ) (k : Tup C.N q) : 𝒳 → ℝ := C.upperB q k - C.lowerB q k

theorem width_apply (q : ℕ) (k : Tup C.N q) (x : 𝒳) :
    C.width q k x = C.upperB q k x - C.lowerB q k x := rfl

theorem lowerB_apply (q : ℕ) (k : Tup C.N q) (x : 𝒳) :
    C.lowerB q k x = Finset.univ.sup' Finset.univ_nonempty fun p : Fin (q + 1) => C.l p (k p) x :=
  Finset.sup'_apply _ _ _

theorem upperB_apply (q : ℕ) (k : Tup C.N q) (x : 𝒳) :
    C.upperB q k x = Finset.univ.inf' Finset.univ_nonempty fun p : Fin (q + 1) => C.u p (k p) x :=
  Finset.inf'_apply _ _ _

theorem l_le_lowerB {q : ℕ} (k : Tup C.N q) (p : Fin (q + 1)) : C.l p (k p) ≤ C.lowerB q k :=
  Finset.le_sup' (f := fun p : Fin (q + 1) => C.l p (k p)) (Finset.mem_univ p)

theorem upperB_le_u {q : ℕ} (k : Tup C.N q) (p : Fin (q + 1)) : C.upperB q k ≤ C.u p (k p) :=
  Finset.inf'_le (f := fun p : Fin (q + 1) => C.u p (k p)) (Finset.mem_univ p)

theorem lowerB_le_iff {q : ℕ} (k : Tup C.N q) (g : 𝒳 → ℝ) :
    C.lowerB q k ≤ g ↔ ∀ p : Fin (q + 1), C.l p (k p) ≤ g := by
  simp [lowerB, Finset.sup'_le_iff]

theorem le_upperB_iff {q : ℕ} (k : Tup C.N q) (g : 𝒳 → ℝ) :
    g ≤ C.upperB q k ↔ ∀ p : Fin (q + 1), g ≤ C.u p (k p) := by
  simp [upperB, Finset.le_inf'_iff]

/-- Restricting a tuple to fewer levels lowers `L`. -/
theorem lowerB_restrict_le {p q : ℕ} (h : p ≤ q) (k : Tup C.N q) :
    C.lowerB p (Tup.restrict h k) ≤ C.lowerB q k :=
  (C.lowerB_le_iff _ _).2 fun r => C.l_le_lowerB k ⟨r.1, _⟩

/-- Restricting a tuple to fewer levels raises `U`. -/
theorem upperB_le_upperB_restrict {p q : ℕ} (h : p ≤ q) (k : Tup C.N q) :
    C.upperB q k ≤ C.upperB p (Tup.restrict h k) :=
  (C.le_upperB_iff _ _).2 fun r => C.upperB_le_u k ⟨r.1, _⟩

/-! ### (C1) -/

/-- **(C1)** If `k_q(g) = k_q(f)`, then `L_q(k_q f) ≤ g ≤ U_q(k_q f)`. -/
theorem bracket_of_idx_eq {q : ℕ} {f g : F} (h : C.idx q g = C.idx q f) :
    C.lowerB q (C.idx q f) ≤ g ∧ (g : 𝒳 → ℝ) ≤ C.upperB q (C.idx q f) := by
  rw [← h]
  exact ⟨(C.lowerB_le_iff _ _).2 fun p => C.l_cell_le p g,
    (C.le_upperB_iff _ _).2 fun p => C.le_u_cell p g⟩

theorem bracket_idx (q : ℕ) (f : F) :
    C.lowerB q (C.idx q f) ≤ f ∧ (f : 𝒳 → ℝ) ≤ C.upperB q (C.idx q f) :=
  C.bracket_of_idx_eq rfl

/-- **(C1)** `0 ≤ Δ_q f`. -/
theorem width_idx_nonneg (q : ℕ) (f : F) (x : 𝒳) : 0 ≤ C.width q (C.idx q f) x := by
  have h := C.bracket_idx q f
  have h1 := h.1 x
  have h2 := h.2 x
  rw [width_apply]
  linarith

/-! ### Representatives and projections -/

/-- A tuple is realized if it is the cell of some `f ∈ F`. -/
def Realized (q : ℕ) (k : Tup C.N q) : Prop := ∃ f : F, C.idx q f = k

/-- The chosen representative of a realized tuple, as an element of `F`. -/
noncomputable def repF (q : ℕ) (k : Tup C.N q) (h : C.Realized q k) : F := Classical.choose h

theorem idx_repF {q : ℕ} {k : Tup C.N q} (h : C.Realized q k) : C.idx q (C.repF q k h) = k :=
  Classical.choose_spec h

open Classical in
/-- The representative `r_q(k)` of a tuple; the zero function off realized tuples. -/
noncomputable def rep (q : ℕ) (k : Tup C.N q) : 𝒳 → ℝ :=
  if h : C.Realized q k then (C.repF q k h : 𝒳 → ℝ) else 0

theorem rep_of_realized {q : ℕ} {k : Tup C.N q} (h : C.Realized q k) :
    C.rep q k = C.repF q k h := by
  unfold rep; simp [h]

theorem rep_of_not_realized {q : ℕ} {k : Tup C.N q} (h : ¬ C.Realized q k) :
    C.rep q k = 0 := by
  unfold rep; simp [h]

theorem rep_mem {q : ℕ} {k : Tup C.N q} (h : C.Realized q k) : C.rep q k ∈ F := by
  rw [C.rep_of_realized h]; exact (C.repF q k h).2

/-- The projection `π_q f = r_q(k_q f)`. -/
noncomputable def proj (q : ℕ) (f : F) : 𝒳 → ℝ := C.rep q (C.idx q f)

/-- `π_q f` is a function of `k_q f`. -/
theorem proj_eq_rep (q : ℕ) (f : F) : C.proj q f = C.rep q (C.idx q f) := rfl

/-- `π_q f` as an element of `F`. -/
noncomputable def projF (q : ℕ) (f : F) : F := C.repF q (C.idx q f) ⟨f, rfl⟩

theorem proj_eq_projF (q : ℕ) (f : F) : C.proj q f = C.projF q f := C.rep_of_realized _

theorem proj_mem (q : ℕ) (f : F) : C.proj q f ∈ F := C.rep_mem ⟨f, rfl⟩

theorem idx_projF (q : ℕ) (f : F) : C.idx q (C.projF q f) = C.idx q f := C.idx_repF _

theorem idx_projF_of_le {p q : ℕ} (h : p ≤ q) (f : F) :
    C.idx p (C.projF q f) = C.idx p f := by
  rw [← C.restrict_idx h, C.idx_projF, C.restrict_idx]

/-- **(C1)** `L_q(k_q f) ≤ π_q f ≤ U_q(k_q f)`. -/
theorem bracket_proj (q : ℕ) (f : F) :
    C.lowerB q (C.idx q f) ≤ C.proj q f ∧ C.proj q f ≤ C.upperB q (C.idx q f) := by
  rw [C.proj_eq_projF]; exact C.bracket_of_idx_eq (C.idx_projF q f)

/-- **(C1)** `|f − π_q f| ≤ Δ_q f`. -/
theorem abs_sub_proj_le (q : ℕ) (f : F) (x : 𝒳) :
    |(f : 𝒳 → ℝ) x - C.proj q f x| ≤ C.width q (C.idx q f) x := by
  have h1 := (C.bracket_idx q f).1 x
  have h2 := (C.bracket_idx q f).2 x
  have h3 := (C.bracket_proj q f).1 x
  have h4 := (C.bracket_proj q f).2 x
  rw [width_apply, abs_sub_le_iff]
  constructor <;> linarith

/-! ### (C2) -/

/-- **(C2)**, for every tuple and every level `p ≤ q`. -/
theorem width_le_bracket {q : ℕ} (k : Tup C.N q) (p : Fin (q + 1)) (x : 𝒳) :
    C.width q k x ≤ C.u p (k p) x - C.l p (k p) x := by
  have h1 := C.l_le_lowerB k p x
  have h2 := C.upperB_le_u k p x
  rw [width_apply]
  linarith

/-- **(C2)** `Δ_q f ≤ u_{q, c_q f} − l_{q, c_q f}`. -/
theorem width_idx_le (q : ℕ) (f : F) (x : 𝒳) :
    C.width q (C.idx q f) x ≤ C.u q (C.cell q f) x - C.l q (C.cell q f) x :=
  C.width_le_bracket (C.idx q f) (Fin.last q) x

theorem bracket_cell_nonneg (q : ℕ) (f : F) (x : 𝒳) :
    0 ≤ C.u q (C.cell q f) x - C.l q (C.cell q f) x :=
  (C.width_idx_nonneg q f x).trans (C.width_idx_le q f x)

/-! ### (C3) -/

/-- **(C3)**, for every tuple: restriction raises the width. -/
theorem width_le_width_restrict {p q : ℕ} (h : p ≤ q) (k : Tup C.N q) (x : 𝒳) :
    C.width q k x ≤ C.width p (Tup.restrict h k) x := by
  have h1 := C.lowerB_restrict_le h k x
  have h2 := C.upperB_le_upperB_restrict h k x
  rw [width_apply, width_apply]
  linarith

theorem width_idx_le_of_le {p q : ℕ} (h : p ≤ q) (f : F) (x : 𝒳) :
    C.width q (C.idx q f) x ≤ C.width p (C.idx p f) x :=
  C.width_le_width_restrict h (C.idx q f) x

/-- **(C3)** `Δ_q f ≤ Δ_{q−1} f`. -/
theorem width_idx_le_pred (q : ℕ) (f : F) (x : 𝒳) :
    C.width q (C.idx q f) x ≤ C.width (q - 1) (C.idx (q - 1) f) x :=
  C.width_idx_le_of_le (Nat.sub_le q 1) f x

theorem abs_proj_sub_proj_le {p q : ℕ} (h : p ≤ q) (f : F) (x : 𝒳) :
    |C.proj q f x - C.proj p f x| ≤ C.width p (C.idx p f) x := by
  have hq := C.bracket_of_idx_eq (C.idx_projF_of_le h f)
  have h1 := hq.1 x
  have h2 := hq.2 x
  have h3 := (C.bracket_proj p f).1 x
  have h4 := (C.bracket_proj p f).2 x
  rw [C.proj_eq_projF q f, width_apply, abs_sub_le_iff]
  constructor <;> linarith

/-- **(C3)** `|π_q f − π_{q−1} f| ≤ Δ_{q−1} f`. -/
theorem abs_proj_sub_proj_pred_le (q : ℕ) (f : F) (x : 𝒳) :
    |C.proj q f x - C.proj (q - 1) f x| ≤ C.width (q - 1) (C.idx (q - 1) f) x :=
  C.abs_proj_sub_proj_le (Nat.sub_le q 1) f x

/-! ### Truncation indicators -/

open Classical in
/-- `A_q(k) = 1{Δ_p(k|_p) ≤ t_p for all p ≤ q}`. -/
noncomputable def indA (t : ℕ → ℝ) (q : ℕ) (k : Tup C.N q) (x : 𝒳) : ℝ :=
  if ∀ p (hp : p ≤ q), C.width p (Tup.restrict hp k) x ≤ t p then 1 else 0

open Classical in
/-- `B_q(k) = A_{q−1}(k|_{q−1}) · 1{Δ_q(k) > t_q}`, with `A_{−1} = 1`; see `indB_zero` and
`indB_succ`. -/
noncomputable def indB (t : ℕ → ℝ) (q : ℕ) (k : Tup C.N q) (x : 𝒳) : ℝ :=
  (if ∀ p (hp : p < q), C.width p (Tup.restrict hp.le k) x ≤ t p then 1 else 0) *
    (if t q < C.width q k x then 1 else 0)

variable (t : ℕ → ℝ)

theorem indA_zero (k : Tup C.N 0) (x : 𝒳) :
    C.indA t 0 k x = if C.width 0 k x ≤ t 0 then 1 else 0 := by
  have key : (∀ p (hp : p ≤ 0), C.width p (Tup.restrict hp k) x ≤ t p) ↔
      C.width 0 k x ≤ t 0 := by
    constructor
    · intro h; exact h 0 le_rfl
    · intro h p hp
      obtain rfl : p = 0 := Nat.le_zero.1 hp
      exact h
  simp only [indA, key]

theorem indA_succ (q : ℕ) (k : Tup C.N (q + 1)) (x : 𝒳) :
    C.indA t (q + 1) k x =
      C.indA t q (Tup.restrict q.le_succ k) x *
        (if C.width (q + 1) k x ≤ t (q + 1) then 1 else 0) := by
  have key : (∀ p (hp : p ≤ q + 1), C.width p (Tup.restrict hp k) x ≤ t p) ↔
      (∀ p (hp : p ≤ q), C.width p (Tup.restrict hp (Tup.restrict q.le_succ k)) x ≤ t p) ∧
        C.width (q + 1) k x ≤ t (q + 1) := by
    constructor
    · intro h; exact ⟨fun p hp => h p (hp.trans q.le_succ), h (q + 1) le_rfl⟩
    · rintro ⟨h1, h2⟩ p hp
      rcases Nat.of_le_succ hp with hp' | rfl
      · exact h1 p hp'
      · exact h2
  simp only [indA, key, ite_zero_mul_ite_zero, mul_one]

theorem indB_zero (k : Tup C.N 0) (x : 𝒳) :
    C.indB t 0 k x = if t 0 < C.width 0 k x then 1 else 0 := by
  have key : (∀ p (hp : p < 0), C.width p (Tup.restrict hp.le k) x ≤ t p) ↔ True :=
    ⟨fun _ => trivial, fun _ p hp => absurd hp (Nat.not_lt_zero p)⟩
  simp only [indB, key, ite_true, one_mul]

theorem indB_succ (q : ℕ) (k : Tup C.N (q + 1)) (x : 𝒳) :
    C.indB t (q + 1) k x =
      C.indA t q (Tup.restrict q.le_succ k) x *
        (if t (q + 1) < C.width (q + 1) k x then 1 else 0) := by
  have key : (∀ p (hp : p < q + 1), C.width p (Tup.restrict hp.le k) x ≤ t p) ↔
      (∀ p (hp : p ≤ q), C.width p (Tup.restrict hp (Tup.restrict q.le_succ k)) x ≤ t p) :=
    ⟨fun h p hp => h p (Nat.lt_succ_of_le hp), fun h p hp => h p (Nat.le_of_lt_succ hp)⟩
  simp only [indB, indA, key]

theorem indA_eq_zero_or_one (q : ℕ) (k : Tup C.N q) (x : 𝒳) :
    C.indA t q k x = 0 ∨ C.indA t q k x = 1 := by
  unfold indA; split_ifs <;> simp

theorem indA_nonneg (q : ℕ) (k : Tup C.N q) (x : 𝒳) : 0 ≤ C.indA t q k x := by
  rcases C.indA_eq_zero_or_one t q k x with h | h <;> simp [h]

theorem indA_le_one (q : ℕ) (k : Tup C.N q) (x : 𝒳) : C.indA t q k x ≤ 1 := by
  rcases C.indA_eq_zero_or_one t q k x with h | h <;> simp [h]

theorem indB_eq_zero_or_one (q : ℕ) (k : Tup C.N q) (x : 𝒳) :
    C.indB t q k x = 0 ∨ C.indB t q k x = 1 := by
  unfold indB; split_ifs <;> simp

theorem indB_nonneg (q : ℕ) (k : Tup C.N q) (x : 𝒳) : 0 ≤ C.indB t q k x := by
  rcases C.indB_eq_zero_or_one t q k x with h | h <;> simp [h]

theorem indB_le_one (q : ℕ) (k : Tup C.N q) (x : 𝒳) : C.indB t q k x ≤ 1 := by
  rcases C.indB_eq_zero_or_one t q k x with h | h <;> simp [h]

private theorem ite_lt_add_ite_le (a b : ℝ) :
    ((if a < b then 1 else 0 : ℝ) + if b ≤ a then 1 else 0) = 1 := by
  by_cases h : a < b
  · simp [h, not_le.2 h]
  · simp [h, not_lt.1 h]

theorem indB_zero_add_indA_zero (k : Tup C.N 0) (x : 𝒳) :
    C.indB t 0 k x + C.indA t 0 k x = 1 := by
  rw [indB_zero, indA_zero, ite_lt_add_ite_le]

theorem indB_succ_add_indA_succ (q : ℕ) (k : Tup C.N (q + 1)) (x : 𝒳) :
    C.indB t (q + 1) k x + C.indA t (q + 1) k x = C.indA t q (Tup.restrict q.le_succ k) x := by
  rw [indB_succ, indA_succ, ← mul_add, ite_lt_add_ite_le, mul_one]

/-- `B_{q+1} ≤ A_q`. -/
theorem indB_succ_le_indA (q : ℕ) (k : Tup C.N (q + 1)) (x : 𝒳) :
    C.indB t (q + 1) k x ≤ C.indA t q (Tup.restrict q.le_succ k) x := by
  have h := C.indB_succ_add_indA_succ t q k x
  have h' := C.indA_nonneg t (q + 1) k x
  linarith

/-- `B_q ≤ A_{q−1}` for `q ≥ 1`. -/
theorem indB_le_indA_pred {q : ℕ} (hq : 1 ≤ q) (k : Tup C.N q) (x : 𝒳) :
    C.indB t q k x ≤ C.indA t (q - 1) (Tup.restrict (Nat.sub_le q 1) k) x := by
  obtain ⟨q, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  exact C.indB_succ_le_indA t q k x

/-- On `A_q = 1`, `Δ_q ≤ t_q`; hence `Δ_q · A_q ≤ t_q · A_q`. -/
theorem width_mul_indA_le (q : ℕ) (k : Tup C.N q) (x : 𝒳) :
    C.width q k x * C.indA t q k x ≤ t q * C.indA t q k x := by
  unfold indA
  split_ifs with h
  · simpa using h q le_rfl
  · simp

theorem width_mul_indA_le_of_nonneg {q : ℕ} (ht : 0 ≤ t q) (k : Tup C.N q) (x : 𝒳) :
    C.width q k x * C.indA t q k x ≤ t q :=
  (C.width_mul_indA_le t q k x).trans
    (mul_le_of_le_one_right ht (C.indA_le_one t q k x))

/-! ### Functions of the cell -/

/-- The majorant `h_q = Δ_q · B_q` of the `B`-pieces, as a function of the tuple. -/
noncomputable def termB (q : ℕ) (k : Tup C.N q) (x : 𝒳) : ℝ := C.width q k x * C.indB t q k x

/-- The majorant `Δ_q · A_q`, as a function of the tuple. -/
noncomputable def termA (q : ℕ) (k : Tup C.N q) (x : 𝒳) : ℝ := C.width q k x * C.indA t q k x

/-- The link `g_q = (π_q f − π_{q−1} f) A_{q−1} f`, as a function of the level-`q` tuple. -/
noncomputable def link (q : ℕ) (k : Tup C.N q) (x : 𝒳) : ℝ :=
  (C.rep q k x - C.rep (q - 1) (Tup.restrict (Nat.sub_le q 1) k) x) *
    C.indA t (q - 1) (Tup.restrict (Nat.sub_le q 1) k) x

theorem link_idx (q : ℕ) (f : F) (x : 𝒳) :
    C.link t q (C.idx q f) x =
      (C.proj q f x - C.proj (q - 1) f x) * C.indA t (q - 1) (C.idx (q - 1) f) x := rfl

theorem termB_idx (q : ℕ) (f : F) (x : 𝒳) :
    C.termB t q (C.idx q f) x = C.width q (C.idx q f) x * C.indB t q (C.idx q f) x := rfl

theorem termA_idx (q : ℕ) (f : F) (x : 𝒳) :
    C.termA t q (C.idx q f) x = C.width q (C.idx q f) x * C.indA t q (C.idx q f) x := rfl

/-- `A_{q−1} f` as a function of the level-`q` cell. -/
theorem indA_pred_idx (q : ℕ) (f : F) (x : 𝒳) :
    C.indA t (q - 1) (C.idx (q - 1) f) x =
      C.indA t (q - 1) (Tup.restrict (Nat.sub_le q 1) (C.idx q f)) x := rfl

/-! ### Lemma D -/

/-- **Lemma D.** Pointwise, for every `Q` (in particular every `Q ≥ 1`),
`f − π_0 f = Σ_{q ≤ Q} (f − π_q f) B_q f + Σ_{1 ≤ q ≤ Q} (π_q f − π_{q−1} f) A_{q−1} f
  + (f − π_Q f) A_Q f`. -/
theorem sub_proj_zero_eq (f : F) (Q : ℕ) (x : 𝒳) :
    (f : 𝒳 → ℝ) x - C.proj 0 f x =
      ∑ q ∈ range (Q + 1), ((f : 𝒳 → ℝ) x - C.proj q f x) * C.indB t q (C.idx q f) x
      + ∑ q ∈ Ico 1 (Q + 1),
          (C.proj q f x - C.proj (q - 1) f x) * C.indA t (q - 1) (C.idx (q - 1) f) x
      + ((f : 𝒳 → ℝ) x - C.proj Q f x) * C.indA t Q (C.idx Q f) x := by
  induction Q with
  | zero =>
    have h0 := C.indB_zero_add_indA_zero t (C.idx 0 f) x
    simp only [zero_add, range_one, sum_singleton, Ico_self, sum_empty, add_zero]
    linear_combination (-((f : 𝒳 → ℝ) x - C.proj 0 f x)) * h0
  | succ Q ih =>
    have h1 := C.indB_succ_add_indA_succ t Q (C.idx (Q + 1) f) x
    rw [C.restrict_idx] at h1
    rw [sum_range_succ, sum_Ico_succ_top (by omega : 1 ≤ Q + 1), Nat.add_sub_cancel]
    linear_combination ih - ((f : 𝒳 → ℝ) x - C.proj (Q + 1) f x) * h1

/-! ### Bounds on the pieces -/

/-- `|(f − π_q f) B_q f| ≤ Δ_q f · B_q f`. -/
theorem abs_sub_proj_mul_indB_le (q : ℕ) (f : F) (x : 𝒳) :
    |((f : 𝒳 → ℝ) x - C.proj q f x) * C.indB t q (C.idx q f) x| ≤
      C.width q (C.idx q f) x * C.indB t q (C.idx q f) x := by
  rw [abs_mul, abs_of_nonneg (C.indB_nonneg t q _ x)]
  exact mul_le_mul_of_nonneg_right (C.abs_sub_proj_le q f x) (C.indB_nonneg t q _ x)

/-- `Δ_q f · B_q f ≤ Δ_{q−1} f · A_{q−1} f` for `q ≥ 1`. -/
theorem width_mul_indB_le_pred {q : ℕ} (hq : 1 ≤ q) (f : F) (x : 𝒳) :
    C.width q (C.idx q f) x * C.indB t q (C.idx q f) x ≤
      C.width (q - 1) (C.idx (q - 1) f) x * C.indA t (q - 1) (C.idx (q - 1) f) x := by
  calc C.width q (C.idx q f) x * C.indB t q (C.idx q f) x
      ≤ C.width (q - 1) (C.idx (q - 1) f) x * C.indB t q (C.idx q f) x :=
        mul_le_mul_of_nonneg_right (C.width_idx_le_pred q f x) (C.indB_nonneg t q _ x)
    _ ≤ C.width (q - 1) (C.idx (q - 1) f) x * C.indA t (q - 1) (C.idx (q - 1) f) x :=
        mul_le_mul_of_nonneg_left (C.indB_le_indA_pred t hq (C.idx q f) x)
          (C.width_idx_nonneg (q - 1) f x)

/-- `Δ_q f · B_q f ≤ t_{q−1} · A_{q−1} f` for `q ≥ 1`. -/
theorem width_mul_indB_le_mul_indA {q : ℕ} (hq : 1 ≤ q) (f : F) (x : 𝒳) :
    C.width q (C.idx q f) x * C.indB t q (C.idx q f) x ≤
      t (q - 1) * C.indA t (q - 1) (C.idx (q - 1) f) x :=
  (C.width_mul_indB_le_pred t hq f x).trans (C.width_mul_indA_le t (q - 1) _ x)

/-- `Δ_q f · B_q f ≤ t_{q−1}` for `q ≥ 1` and `t_{q−1} ≥ 0`. -/
theorem width_mul_indB_le {q : ℕ} (hq : 1 ≤ q) (ht : 0 ≤ t (q - 1)) (f : F) (x : 𝒳) :
    C.width q (C.idx q f) x * C.indB t q (C.idx q f) x ≤ t (q - 1) :=
  (C.width_mul_indB_le_pred t hq f x).trans (C.width_mul_indA_le_of_nonneg t ht _ x)

/-- `|(π_q f − π_{q−1} f) A_{q−1} f| ≤ Δ_{q−1} f · A_{q−1} f`. -/
theorem abs_link_le (q : ℕ) (f : F) (x : 𝒳) :
    |(C.proj q f x - C.proj (q - 1) f x) * C.indA t (q - 1) (C.idx (q - 1) f) x| ≤
      C.width (q - 1) (C.idx (q - 1) f) x * C.indA t (q - 1) (C.idx (q - 1) f) x := by
  rw [abs_mul, abs_of_nonneg (C.indA_nonneg t _ _ x)]
  exact mul_le_mul_of_nonneg_right (C.abs_proj_sub_proj_pred_le q f x) (C.indA_nonneg t _ _ x)

/-- `|(π_q f − π_{q−1} f) A_{q−1} f| ≤ t_{q−1} · A_{q−1} f`. -/
theorem abs_link_le_mul_indA (q : ℕ) (f : F) (x : 𝒳) :
    |(C.proj q f x - C.proj (q - 1) f x) * C.indA t (q - 1) (C.idx (q - 1) f) x| ≤
      t (q - 1) * C.indA t (q - 1) (C.idx (q - 1) f) x :=
  (C.abs_link_le t q f x).trans (C.width_mul_indA_le t (q - 1) _ x)

/-- `|(π_q f − π_{q−1} f) A_{q−1} f| ≤ t_{q−1}` when `t_{q−1} ≥ 0`. -/
theorem abs_link_le_of_nonneg (q : ℕ) (ht : 0 ≤ t (q - 1)) (f : F) (x : 𝒳) :
    |(C.proj q f x - C.proj (q - 1) f x) * C.indA t (q - 1) (C.idx (q - 1) f) x| ≤ t (q - 1) :=
  (C.abs_link_le t q f x).trans (C.width_mul_indA_le_of_nonneg t ht _ x)

/-- `|(f − π_Q f) A_Q f| ≤ Δ_Q f · A_Q f`. -/
theorem abs_sub_proj_mul_indA_le (Q : ℕ) (f : F) (x : 𝒳) :
    |((f : 𝒳 → ℝ) x - C.proj Q f x) * C.indA t Q (C.idx Q f) x| ≤
      C.width Q (C.idx Q f) x * C.indA t Q (C.idx Q f) x := by
  rw [abs_mul, abs_of_nonneg (C.indA_nonneg t _ _ x)]
  exact mul_le_mul_of_nonneg_right (C.abs_sub_proj_le Q f x) (C.indA_nonneg t _ _ x)

/-- `|(f − π_Q f) A_Q f| ≤ t_Q · A_Q f`. -/
theorem abs_sub_proj_mul_indA_le_mul (Q : ℕ) (f : F) (x : 𝒳) :
    |((f : 𝒳 → ℝ) x - C.proj Q f x) * C.indA t Q (C.idx Q f) x| ≤
      t Q * C.indA t Q (C.idx Q f) x :=
  (C.abs_sub_proj_mul_indA_le t Q f x).trans (C.width_mul_indA_le t Q _ x)

/-- `|(f − π_Q f) A_Q f| ≤ t_Q` when `t_Q ≥ 0`. -/
theorem abs_sub_proj_mul_indA_le_of_nonneg {Q : ℕ} (ht : 0 ≤ t Q) (f : F) (x : 𝒳) :
    |((f : 𝒳 → ℝ) x - C.proj Q f x) * C.indA t Q (C.idx Q f) x| ≤ t Q :=
  (C.abs_sub_proj_mul_indA_le t Q f x).trans (C.width_mul_indA_le_of_nonneg t ht _ x)

/-! ### Measurability -/

section Measurability

variable [MeasurableSpace 𝒳] {C}
variable (hm : ∀ q i, Measurable (C.l q i) ∧ Measurable (C.u q i))
include hm

theorem measurable_lowerB (q : ℕ) (k : Tup C.N q) : Measurable (C.lowerB q k) :=
  Finset.measurable_sup' _ fun p _ => (hm p (k p)).1

theorem measurable_upperB (q : ℕ) (k : Tup C.N q) : Measurable (C.upperB q k) :=
  Finset.inf'_induction (p := Measurable) Finset.univ_nonempty _
    (fun _ hf _ hg => hf.inf hg) fun p _ => (hm p (k p)).2

theorem measurable_width (q : ℕ) (k : Tup C.N q) : Measurable (C.width q k) :=
  (measurable_upperB hm q k).sub (measurable_lowerB hm q k)

theorem measurable_indA (q : ℕ) (k : Tup C.N q) : Measurable (C.indA t q k) := by
  classical
  have hS : MeasurableSet {x | ∀ p (hp : p ≤ q), C.width p (Tup.restrict hp k) x ≤ t p} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun p => MeasurableSet.iInter fun hp =>
      measurableSet_le (measurable_width hm p _) measurable_const
  have h : C.indA t q k =
      Set.indicator {x | ∀ p (hp : p ≤ q), C.width p (Tup.restrict hp k) x ≤ t p} 1 := by
    funext x
    simp only [indA, Set.indicator, Set.mem_ofPred_eq, Pi.one_apply]
  rw [h]
  exact measurable_one.indicator hS

theorem measurable_indB (q : ℕ) (k : Tup C.N q) : Measurable (C.indB t q k) := by
  classical
  have hS : MeasurableSet {x | ∀ p (hp : p < q), C.width p (Tup.restrict hp.le k) x ≤ t p} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun p => MeasurableSet.iInter fun hp =>
      measurableSet_le (measurable_width hm p _) measurable_const
  have hT : MeasurableSet {x | t q < C.width q k x} :=
    measurableSet_lt measurable_const (measurable_width hm q k)
  have h : C.indB t q k = fun x =>
      Set.indicator {x | ∀ p (hp : p < q), C.width p (Tup.restrict hp.le k) x ≤ t p} 1 x *
        Set.indicator {x | t q < C.width q k x} 1 x := by
    funext x
    simp only [indB, Set.indicator, Set.mem_ofPred_eq, Pi.one_apply]
  rw [h]
  exact (measurable_one.indicator hS).mul (measurable_one.indicator hT)

theorem measurable_termA (q : ℕ) (k : Tup C.N q) : Measurable (C.termA t q k) :=
  (measurable_width hm q k).mul (measurable_indA t hm q k)

theorem measurable_termB (q : ℕ) (k : Tup C.N q) : Measurable (C.termB t q k) :=
  (measurable_width hm q k).mul (measurable_indB t hm q k)

end Measurability

section MeasurabilityF

variable [MeasurableSpace 𝒳] {C}
variable (hF : ∀ g ∈ F, Measurable g)
include hF

theorem measurable_rep (q : ℕ) (k : Tup C.N q) : Measurable (C.rep q k) := by
  by_cases h : C.Realized q k
  · exact hF _ (C.rep_mem h)
  · rw [C.rep_of_not_realized h]; exact measurable_const

theorem measurable_proj (q : ℕ) (f : F) : Measurable (C.proj q f) :=
  hF _ (C.proj_mem q f)

variable (hm : ∀ q i, Measurable (C.l q i) ∧ Measurable (C.u q i))
include hm

theorem measurable_link (q : ℕ) (k : Tup C.N q) : Measurable (C.link t q k) :=
  ((measurable_rep hF q k).sub (measurable_rep hF _ _)).mul (measurable_indA t hm _ _)

theorem measurable_sub_proj_mul_indB (q : ℕ) (f : F) :
    Measurable fun x => ((f : 𝒳 → ℝ) x - C.proj q f x) * C.indB t q (C.idx q f) x :=
  ((hF _ f.2).sub (measurable_proj hF q f)).mul (measurable_indB t hm _ _)

theorem measurable_proj_sub_proj_mul_indA (q : ℕ) (f : F) :
    Measurable fun x =>
      (C.proj q f x - C.proj (q - 1) f x) * C.indA t (q - 1) (C.idx (q - 1) f) x :=
  measurable_link t hF hm q (C.idx q f)

theorem measurable_sub_proj_mul_indA (Q : ℕ) (f : F) :
    Measurable fun x => ((f : 𝒳 → ℝ) x - C.proj Q f x) * C.indA t Q (C.idx Q f) x :=
  ((hF _ f.2).sub (measurable_proj hF Q f)).mul (measurable_indA t hm _ _)

end MeasurabilityF

end BracketChain

end Hellinger.VdW
