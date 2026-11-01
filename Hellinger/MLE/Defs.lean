/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.Definitions
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
Objects for the corrected sieve MLE theorem, Theorem 8 of the paper.

Densities are pointwise `ℝ≥0`-valued measurable functions with respect to one fixed,
arbitrary reference measure `μ`; no σ-finiteness is assumed. Pointwise representatives
are kept: brackets, sample likelihoods and empirical suprema all evaluate them pointwise.
Entropies, bracketing integrals, moments and outer expectations take extended values.
Outer probability is a measure applied to an arbitrary set, which mathlib evaluates as the
outer measure; outer expectation is the infimum of `lintegral` over measurable majorants.
-/

@[expose] public section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal

namespace Hellinger.MLE

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-! ### Densities and the Hellinger distance -/

/-- A probability density with respect to `μ`: a measurable `ℝ≥0`-valued function of mass one. -/
structure IsProbDensity (μ : Measure 𝒳) (p : 𝒳 → ℝ≥0) : Prop where
  measurable : Measurable p
  lintegral_eq_one : ∫⁻ x, (p x : ℝ≥0∞) ∂μ = 1

/-- The law `p · μ` of a density. -/
noncomputable def law (μ : Measure 𝒳) (p : 𝒳 → ℝ≥0) : Measure 𝒳 :=
  μ.withDensity fun x ↦ (p x : ℝ≥0∞)

/-- Squared Hellinger distance between nonnegative functions, with the paper's
normalization `∫ (√f - √g)^2 dμ` (no factor `1/2`). The functions need not be normalized. -/
noncomputable def hellingerFunSq (μ : Measure 𝒳) (f g : 𝒳 → ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((Real.sqrt (f x) - Real.sqrt (g x)) ^ 2) ∂μ

/-- Hellinger distance: the nonnegative square root of `hellingerFunSq`. -/
noncomputable def hdist (μ : Measure 𝒳) (f g : 𝒳 → ℝ≥0) : ℝ≥0∞ :=
  hellingerFunSq μ f g ^ (1 / 2 : ℝ)

/-! ### Brackets, bracketing numbers and the nonstandardized bracketing integral -/

/-- A finite family of brackets, each admissible and of size below `ε`, covers `F` pointwise.
Bracket endpoints need not belong to `F`. -/
def IsBracketCover {β : Type*} [Preorder β] (adm : (𝒳 → β) → (𝒳 → β) → Prop)
    (size : (𝒳 → β) → (𝒳 → β) → ℝ≥0∞) (ε : ℝ≥0∞) (F : Set (𝒳 → β))
    {n : ℕ} (b : Fin n → (𝒳 → β) × (𝒳 → β)) : Prop :=
  (∀ i, adm (b i).1 (b i).2 ∧ (b i).1 ≤ (b i).2 ∧ size (b i).1 (b i).2 < ε) ∧
    ∀ f ∈ F, ∃ i, (b i).1 ≤ f ∧ f ≤ (b i).2

/-- The bracketing number: the least size of a bracket cover, and `⊤` when no finite cover
exists. The empty class has bracketing number `0`. -/
noncomputable def bracketingNumber {β : Type*} [Preorder β]
    (adm : (𝒳 → β) → (𝒳 → β) → Prop) (size : (𝒳 → β) → (𝒳 → β) → ℝ≥0∞)
    (ε : ℝ≥0∞) (F : Set (𝒳 → β)) : ℕ∞ :=
  ⨅ (n : ℕ) (_ : ∃ b : Fin n → (𝒳 → β) × (𝒳 → β), IsBracketCover adm size ε F b), (n : ℕ∞)

/-- The integrand `√(1 + log N)`. An infinite bracketing number gives `⊤`. `Real.log 0 = 0`,
so the empty class (`N = 0`) has integrand `1`, the same as a single bracket. -/
noncomputable def entropyIntegrand (N : ℕ∞) : ℝ≥0∞ :=
  if N = ⊤ then ⊤ else ENNReal.ofReal (Real.sqrt (1 + Real.log (N.toNat : ℝ)))

/-- The nonstandardized bracketing integral `∫₀^δ √(1 + log N(ε)) dε`, in extended values.
The bracketing number is antitone in `ε` and `entropyIntegrand` is monotone, so the integrand
is antitone, hence measurable, and this lower integral is the genuine integral. -/
noncomputable def bracketingIntegral {β : Type*} [Preorder β]
    (adm : (𝒳 → β) → (𝒳 → β) → Prop) (size : (𝒳 → β) → (𝒳 → β) → ℝ≥0∞)
    (δ : ℝ) (F : Set (𝒳 → β)) : ℝ≥0∞ :=
  ∫⁻ ε in Ioc 0 δ, entropyIntegrand (bracketingNumber adm size (ENNReal.ofReal ε) F)

/-- Hellinger brackets: measurable nonnegative endpoints of finite `μ`-mass. -/
def HellingerAdmissible (μ : Measure 𝒳) (l u : 𝒳 → ℝ≥0) : Prop :=
  Measurable l ∧ Measurable u ∧ ∫⁻ x, (l x : ℝ≥0∞) ∂μ < ∞ ∧ ∫⁻ x, (u x : ℝ≥0∞) ∂μ < ∞

/-- `N_[](ε, F, h)`. -/
noncomputable def hBracketingNumber (μ : Measure 𝒳) (ε : ℝ≥0∞) (F : Set (𝒳 → ℝ≥0)) : ℕ∞ :=
  bracketingNumber (HellingerAdmissible μ) (hdist μ) ε F

/-- `J̃_[](δ, F, h)`. -/
noncomputable def hBracketingIntegral (μ : Measure 𝒳) (δ : ℝ) (F : Set (𝒳 → ℝ≥0)) : ℝ≥0∞ :=
  bracketingIntegral (HellingerAdmissible μ) (hdist μ) δ F

/-! ### The Bernstein functional -/

/-- `‖f‖²_{P,B} = 2 P(e^{|f|} - 1 - |f|)`. Not a norm: neither homogeneous nor subadditive. -/
noncomputable def bernsteinFunSq (P : Measure 𝒳) (f : 𝒳 → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (bernsteinKernel 1 (f x)) ∂P

/-- `‖f‖_{P,B}`, the nonnegative square root of `bernsteinFunSq`. -/
noncomputable def bernsteinFun (P : Measure 𝒳) (f : 𝒳 → ℝ) : ℝ≥0∞ :=
  bernsteinFunSq P f ^ (1 / 2 : ℝ)

/-- Bernstein brackets: measurable endpoints of finite Bernstein size. -/
def BernsteinAdmissible (P : Measure 𝒳) (l u : 𝒳 → ℝ) : Prop :=
  Measurable l ∧ Measurable u ∧ bernsteinFun P l < ∞ ∧ bernsteinFun P u < ∞

/-- Bracket size `‖u - l‖_{P,B}`. -/
noncomputable def bernsteinBracketSize (P : Measure 𝒳) (l u : 𝒳 → ℝ) : ℝ≥0∞ :=
  bernsteinFun P (u - l)

/-- `J̃_[](δ, F, ‖·‖_{P,B})`. -/
noncomputable def bBracketingIntegral (P : Measure 𝒳) (δ : ℝ) (F : Set (𝒳 → ℝ)) : ℝ≥0∞ :=
  bracketingIntegral (BernsteinAdmissible P) (bernsteinBracketSize P) δ F

/-! ### Outer expectation, stochastic order and the empirical process -/

section Outer

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Outer expectation `E^* Z`: the infimum of `∫⁻ g` over measurable pointwise majorants `g`.
(`∫⁻` of a nonmeasurable function is an inner integral and is not used.) -/
noncomputable def outerLIntegral (ℙ : Measure Ω) (Z : Ω → ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ (g : Ω → ℝ≥0∞) (_ : Measurable g) (_ : Z ≤ g), ∫⁻ ω, g ω ∂ℙ

/-- `Z_n = O_P^*(b_n)` for nonnegative extended `Z_n`: for every `ε > 0` there are `K > 0` and
`N` with outer probability of `{Z_n > K b_n}` at most `ε` for `n ≥ N`. The probability of an
arbitrary set is its outer measure. A zero rate is handled without division. -/
def OPStar (ℙ : Measure Ω) (Z : ℕ → Ω → ℝ≥0∞) (b : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, ∀ n ≥ N,
    ℙ {ω | ENNReal.ofReal (K * b n) < Z n ω} ≤ ENNReal.ofReal ε

/-- The first `n` observations of a sequence. -/
def sample (X : ℕ → Ω → 𝒳) (n : ℕ) (ω : Ω) : Fin n → 𝒳 := fun i ↦ X i ω

end Outer

/-- The empirical process `𝔾_n f = √n (ℙ_n f - P f)` at a sample point `x : Fin n → 𝒳`.
It is used only for classes of functions with finite Bernstein size, which are integrable. -/
noncomputable def empiricalProcess (P : Measure 𝒳) {n : ℕ} (f : 𝒳 → ℝ) (x : Fin n → 𝒳) : ℝ :=
  Real.sqrt n * ((n : ℝ)⁻¹ * ∑ i, f (x i) - ∫ y, f y ∂P)

/-- `sup_{f ∈ F} |𝔾_n f|` in extended values; `0` for an empty class. -/
noncomputable def empiricalSup (P : Measure 𝒳) {n : ℕ} (F : Set (𝒳 → ℝ)) (x : Fin n → 𝒳) :
    ℝ≥0∞ :=
  ⨆ f ∈ F, ENNReal.ofReal |empiricalProcess P f x|

/-! ### Sample likelihood -/

/-- The likelihood `∏ p(x_i)`. -/
noncomputable def likelihood {n : ℕ} (x : Fin n → 𝒳) (p : 𝒳 → ℝ≥0) : ℝ≥0 := ∏ i, p (x i)

/-- The optimization deficit `(ℙ_n log p - ℙ_n log q)_+` of `q` relative to `p`, with
`log 0 = -∞`. A zero likelihood for `q` against a positive one for `p` gives `⊤`; two zero
likelihoods give `0`. -/
noncomputable def logLikDeficit {n : ℕ} (x : Fin n → 𝒳) (p q : 𝒳 → ℝ≥0) : ℝ≥0∞ :=
  if likelihood x p = 0 then 0
  else if likelihood x q = 0 then ⊤
  else ENNReal.ofReal
    ((Real.log (likelihood x p : ℝ) - Real.log (likelihood x q : ℝ)) / n)

/-! ### Rates, shells and the annular entropy-tail condition -/

/-- `a_n = max(δ_n, n^{-1/2})`. Positive for `n ≥ 1`. -/
noncomputable def rate (δ : ℕ → ℝ) (n : ℕ) : ℝ := max (δ n) (Real.sqrt n)⁻¹

/-- `s_{nj} = 2^{j/2} a`, written as `(√2)^j a` so no natural-number division occurs. -/
noncomputable def shellScale (a : ℝ) (j : ℕ) : ℝ := Real.sqrt 2 ^ j * a

/-- The Hellinger ball `S_{n,r} = {p ∈ S : h(p₀, p) ≤ r}`. -/
def hBall (μ : Measure 𝒳) (p₀ : 𝒳 → ℝ≥0) (S : Set (𝒳 → ℝ≥0)) (r : ℝ) : Set (𝒳 → ℝ≥0) :=
  {p ∈ S | hdist μ p₀ p ≤ ENNReal.ofReal r}

/-- The annulus `{p ∈ S : s < h(p₀, p) ≤ √2 s}`: strict lower and weak upper endpoint. -/
def annulus (μ : Measure 𝒳) (p₀ : 𝒳 → ℝ≥0) (S : Set (𝒳 → ℝ≥0)) (s : ℝ) : Set (𝒳 → ℝ≥0) :=
  {p ∈ S | ENNReal.ofReal s < hdist μ p₀ p ∧ hdist μ p₀ p ≤ ENNReal.ofReal (Real.sqrt 2 * s)}

/-- `K_{nj}`: zero on an empty annulus, else `J̃_[](√2 s, A, h)`. -/
noncomputable def annulusEntropy (μ : Measure 𝒳) (p₀ : 𝒳 → ℝ≥0) (S : Set (𝒳 → ℝ≥0))
    (s : ℝ) : ℝ≥0∞ := by
  classical
  exact if annulus μ p₀ S s = ∅ then 0
    else hBracketingIntegral μ (Real.sqrt 2 * s) (annulus μ p₀ S s)

/-- `u_{nj} = K_{nj} / (√n s_{nj}²)`. -/
noncomputable def shellTerm (μ : Measure 𝒳) (p₀ : 𝒳 → ℝ≥0) (S : Set (𝒳 → ℝ≥0))
    (n : ℕ) (a : ℝ) (j : ℕ) : ℝ≥0∞ :=
  annulusEntropy μ p₀ S (shellScale a j) /
    ENNReal.ofReal (Real.sqrt n * shellScale a j ^ 2)

/-- `T_n(k) = Σ_{j ≥ k, s_{nj} < √2} u_{nj}`. For `a > 0` only finitely many terms are
nonzero; the extended sum is used so that no finiteness is presupposed. -/
noncomputable def shellTail (μ : Measure 𝒳) (p₀ : 𝒳 → ℝ≥0) (S : ℕ → Set (𝒳 → ℝ≥0))
    (δ : ℕ → ℝ) (n k : ℕ) : ℝ≥0∞ := by
  classical
  exact ∑' j, if k ≤ j ∧ shellScale (rate δ n) j < Real.sqrt 2 then
    shellTerm μ p₀ (S n) n (rate δ n) j else 0

/-- Condition (D): `lim_k limsup_n T_n(k) = 0`, in the order "uniform eventually in `n`,
then a fixed large cutoff `k`". -/
def AnnularTailCondition (μ : Measure 𝒳) (p₀ : 𝒳 → ℝ≥0) (S : ℕ → Set (𝒳 → ℝ≥0))
    (δ : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ k N : ℕ, ∀ n ≥ N, shellTail μ p₀ S δ n k ≤ ENNReal.ofReal ε

/-- Condition (H), the power envelope: for fixed `C > 0`, `1 ≤ β < 2` and `n₀`,
`J̃_[](r, S_{n,r}, h) ≤ C √n a_n^{2-β} r^β` for `n ≥ n₀` and `r ≥ a_n`. -/
def PowerEnvelopeCondition (μ : Measure 𝒳) (p₀ : 𝒳 → ℝ≥0) (S : ℕ → Set (𝒳 → ℝ≥0))
    (δ : ℕ → ℝ) : Prop :=
  ∃ C β : ℝ, 0 < C ∧ 1 ≤ β ∧ β < 2 ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ r : ℝ, rate δ n ≤ r →
    hBracketingIntegral μ r (hBall μ p₀ (S n) r) ≤
      ENNReal.ofReal (C * Real.sqrt n * rate δ n ^ (2 - β) * r ^ β)

/-- Condition (G), the whole-sieve bound at the positive radius `a_n`:
`J̃_[](a_n, S_n, h) ≤ C √n a_n²` eventually. -/
def WholeSieveCondition (μ : Measure 𝒳) (S : ℕ → Set (𝒳 → ℝ≥0)) (δ : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
    hBracketingIntegral μ (rate δ n) (S n) ≤ ENNReal.ofReal (C * Real.sqrt n * rate δ n ^ 2)

end Hellinger.MLE
