/-
Copyright (c) 2026 Tetsuya Kaji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Kaji
-/
module

public import Hellinger.MLE.Defs

/-!
The maximal inequality used in the proof of Theorem 8: van der Vaart and Wellner (2023),
Theorem 2.14.18' (printed p. 339; nonstandardized bracketing integral defined on printed
p. 338).

`VdW_2_14_18_prime` is the statement, as a `Prop`; it is proved, with `K₀ = 80`, as
`External.vdw_2_14_18_prime` in `Hellinger/VdW/Main.lean`. Theorems that take it as an
explicit hypothesis display the dependence in their types; each also has an unconditional
form.

Correspondence with van der Vaart and Wellner, who state the theorem for coordinate
projections on a product probability space:
* the class `F` is an arbitrary set of measurable real functions with `‖f‖_{P,B} ≤ δ`;
* `E^*_P ‖𝔾_n‖_F` is the outer expectation on the canonical space `(𝒳ⁿ, Pⁿ)` of
  `sup_{f ∈ F} |𝔾_n f|`; coordinate projections from the infinite product onto `𝒳ⁿ` are
  perfect (van der Vaart and Wellner 2023, Lemma 1.2.5; the lemma is stated for bounded maps
  and extends to `ℝ≥0∞` by truncation, `(T ∧ M)^* = T^* ∧ M` by Lemma 1.2.2(ix), and monotone
  convergence), so this agrees with their outer expectation.
  The inequality `E^*` on the infinite product `≤ E^*` on `𝒳ⁿ` always holds; perfectness gives
  the non-trivial reverse direction, which shows that this statement is no stronger than
  theirs;
* `J̃_[](δ, F, ‖·‖_{P,B})` uses brackets of size `‖u - l‖_{P,B} < ε` with measurable endpoints
  of finite Bernstein size. Requiring measurability can only enlarge bracketing numbers and
  so weakens, never strengthens, the stated bound;
* `≲` is a universal constant `K₀`, chosen before the space, measure, class, sample size and
  radius.
The transfer to an arbitrary probability space carrying an i.i.d. sample is a proved lemma,
not part of this statement.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace Hellinger.MLE.External

universe u

/-- van der Vaart and Wellner (2023), Theorem 2.14.18', on the canonical product space. -/
def VdW_2_14_18_prime : Prop :=
  ∃ K₀ : ℝ≥0, ∀ (𝒳 : Type u) [MeasurableSpace 𝒳] (P : Measure 𝒳) [IsProbabilityMeasure P]
    (F : Set (𝒳 → ℝ)) (n : ℕ) (δ : ℝ), 0 < n → 0 < δ →
    (∀ f ∈ F, Measurable f ∧ bernsteinFun P f ≤ ENNReal.ofReal δ) →
    outerLIntegral (Measure.pi fun _ : Fin n ↦ P) (empiricalSup P F) ≤
      (K₀ : ℝ≥0∞) * bBracketingIntegral P δ F *
        (1 + bBracketingIntegral P δ F / ENNReal.ofReal (δ ^ 2 * Real.sqrt n))

end Hellinger.MLE.External
