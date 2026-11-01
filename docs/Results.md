# Result map

This map connects 49 principal results to Theorems 1, 2 and 8 and Section 4 of [Kaji (2026)](https://doi.org/10.1007/s42973-026-00243-x), together with the sharpened constants.
The [mathematical notes](../NOTES.md) record the corrections and endpoint clarifications used below.
Every declaration is available through `import Hellinger`; [declarations.json](../declarations.json) gives the machine-readable map and related declarations.

## Notation and domains

Let `μ = P₀` and `ν = P` be probability measures on an arbitrary measurable space, `R = p₀/p`, and `L = log R`.
Write `H² = ∫(√p₀ − √p)²`, `K = KL(μ, ν)`, `Vₖ = E₀|L|ᵏ`, `Vₖ,₀ = E₀|L − K|ᵏ`, and `Bδ² = 2E₀[exp(|δL|) − 1 − |δL|]`.
For a fixed real `q > 1`, set `Tδ(q) = E₀[Rᵟ; R > q]` and `Aₖ(q) = E₀[Lᵏ; R > q]`.
The nonnegative quantities take values in `[0, ∞]`; singular-support contributions are retained.
Only the centered moment requires `K < ∞`.
No common dominating measure is required for an entire family: a dominating measure can be chosen separately for each pair.
The density identities are proved in [HellingerBridge.lean](../Hellinger/HellingerBridge.lean), [DensityBridge.lean](../Hellinger/Comparison/DensityBridge.lean), and [DensityTailBridge.lean](../Hellinger/Comparison/DensityTailBridge.lean).

The explicit constants in [Constants.lean](../Hellinger/Constants.lean) are

```text
b(q,δ) = (1 − q^(−δ))²                 C_B(q,δ) = 2δ(1 + √q)²
C_K(q) = 1 + √q                        a_K(q) = min(1/3, (1 − 1/q)/2)
J(q) = (1 − q^(−1/2))^(−2)             C_I(q) = J(q)
C_V(q,k) = max(4√q (log q)^(k−2), J(q)(k/e)^k).
```

The intended domains are `0 < δ ≤ 1` for the Bernstein comparison, `k ≥ 2` for the full log-moment comparison, and `k' ≥ k > 0` for log-tail interpolation.
Power-tail interpolation covers every `δ' ≥ δ > 0`, without an upper bound of one.
Some individual Lean lemmas have broader domains, including finite measures or arbitrary positive Bernstein scale; their types state those hypotheses explicitly.

## Theorem 1

| Article locator | Formal statement | Lean declaration |
| --- | --- | --- |
| Theorem 1 | `b(q,δ) Tδ(q) ≤ Bδ²` | [`Hellinger.bernsteinLowerCoeff_mul_tailPower_le_bernsteinSq`](../Hellinger/BernsteinBounds.lean) |
| Theorem 1 | `Bδ² ≤ C_B(q,δ) H² + 2Tδ(q)` | [`Hellinger.bernsteinSq_le_hellinger_add_tailPower`](../Hellinger/BernsteinBounds.lean) |
| Theorem 1(i) | `H² ≤ K` | [`Hellinger.hellingerSq_le_kl`](../Hellinger/KL.lean) |
| Theorem 1(i) | `K ≤ C_K(q) H² + δ⁻¹Tδ(q)` | [`Hellinger.kl_le_hellinger_add_tailPower`](../Hellinger/KLPower.lean) |
| Theorem 1(ii) | `2^(−k) Vₖ,₀ ≤ Vₖ` for real `k ≥ 2` and finite KL | [`Hellinger.two_neg_rpow_mul_centeredLogMoment_le_logMoment`](../Hellinger/Centering.lean) |
| Theorem 1(ii) | `Vₖ ≤ Γ(k+1) δ^(−k) Bδ²/2` for real `k ≥ 2` | [`Hellinger.logMoment_le_gamma_bernsteinSq`](../Hellinger/GammaMoment.lean) |

## Theorem 2

| Article locator | Formal statement | Lean declaration |
| --- | --- | --- |
| Theorem 2(i) | `a_K(q) A₁(q) ≤ K` | [`Hellinger.klTailLowerCoeff_mul_tailLogMoment_le_kl`](../Hellinger/KLBounds.lean) |
| Theorem 2(i) | `K ≤ C_K(q) H² + A₁(q)` | [`Hellinger.kl_le_hellinger_add_tailLogMoment`](../Hellinger/KLBounds.lean) |
| Theorem 2(ii) | `Aₖ(q) ≤ Vₖ` | [`Hellinger.tailLogMoment_le_logMoment`](../Hellinger/VariationBounds.lean) |
| Theorem 2(ii) | `Vₖ ≤ C_V(q,k) H² + Aₖ(q)` for real `k ≥ 2` | [`Hellinger.logMoment_le_hellinger_add_tailLogMoment`](../Hellinger/VariationBounds.lean) |
| Theorem 2(iii) | `Aₖ(q) ≤ J(q)(H²)^(1−k/k') Aₖ'(q)^(k/k')` for `k' ≥ k > 0` | [`Hellinger.tailLogMoment_interpolation`](../Hellinger/Interpolation.lean) |

At equal exponents, interpolation is also proved directly as `Aₖ(q) ≤ J(q) Aₖ(q)`, including zero and infinity.
The cutoff-four statements are in [CutoffFour.lean](../Hellinger/CutoffFour.lean) and [CutoffFourMoments.lean](../Hellinger/CutoffFourMoments.lean).
Their constants are `18δ`, `3`, `1/3`, `4 max(2(log 4)^(k−2), (k/e)^k)`, and `4`, exactly as in the article.

## Uniform equivalences

For a probability family `F` with fixed reference `μ`, [`Hellinger.UniformHellingerBound`](../Hellinger/Uniform.lean) means

```lean
∃ C : ℝ≥0, ∀ ν ∈ F, d ν ≤ (C : ℝ≥0∞) * Hellinger.hellingerSq μ ν
```

Thus one finite nonnegative constant precedes every family member.
It may depend on the fixed cutoff, exponents, reference measure, and family.
The statements include empty families and members equal to the reference.

| Article locator | Uniform equivalence | Lean declaration |
| --- | --- | --- |
| Section 3.1, (BN) and (NC) | `Bδ² ≤ C H²` iff `Tδ(q) ≤ M H²` for fixed `0 < δ ≤ 1` | [`Hellinger.uniform_bernsteinSq_iff_tailPower`](../Hellinger/UniformBernstein.lean) |
| Section 3.2, (KD) and (L1) | `K ≤ C H²` iff `A₁(q) ≤ M H²` | [`Hellinger.uniform_kl_iff_tailLogMoment`](../Hellinger/UniformKL.lean) |
| Section 3.2, (KV) and (Lk) | `Vₖ ≤ C H²` iff `Aₖ(q) ≤ M H²` for fixed real `k ≥ 2` | [`Hellinger.uniform_logMoment_iff_tailLogMoment`](../Hellinger/UniformVariation.lean) |

## Comparison

Here `NCδ` denotes uniform Hellinger control of `Tδ(q)`.
`WSδ` uses the native tail threshold `exp(1/δ)`.
`CM` is the infimum of `a E₀[R | R ≥ (1 + 1/(2a))²]` over real `a ≥ 1`, with conditional mean zero on a null event.
`FM` denotes finiteness of `E₀R`; uniform FM and uniform CM require one finite bound before every family member.
Pointwise UB is defined for specified total ratio representatives.
Its implication to CM is proved through an explicit almost-everywhere agreement with the density ratio; pointwise and essential bounds are not identified by definition.

| Article locator | Result | Lean declaration |
| --- | --- | --- |
| Section 4.1 | `Tδ(q) ≤ Tδ'(q)` for `0 < δ ≤ δ'` | [`Hellinger.Comparison.tailPower_mono_exponent`](../Hellinger/Comparison/PowerTail.lean) |
| Proposition 3 | `Tδ(q) ≤ J(q)(H²)^(1−δ/δ') Tδ'(q)^(δ/δ')`, including equal exponents | [`Hellinger.Comparison.tailPower_interpolation`](../Hellinger/Comparison/PowerTail.lean) |
| Section 4.1 | Uniform power-tail control transfers from a larger exponent to a smaller positive exponent | [`Hellinger.Comparison.uniform_tailPower_of_larger_exponent`](../Hellinger/Comparison/PowerTail.lean) |
| Example 1 | Uniform density versus density `2x` on `(0,1)`: half-power control holds and exponent-one control fails | [`Hellinger.Comparison.Examples.Power.power_density_separation`](../Hellinger/Comparison/Examples/Power.lean) |
| Section 4, (WS) and (NC) | Uniform WS and ordinary-cutoff power-tail control are equivalent | [`Hellinger.uniform_ws_iff_tailPower`](../Hellinger/Comparison/Cutoff.lean) |
| Proposition 4 | The explicit WS log-tail bound for every real `k > 0`, including multiplier zero | [`Hellinger.Comparison.tailLogMoment_le_of_ws`](../Hellinger/Comparison/WS.lean) |
| Section 4.2 | WS gives KL and real-order log-moment Hellinger bounds | [`Hellinger.Comparison.kl_and_logMoment_le_of_ws`](../Hellinger/Comparison/WS.lean) |
| Proposition 5(i) | A CM bound gives exponent-one NC; cutoff four retains coefficient `(2M + 1)²` | [`Hellinger.Comparison.tailPower_one_le_of_conditionalMoment_le`](../Hellinger/Comparison/ConditionalMoment.lean) |
| Proposition 5(ii) | Finite exponent-one tail gives finite CM for a fixed pair | [`Hellinger.Comparison.conditionalMoment_lt_top_of_tailPower_one_lt_top`](../Hellinger/Comparison/FiniteMoment.lean) |
| Example 2 | A probability family has one NC₁ multiplier and no uniform CM bound; the printed global NC coefficient is retained | [`Hellinger.Comparison.Examples.CMSeparation.cm_family_separation`](../Hellinger/Comparison/Examples/CMSeparation.lean) |
| Proposition 6 | One pointwise ratio bound for the family gives one CM bound | [`Hellinger.Comparison.uniform_conditionalMoment_of_uniform_ratio_representative_bound`](../Hellinger/Comparison/Boundedness.lean) |
| Example 3 | A nonzero Normal location shift has no finite ratio bound, even almost everywhere | [`Hellinger.Comparison.Examples.Normal.normal_location_fails_ub`](../Hellinger/Comparison/Examples/Normal.lean) |
| Example 3 | Every bounded Normal parameter set has one finite CM bound, including the zero parameter | [`Hellinger.Comparison.Examples.Normal.uniform_conditionalMoment_normalFamily`](../Hellinger/Comparison/Examples/NormalControl.lean) |
| Proposition 7 | Uniform NC₁ gives a uniform full first ratio moment | [`Hellinger.Comparison.uniform_fullRatioMoment_of_uniform_tailPower_one`](../Hellinger/Comparison/FiniteMoment.lean) |
| Proof of Proposition 7 | `E₀R ≤ T₁(q) + √q(√q + 1)√(H²) + 1`; at four the coefficient is `6` | [`Hellinger.Comparison.fullRatioMoment_le_tailPower_add_sqrt_hellinger`](../Hellinger/Comparison/RefinedMoment.lean) |
| Example 4 | Half-power NC and Bernstein control can hold while the full moment is infinite | [`Hellinger.Comparison.Examples.Power.fractional_nc_without_full_moment`](../Hellinger/Comparison/Examples/PowerConsequences.lean) |
| Example 5 | One full-moment bound `2` for the two-piece family does not give uniform fractional NC | [`Hellinger.Comparison.Examples.FMSeparation.fm_family_separation`](../Hellinger/Comparison/Examples/FMSeparation.lean) |
| Section 4 comparison diagram | Typed forward implications for families, with separate fixed-pair equivalences and strict separations | [`Hellinger.Comparison.Summary.forward_implications`](../Hellinger/Comparison/Summary.lean) |

The complete WS coefficient is `δ^(−k)[J(q) + J(e) log(max(exp(k), M))^k]`, where `J(e) = e/(√e − 1)²`.
At cutoff four, the first term in brackets is exactly `4`.
For `CM ≤ M`, the general-cutoff CM bound is `T₁(q) ≤ [(2M + 1)² + 4J(q)] H²`; the separate cutoff-four theorem retains the sharper coefficient `(2M + 1)²`.
The CM and WS cutoff-four specializations are `Hellinger.Comparison.tailPower_four_le_of_conditionalMoment_le` and `Hellinger.Comparison.tailLogMoment_four_le_of_ws` in their respective modules.

For a fixed pair, exponent-one NC, finite CM, and finite FM are equivalent; see `Hellinger.Comparison.Summary.pairwise_nc_one_iff_fm` and `pairwise_cm_iff_fm` in [Summary.lean](../Hellinger/Comparison/Summary.lean).
The family counterexamples concern a constant shared by all members.
The forward implication theorem distinguishes a uniform full-moment bound from memberwise finiteness, while `Hellinger.Comparison.Summary.strict_separations` collects the four separation examples.
The FM family fails uniform tail control for every fixed positive exponent; its Bernstein consequence applies on `0 < δ ≤ 1`.

For the Normal model, [NormalConditional.lean](../Hellinger/Comparison/Examples/NormalConditional.lean) proves the article's CM upper bound by the conditional mean at threshold `e`, and [NormalRare.lean](../Hellinger/Comparison/Examples/NormalRare.lean) proves its corrected limit.
[NormalControl.lean](../Hellinger/Comparison/Examples/NormalControl.lean) uses the admissible choice `a = 1`, at threshold `9/4`, to obtain a finite bound on every bounded parameter set.
The corresponding upper envelope tends to `9/4`; this statement concerns that candidate envelope, without asserting a limit for the optimized CM infimum.

## Theorem 8

Theorem 8 concerns the sieve maximum likelihood estimator; the setting, conditions and proof are described in the [Theorem 8 note](Theorem8.md), and the precise statement is in the [mathematical notes](../NOTES.md#2-theorem-8-as-proved).
The rate theorems also have forms taking the maximal inequality `Hellinger.MLE.External.VdW_2_14_18_prime` as a hypothesis; the table lists the unconditional forms. `Hellinger.MLE.theorem8_via_weakLaw` is corrected Theorem 8 derived through `theorem8_of_weakLaw`.

| Article locator | Result | Lean declaration |
| --- | --- | --- |
| Theorem 8 | `h(p₀, p̂_n) = O_P^*(max(δ_n, n^(−1/2)))` under the annular entropy-tail condition (D) | [`Hellinger.MLE.theorem8_unconditional`](../Hellinger/MLE/Theorem8Unconditional.lean) |
| Theorem 8 | The same rate under the power envelope (H); (H) implies (D) | [`Hellinger.MLE.theorem8_of_powerEnvelope_unconditional`](../Hellinger/MLE/Theorem8Unconditional.lean) |
| Theorem 8 | The same rate under the whole-sieve bound (G); (G) implies (H) | [`Hellinger.MLE.theorem8_of_wholeSieve_unconditional`](../Hellinger/MLE/Theorem8Unconditional.lean) |
| Proof of Theorem 8 | van der Vaart and Wellner (2023), Theorem 2.14.18', with `K₀ = 80` | [`Hellinger.MLE.External.vdw_2_14_18_prime`](../Hellinger/VdW/Main.lean) |
| Discussion of Theorem 8 | The rate under the weak-law truncation condition, in place of the squared log tail | [`Hellinger.MLE.theorem8_weakLaw_unconditional`](../Hellinger/MLE/Theorem8WeakLaw.lean) |
| Discussion of Theorem 8 | The rate under the first-moment log tail | [`Hellinger.MLE.theorem8_firstMoment_unconditional`](../Hellinger/MLE/Theorem8WeakLaw.lean) |
| Theorem 8 | Theorem 8 follows from the weak-law version | [`Hellinger.MLE.theorem8_of_weakLaw`](../Hellinger/MLE/Theorem8WeakLaw.lean) |
| Theorem 8 | The hypotheses are jointly satisfiable, with a nonempty annulus | [`Hellinger.MLE.nonvacuous_nondegenerate`](../Hellinger/MLE/WitnessNondegenerate.lean) |

The hypotheses are bundled as `Hellinger.MLE.MLEHypotheses` ([Statements.lean](../Hellinger/MLE/Statements.lean)) and `Hellinger.MLE.MLEBaseHypotheses` with `Hellinger.MLE.WeakLawTruncation` ([WeakLawStatements.lean](../Hellinger/MLE/WeakLawStatements.lean)); each theorem's type is a named statement such as `Hellinger.MLE.Theorem8Statement`.
The ordinary `O_P` forms for a measurable error are `theorem8_measurable_unconditional` and `theorem8_weakLaw_measurable_unconditional`.

## Sharpened constants

These bounds use the constants the article's proofs give before rounding; see the [constants note](SharpConstants.md).
Each sharpened coefficient is at least as good as the article's, and the corresponding `*_of_sharp` theorem in [Main.lean](../Hellinger/Sharp/Main.lean) re-derives the article's bound from it.

| Article locator | Sharpened statement | Lean declaration |
| --- | --- | --- |
| Theorem 2(i) | `K ≤ J(q)(log q − 1 + 1/q) H² + A₁(q)` | [`Hellinger.Sharp.kl_le_hellinger_add_tailLogMoment_sharp`](../Hellinger/Sharp/KL.lean) |
| Theorem 1(i) | `K ≤ J(q)(log q − 1 + 1/q) H² + (eδ)⁻¹ Tδ(q)` | [`Hellinger.Sharp.kl_le_hellinger_add_tailPower_sharp`](../Hellinger/Sharp/KL.lean) |
| Theorem 2(i) | `(1 − (1 − 1/q)/log q) A₁(q) ≤ K` | [`Hellinger.Sharp.klTailLowerSharpCoeff_mul_tailLogMoment_le_kl`](../Hellinger/Sharp/KL.lean) |
| Theorem 1 | `2(1 − q^(−δ)(1 + δ log q)) Tδ(q) ≤ Bδ²` for every `δ > 0` | [`Hellinger.Sharp.bernsteinLowerSharpCoeff_mul_tailPower_le_bernsteinSq`](../Hellinger/Sharp/Bernstein.lean) |
| Theorem 1 | `Bδ² ≤ 2δ²(1 + √q)² H² + 2Tδ(q)` for `0 < δ ≤ 1` | [`Hellinger.Sharp.bernsteinSq_le_hellinger_add_tailPower_sq`](../Hellinger/Sharp/Bernstein.lean) |
| Theorem 2(ii) | `Vₖ ≤ max(J(q)(log q)^k, B_k) H² + Aₖ(q)` for real `k ≥ 2` | [`Hellinger.Sharp.logMoment_le_hellinger_add_tailLogMoment_sharp`](../Hellinger/Sharp/Variation.lean) |
| Theorem 2(iii), Proposition 3 | Interpolation with `J(q)^(1−k/k')` in place of `J(q)` | [`Hellinger.Sharp.tailLogMoment_interpolation_sharp`](../Hellinger/Sharp/Variation.lean) |
| Proposition 5(i) | `CM ≤ M` gives `T₁(q) ≤ 4M² H²` for every `q ≥ 9/4` | [`Hellinger.Sharp.tailPower_le_of_conditionalMoment_le_sharp`](../Hellinger/Sharp/Bernstein.lean) |
| Theorems 1–2, Proposition 5 | Each sharpened coefficient is at least as good as the article's | [`Hellinger.Sharp.sharpCoeffs_improve`](../Hellinger/Sharp/Main.lean) |

Here `B_k = sup_{0<r<1} r|log r|^k/(√r − 1)²`; for `k = 2` the variation coefficient is `J(q)(log q)²`, which is `16(log 2)² ≈ 7.69` at cutoff four.
