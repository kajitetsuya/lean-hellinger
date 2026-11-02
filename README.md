# Lean Formalization of "The Hellinger Bounds on the Kullback–Leibler Divergence and the Bernstein Norm"

This Lean package formalizes Theorems 1, 2 and 8 and the Comparison section of Kaji (2026), [*The Hellinger bounds on the Kullback–Leibler divergence and the Bernstein norm*](https://doi.org/10.1007/s42973-026-00243-x).
It characterizes when squared Hellinger distance controls Kullback–Leibler (KL) divergence, log-likelihood moments, and the squared Bernstein functional.

The single library `Hellinger` covers arbitrary probability measures on a measurable space, real exponents, unbounded likelihood ratios, and extended values including infinity.
The ordinary tail cutoff is any fixed real `q > 1`; corollaries retain the paper's exact cutoff-four constants.
Theorem 8, the rate of convergence of the sieve maximum likelihood estimator, is proved under a corrected entropy condition, together with every outside result its proof uses.

## Theorem 1: Bernstein and KL bounds

Two-sided Bernstein bounds identify the relevant power tail of the likelihood ratio.
Further results give the Hellinger lower bound for KL, its power-tail upper bound, the Gamma bound for every real moment order `k ≥ 2`, and the centered-moment comparison.
Only the centered clause requires finite KL; its uncentered moment may still be infinite.

## Theorem 2: logarithmic tails

Two-sided KL and log-moment bounds use truncated logarithmic moments.
Interpolation covers every real pair `k' ≥ k > 0`, including equal exponents and zero or infinite quantities.
All constants are explicit functions of the fixed cutoff and exponents.

## Uniform families

The package proves the three equivalences between uniform Hellinger bounds and the corresponding power or logarithmic tail bounds.
Uniform means that one finite nonnegative constant is chosen before every family member.
The cutoff stays fixed across the family, and empty families are included.

## Comparison

The comparison results cover exponent monotonicity and interpolation, the WS tail condition, conditional moments (CM), bounded likelihood ratios (UB), and full moments (FM).
Explicit probability models establish the strict separations, including the Normal location model on bounded parameter sets.
Pairwise finiteness and uniform family bounds have separate statements; pointwise UB is connected to the measure-level bounds through explicit ratio representatives.
The native WS threshold `exp(1/δ)` and CM thresholds `(1 + 1/(2a))²`, `a ≥ 1`, retain their definitions.

## Theorem 8: sieve maximum likelihood

The formal Theorem 8 gives `h(p₀, p̂_n) = O_P^*(max(δ_n, n^(−1/2)))` for an approximate sieve maximum likelihood estimator, with densities relative to an arbitrary reference measure and a possibly nonmeasurable estimator.
The article's single-radius entropy condition does not suffice; it is replaced by an annular entropy-tail condition, implied by simpler power-envelope and whole-sieve bounds.
The proof uses the Bernstein-norm bracketing maximal inequality of van der Vaart and Wellner (2023), Theorem 2.14.18', which is proved in the package with an explicit constant.
A weak-law version replaces the squared log-tail assumption by a weaker truncation condition; the article's version is a corollary.
See the [Theorem 8 note](docs/Theorem8.md), and the [mathematical notes](NOTES.md#2-theorem-8-as-proved) for the precise statement.

## Sharpened constants

The constants of Theorems 1 and 2 and Proposition 5 are rounded in the article.
The package also proves the bounds with the constants their proofs give, for example `4 log 4 − 3 ≈ 2.545` in place of `3` for the KL bound, and re-derives every article bound from its sharpened form.
Four of these coefficients are the best possible in their pointwise inequalities; see the [constants note](docs/SharpConstants.md).

See the [result map](docs/Results.md) for all 49 principal results and their declarations, and [mathematical notes](NOTES.md) for corrections, endpoint clarifications, extensions and the auxiliary results proved in the package.

## Build and use

Install [Lean through elan](https://github.com/leanprover/elan), then run these commands from the package directory:

```sh
lake exe cache get
lake build
python scripts/verify.py
```

The toolchain is Lean `4.35.0`; mathlib is pinned to commit `56a005855ea17e0b0958f73ec801ae140b0a1679` in the Lake files.
The verifier builds the public library, checks the [declaration manifest](declarations.json), and inspects the axiom dependencies of every local declaration.
The permitted foundational axioms are `propext`, `Classical.choice`, and `Quot.sound`.

Import the root module to use the library:

```lean
import Hellinger

#check Hellinger.hellingerSq_le_kl
#check Hellinger.uniform_bernsteinSq_iff_tailPower
#check Hellinger.Comparison.tailPower_interpolation
#check Hellinger.Comparison.Examples.Normal.uniform_conditionalMoment_normalFamily
#check Hellinger.MLE.theorem8_unconditional
#check Hellinger.MLE.External.vdw_2_14_18_prime
#check Hellinger.Sharp.kl_le_hellinger_add_tailLogMoment_sharp
```

The normalization is `H² = ∫ (√p₀ − √p)²`, without a factor of `1/2`, and `Bδ² = 2 E₀[exp(|δL|) − 1 − |δL|]`, where `L = log(p₀/p)`.
KL is mathlib's extended nonnegative KL divergence.
The definitions retain singular-support contributions and define a conditional mean on a null conditioning event to be zero.

## Citation and license

Tetsuya Kaji (2026), “The Hellinger bounds on the Kullback–Leibler divergence and the Bernstein norm,” *The Japanese Economic Review* **77**(2), 333–354. [Published article DOI: 10.1007/s42973-026-00243-x](https://doi.org/10.1007/s42973-026-00243-x); [arXiv DOI: 10.48550/arXiv.2601.17860](https://doi.org/10.48550/arXiv.2601.17860) ([version 1](https://arxiv.org/abs/2601.17860v1)).

Citation metadata is in [CITATION.cff](CITATION.cff) and [references.bib](references.bib).
Version `0.1.0` is released under [Apache-2.0](LICENSE).
