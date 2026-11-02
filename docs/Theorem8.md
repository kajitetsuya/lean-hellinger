# Theorem 8: sieve maximum likelihood

This note describes the formalization of the sieve maximum likelihood theorem, Theorem 8 of [Kaji (2026)](https://doi.org/10.1007/s42973-026-00243-x).
It covers the corrected statement, its sufficient conditions, the maximal inequality it uses, and a strengthening under a weak-law truncation condition.
The modules are [Hellinger/MLE](../Hellinger/MLE) and [Hellinger/VdW](../Hellinger/VdW); the [result map](Results.md#theorem-8) lists the declarations.

## Setting

All definitions are in [Defs.lean](../Hellinger/MLE/Defs.lean).

- **Densities.** One arbitrary reference measure `μ` on the sample space `𝒳`; no σ-finiteness is assumed. Densities are measurable functions `𝒳 → ℝ≥0` of mass one (`IsProbDensity`), and `P₀ = p₀ · μ`. Pointwise representatives are kept, so brackets, likelihoods and empirical suprema evaluate them pointwise.
- **Hellinger distance.** `h(f, g) = (∫ (√f − √g)² dμ)^{1/2}`, with the paper's normalization and no factor `1/2`.
- **Brackets and entropy.** Brackets have measurable endpoints and are ordered pointwise. The nonstandardized bracketing integral is `J̃_[](δ, F, d) = ∫₀^δ √(1 + log N_[](ε, F, d)) dε` in `[0, ∞]`; it is `∞` when some bracketing number is infinite.
- **The Bernstein "norm".** `‖f‖²_{P,B} = 2 P(e^{|f|} − 1 − |f|)` is the squared Bernstein "norm". It is neither homogeneous nor subadditive.
- **Sample and estimator.** `X₁, X₂, …` are i.i.d. with law `P₀` on an arbitrary probability space. The sieve `𝒫_n` consists of probability densities; `p_n ∈ 𝒫_n` is deterministic. The estimator `p̂_n ∈ 𝒫_n` may be any, possibly nonmeasurable, map on the underlying probability space, in particular any function of the sample.
- **Rates.** `a_n = max(δ_n, n^{−1/2})`. `Z_n = O_P^*(b_n)` means that for every `ε > 0` there are `K > 0` and `N` with outer probability of `{Z_n > K b_n}` at most `ε` for `n ≥ N`. Outer probability is the outer measure, and outer expectation is the infimum of integrals of measurable majorants.

The hypotheses of the paper are collected in `Hellinger.MLE.MLEHypotheses` ([Statements.lean](../Hellinger/MLE/Statements.lean)):

1. `h(p₀, p_n) ≤ D δ_n` eventually;
2. `P₀[(log(p₀/p_n))² 1{p₀/p_n > 4}] ≤ M δ_n²` eventually, with value `∞` when `P₀` is not absolutely continuous with respect to `p_n · μ`;
3. `ℙ_n log p̂_n ≥ ℙ_n log p_n − O_P(δ_n²)`, stated as `O_P^*(δ_n²)` control of the deficit `(ℙ_n log p_n − ℙ_n log p̂_n)₊`, with `log 0 = −∞`.

The conclusion is `h(p₀, p̂_n) = O_P^*(a_n)`.

## The entropy condition

The paper's entropy assumption `J̃_[](δ_n, 𝒫_{n,δ_n}, h) ≤ δ_n² √n`, at the single radius `δ_n`, does not suffice.
The proof uses concavity of `r ↦ J̃_[](r, 𝒫_{n,r}, h)`, which holds for a fixed class but not when the class grows with `r`.

**Counterexample.** Let `p₀` be uniform on `[0, 1)`, split into `2n` equal cells, and let the sieve contain `p₀` and every density equal to `3/2` on exactly `n` cells and `1/2` on the others. Take `p_n = p₀` and `δ_n = n^{−1/2}`.

- Every other sieve member is at the fixed Hellinger distance `c = (2 − √(3/2) − √(1/2))^{1/2} > 0` from `p₀`.
- For large `n` the local class at radius `δ_n` is `{p₀}`, so the entropy assumption holds; the approximation and log-tail terms vanish.
- A sample of size `n` meets at most `n` cells, so an exact maximizer puts density `3/2` at every observation and stays at distance `c` from `p₀`.

This is formalized as `Hellinger.MLE.printedTheorem8_false : ¬ PrintedTheorem8Statement` in [PrintedCounterexample.lean](../Hellinger/MLE/PrintedCounterexample.lean). `PrintedTheorem8Statement` is the article's theorem with the single-radius condition required for every `n`. Below a fixed sample size the sieve is `{p₀}`, so every hypothesis holds for every `n`. The estimator is an exact maximizer over the whole sieve (`estimator_isMLE`), and its Hellinger error is `c` on every sample point (`hdist_estimator`).

The formal theorem replaces the entropy assumption with an **annular entropy-tail condition (D)**.
With shells `s_{nj} = 2^{j/2} a_n` and annuli `A_{nj} = {p ∈ 𝒫_n : s_{nj} < h(p₀, p) ≤ √2 s_{nj}}`, let

```
K_{nj} = J̃_[](√2 s_{nj}, A_{nj}, h)   (0 for an empty annulus),
T_n(k) = Σ_{j ≥ k, s_{nj} < √2} K_{nj} / (√n s_{nj}²).
```

Condition (D) is `lim_k limsup_n T_n(k) = 0` (`AnnularTailCondition`).
Two simpler sufficient conditions are proved:

- **(H) power envelope:** `J̃_[](r, 𝒫_{n,r}, h) ≤ C √n a_n^{2−β} r^β` for `r ≥ a_n` and large `n`, with `1 ≤ β < 2`. Then (H) ⇒ (D).
- **(G) whole sieve:** `J̃_[](a_n, 𝒫_n, h) ≤ C √n a_n²` for large `n`. Then (G) ⇒ (H) with `β = 1`.

## Corrected Theorem 8

`Hellinger.MLE.theorem8_unconditional : Theorem8Statement` proves `h(p₀, p̂_n) = O_P^*(a_n)` under `MLEHypotheses` and (D).
The measurable form gives the ordinary `O_P` statement when the error is measurable; the (H) and (G) forms follow from the implications above.
`nonvacuous` and `nonvacuous_nondegenerate` exhibit models satisfying all hypotheses; the second has a nonempty annulus.

The proof is a direct shell argument with `m_p = log((p₀ + p)/(2p₀))`:

- **Curvature.** `P₀ m_p ≤ −h(p₀, p)²/16` ([Mixture.lean](../Hellinger/MLE/Mixture.lean)).
- **Bracket transfer.** `‖m_u − m_l‖_{P₀,B} ≤ √6 h(l, u)`, hence `J̃_[](3r, m(F), B) ≤ 3 J̃_[](r, F, h)` ([EntropyTransfer.lean](../Hellinger/MLE/EntropyTransfer.lean)).
- **Comparator.** `ℙ_n m_{p̂_n} ≥ −Z_n` almost surely, with `Z_n = O_P^*(a_n²)` built from the deficit and the log-likelihood ratio of `p_n` ([Comparator.lean](../Hellinger/MLE/Comparator.lean)).
- **Shells.** For each shell, the maximal inequality below bounds the empirical process over the annulus. Summing gives, for every `k` and large `n`,

```
P^*{h(p₀, p̂_n) > 2^{k/2} a_n} ≤ P^*{Z_n > 2^k a_n²/32} + 96 K₀ (T_n(k) + T_n(k)²)
```

(`tail_le_shell_bound` in [Theorem8.lean](../Hellinger/MLE/Theorem8.lean)).
Condition (D) makes the last term small for a fixed large `k`.

The constants are proof devices; any positive constants serve the argument.

## The maximal inequality

The shell bound uses van der Vaart and Wellner (2023), *Weak Convergence and Empirical Processes*, 2nd ed., Theorem 2.14.18': there is a universal `K₀` such that, for every probability space `(𝒳, P)`, `n ≥ 1`, `δ > 0` and class `F` of measurable functions with `‖f‖_{P,B} ≤ δ`,

```
E^* sup_{f ∈ F} |𝔾_n f| ≤ K₀ J (1 + J/(δ² √n)),   J = J̃_[](δ, F, ‖·‖_{P,B}).
```

The statement is the `Prop` `Hellinger.MLE.External.VdW_2_14_18_prime` ([External.lean](../Hellinger/MLE/External.lean)), stated on the canonical product space.
It is proved, with `K₀ = 80`, as `Hellinger.MLE.External.vdw_2_14_18_prime` ([VdW/Main.lean](../Hellinger/VdW/Main.lean)).
Theorems stated with this `Prop` as a hypothesis (`theorem8`, `theorem8_weakLaw`, …) record which results use it; each has an unconditional form.

The proof follows the outline of van der Vaart and Wellner, with four changes:

- **Chain.** A finite chain to a level `Q` with `2^Q ≥ 2n` is used, with a deterministic remainder.
- **Brackets.** Cells are intersections of brackets at successive levels.
- **Maximal inequality.** A single moment-generating-function (log-sum-exp) inequality, `E max ≤ 2σ √L(m) + 2 (K/√n) L(m)` with `L(m) = 1 + log m`, replaces Bernstein's inequality and the Orlicz-norm maximal lemma ([MgfMaximal.lean](../Hellinger/VdW/MgfMaximal.lean)).
- **Entropy sums.** The dyadic radii start at `δ`, and the entropy sums are compared with the bracketing integral ([EntropySums.lean](../Hellinger/VdW/EntropySums.lean)).

The final assembly gives `77 J + 4 J²/(δ² √n) ≤ 80 J (1 + J/(δ² √n))`.

## A weak-law strengthening

A footnote in the discussion following Theorem 8 notes that the squared log-tail assumption (hypothesis 2) can be relaxed through a weak law of large numbers for arrays.
The formalization proves the relaxation in the following form, with no law-of-large-numbers input beyond Chebyshev and Markov.

Let `T_n` be the log tail `log(p₀/p_n) 1{p₀ > 4 p_n}`, extended by `∞` on the singular set `{p₀ > 0 = p_n}` (`extTail`).
The **weak-law truncation condition (W)** asks for thresholds `L_n ∈ [0, ∞]` and a finite `M` with

```
n P₀(T_n > L_n) → 0,      P₀[T_n 1{T_n ≤ L_n}] ≤ M a_n²   eventually
```

(`WeakLawTruncation`, [WeakLawStatements.lean](../Hellinger/MLE/WeakLawStatements.lean)).
No absolute continuity is assumed.

- **Main theorem.** `Hellinger.MLE.theorem8_weakLaw_unconditional` proves `h(p₀, p̂_n) = O_P^*(a_n)` under hypotheses 1 and 3, (W) and (D) (`MLEBaseHypotheses`). The measurable, (H) and (G) forms are proved as well.
- **First moment.** The case `L_n = ∞` is the first-moment condition `P₀[log(p₀/p_n) 1{p₀/p_n > 4}] ≤ M a_n²` (`theorem8_firstMoment_unconditional`, `firstMoment_implies_weakLaw`).
- **The paper's version.** Hypothesis 2 implies the first-moment condition by interpolation (`squaredTail_implies_firstMoment`). Hence `theorem8_of_weakLaw` derives `Theorem8Statement` from the strengthened theorem, and `theorem8_via_weakLaw` is corrected Theorem 8 obtained this way.
- **Strictly weaker hypothesis** (not formalized). Take `μ` Lebesgue measure on `[0, 1]`, `p₀ = 1`, `δ_n = n^{−1/2}`, and let `p_n = e^{−n³}` on a set of measure `n^{−2}`, renormalized elsewhere. Then (W) holds with `L_n = n²`, while the first moment is of order `n` and diverges.

The proof splits `log(p₀/p_n)` into a central part on `{p₀ ≤ 4 p_n}`, controlled by Chebyshev with `P₀ C_n² ≤ 8 h²` and `P₀ C_n ≤ 3 h²`, and the truncated tail, controlled by a union bound for `{∃ i < n : T_n(X_i) > L_n}` and Markov's inequality for the truncated mean.
The finite-`n` bound acquires one extra term, the probability of that exceptional event ([WeakLawShell.lean](../Hellinger/MLE/WeakLawShell.lean), [WeakLawComparator.lean](../Hellinger/MLE/WeakLawComparator.lean)).
`nonvacuous_weakLaw` exhibits a model satisfying all the hypotheses.

## Remark: a critical-radius condition

This remark is not formalized.
With `J_n(r) = J̃_[](r, 𝒫_{n,r}, h)`, a sharper likelihood-concentration argument, using Wong and Shen (1995, *Annals of Statistics* 23, Theorem 1), allows the condition

```
(C)   J_n(r) ≤ η √n r²   for all r ≥ A a_n and all large n,
```

where `η > 0` lies below a small universal threshold.
Unlike (H), condition (C) lets the normalized entropy `J_n(r)/(√n r²)` stay at a small positive constant across scales.
