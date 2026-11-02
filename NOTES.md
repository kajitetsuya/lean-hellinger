# Mathematical notes

These notes describe the relation between the formal statements and the [published version of record](https://doi.org/10.1007/s42973-026-00243-x), published on 27 February 2026.
Section 1 distinguishes corrections from endpoint clarifications. Section 2 states Theorem 8 as proved, Section 3 lists the extensions beyond the article, and Section 4 lists the auxiliary results that are proved in the package rather than assumed.

## 1. Corrections and clarifications

1. **Finite Kullback–Leibler divergence for centering (domain clarification; Theorem 1(ii)).** The centered Kullback–Leibler variation requires a finite real mean, so this clause assumes `FiniteKL μ ν`. The uncentered variation can be infinite. No finiteness hypothesis on the Kullback–Leibler divergence is added to the other bounds. See `Hellinger.two_neg_rpow_mul_centeredLogMoment_le_logMoment` in [Centering.lean](Hellinger/Centering.lean).

2. **Fractional-power proof sign (correction; proof of Theorem 1).** For `1/4 ≤ x < 1`, the displayed rearrangement should read `δ ≤ log(1 − √x) / log(√x)`, with `≤` in place of `≥`. This is consistent with `0 < δ ≤ 1` and the right-hand side being at least one. The formal Bernstein estimate is proved in `Hellinger.bernstein_density_regular_upper` in [BernsteinScalar.lean](Hellinger/BernsteinScalar.lean).

3. **The WS coefficient at zero (endpoint clarification; Proposition 4).** Write `log(max(exp(k), M))` in place of `max(k, log(M))`. The expressions agree for `M > 0`; the former also has the defined value `k` at `M = 0`. The log-tail estimate retains every real order `k > 0`. See `Hellinger.Comparison.wsLogScale_eq_max` and `Hellinger.Comparison.wsLogScale_zero` in [WSScalar.lean](Hellinger/Comparison/WSScalar.lean), and `Hellinger.Comparison.tailLogMoment_four_le_of_ws` in [WS.lean](Hellinger/Comparison/WS.lean).

4. **The Normal conditional-mean limit (correction and endpoint clarification; Example 3).** The displayed CDF quotient for threshold `e` tends to `e`, rather than the printed value `1`, as `θ → 0` through nonzero values. At `θ = 0`, the actual conditional mean is zero because its conditioning event is null. These are distinct statements. The displayed CM upper bound and one finite CM bound on each bounded parameter set are formalized. See `Hellinger.Comparison.Examples.Normal.normal_exp_one_cdf_limit` in [NormalRare.lean](Hellinger/Comparison/Examples/NormalRare.lean), `Hellinger.Comparison.Examples.Normal.conditionalRatioMean_zero` in [Normal.lean](Hellinger/Comparison/Examples/Normal.lean), and `Hellinger.Comparison.Examples.Normal.uniform_conditionalMoment_normalFamily` in [NormalControl.lean](Hellinger/Comparison/Examples/NormalControl.lean).

5. **The two-piece FM model (correction and endpoint clarification; Example 5).** Its squared Hellinger distance is `θ(1 − √θ)² + (1 − θ)(1 − √(1 + θ))²`: the second weight is the interval length `1 − θ`. The full-moment identity `1 + (1 − θ)/(1 + θ)` holds for positive `θ` and has limit `2` at zero; the actual full moment at `θ = 0` is `1`. The uniform upper bound `2` and the family separation remain valid. See `Hellinger.Comparison.Examples.FMSeparation.hellingerSq_eq`, `fullRatioMoment_eq_of_pos`, and `fullRatioMoment_zero` in [FMSeparation.lean](Hellinger/Comparison/Examples/FMSeparation.lean).

6. **The entropy condition of Theorem 8 (correction; Section 5).** The single-radius condition `J̃_[](δ_n, 𝒫_{n,δ_n}, h) ≤ δ_n² √n` does not suffice. The proof applies concavity to `r ↦ J̃_[](r, 𝒫_{n,r}, h)`, but the class grows with `r`. A two-level sieve on `2n` cells of `[0, 1)` satisfies every hypothesis of the article's theorem while an exact maximizer stays at a fixed positive distance from `p₀`. `Hellinger.MLE.printedTheorem8_false` proves that the printed statement is false ([PrintedCounterexample.lean](Hellinger/MLE/PrintedCounterexample.lean)); see [the Theorem 8 note](docs/Theorem8.md#the-entropy-condition). The formal theorem replaces the condition with the annular entropy-tail condition (D) below; the simpler conditions (H) and (G) imply (D).

## 2. Theorem 8 as proved

The following statement is that of `Hellinger.MLE.theorem8_unconditional` and, for Theorem 8′, `Hellinger.MLE.theorem8_weakLaw_unconditional` and `Hellinger.MLE.theorem8_firstMoment_unconditional`. Its text uses only standard LaTeX with `amsmath` and `amssymb`, so it can be pasted into a TeX document.

Setting. Let $(\mathcal X,\mathcal A)$ be a measurable space and $\mu$ an arbitrary measure on it; no $\sigma$-finiteness is assumed. A density is a measurable function $p\colon\mathcal X\to[0,\infty)$ with $\int p\ d\mu=1$. Let $p_0$ be a density, let $P_0=p_0\mu$, and let $X_1,X_2,\dots$ be independent random variables with law $P_0$ on a probability space $(\Omega,\mathcal F,\Pr)$. Let $\mathbb P_n$ be the empirical measure of $X_1,\dots,X_n$, and for each $n$ let $\mathcal P_n$ be a set of densities. The Hellinger distance is $h(p,q)=\bigl(\int(\sqrt{p}-\sqrt{q})^2 d\mu\bigr)^{1/2}$. A bracket $[l,u]$ consists of measurable functions $0\le l\le u$ with $\int l\ d\mu < \infty$ and $\int u\ d\mu < \infty$. For a set $\mathcal G$ of densities, $N_{[]}(\varepsilon,\mathcal G,h)$ is the least number of brackets with $h(l,u) < \varepsilon$ that cover $\mathcal G$ pointwise, or $+\infty$ if there is no finite cover; it is $0$ for the empty set, in which case the integrand below is $1$. Let

$$
\tilde J_{[]}(\delta,\mathcal G,h)=\int_0^{\delta}\sqrt{1+\log N_{[]}(\varepsilon,\mathcal G,h)}\ d\varepsilon\in[0,\infty].
$$

Given $\delta_n\ge 0$, write $a_n=\max(\delta_n,n^{-1/2})$. Probabilities of possibly nonmeasurable events are outer probabilities $\Pr^{\ast}$, and $Z_n=O_{\Pr}^{\ast}(b_n)$ means that for every $\varepsilon>0$ there are $K>0$ and $N$ with $\Pr^{\ast}(Z_n>Kb_n)\le\varepsilon$ for all $n\ge N$.

Condition (D). For $j\ge 0$ let $s_{nj}=2^{j/2}a_n$, let $A_{nj}$ be the set of $p\in\mathcal P_n$ with $s_{nj} < h(p_0,p)\le\sqrt{2}s_{nj}$, let $K_{nj}=\tilde J_{[]}(\sqrt{2}s_{nj},A_{nj},h)$ if $A_{nj}$ is nonempty and $K_{nj}=0$ otherwise, and let

$$
T_n(k)=\sum_{j\ge k,\ s_{nj}<\sqrt{2}}\frac{K_{nj}}{\sqrt{n}\ s_{nj}^2}.
$$

Condition (D) holds if for every $\varepsilon>0$ there are $k$ and $N$ with $T_n(k)\le\varepsilon$ for all $n\ge N$.

Theorem 8. Suppose that there are $\delta_n\ge 0$, $p_n\in\mathcal P_n$ and constants $D,M\in[0,\infty)$ such that, for all sufficiently large $n$,

$$
h(p_0,p_n)\le D\delta_n
\quad\text{and}\quad
P_0\Bigl[\Bigl(\log\frac{p_0}{p_n}\Bigr)^{2}\mathbf{1}\bigl\lbrace p_0>4p_n\bigr\rbrace\Bigr]\le M\delta_n^2,
$$

where the second left side is $+\infty$ unless $P_0\ll p_n\mu$, and that condition (D) holds. Let $\hat p_n\in\mathcal P_n$ be any map on $\Omega$, not necessarily measurable (for instance, any function of $X_1,\dots,X_n$), such that

$$
\bigl(\mathbb P_n\log p_n-\mathbb P_n\log\hat p_n\bigr)_+=O_{\Pr}^{\ast}(\delta_n^2),
$$

where $\log 0=-\infty$, the difference is $0$ if $\prod_{i=1}^n p_n(X_i)=0$, and it is $+\infty$ if $\prod_{i=1}^n\hat p_n(X_i)=0 < \prod_{i=1}^n p_n(X_i)$. Then $h(p_0,\hat p_n)=O_{\Pr}^{\ast}(a_n)$.

Condition (D) holds in particular under either of the following conditions, where $\mathcal P_{n,r}$ is the set of $p\in\mathcal P_n$ with $h(p_0,p)\le r$. (H) There are $C>0$ and $\beta\in[1,2)$ such that $\tilde J_{[]}(r,\mathcal P_{n,r},h)\le C\sqrt{n}a_n^{2-\beta}r^{\beta}$ for all large $n$ and all $r\ge a_n$. (G) There is $C>0$ such that $\tilde J_{[]}(a_n,\mathcal P_n,h)\le C\sqrt{n}a_n^2$ for all large $n$.

Theorem $8'$. The conclusion of Theorem 8 remains true when the condition on $(\log(p_0/p_n))^2$ is replaced by the following. Let $T_n=+\infty$ where $p_0>0=p_n$, let $T_n=\log(p_0/p_n)$ where $p_0>4p_n>0$, and let $T_n=0$ elsewhere. There are $L_n\in[0,\infty]$ and $M < \infty$ such that

$$
nP_0(T_n>L_n)\to 0
\quad\text{and}\quad
P_0\bigl[T_n\mathbf{1}\bigl\lbrace T_n\le L_n\bigr\rbrace\bigr]\le Ma_n^2\ \text{for all large } n.
$$

With $L_n=+\infty$, it suffices that $P_0\bigl[\log(p_0/p_n)\mathbf{1}\bigl\lbrace p_0>4p_n\bigr\rbrace\bigr]\le Ma_n^2$ for all large $n$, where the left side is $+\infty$ unless $P_0\ll p_n\mu$. The condition of Theorem 8 implies this first-moment condition, so Theorem 8 is a corollary of Theorem $8'$.

In Lean, the hypotheses are `Hellinger.MLE.MLEHypotheses` and `Hellinger.MLE.AnnularTailCondition`, and the conclusion is `Hellinger.MLE.RateConclusion` ([Statements.lean](Hellinger/MLE/Statements.lean), [Defs.lean](Hellinger/MLE/Defs.lean)). For a measurable error the conclusion is the ordinary `O_P` statement (`theorem8_measurable_unconditional`), and the weak-law condition is `Hellinger.MLE.WeakLawTruncation` ([WeakLawStatements.lean](Hellinger/MLE/WeakLawStatements.lean)). The weak-law condition is strictly weaker than the first-moment condition, by an example that is not formalized; see [the Theorem 8 note](docs/Theorem8.md#a-weak-law-strengthening).

## 3. Extensions beyond the article

- **Arbitrary cutoff.** Every bound of Theorems 1 and 2 and Section 4 holds for a fixed real cutoff `q > 1`; the cutoff-four statements are corollaries.
- **Theorem 8′.** The footnote in the discussion of Theorem 8 suggests relaxing the squared log-tail condition through a weak law of large numbers for arrays. Theorem 8′ above carries this out with Chebyshev's and Markov's inequalities and a union bound; no further law of large numbers is needed.
- **Sharpened constants.** [Hellinger/Sharp](Hellinger/Sharp) proves the bounds of Theorems 1 and 2 and Proposition 5 with the constants their proofs give before rounding, and re-derives the article's statements from them. For example, the coefficient `3` of the Kullback–Leibler divergence bound becomes `4 log 4 − 3 ≈ 2.545`, and the interpolation factor `4√M` becomes `2√M`. See [the constants note](docs/SharpConstants.md).
- **Lower bound on the Bernstein "norm".** The lower bound of Theorem 1 on the Bernstein "norm" holds for every `δ > 0`, not only `0 < δ ≤ 1`, with the sharpened coefficient `2(1 − q^(−δ)(1 + δ log q))`.

## 4. Auxiliary results proved in the package

The formalization assumes nothing beyond mathlib and the foundational axioms `propext`, `Classical.choice` and `Quot.sound`.
In particular, every outside result used in the proofs is proved in the package:

- **van der Vaart and Wellner (2023), Theorem 2.14.18'.** This is the bracketing maximal inequality for the Bernstein "norm": for every class `F` of measurable functions with `‖f‖_{P,B} ≤ δ`, `E* ‖𝔾_n‖_F ≤ K₀ J (1 + J/(δ²√n))` with `J = J̃_[](δ, F, ‖·‖_{P,B})`. It is stated as the `Prop` `Hellinger.MLE.External.VdW_2_14_18_prime` on the canonical product space ([External.lean](Hellinger/MLE/External.lean)) and proved with `K₀ = 80` as `Hellinger.MLE.External.vdw_2_14_18_prime` ([VdW/Main.lean](Hellinger/VdW/Main.lean)). Its transfer to an arbitrary probability space carrying the sample is `Hellinger.MLE.outerLIntegral_sample_le` ([ProbabilityRates.lean](Hellinger/MLE/ProbabilityRates.lean)).
- **Bernstein's inequality and the finite maximal inequality.** van der Vaart and Wellner derive the theorem from Bernstein's inequality (Lemma 2.2.10) and the Orlicz-norm maximal inequality (Lemma 2.2.13). The package replaces both with a direct moment-generating-function argument ([MgfMaximal.lean](Hellinger/VdW/MgfMaximal.lean)):
  - **Bernstein moment bound.** If `‖g‖²_{P,B} ≤ σ²` and `0 ≤ λ ≤ 1`, then `E exp(λ(g − Pg)) ≤ exp(λ²σ²/2)` (`Hellinger.VdW.mgf_le_of_bernstein`). For `|g| ≤ K`, `P g² ≤ σ²` and `0 ≤ λ ≤ 1/K`, `E exp(λ(g − Pg)) ≤ exp(λ²σ²)` (`mgf_le_of_bounded`). These are the moment-generating-function bounds from which Bernstein's inequality is usually derived.
  - **Maximal inequality for finitely many functions.** `E max_{i ≤ m} |𝔾_n g_i| ≤ 2σ√(1 + log m) + 2(K/√n)(1 + log m)`, in the Bernstein "norm" and bounded forms (`lintegral_iSup_empiricalProcess_le_of_bernstein`, `lintegral_iSup_empiricalProcess_le_of_bounded`). This is the bound that Bernstein's inequality and Lemma 2.2.13 give together, up to constants. The tail form of Bernstein's inequality is not needed and is not stated separately.
  - **The Bernstein "norm".** `φ(λx) ≤ λ²φ(x)` for `0 ≤ λ ≤ 1`, `x ≥ 0`, with `φ(x) = eˣ − 1 − x`; `P g² ≤ ‖g‖²_{P,B}`; and integrability of functions of finite Bernstein "norm".
- **Bracketing chaining.** A finite chain with intersection brackets and a deterministic remainder ([Chaining.lean](Hellinger/VdW/Chaining.lean)), and the comparison of dyadic entropy sums with the bracketing integral ([EntropySums.lean](Hellinger/VdW/EntropySums.lean)).
- **Probability tools** ([ProbabilityRates.lean](Hellinger/MLE/ProbabilityRates.lean)): Chebyshev's inequality for i.i.d. sample means in `O_P^*` form (`opStar_sampleMean`), Markov's inequality for outer expectations, the transfer of outer probabilities to the canonical product space, and the calculus of `O_P^*`.
- **Density bridges** ([DensityBridge.lean](Hellinger/MLE/DensityBridge.lean)): the Hellinger distance of densities equals the measure-level squared Hellinger distance, and the log-likelihood ratio of two laws equals `log(p₀/p)` almost surely, for an arbitrary reference measure without σ-finiteness.
- **Likelihood geometry for Theorem 8:**
  - curvature `P₀ log((p₀ + p)/(2p₀)) ≤ −h(p₀, p)²/16` (`integral_mixLog_le`, [Mixture.lean](Hellinger/MLE/Mixture.lean));
  - the bound on the Bernstein "norm" `‖log((p₀ + p)/(2p₀))‖_{P₀,B} ≤ 3h(p₀, p)` (`bernsteinFun_mixLog_le`);
  - the bracket transfer `‖m_u − m_l‖_{P₀,B} ≤ √6 h(l, u)` with `J̃_[](3r, m(F), B) ≤ 3 J̃_[](r, F, h)` ([EntropyTransfer.lean](Hellinger/MLE/EntropyTransfer.lean)).
- **Interpolation.** The article's interpolation of log tails (Theorem 2(iii)) is itself formalized and is used to derive the first-moment condition from the squared log-tail condition.

Measure theory, product measures, independence, variance and the Kullback–Leibler divergence are taken from mathlib.

The arbitrary fixed cutoff `q > 1` is a generalization, with the exact cutoff-four bounds retained as corollaries.
Extended values and singular support are explicit; equal-exponent interpolation and empty families are included.
Uniform family claims quantify one constant before the family member, separately from fixed-pair finiteness.
Pointwise ratio bounds use specified representatives and have explicit bridges to almost-everywhere bounds.
These conventions and generalizations are detailed in the [result map](docs/Results.md).
