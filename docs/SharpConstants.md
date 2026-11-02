# Sharpened constants

The constants of Theorems 1 and 2 and Proposition 5 of [Kaji (2026)](https://doi.org/10.1007/s42973-026-00243-x) are rounded for readability.
The module [Hellinger/Sharp](../Hellinger/Sharp) proves the same bounds with the constants their proofs give before rounding.
Each coefficient is at least as good as the paper's, and every bound of the paper is re-derived from its sharpened form (`*_of_sharp` in [Main.lean](../Hellinger/Sharp/Main.lean)).
The coefficients and statements are in [Statements.lean](../Hellinger/Sharp/Statements.lean); "Sharp" in a declaration name marks this module, not a sharpness claim.

Notation follows the [result map](Results.md): `q > 1` is the fixed cutoff, `J(q) = (1 − q^(−1/2))^(−2)`, `H²` is the squared Hellinger distance, `K` the Kullback–Leibler divergence, `Vₖ` the `k`th order Kullback–Leibler variation, `Bδ²` the squared Bernstein "norm", `Tδ(q)` the power tail and `Aₖ(q)` the log tail.

## Coefficients

| Bound | Paper (general `q`) | Sharpened | At `q = 4` | Lean declaration |
| --- | --- | --- | --- | --- |
| `K ≤ C H² + A₁(q)` | `1 + √q` | `J(q)(log q − 1 + 1/q)` | `3` → `4 log 4 − 3 ≈ 2.545` | [`Hellinger.Sharp.kl_le_hellinger_add_tailLogMoment_sharp`](../Hellinger/Sharp/KL.lean) |
| `A₁(q) ≤ c Tδ(q)` | `δ⁻¹` | `(eδ)⁻¹` | | [`Hellinger.Sharp.tailLogMoment_one_le_tailPower_sharp`](../Hellinger/Sharp/KL.lean) |
| `K ≤ C H² + c Tδ(q)` | `1 + √q`, `δ⁻¹` | `J(q)(log q − 1 + 1/q)`, `(eδ)⁻¹` | | [`Hellinger.Sharp.kl_le_hellinger_add_tailPower_sharp`](../Hellinger/Sharp/KL.lean) |
| `a A₁(q) ≤ K` | `min(1/3, (1 − 1/q)/2)` | `1 − (1 − 1/q)/log q` | `1/3` → `≈ 0.459` | [`Hellinger.Sharp.klTailLowerSharpCoeff_mul_tailLogMoment_le_kl`](../Hellinger/Sharp/KL.lean) |
| `b Tδ(q) ≤ Bδ²` | `(1 − q^(−δ))²`, `δ ≤ 1` | `2(1 − q^(−δ)(1 + δ log q))`, every `δ > 0` | `δ = 1`: `0.5625` → `≈ 0.807` | [`Hellinger.Sharp.bernsteinLowerSharpCoeff_mul_tailPower_le_bernsteinSq`](../Hellinger/Sharp/Bernstein.lean) |
| `Bδ² ≤ C H² + 2Tδ(q)` | `2δ(1 + √q)²` | `2δ²(1 + √q)²`, `δ ≤ 1` | `18δ` → `18δ²` | [`Hellinger.Sharp.bernsteinSq_le_hellinger_add_tailPower_sq`](../Hellinger/Sharp/Bernstein.lean) |
| `Vₖ ≤ C H² + Aₖ(q)`, `k ≥ 2` | `max(4√q (log q)^(k−2), J(q)(k/e)^k)` | `max(J(q)(log q)^k, B_k)` | `k = 2`: `8` → `16(log 2)² ≈ 7.69` | [`Hellinger.Sharp.logMoment_le_hellinger_add_tailLogMoment_sharp`](../Hellinger/Sharp/Variation.lean) |
| `Aₖ(q) ≤ C (H²)^(1−k/k') Aₖ'(q)^(k/k')` | `J(q)` | `J(q)^(1−k/k')` | `4` → `4^(1−k/k')` | [`Hellinger.Sharp.tailLogMoment_interpolation_sharp`](../Hellinger/Sharp/Variation.lean) |
| `Tδ(q) ≤ C (H²)^(1−δ/δ') Tδ'(q)^(δ/δ')` | `J(q)` | `J(q)^(1−δ/δ')` | `4` → `4^(1−δ/δ')` | [`Hellinger.Sharp.tailPower_interpolation_sharp`](../Hellinger/Sharp/Variation.lean) |
| `T₁(q) ≤ C H²` under `CM ≤ M` | `(2M + 1)²` at `q = 4` | `4M²` at every `q ≥ 9/4` | | [`Hellinger.Sharp.tailPower_le_of_conditionalMoment_le_sharp`](../Hellinger/Sharp/Bernstein.lean) |

Here `B_k = sup_{0 < r < 1} r |log r|^k / (√r − 1)²`, which is finite for `k ≥ 2`; for `k = 2` the coefficient equals `J(q)(log q)²` for every `q > 1`.
The comparisons with the paper's coefficients are `Hellinger.Sharp.sharpCoeffs_improve`; the closed forms at `q = 4` and `k = 2` are `Hellinger.Sharp.sharpCoeff_values`.

## Which coefficients are sharp

Each bound reduces to a pointwise inequality for the likelihood ratio `x = dP₀/dP`.

- **Pointwise-sharp.** The coefficients of the upper and lower-tail bounds on the Kullback–Leibler divergence, the lower bound on the Bernstein "norm" and the bound on the Kullback–Leibler variation are the best constants in their pointwise inequalities.
  - Kullback–Leibler upper bound: `klFun(x)/(√x − 1)²` with `klFun(x) = x log x − x + 1`, maximized over `[0, q]` at `x = q`.
  - Kullback–Leibler lower tail: `klFun(x)/(x log x)`, with infimum over `x > q` approached as `x → q`.
  - Bernstein lower: the ratio `2(1 − x^(−δ)(1 + δ log x))` is increasing in `x`.
  - Variation: on `(1, q]` the ratio `x |log x|^k/(√x − 1)²` is nondecreasing for `k ≥ 2`, and on `(0, 1)` it is bounded by `B_k`.

  A two-point perturbation shows that these constants cannot be improved at the measure level either; that argument is not formalized.
- **Improved, not claimed sharp.** The factor `(eδ)⁻¹` comes from `u ≤ e^(u−1)`; it is the best pointwise constant only when `δ log q ≤ 1`. The coefficients `2δ²(1 + √q)²`, `J(q)^(1−k/k')` and `4M²` are improvements obtained by tightening the paper's arguments.

## Remarks

- **Bernstein lower bound.** The paper states it for `0 < δ ≤ 1`, the domain of the Bernstein comparison. The lower bound itself holds for every `δ > 0`.
- **Bernstein upper bound.** Its `δ²` form uses `sinh(δu) ≤ δ sinh u` for `0 < δ ≤ 1`.
- **Conditional moments.** The improvement comes from `(2a + 1)² = 4a² (1 + 1/(2a))²` together with the bound below of the conditional ratio mean by its threshold. The cutoff `9/4` is the largest native CM threshold, so the bound holds at every larger cutoff without a transfer term.
- **Interpolation.** In the example preceding Theorem 2, where `A₂(4) ≤ M H²` gives `A₁(4) ≤ 4√M H²`, the factor `4√M` improves to `2√M`.
