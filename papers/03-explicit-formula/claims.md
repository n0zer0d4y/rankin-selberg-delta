# Claims and evidence — the explicit formula for the Rankin–Selberg square

| # | Claim (precise) | Rigor | Digits | Novelty | Certificate | Lean statement | Witness | Notes |
| --- | --------------- | ----- | ------ | ------- | ----------- | -------------- | ------- | ----- |
| 1 | For a level-one cusp form f of weight k > 0, `rsHent k f` is entire, and `rsHent k f s = (s − 1) G(s)` for s ≠ 0, 1, where G = `Gfull k f` | proved |  | classical; formalisation not found elsewhere |  | lean/RankinSelbergDelta/RankinSelberg/ExplicitFormula.lean: RankinSelbergDelta.RankinSelberg.differentiable\_rsHent, RankinSelbergDelta.RankinSelberg.rsHent\_eq | RankinSelbergDelta.CuspForm.rsD\_simplePole\_hyps\_satisfiable | G equals ζ(2s) D(s + k − 1) for Re s > 1 (`Gfull_eq`). |
| 2 | For a level-one Hecke eigenform f of weight k > 0, there are σ₀ ≥ 2 and K such that for all T ≥ 2 the zeros of `rsHent k f` with −1 ≤ Re s ≤ σ₀ and 1 ≤ \|Im s\| ≤ T are finite in number and, counted with multiplicity, at most K T log T | proved |  | classical (Riemann–von Mangoldt upper bound); formalisation not found elsewhere |  | lean/RankinSelbergDelta/RankinSelberg/FiniteHeightReach.lean: RankinSelbergDelta.RankinSelberg.exists\_wcount\_zeros\_rsHent\_le\_mul\_log | RankinSelbergDelta.Hecke.Lfunction\_ne\_zero\_Delta\_hyps\_satisfiable | Upper bound only; no asymptotic. |
| 3 | For such f, 1 < σ < 2 and g : ℝ → ℂ continuous with ĝ entire, the integrability hypotheses on g e^{σx}, its reflection and their Fourier transforms, decay ‖ĝ(s)‖ (Im s)² ≤ B on the strip, and an integrable archimedean integrand: Σ\_u div(rsHent)(u) ĝ(u) over the strip 1 − σ ≤ Re u ≤ σ equals ĝ(1) − Σ\_{n≥2} Λ\_G(n) g(log n) − Σ\_{n≥2} Λ\_G(n) g(−log n)/n − (1/2π) ∫ (rsPre′/rsPre(σ − it) + rsPre′/rsPre(1 − σ + it)) ĝ(1 − σ + it) dt | proved |  | classical (Weil); formalisation not found elsewhere |  | lean/RankinSelbergDelta/RankinSelberg/ZeroSum.lean: RankinSelbergDelta.RankinSelberg.explicitFormula\_Gfull\_tsum | RankinSelbergDelta.RankinSelberg.explicitFormula\_Gfull\_tsum\_hyps\_satisfiable | The witness gives σ and a smooth bump g; #4 shows such g meet every hypothesis of #3. |
| 4 | #3 holds for every smooth compactly supported g, with no further hypothesis on g | proved |  |  |  | lean/RankinSelbergDelta/RankinSelberg/ZeroSum.lean: RankinSelbergDelta.RankinSelberg.explicitFormula\_Gfull\_tsum\_of\_smooth | RankinSelbergDelta.RankinSelberg.explicitFormula\_Gfull\_tsum\_hyps\_satisfiable | The witness exhibits σ = 3/2 and a bump with g(0) = 1. |
| 5 | #4 for the normalised discriminant fΔ = Δ/1728, with no hypothesis on the form | proved |  |  |  | lean/RankinSelbergDelta/Delta.lean: RankinSelbergDelta.Delta.explicit\_formula\_Delta | RankinSelbergDelta.Delta.explicit\_formula\_Delta\_hyps\_satisfiable |  |

## Reasoning

### #1

- `rsHent(s) = rsPreS(s) (s(s − 1) J(s) + ∫_𝒟 Φ)`; `rsPreS` is a product of exponentials and reciprocal Gamma functions, and J is the integral of Φ against the truncated Eisenstein series, entire by differentiation under the integral. So `rsHent` is entire.
- On Re s > 1, unfolding identifies G with ζ(2s) D(s + k − 1); `rsHent_eq` is the algebraic identity between the two expressions away from s = 0, 1.

### #2

- Jensen's formula on discs of fixed radius centred on Re s = σ₀ counts zeros in the band at unit-spaced heights. The centre value is bounded below (`exists_norm_Gfull_ge`: ‖G‖ ≥ 3/8 on Re s = σ₀) and the circle average is bounded through polynomial growth (`exists_norm_Gfull_le_halfStrip`).
- Each unit interval of height contributes O(log T); summing over at most T intervals gives O(T log T). The count uses the divisor, so zeros are counted with multiplicity.

### #3

- The finite version on rectangles (`explicitFormula_Gfull`) comes from the argument principle, the prime-side limit on the right edge, the functional equation on the left edge, and the vanishing of the horizontal edges along zero-avoiding heights.
- Absolute summability of the zero sum (`summable_norm_zeroSum_Gfull`) follows from the decay hypothesis and #2 by Abel summation. The rectangle sums then converge to the full series (`tsum_divisor_mul_eq_of_tendsto_rect`).

### #4

- For g smooth with compact support, ĝ is entire (`analyticAt_ghat`), the Fourier transforms of g e^{σx} and of its reflection are integrable, ĝ decays like \|Im s\|^{−N} on vertical lines by integration by parts, and the archimedean kernel grows at most polynomially (`ArchimedeanKernel.lean`). These discharge every hypothesis of #3.

### #5

- #4 applied with k = 12 and f = fΔ, with `isHeckeEigenCoeffs_rsCoeff_fΔ`.
