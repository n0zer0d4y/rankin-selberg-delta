# Claims and evidence — the Rankin–Selberg pole and L(Δ, 1 + it) ≠ 0

| # | Claim (precise) | Rigor | Digits | Novelty | Certificate | Lean statement | Witness | Notes |
| --- | --------------- | ----- | ------ | ------- | ----------- | -------------- | ------- | ----- |
| 1 | For a level-one cusp form f of weight k > 0 with f ≠ 0, the real continuation `rsDcont` of D(σ) = Σ \|a(n)\|² n^{−σ} agrees with D for σ > k + 1, and (σ − k) · rsDcont(σ) → (4π)^k/Γ(k) · (3/π) ∫\_𝒟 \|f\|² y^k dμ > 0 as σ → k⁺ | proved |  | classical (Rankin 1939, Selberg 1940); formalisation not found elsewhere |  | lean/RankinSelbergDelta/RankinSelberg/RSPole.lean: RankinSelbergDelta.RankinSelberg.rsD\_simplePole | RankinSelbergDelta.CuspForm.rsD\_simplePole\_hyps\_satisfiable | The limit is along real σ; see #2 for the complex continuation. |
| 2 | For such f, rsG(s) = ζ(2s) D(s + k − 1) for 1 < Re s < 9/4; rsG is holomorphic on 0 < Re s < 9/4 except at s = 1; and (s − 1) rsG(s) → rsPre(1) ∫\_𝒟 \|f\|² y^k dμ as s → 1 in ℂ | proved |  | classical; formalisation not found elsewhere |  | lean/RankinSelbergDelta/RankinSelberg/SimplePole.lean: RankinSelbergDelta.RankinSelberg.rsD\_continuation | RankinSelbergDelta.CuspForm.rsD\_simplePole\_hyps\_satisfiable | Only hypothesis 0 < k. Equivalently, D continues meromorphically to k − 1 < Re w < k + 5/4 with its only pole at w = k. |
| 3 | For the normalised discriminant fΔ = Δ/1728 (coefficients τ(n)), #1 holds with k = 12 and no remaining hypothesis | proved |  |  |  | lean/RankinSelbergDelta/Delta.lean: RankinSelbergDelta.Delta.rankinSelberg\_pole\_Delta | (no hypotheses) | Uses fΔ\_ne\_zero, proved in the same file from Δ\_ne\_zero. |
| 4 | Δ = E₄³ − E₆² is a nonzero level-one cusp form of weight 12, and T\_p Δ = c\_p Δ for every prime p; the coefficients of fΔ satisfy IsHeckeEigenCoeffs (a(0) = 0, a(1) = 1, multiplicativity on coprime arguments, a(p^{r+2}) = a(p) a(p^{r+1}) − p^{11} a(p^r)) and are real | proved |  | classical; formalised independently elsewhere (see Notes) |  | lean/RankinSelbergDelta/CuspForm/DeltaHeckeEigenform.lean: RankinSelbergDelta.Hecke.heckeT\_Delta\_eq\_smul; lean/RankinSelbergDelta/CuspForm/NormalizedDelta.lean: isHeckeEigenCoeffs\_rsCoeff\_fΔ, hreal\_fΔ; lean/RankinSelbergDelta/CuspForm/Discriminant.lean: Δ\_ne\_zero | (no hypotheses) | Not new in Lean: Birkbeck's LeanModularForms has Hecke operators and eigenforms, and MathProof (Zenodo 10.5281/zenodo.23636675) has τ and Ramanujan's congruences. Proved here independently because the chain needs these exact statements. |
| 5 | For a level-one Hecke eigenform f of weight k > 0 (IsHeckeEigenCoeffs) and y ≠ 0, G(1 + iy) ≠ 0, where G(s) = ζ(2s) D(s + k − 1) | proved |  | classical (de la Vallée Poussin's argument on the Rankin–Selberg square) |  | lean/RankinSelbergDelta/RankinSelberg/EulerProduct.lean: RankinSelbergDelta.RankinSelberg.rs\_square\_ne\_zero | RankinSelbergDelta.Hecke.Lfunction\_ne\_zero\_Delta\_hyps\_satisfiable | Rests on Λ\_G(p^m) = \|α\_p^m + β\_p^m\|² log p ≥ 0 and the simple pole of #2. |
| 6 | For a level-one Hecke eigenform f of weight k > 0 with real coefficients and real t ≠ 0, L(f, 1 + it) ≠ 0, where L(f, w) is the entire continuation of Σ a(n) n^{−(w + (k−1)/2)} | proved |  | classical; formalisation not found elsewhere |  | lean/RankinSelbergDelta/RankinSelberg/EdgeNonvanishing.lean: RankinSelbergDelta.RankinSelberg.Lfunction\_ne\_zero\_on\_one\_line | RankinSelbergDelta.Hecke.Lfunction\_ne\_zero\_Delta\_hyps\_satisfiable | L is the library's `Lfun`, not Mathlib's modular-form L-function. |
| 7 | L(Δ, 1 + it) ≠ 0 for every real t ≠ 0, with L(Δ, w) = Σ τ(n) n^{−(w + 11/2)} continued | proved |  |  |  | lean/RankinSelbergDelta/CuspForm/NormalizedDelta.lean: RankinSelbergDelta.Hecke.Lfunction\_ne\_zero\_Delta | RankinSelbergDelta.Hecke.Lfunction\_ne\_zero\_Delta\_hyps\_satisfiable | #6 with every structural hypothesis discharged by #4. |

## Reasoning

### #1

- Unfolding (`unfolding_integral_eisensteinE`) turns ∫\_𝒟 y^k \|f\|² E(z, s) dμ into an integral over the strip.
- The mean-square identity (`integral_sq_eq_tsum`) and the Mellin identity (`rsMellin_eq`) identify it with Γ(s + k − 1)/(4π)^{s+k−1} · D(s + k − 1).
- E(z, s) has a simple pole at s = 1 with residue 3/π (theta functional equation, `EpsteinTheta.lean`), uniformly enough on 𝒟 to pass the limit through the integral.
- The residue is positive because ∫\_𝒟 \|f\|² y^k dμ > 0 when f ≠ 0 (a continuous nonnegative function, positive somewhere, on a set of positive measure).
- What would change the conclusion: nothing at the level of the statement; it is kernel-checked. The point to read is the meaning of `rsDcont` (a real function of σ), which the statement makes explicit.

### #2

- `rsG` is defined as rsPre(s)(J(s) − (1/s + 1/(1 − s)) ∫\_𝒟 Φ), with J(s) the integral of Φ against the truncated Eisenstein series.
- The three conjuncts are `rsG_eq_zeta_mul_rsD`, `differentiableAt_rsG` and `tendsto_rsG_residue`.

### #3

- rsD\_simplePole applied with k = 12 and f = fΔ. The hypothesis fΔ ≠ 0 follows from Δ ≠ 0, since 1/1728 ≠ 0.

### #4

- Δ is E₄³ − E₆², with Mathlib's normalised Eisenstein series. Its constant coefficient is 0 and its first coefficient is 1728, so it is a nonzero cusp form.
- T\_p is defined on q-expansions and maps level-one cusp forms to cusp forms (`heckeTCuspForm`).
- Every level-one cusp form of weight 12 is a multiple of η²⁴ (`exists_eq_mul_η24`), hence T\_p Δ is a multiple of Δ.
- Reading off q-coefficients gives the Hecke relations for τ(n) (`HeckeMultiplicativity.lean`).

### #5

- The logarithm of G for Re s > 1 has nonnegative coefficients Λ\_G(n) (`rsVonMangoldt_nonneg`), so the 3-4-1 product \|G(σ)³ G(σ+iy)⁴ G(σ+2iy)\| is at least 1 (`Gfull_product_ge_one`).
- With the simple pole at s = 1 (#2, `Gfull_isBigO`), holomorphy at 1 + iy and continuity at 1 + 2iy, the abstract de la Vallée Poussin theorem `trs_ne_zero` gives G(1 + iy) ≠ 0.

### #6

- For σ > 1, ζ(σ) L(σ+it)² L(σ−it)² G(σ+2it) G(σ)² G(σ−2it) is the exponential of a series with nonnegative terms (`isoProduct_eq`), so its modulus is at least 1 (`one_le_norm_isoProduct`).
- If L(1 + it) = 0, then L(σ ± it) = O(σ − 1) (the conjugate zero comes from the real coefficients), ζ(σ) and G(σ) are O(1/(σ − 1)), and G(σ ± 2it) stays bounded because 2t ≠ 0. The product is O(σ − 1), a contradiction.

### #7

- #6 applied to fΔ, with the hypotheses of #4.
