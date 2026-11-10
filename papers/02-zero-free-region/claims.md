# Claims and evidence — a zero-free region for the Rankin–Selberg square

| # | Claim (precise) | Rigor | Digits | Novelty | Certificate | Lean statement | Witness | Notes |
| --- | --------------- | ----- | ------ | ------- | ----------- | -------------- | ------- | ----- |
| 1 | If P, Z, W : ℝ → ℝ satisfy, for 1 < σ ≤ 2, 3P + 4Z + W ≥ 0, P ≤ 1/(σ − 1) + C, Z ≤ −1/(σ − β) + C log \|γ\| and W ≤ C log \|γ\|, with C > 0, 3/4 < β < 1 and log \|γ\| ≥ 1, then β ≤ 1 − 1/(160 C log \|γ\|) | proved |  | classical (de la Vallée Poussin) |  | lean/RankinSelbergDelta/RankinSelberg/ZeroFreeRegion.lean: RankinSelbergDelta.RankinSelberg.zero\_free\_of\_logDeriv\_341 | (instantiated by #2) | A real-variable lemma; the statement prints 1 − 1/(20 · (8C) · log \|γ\|). |
| 2 | For a level-one Hecke eigenform f of weight k > 0, there are C > 0 and t₀ ≥ 3 such that every zero β + iγ of G(s) = ζ(2s) D(s + k − 1) with 3/4 < β < 1 and \|γ\| ≥ t₀ has β ≤ 1 − 1/(160 C log \|γ\|) | proved |  | classical; formalisation not found elsewhere |  | lean/RankinSelbergDelta/RankinSelberg/RSZeroFree.lean: RankinSelbergDelta.RankinSelberg.rs\_zero\_free\_region | RankinSelbergDelta.Hecke.Lfunction\_ne\_zero\_Delta\_hyps\_satisfiable | G is `Gfull k f`. The constants are existential and not computed. |
| 3 | #2 for the normalised discriminant fΔ = Δ/1728, with no remaining hypothesis | proved |  |  |  | lean/RankinSelbergDelta/Delta.lean: RankinSelbergDelta.Delta.zero\_free\_region\_Delta | (no hypotheses) | After normalisation G is ζ(s) L(sym² Δ, s); the region covers the zeros of both factors. |

## Reasoning

### #1

- The proof evaluates the four inequalities at σ = 1 + 4(1 − β), which lies in (1, 2) because 3/4 < β < 1.
- There, 1/(σ − 1) = 1/(4(1 − β)) and 1/(σ − β) = 1/(5(1 − β)). With L = log \|γ\|, substituting into 0 ≤ 3P + 4Z + W gives 0 ≤ 3/(4(1 − β)) − 4/(5(1 − β)) + 3C + 5CL.
- Since 3/4 − 4/5 = −1/20 and L ≥ 1, this gives 1/(20(1 − β)) ≤ 3C + 5CL ≤ 8CL, that is, 1 − β ≥ 1/(160 C L).

### #2

- The arithmetic input is the 3-4-1 inequality for −G′/G = Σ Λ\_G(n) n^{−s}, from Λ\_G ≥ 0 (`rsVonMangoldt_nonneg`) and 3 + 4 cos θ + cos 2θ ≥ 0.
- The analytic inputs are the pole bound (`neg_re_logDeriv_Gfull_le_pole`, from the simple pole of `rsD_continuation`) and the two bounds at height γ (`neg_re_logDeriv_Gfull_le`, `neg_re_logDeriv_Gfull_le_of_zero`). These come from Borel–Carathéodory, a lower bound for \|G\| on a line Re s = σ₀ ≥ 2 and polynomial growth in vertical strips.
- `rs_zero_free_region_of_pole` combines them through #1. Its hypotheses k > 0 and IsHeckeEigenCoeffs hold for fΔ (the witness).

### #3

- #2 applied with k = 12 and f = fΔ, with `isHeckeEigenCoeffs_rsCoeff_fΔ` for the Hecke hypothesis.
