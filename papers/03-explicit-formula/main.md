---
title: "The explicit formula for the Rankin–Selberg square of a Hecke eigenform, formalised in Lean 4"
authors: ["Nozero Day"]
note: "Produced autonomously by AI agents running inside a custom research harness; see the repository README. Unrefereed."
status: draft
date: "2026-11-10"
---

# The explicit formula for the Rankin–Selberg square of a Hecke eigenform, formalised in Lean 4

## Summary

**The mathematics is classical.** For a level-one Hecke eigenform f of weight k, the Rankin–Selberg square G(s) = ζ(2s) D(s + k − 1), with D(w) = Σ |a(n)|² n^{−w}, continues meromorphically to ℂ. Its only pole is a simple one at s = 1, so H(s) = (s − 1) G(s) is entire. Weil's explicit formula relates a sum over the zeros of H to a sum over prime powers, weighted by the coefficients Λ\_G of −G′/G, plus an archimedean term from the Gamma factors (see [IK04] and [We52]).

**What is new is the formalisation.** This repository proves in Lean 4 with Mathlib:

- **The entire function** (`rsHent`, `differentiable_rsHent`, `rsHent_eq`). `rsHent k f` is entire and equals (s − 1) G(s) for s ≠ 0, 1.
- **The zero count** (`exists_wcount_zeros_rsHent_le_mul_log`). The number of zeros of `rsHent` with −1 ≤ Re s ≤ σ₀ and 1 ≤ |Im s| ≤ T, counted with multiplicity, is O(T log T).
- **The explicit formula as a series over all zeros** (`explicitFormula_Gfull_tsum`, and `explicitFormula_Gfull_tsum_of_smooth` for smooth compactly supported test functions). For 1 < σ < 2 the sum of ĝ over the zeros of `rsHent` in the strip 1 − σ ≤ Re s ≤ σ converges absolutely, and

  Σ\_ρ m\_ρ ĝ(ρ) = ĝ(1) − Σ\_{n≥2} Λ\_G(n) g(log n) − Σ\_{n≥2} Λ\_G(n) g(−log n)/n − (1/2π) ∫ (archimedean kernel) · ĝ dt,

  where ĝ(s) = ∫ g(x) e^{sx} dx.
- **The formula for Δ** (`explicit_formula_Delta`). The same identity for f = Δ/1728, for every smooth compactly supported g, with no remaining hypothesis.

## The formal statement

From `RankinSelbergDelta/RankinSelberg/ZeroSum.lean`:

```lean
theorem explicitFormula_Gfull_tsum_of_smooth (f : F) (hk : 0 < k)
    (hf : IsHeckeEigenCoeffs (rsCoeff f) k) {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ < 2) (g : ℝ → ℂ)
    (hg : ContDiff ℝ ∞ g) (hgs : HasCompactSupport g) :
    ∑' u, ((MeromorphicOn.divisor (rsHent k f) (ZeroSum.strip σ)) u : ℂ) * ghat g u
      = ghat g 1
        - ∑' n, (if 2 ≤ n then (rsVonMangoldt (rsCoeff f) k n : ℂ) * g (Real.log n) else 0)
        - ∑' n, (if 2 ≤ n then (rsVonMangoldt (rsCoeff f) k n : ℂ) * (g (-(Real.log n)) / n)
            else 0)
        - (1 / (2 * Real.pi)) * ∫ t : ℝ, (logDeriv (rsPre k) ((σ : ℂ) - t * Complex.I)
            + logDeriv (rsPre k) (((1 - σ : ℝ) : ℂ) + t * Complex.I))
            * ghat g (((1 - σ : ℝ) : ℂ) + t * Complex.I)
```

- **The zero side.** `MeromorphicOn.divisor (rsHent k f) (ZeroSum.strip σ)` is Mathlib's divisor of the entire function `rsHent` on the strip: at each zero it is the order of vanishing, and elsewhere 0. Since `rsHent(s) = (s − 1) G(s)` away from s = 0, 1, and `rsHent` does not vanish at s = 1 (its value there is the residue of G), the zeros counted are the zeros of G in the strip, together with s = 0 exactly when `rsHent(0) = 0`. For k ≥ 2, `rsHent(0) = rsPreS(0) ∫_𝒟 Φ ≠ 0`, so no extra term occurs.
- **The prime side.** `rsVonMangoldt (rsCoeff f) k n` is Λ\_G(n), equal to |α\_p^m + β\_p^m|² log p for n = p^m and 0 otherwise.
- **The archimedean side.** `rsPre k (s) = (4π)^{s+k−1} π^s / (2 Γ(s + k − 1) Γ(s))` is the reciprocal Gamma factor, so its logarithmic derivative is the digamma term of the completed function.

The general form, `explicitFormula_Gfull_tsum`, replaces smoothness and compact support by the hypotheses actually used: ĝ entire, the integrability of g e^{σx}, of the reflected function and of their Fourier transforms, decay ‖ĝ(s)‖ (Im s)² ≤ B in the strip for |Im s| ≥ 1, and integrability of the archimedean integrand. `explicitFormula_Gfull_of_smooth` is the version before summation: a limit of finite sums over rectangles [1 − σ, σ] × [−T\_j, T\_j] along heights T\_j ∈ [j, j + 1].

## Proof outline

**1. The entire function** (`RankinSelberg/FunctionalEquation.lean`, `RankinSelberg/ExplicitFormula.lean`). `rsHent(s) = rsPreS(s) (s(s − 1) J(s) + ∫_𝒟 Φ)`, with J the integral of Φ = y^k |f|² against the truncated Eisenstein series. Each factor is entire (`differentiable_rsHent`). The functional equation of the Eisenstein series gives the reflection used for the left edge (`logDeriv_Gfull_one_sub`).

**2. The argument principle on a rectangle** (`RankinSelberg/ExplicitFormulaRect.lean`). For a rectangle in which `rsHent` has no zero on the boundary, 2πi Σ\_ρ m\_ρ h(ρ) equals the contour integral of (H′/H) h, by a general argument principle for analytic weights.

**3. The four edges.**
- **Right edge** (`RankinSelberg/PrimeSideLimit.lean`). On Re s = σ > 1, −G′/G = Σ Λ\_G(n) n^{−s}. The series is integrated term by term, and Laplace inversion at y = log n gives the prime sum (dominated convergence through Tannery's theorem).
- **Left edge.** The functional equation reflects it to the right edge, giving the second prime sum and the archimedean term.
- **Horizontal edges** (`RankinSelberg/ExplicitFormula.lean`). The edges are taken at heights T\_j ∈ [j, j + 1] that stay a fixed distance from every zero; they exist by a pigeonhole argument on the zero count. Along them the logarithmic derivative is O(log T) (Davenport's local expansion), and the edge integrals vanish in the limit.

**4. The zero count** (`RankinSelberg/ZeroCountPrimeSide.lean`, `RankinSelberg/ZeroCountMultiplicity.lean`, `RankinSelberg/FiniteHeightReach.lean`). Jensen's formula on discs centred on a line Re s = σ₀ ≥ 2 gives N(T + 1) − N(T) = O(log T). The inputs are a lower bound for |G| on that line and polynomial growth in strips. Summing gives O(T log T) with multiplicity.

**5. Summation over all zeros** (`RankinSelberg/ZeroSum.lean`). The decay ‖ĝ(s)‖ (Im s)² ≤ B and Abel summation against the zero count make Σ\_ρ m\_ρ |ĝ(ρ)| converge (`summable_norm_zeroSum_Gfull`). The rectangle limits of step 3 then identify the full series (`explicitFormula_Gfull_tsum`).

**6. Smooth test functions** (`RankinSelberg/ExplicitFormulaSmooth.lean`). For g smooth with compact support, every analytic hypothesis follows. ĝ is entire, the Fourier transforms are integrable, ĝ decays polynomially on vertical lines (integration by parts), and the archimedean kernel grows at most polynomially (`RankinSelberg/ArchimedeanKernel.lean`).

## Scope and limits

- **Normalisation.** ĝ(s) = ∫ g(x) e^{sx} dx is a two-sided Laplace transform, so the formula is centred at Re s = 1/2 and uses the unnormalised G. A reader comparing with a textbook version should translate the variables accordingly.
- **The archimedean term is left as an integral.** It is not evaluated in closed form through digamma values.
- **No positivity is claimed.** The library also proves the easy direction of Weil's criterion for G (`weilForm_Gfull_nonneg_of_line`): if every zero of G lies on Re s = 1/2, the zero side of the self-dual Weil form is nonnegative. The converse is not proved.
- **Not new mathematics.** The explicit formula is classical. The contribution is a kernel-checked derivation for this G, with every analytic input proved.

## References

- [IK04] H. Iwaniec, E. Kowalski, Analytic Number Theory, AMS Colloquium Publications 53 (2004), doi:10.1090/coll/053.
- [We52] A. Weil, Sur les "formules explicites" de la théorie des nombres premiers (1952); reprinted in Œuvres Scientifiques / Collected Papers, Springer (1979), 570–583, doi:10.1007/978-1-4757-1705-1_60.
- [Da00] H. Davenport, Multiplicative Number Theory, 3rd ed., revised by H. L. Montgomery, Graduate Texts in Mathematics 74, Springer (2000).
