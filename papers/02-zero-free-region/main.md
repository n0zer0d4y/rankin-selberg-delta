---
title: "A zero-free region for the Rankin–Selberg square of a Hecke eigenform, formalised in Lean 4"
authors: ["Nozero Day"]
note: "Produced autonomously by AI agents running inside a custom research harness; see the repository README. Unrefereed."
status: draft
date: "2026-11-10"
---

# A zero-free region for the Rankin–Selberg square of a Hecke eigenform, formalised in Lean 4

## Summary

**The mathematics is classical.** Let f be a level-one Hecke eigenform of weight k, with normalised coefficients a(n), and let

  G(s) = ζ(2s) D(s + k − 1),  D(w) = Σ\_{n≥1} |a(n)|² n^{−w}

be its Rankin–Selberg square. For Δ, after normalising the coefficients, G(s) is ζ(s) L(sym² Δ, s). G has an Euler product with nonnegative logarithmic coefficients, a simple pole at s = 1, and polynomial growth in vertical strips. De la Vallée Poussin's method then gives a zero-free region of the classical shape: no zeros with σ > 1 − c / log |t| for large |t| (see [IK04] and [Da00]).

**What is new is the formalisation.** This repository proves the region in Lean 4 with Mathlib, for every level-one Hecke eigenform of positive weight, and specialises it to Δ with no remaining hypothesis.

- **`rs_zero_free_region`** (general f). There are constants C > 0 and t₀ ≥ 3 such that every zero β + iγ of G with 3/4 < β < 1 and |γ| ≥ t₀ satisfies β ≤ 1 − 1/(160 C log |γ|).
- **`zero_free_region_Delta`.** The same statement for f = Δ/1728.

The constants C and t₀ are produced by the proof but not computed.

## The formal statement

From `RankinSelbergDelta/RankinSelberg/RSZeroFree.lean`:

```lean
theorem rs_zero_free_region (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k) :
    ∃ C t₀ : ℝ, 0 < C ∧ 3 ≤ t₀ ∧ ∀ β γ : ℝ, 3 / 4 < β → β < 1 → t₀ ≤ |γ| →
      Gfull k f ((β : ℂ) + Complex.I * γ) = 0 →
      β ≤ 1 - 1 / (20 * (8 * C) * Real.log |γ|)
```

`Gfull k f` is G: it equals ζ(2s) D(s + k − 1) for Re s > 1 (`Gfull_eq`) and the continuation `rsG` for Re s < 2. `IsHeckeEigenCoeffs (rsCoeff f) k` is the Hecke structure of the coefficients (a(1) = 1, multiplicativity on coprime arguments, and the prime-power recursion). The Δ version, in `RankinSelbergDelta/Delta.lean`, discharges it with `isHeckeEigenCoeffs_rsCoeff_fΔ`.

## Proof outline

**1. The optimisation** (`RankinSelberg/ZeroFreeRegion.lean`, `zero_free_of_logDeriv_341`). This step is abstract and uses only real inequalities. Suppose three real functions P, Z, W on (1, 2] satisfy, with L = log |γ| ≥ 1 and some C > 0:
- 3P(σ) + 4Z(σ) + W(σ) ≥ 0;
- P(σ) ≤ 1/(σ − 1) + C;
- Z(σ) ≤ −1/(σ − β) + C L;
- W(σ) ≤ C L.

Then β ≤ 1 − 1/(160 C L). The proof evaluates the inequalities at σ = 1 + 4(1 − β), which lies in (1, 2) because 3/4 < β < 1.

**2. The 3-4-1 inequality** (`RankinSelberg/EulerProduct.lean`, `Shared/MertensLocal.lean`, `RankinSelberg/RSZeroFree.lean`). For Re s > 1, −G′/G(s) = Σ Λ\_G(n) n^{−s}, with Λ\_G(p^m) = |α\_p^m + β\_p^m|² log p ≥ 0 (`rsVonMangoldt_nonneg`). Since 3 + 4 cos θ + cos 2θ = 2(1 + cos θ)² ≥ 0, the combination 3 Re(−G′/G)(σ) + 4 Re(−G′/G)(σ + iγ) + Re(−G′/G)(σ + 2iγ) is nonnegative. This is P, Z, W of step 1, with P(σ) = −Re(G′/G)(σ) and so on.

**3. The pole bound** (`neg_re_logDeriv_Gfull_le_pole`, `RankinSelberg/LogDerivBounds.lean`). From the simple pole of G at s = 1 (`rsD_continuation`), −Re(G′/G)(σ) ≤ 1/(σ − 1) + C on (1, 2].

**4. The bounds at height γ** (`neg_re_logDeriv_Gfull_le`, `neg_re_logDeriv_Gfull_le_of_zero`).
- The Borel–Carathéodory inequality and Davenport's disc lemma give the local expansion of G′/G as a sum over nearby zeros plus O(log |t|) (`neg_re_logDeriv_le`, `logDeriv_bound_setup`).
- The inputs are a lower bound for |G| on a line Re s = σ₀ ≥ 2 (`exists_norm_Gfull_ge`) and an upper bound of polynomial growth in vertical strips (`StripGrowth.lean`). The upper bound rests on Gamma-function bounds proved without Stirling's formula (`GammaGrowth.lean`).
- Dropping the nonnegative contributions of the other zeros gives −Re(G′/G)(σ + 2iγ) ≤ C log |γ|, and, at a zero β + iγ, −Re(G′/G)(σ + iγ) ≤ −1/(σ − β) + C log |γ|.

**5. Assembly** (`rs_zero_free_region_of_pole`, `rs_zero_free_region`). Steps 2–4 supply the four hypotheses of step 1, which gives the region.

## Scope and limits

- **The constant is not explicit.** C and t₀ are existential. The proof produces them, but nothing here evaluates them, so the region cannot be compared numerically with published explicit regions.
- **The region is for G, not for L(f, s).** It concerns the zeros of the Rankin–Selberg square G. For f = Δ, G(s) is ζ(s) L(sym² Δ, s) after normalisation, so the region bounds the zeros of ζ and of L(sym² Δ, s) together. A zero-free region for L(f, s) itself is not proved here; the edge nonvanishing of L(f, s) on Re s = 1 is paper 1.
- **Ramanujan's bound is not used.** The arithmetic input is the nonnegativity of Λ\_G, which follows from the Hecke relations alone.
- **Not new mathematics.** The region is classical. The contribution is the kernel-checked formalisation, including the analytic inputs (Borel–Carathéodory, Gamma bounds, growth in strips) for this G.

## References

- [Da00] H. Davenport, Multiplicative Number Theory, 3rd ed., revised by H. L. Montgomery, Graduate Texts in Mathematics 74, Springer (2000).
- [IK04] H. Iwaniec, E. Kowalski, Analytic Number Theory, AMS Colloquium Publications 53 (2004), doi:10.1090/coll/053.
- [Ra39] R. A. Rankin, Contributions to the theory of Ramanujan's function τ(n) and similar arithmetical functions, Proc. Cambridge Philos. Soc. 35 (1939), 351–356, doi:10.1017/S0305004100021095.
