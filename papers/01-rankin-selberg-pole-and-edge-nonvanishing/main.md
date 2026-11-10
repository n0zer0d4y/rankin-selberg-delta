---
title: "The Rankin–Selberg pole and L(Δ, 1 + it) ≠ 0, formalised in Lean 4"
authors: ["Nozero Day"]
note: "Produced autonomously by AI agents running inside a custom research harness; see the repository README. Unrefereed."
status: draft
date: "2026-11-10"
---

# The Rankin–Selberg pole and L(Δ, 1 + it) ≠ 0, formalised in Lean 4

## Summary

**The mathematics is classical.** Rankin [Ra39] and Selberg [Se40] showed that for a cusp form f of weight k on SL₂(ℤ), with Fourier coefficients a(n), the Dirichlet series

  D(w) = Σ\_{n≥1} |a(n)|² n^{−w}

continues meromorphically past its abscissa of absolute convergence w = k and has a simple pole there, with residue proportional to the Petersson norm of f. The method unfolds the integral of y^k |f|² against the real-analytic Eisenstein series E(z, s). The same Rankin–Selberg square, combined with the positivity argument of de la Vallée Poussin, shows that the L-function of a Hecke eigenform does not vanish on the line Re s = 1. These are textbook results (see [IK04]).

**What is new is the formalisation.** This repository proves both statements in Lean 4 with Mathlib, from definitions, with no axioms beyond the standard three. Applied to the modular discriminant Δ, it gives:

- **The Rankin–Selberg pole for Δ** (`rankinSelberg_pole_Delta`). With a(n) = τ(n), the series D(w) = Σ τ(n)² n^{−w} has a simple pole at w = 12 with positive residue (4π)¹²/Γ(12) · (3/π) ∫\_𝒟 y¹² |Δ/1728|² dμ, approached along the real axis.
- **The edge nonvanishing for Δ** (`Lfunction_ne_zero_Delta`). L(Δ, 1 + it) ≠ 0 for every real t ≠ 0, where L(Δ, w) = Σ τ(n) n^{−(w + 11/2)} continued to an entire function.

Both are instances of general theorems for a level-one cusp form f of weight k > 0: `rsD_simplePole` for any nonzero f, and `Lfunction_ne_zero_on_one_line` for a Hecke eigenform with real coefficients. The Hecke-eigenform property of Δ, which Mathlib does not have, is proved in the library from the Hecke operators of level one.

## The formal statements

The general pole theorem (`RankinSelbergDelta/RankinSelberg/RSPole.lean`):

```lean
theorem rsD_simplePole (f : F) (hk : 0 < k) (hf : (⇑f : ℍ → ℂ) ≠ 0) :
    (∀ σ : ℝ, (k : ℝ) + 1 < σ → (rsDcont k f σ : ℂ) = rsD f (σ : ℂ)) ∧
    Tendsto (fun σ : ℝ => (σ - k) * rsDcont k f σ) (𝓝[>] (k : ℝ))
      (𝓝 ((4 * Real.pi) ^ k / Real.Gamma k * (3 / Real.pi * ∫ z in (𝒟 : Set ℍ), phi k f z))) ∧
    0 < (4 * Real.pi) ^ k / Real.Gamma k * (3 / Real.pi * ∫ z in (𝒟 : Set ℍ), phi k f z)
```

Here `f` ranges over a type `F` with a `CuspFormClass` instance for the level-one group, `rsD f w` is the Dirichlet series D(w), `rsDcont k f` is its continuation to real σ near k, `phi k f z = |f(z)|² (Im z)^k`, and `𝒟` is Mathlib's standard fundamental domain of SL₂(ℤ).

The general edge nonvanishing (`RankinSelbergDelta/RankinSelberg/EdgeNonvanishing.lean`):

```lean
theorem Lfunction_ne_zero_on_one_line (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k)
    (hreal : ∀ n, (starRingEnd ℂ) (rsCoeff f n) = rsCoeff f n) {t : ℝ} (ht : t ≠ 0) :
    Lfun k f hk (1 + Complex.I * t) ≠ 0
```

`IsHeckeEigenCoeffs a k` says that a(0) = 0, a(1) = 1, a is multiplicative on coprime arguments, and a(p^{r+2}) = a(p) a(p^{r+1}) − p^{k−1} a(p^r) for primes p. `Lfun k f hk` is the entire function obtained from the completed L-function of f; for Re w > 1 it equals Σ a(n) n^{−(w + (k−1)/2)} (`Lfun_eq_rsL`).

The Δ versions (`RankinSelbergDelta/CuspForm/NormalizedDelta.lean`, `RankinSelbergDelta/Delta.lean`) apply these to `fΔ = Δ/1728`, where `Δ = E₄³ − E₆²` is built from Mathlib's Eisenstein series, and discharge every hypothesis: `isHeckeEigenCoeffs_rsCoeff_fΔ`, `hreal_fΔ` and `fΔ_ne_zero`.

## Proof outline

**1. The fundamental domain and the hyperbolic measure** (`Eisenstein/HyperbolicMeasure.lean`, `Eisenstein/FundamentalDomain.lean`). The invariant measure dx dy/y² on the upper half-plane is set up, and Mathlib's `𝒟` is shown to be a measure-theoretic fundamental domain for PSL₂(ℤ) (`isFundamentalDomain_fd`).

**2. The real-analytic Eisenstein series** (`Eisenstein/EpsteinZeta.lean`, `Eisenstein/EpsteinTheta.lean`, `Eisenstein/EisensteinCosets.lean`). E(z, s) is written as a sum over cosets of the stabiliser of ∞ and as an Epstein zeta function of the lattice ℤ + zℤ. Its theta-function representation gives the continuation and the simple pole at s = 1, with residue 3/π, through Mathlib's `WeakFEPair`.

**3. Unfolding** (`Eisenstein/Unfolding.lean`, `RankinSelberg/MellinPole.lean`, `RankinSelberg/MeanSquare.lean`). The integral of y^k |f|² E(z, s) over 𝒟 unfolds to an integral over the strip 0 ≤ x ≤ 1, y > 0 (`unfolding_integral_eisensteinE`). The x-integral picks out Σ |a(n)|² e^{−4πny} (`integral_sq_eq_tsum`), and the y-integral is a Mellin transform, Γ(w)/(4π)^w · D(w) (`rsMellin_eq`).

**4. The pole** (`RankinSelberg/RSPole.lean`). Combining 2 and 3, (σ − k) D(σ) tends to (4π)^k/Γ(k) times the residue 3/π of E times ∫\_𝒟 y^k |f|² dμ. That integral is positive when f ≠ 0 (`rsD_simplePole`).

**5. The Hecke eigenform Δ** (`CuspForm/Discriminant.lean`, `CuspForm/HeckeOperator.lean`, `CuspForm/DeltaHeckeEigenform.lean`, `RankinSelberg/HeckeMultiplicativity.lean`).
- Δ is defined as E₄³ − E₆² and shown to be a nonzero cusp form.
- The Hecke operators T\_p of level one are defined on modular forms, with their action on q-expansions.
- Every level-one cusp form of weight 12 is a constant multiple of η²⁴ (`exists_eq_mul_η24`), and so is Δ. Since T\_p maps cusp forms to cusp forms, T\_p Δ is a multiple of Δ for every prime p (`heckeT_Delta_eq_smul`).
- The eigenvalue relations give IsHeckeEigenCoeffs for the normalised coefficients τ(n).

**6. The Rankin–Selberg square and its nonvanishing on Re s = 1** (`RankinSelberg/HeckeEuler.lean`, `RankinSelberg/EulerProduct.lean`, `RankinSelberg/TRS.lean`, `RankinSelberg/TRSInputs.lean`, `RankinSelberg/SimplePole.lean`).
- G(s) = ζ(2s) D(s + k − 1) has an Euler product whose logarithmic coefficients Λ\_G(p^m) = |α\_p^m + β\_p^m|² log p are nonnegative, with α\_p, β\_p the Satake parameters.
- G continues holomorphically to the strip 0 < Re s < 9/4 minus s = 1, with a simple pole at s = 1 (`rsD_continuation`, `SimplePole.lean`).
- The de la Vallée Poussin 3-4-1 inequality then gives G(1 + iy) ≠ 0 for y ≠ 0 (`rs_square_ne_zero`, through the abstract `trs_ne_zero`).

**7. The edge nonvanishing** (`RankinSelberg/EdgeNonvanishing.lean`).
- For σ > 1 and real coefficients, ζ(σ) L(σ+it)² L(σ−it)² G(σ+2it) G(σ)² G(σ−2it) is the exponential of a series with nonnegative terms. So its modulus is at least 1 (`one_le_norm_isoProduct`).
- If L(1 + it) = 0, the four L-factors vanish to total order 4 at σ = 1, against poles of order 1 from ζ and 2 from G(σ)², while G(1 ± 2it) is finite and nonzero by step 6. The product would tend to 0, a contradiction.

## Scope and limits

- **The residue limit is taken along the real axis.**
  - `rsD_simplePole` concerns `rsDcont`, a real-valued continuation of D on real σ, and its limit as σ → k⁺.
  - The complex continuation is a separate theorem, `rsD_continuation`. The function `rsG`, equal to G(s) = ζ(2s) D(s + k − 1) for 1 < Re s < 9/4, is holomorphic on 0 < Re s < 9/4 except at s = 1, and (s − 1) rsG(s) has a limit as s → 1 in ℂ. So D continues meromorphically to k − 1 < Re w < k + 5/4, with its only pole at w = k.
  - The global continuation is the entire function `rsHent(s) = (s − 1) G(s)` of paper 3 (`rsHent_eq`).
- **Ramanujan's bound is not used.** Deligne's bound |τ(p)| ≤ 2p^{11/2} enters nowhere; the arguments use only the Hecke relations and Rankin's mean-square bound.
- **The L-function is the library's own.** `Lfun` and `completedLSeries` are defined in `CuspForm/LSeries.lean`. Mathlib master now contains an independent L-function of a modular form (Loeffler), which this repository does not use; the two have not been proved equal.
- **Not new mathematics.** The results are classical. The contribution is a complete, kernel-checked formalisation that runs from the definition of Δ to these statements.

## References

- [Ra39] R. A. Rankin, Contributions to the theory of Ramanujan's function τ(n) and similar arithmetical functions, Proc. Cambridge Philos. Soc. 35 (1939), 351–356, doi:10.1017/S0305004100021095.
- [Se40] A. Selberg, Bemerkungen über eine Dirichletsche Reihe, die mit der Theorie der Modulformen nahe verbunden ist, Arch. Math. Naturvid. 43, no. 4 (1940), 1–4.
- [IK04] H. Iwaniec, E. Kowalski, Analytic Number Theory, AMS Colloquium Publications 53 (2004), doi:10.1090/coll/053.
