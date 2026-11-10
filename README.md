# rankin-selberg-delta

[![proofmap: browse the Lean proofs](https://img.shields.io/badge/proofmap-browse_the_Lean_proofs-1e7b45?logo=data:image/svg%2bxml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHZpZXdCb3g9IjAgMCAzMiAzMiI+PHBhdGggZD0iTTcgMTZoN00xOCA5aDdNMTggMjNoN00xNCAxNmw0LTdNMTQgMTZsNCA3IiBzdHJva2U9IndoaXRlIiBzdHJva2Utd2lkdGg9IjIuNSIgc3Ryb2tlLWxpbmVjYXA9InJvdW5kIiBmaWxsPSJub25lIi8+PC9zdmc+)](https://n0zer0d4y.github.io/rankin-selberg-delta/lean/proofmap.html)
[![Lean 4](https://img.shields.io/badge/Lean_4-v4.28.0_%2B_Mathlib-blue)](lean/lean-toolchain)

The Rankin–Selberg method for level-one cusp forms, formalised in Lean 4 with Mathlib, from the modular discriminant Δ = E₄³ − E₆² to the explicit formula. The library proves three classical results for every level-one Hecke eigenform and states each of them for Δ with every hypothesis discharged. The mathematics is textbook material; what is new is that the whole chain is machine-checked. You can [browse it as an interactive proof map](#browsing-the-lean-proofs).

> **Status: unrefereed.** This library was produced autonomously by AI agents running inside a custom research harness; a human set the goals and decided what to publish. No human expert has reviewed it yet; such review is very welcome. The theorems are classical; the claim is about the formalisation. Searches in November 2026 found no other Lean formalisation of the Rankin–Selberg continuation, of L(f, 1 + it) ≠ 0 for a modular form, or of the zero-free region and explicit formula below. That is evidence of novelty, not proof of it; see [Prior art](#prior-art).

## The three results

Throughout, f is a level-one cusp form of weight k with q-coefficients a(n), D(w) = Σ |a(n)|² n^{−w} is its Rankin–Selberg Dirichlet series, and G(s) = ζ(2s) D(s + k − 1) is its Rankin–Selberg square. For Δ, after normalising the coefficients, G(s) is ζ(s) L(sym² Δ, s).

### 1. The Rankin–Selberg pole, and L(f, 1 + it) ≠ 0

[`papers/01-rankin-selberg-pole-and-edge-nonvanishing/`](papers/01-rankin-selberg-pole-and-edge-nonvanishing/main.md)

- **The question.** Rankin (1939) and Selberg (1940) showed that D(w) continues past w = k with a simple pole there, whose residue is a positive multiple of the Petersson norm of f. Combined with de la Vallée Poussin's positivity argument, the same square shows that L(f, s) does not vanish on Re s = 1.
- **The answer, in Lean.**
  - `rsD_simplePole`: for f ≠ 0, D(σ) continues to real σ near k (`rsDcont`), and (σ − k) times this continuation tends to (4π)^k / Γ(k) · (3/π) ∫\_𝒟 y^k |f|² dμ > 0 as σ → k⁺.
  - `rsD_continuation`: G continues holomorphically to 0 < Re s < 9/4, except for a simple pole at s = 1.
  - `Lfunction_ne_zero_on_one_line`: L(f, 1 + it) ≠ 0 for a Hecke eigenform f with real coefficients and every real t ≠ 0.
  - For Δ: `rankinSelberg_pole_Delta` and `Lfunction_ne_zero_Delta`, with no remaining hypothesis.
- **The method.** The real-analytic Eisenstein series E(z, s) is built as an Epstein zeta function, with its pole at s = 1 from the theta functional equation. The Rankin–Selberg integral is unfolded over the fundamental domain. For the nonvanishing, an isobaric product of ζ, L(f, ·) and G has a logarithm with nonnegative coefficients.
- **Rigor.** Proved in Lean 4, depending only on the standard axioms. The Hecke-eigenform property of Δ is proved in the library from level-one Hecke operators; that part is not new in Lean (see [Prior art](#prior-art)).

### 2. A zero-free region for the Rankin–Selberg square

[`papers/02-zero-free-region/`](papers/02-zero-free-region/main.md)

- **The question.** The classical de la Vallée Poussin region for G, the Rankin–Selberg square of a Hecke eigenform.
- **The answer, in Lean.** `rs_zero_free_region`: there are C > 0 and t₀ ≥ 3 such that every zero β + iγ of G with 3/4 < β < 1 and |γ| ≥ t₀ satisfies β ≤ 1 − 1/(160 C log |γ|). For Δ: `zero_free_region_Delta`.
- **The method.** The 3-4-1 inequality for −G′/G, whose coefficients Λ\_G(p^m) = |α\_p^m + β\_p^m|² log p are nonnegative. Then the Borel–Carathéodory inequality, Davenport's local expansion of G′/G, and growth bounds in vertical strips that rest on Gamma bounds proved without Stirling's formula.
- **Rigor.** Proved in Lean 4. The constants C and t₀ are existential; they are not computed.

### 3. The explicit formula

[`papers/03-explicit-formula/`](papers/03-explicit-formula/main.md)

- **The question.** Weil's explicit formula for G, relating its zeros to its prime-power coefficients Λ\_G(n).
- **The answer, in Lean.**
  - `rsHent`: the entire function (s − 1) G(s).
  - `exists_wcount_zeros_rsHent_le_mul_log`: in a vertical band, its zeros with 1 ≤ |Im s| ≤ T number O(T log T), with multiplicity.
  - `explicitFormula_Gfull_tsum_of_smooth`: for every smooth compactly supported test function g, the sum of ĝ over all zeros in the strip 1 − σ ≤ Re s ≤ σ (for any 1 < σ < 2) converges absolutely (`summable_norm_zeroSum_Gfull`) and equals ĝ(1) minus two prime sums minus an archimedean integral. `explicitFormula_Gfull_tsum` gives the same under weaker hypotheses on g.
  - For Δ: `explicit_formula_Delta`.
- **The method.** The argument principle on rectangles, with the right edge through Laplace inversion and the left edge through the functional equation. The horizontal edges are taken at heights chosen to avoid the zeros. The full series converges by Jensen's formula and Abel summation.
- **Rigor.** Proved in Lean 4. Zeros are counted through Mathlib's `MeromorphicOn.divisor`.

The library also contains Hurwitz's theorem in zero-locus form (`Shared/HurwitzZeroLocus.lean`), which no other Lean library we found has.

## How these results were produced

The research was carried out autonomously by AI agents running inside a custom research harness. The proofs are written in Lean 4 with Mathlib and checked by the Lean kernel. What the system adds is discipline about evidence:

- **Every claim is tied to a Lean theorem.** Each claim in a paper names the declaration it rests on, and the axioms of every such declaration are listed by [`lean/AxiomCheck.lean`](lean/AxiomCheck.lean).
- **Every claim carries a rigor grade** (see [`docs/verification.md`](docs/verification.md)): proved in Lean, cited, or conjectural.
- **Statements are checked for vacuity.** Every main theorem about cusp forms has a named witness showing that its hypotheses can all hold, and the headline theorems are also stated for Δ with no remaining hypothesis. All 50 modules, exactly as released, were also run through an automated audit: each of their 901 theorems depends only on the standard axioms, and none was flagged by probes that look for contradictory hypotheses, a conclusion that is `True` or one of its own hypotheses, or an existential met by a trivial constant. Such probes can detect vacuity but cannot rule it out; the witnesses do that for the main theorems.
- **Two agents wrote the library.** Ten of the 50 modules were written by one agent and then rebuilt and audited by the other before they were kept; the other 40 were written by the second agent.
- **Work persists across sessions** through a research memory that links each fact to the evidence behind it.

A human set the research goals and decided what to publish; the system chose the specific problems and carried out the work.

## Repository layout

```
papers/                       one folder per result
  01-.../ 02-.../ 03-.../     main.md (the paper), claims.md (each claim with its Lean declaration and rigor grade)
lean/                         Lake package RankinSelbergDelta (Lean 4 + Mathlib), and proofmap.html, its interactive proof map (settings in proofmap.toml)
  RankinSelbergDelta/
    CuspForm/                 Δ = E₄³ − E₆², level-one Hecke operators, Δ as a Hecke eigenform, the L-function of a cusp form
    Eisenstein/               the hyperbolic measure, the fundamental domain, Epstein zeta, the real-analytic Eisenstein series, unfolding
    RankinSelberg/            the pole, the continuation, the Euler product, nonvanishing on Re s = 1, the zero-free region, the explicit formula, the self-dual Weil form
    Analysis/ Continuation/ Shared/   supporting analysis: Paley–Wiener tails, the residue of ζ, Hurwitz's theorem, the 3-4-1 inequality
    Delta.lean                the main theorems specialised to Δ
docs/                         reproducing.md, verification.md
```

## Reproducing

[`docs/reproducing.md`](docs/reproducing.md) gives the details. In brief:

```
cd lean && lake exe cache get && lake build && lake env lean AxiomCheck.lean
```

`AxiomCheck.lean` prints the axioms of every theorem cited in a `claims.md`; each should be among `propext`, `Classical.choice` and `Quot.sound`. To regenerate the proof map, install [proofmap](https://github.com/n0zer0d4y/proofmap) and run `proofmap build` in `lean/`.

## How much to trust each claim

Every claim carries a rigor grade in its paper's `claims.md`; see [`docs/verification.md`](docs/verification.md).

- **proved:** a Lean theorem, kernel-checked, depending only on `propext`, `Classical.choice` and `Quot.sound`. Every claim in the three papers is in this class.
- **reference:** a published result.
- **conjectural:** a written argument that is not formalised. None of the claims is in this class.

A Lean theorem is only as good as its statement. [`docs/verification.md`](docs/verification.md) lists what the statements say and do not say: for example, the pole of `rsD_simplePole` is approached along the real axis, the L-function is the library's own rather than Mathlib's, and the zero-free constant is not explicit.

## Browsing the Lean proofs

**[Open the proof map](https://n0zer0d4y.github.io/rankin-selberg-delta/lean/proofmap.html)** to review the Lean library in your browser, without installing Lean. The page was generated from the compiled library by [proofmap](https://github.com/n0zer0d4y/proofmap). It shows:

- **Map:** the main theorems and the lemmas and definitions they rest on.
- **Outline:** the formalisation as a table of contents, with each result's docstring.
- **Health:** a check that nothing depends on `sorry` or on an axiom outside `propext`, `Classical.choice` and `Quot.sound`. This is the same check as `AxiomCheck.lean`, extended to every declaration.
- **Path finder:** how a given definition reaches a given theorem.

Each declaration shows its statement and source, with a link to its lines here on GitHub. The page is a single offline file, [`lean/proofmap.html`](lean/proofmap.html). To read it offline, download it and open it in any browser; it loads nothing from the network.

## Prior art

Lean formalisations checked (November 2026):

- **Mathlib.** This library uses Mathlib's Dedekind η function (`ModularForm.eta`) to prove that its own Δ = E₄³ − E₆² is a constant multiple of η²⁴. Mathlib master (newer than the v4.28.0 used here) also defines Δ as η²⁴ (C. Birkbeck, `Mathlib/NumberTheory/ModularForms/Discriminant.lean`) and the L-function of a modular form with its functional equation (D. Loeffler, `Mathlib/NumberTheory/ModularForms/LFunction.lean`). This library uses neither: its Δ and its L-function are defined independently, and they have not been proved equal to Mathlib's.
- **D. Loeffler, M. Stoll**, "Formalizing zeta and L-functions in Lean", arXiv:2503.00959, doi:10.46298/afm.15328: ζ and Dirichlet L-functions in Mathlib, with Dirichlet's theorem on primes in arithmetic progressions. The abstract nonvanishing theorem `trs_ne_zero` of this library generalises the de la Vallée Poussin argument Mathlib uses for them.
- **C. Birkbeck et al., LeanModularForms** (`hecke-ring` branch): Hecke operators and Hecke rings, eigenforms and newforms, multiplicativity of coefficients, the Petersson inner product with a fundamental-domain tiling, and L-functions of modular forms. **The Hecke-operator part of this library, and the proof that Δ is a Hecke eigenform, are not new in Lean.**
- **MathProof**, Zenodo doi:10.5281/zenodo.23636675: τ(n) as the q-coefficients of Δ, Ramanujan's congruence τ(n) ≡ σ₁₁(n) mod 691, and τ(n) ≠ 0 for n ≤ 65536.
- **PrimeNumberTheoremAnd** (A. Kontorovich, T. Tao et al.): explicit estimates and zero-free regions for ζ; no modular-form or Rankin–Selberg material.

None of these contains real-analytic Eisenstein series with unfolding, the Rankin–Selberg continuation of Σ |a(n)|² n^{−s}, L(f, 1 + it) ≠ 0 for a modular form f, a zero-free region or an explicit formula for a degree-4 L-function, or Hurwitz's theorem.

Classical sources:

- R. A. Rankin, Contributions to the theory of Ramanujan's function τ(n) and similar arithmetical functions, Proc. Cambridge Philos. Soc. 35 (1939), 351–356, doi:10.1017/S0305004100021095;
- A. Selberg, Bemerkungen über eine Dirichletsche Reihe, die mit der Theorie der Modulformen nahe verbunden ist, Arch. Math. Naturvid. 43, no. 4 (1940), 1–4;
- A. Weil, Sur les "formules explicites" de la théorie des nombres premiers (1952); reprinted in Œuvres Scientifiques / Collected Papers, Springer (1979), 570–583, doi:10.1007/978-1-4757-1705-1_60;
- H. Davenport, Multiplicative Number Theory, 3rd ed., revised by H. L. Montgomery, Graduate Texts in Mathematics 74, Springer (2000);
- H. Iwaniec, E. Kowalski, Analytic Number Theory, AMS Colloquium Publications 53 (2004), doi:10.1090/coll/053.

Not yet checked: the Lean Zulip archive in depth, and the FLT project (which works with quaternionic automorphic forms).

## License

Code (`lean/`): MIT, see [`LICENSE`](LICENSE). Papers and documentation: CC BY 4.0, see [`LICENSE-docs`](LICENSE-docs).

## Citation

See [`CITATION.cff`](CITATION.cff).
