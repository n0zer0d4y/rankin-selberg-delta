# Verification

## Rigor grades

Each paper folder has a `claims.md` with one row per claim: the exact statement, its rigor grade, the Lean declaration it rests on, and notes. Under `## Reasoning` it gives the argument for each row.

| Grade       | Meaning                                                                                                             | How to check it                                          |
| ----------- | ------------------------------------------------------------------------------------------------------------------- | -------------------------------------------------------- |
| proved      | a Lean 4 theorem, kernel-checked, depending only on the standard axioms `propext`, `Classical.choice`, `Quot.sound` | `cd lean && lake build && lake env lean AxiomCheck.lean` |
| reference   | a published result                                                                                                  | the cited paper                                          |
| conjectural | a written argument that is not formalised                                                                           | read the argument; independent review is welcome         |

This repository contains no numerical certificates. Every claim graded `proved` is a Lean theorem.

## What the Lean statements say, and what they do not

A Lean theorem is only as good as its statement. The points a reader should check are listed here, and again in each `claims.md`.

- **The objects are defined from scratch** and do not reuse Mathlib's L-function of a modular form.
  - `rsCoeff f n` is the `n`-th `q`-coefficient of `f`, read off Mathlib's `qExpansion`.
  - The L-functions (`Lfun`, `Gfull`, `rsD`) and the entire function `rsHent` are defined in this library, and the main theorems are about these definitions. They are stated against Mathlib's `CuspForm`, `qExpansion`, `riemannZeta` and `Complex.Gamma`.
- **The modular discriminant is Mathlib-independent too.** `RankinSelbergDelta.CuspForm.Δ` is defined in this library as `E₄³ − E₆²`, using Mathlib's Eisenstein series, and `fΔ = Δ/1728` is its normalisation with `a(1) = 1`.
- **The Hecke-eigenform property is an explicit structure, not an assumption.** For a general form `f`, the main theorems take `IsHeckeEigenCoeffs (rsCoeff f) k` as a hypothesis: multiplicativity and the prime-power recursion of the coefficients. For `fΔ` this hypothesis is proved, from the Hecke operators of level one (`CuspForm/HeckeOperator.lean`, `CuspForm/DeltaHeckeEigenform.lean`). Ramanujan's bound `|τ(p)| ≤ 2p^{11/2}` (Deligne) is not used anywhere.
- **The Rankin–Selberg pole is stated along the real axis.**
  - `rsD_simplePole` says that `rsDcont`, a real-valued continuation of `D(σ)` for real `σ`, agrees with `D` for `σ > k + 1` and that `(σ − k) · rsDcont(σ)` has a positive limit as `σ → k⁺`.
  - The complex continuation is stated separately.
    - `rsD_continuation`: G(s) = ζ(2s) D(s + k − 1) continues holomorphically to the strip 0 < Re s < 9/4 minus s = 1, with a simple pole at s = 1.
    - Globally, `rsHent` is an entire function with `rsHent(s) = (s − 1) G(s)` (`rsHent_eq`). It is what the explicit formula uses.
- **The zero-free region has an inexplicit constant.** `rs_zero_free_region` gives some `C > 0` and `t₀ ≥ 3`; their values are not computed.
- **The explicit formula counts zeros through Mathlib's divisor.** The sum over zeros is weighted by `MeromorphicOn.divisor (rsHent k f)`, on a rectangle in the finite version and on the strip `1 − σ ≤ Re s ≤ σ` in the series version, so zeros are counted with multiplicity, and the pole of `G` at `s = 1` is absorbed by the factor `s − 1`.

## Review

- **The Lean library** is checked by the Lean kernel; `AxiomCheck.lean` lists the axioms of every theorem cited in a `claims.md`.
- **An automated audit of the released files.** All 50 modules of `lean/RankinSelbergDelta/`, exactly as released, were audited theorem by theorem: 901 theorems, every one depending only on `propext`, `Classical.choice` and `Quot.sound`, with no declared axioms. Each theorem was also run through probes that look for hypotheses that contradict each other, a conclusion that is `True` or one of its own hypotheses, or an existential met by a trivial constant; none fired. Probes can detect vacuity but cannot rule it out.
- **Witnesses.** Every main theorem about cusp forms has a named witness that its hypotheses can be met, and the headline theorems are also stated for Δ with no remaining hypothesis.
- **Two agents.** Ten of the 50 modules were written by one agent of the research system and then rebuilt and audited by the other before they were kept; the other 40 were written by the second agent. The statements were not reviewed adversarially line by line.
- **Human review.** No human expert has reviewed the formalisation yet.
