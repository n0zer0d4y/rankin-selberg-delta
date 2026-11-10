import RankinSelbergDelta.CuspForm.NormalizedDelta
import RankinSelbergDelta.RankinSelberg.RSPole
import RankinSelbergDelta.RankinSelberg.RSZeroFree
import RankinSelbergDelta.RankinSelberg.ExplicitFormulaSmooth
import RankinSelbergDelta.RankinSelberg.ZeroSum

/-!
# The main theorems, specialised to the modular discriminant

The library proves its results for a level-one Hecke eigenform `f` of weight `k`. This file states
them for the normalised discriminant `fΔ = Δ/1728`, whose `q`-coefficients are Ramanujan's `τ(n)`.
Every hypothesis on the form is discharged: `fΔ` is a Hecke eigenform
(`isHeckeEigenCoeffs_rsCoeff_fΔ`), has real coefficients (`hreal_fΔ`) and is nonzero (`fΔ_ne_zero`).

With `G(s) = ζ(2s) · Σ τ(n)² n^{-(s+11)}`, the Rankin–Selberg square of `Δ` (`Gfull 12 fΔ`, equal
to `ζ(s) L(sym² Δ, s)` after normalisation):

* `rankinSelberg_pole_Delta`: `D(w) = Σ |τ(n)|² n^{-w}` has a simple pole at `w = 12` with positive
  residue, approached along the real axis.
* `Lfunction_ne_zero_Delta` (in `CuspForm/NormalizedDelta.lean`): `L(Δ, 1 + it) ≠ 0` for real `t ≠ 0`.
* `zero_free_region_Delta`: a de la Vallée Poussin zero-free region for `G`.
* `explicit_formula_Delta`: the Weil explicit formula for `G`, as a series over all zeros, for
  smooth compactly supported test functions.
-/

open Complex Filter Topology MeasureTheory
open scoped ContDiff Modular

namespace RankinSelbergDelta.Delta

open RankinSelbergDelta.RankinSelberg RankinSelbergDelta.Hecke RankinSelbergDelta.Eisenstein

noncomputable section

/-- The normalised discriminant is not the zero function. -/
theorem fΔ_ne_zero : (⇑fΔ : UpperHalfPlane → ℂ) ≠ 0 := by
  intro h
  apply RankinSelbergDelta.CuspForm.Δ_ne_zero
  funext z
  have hz : (1 / 1728 : ℂ) * RankinSelbergDelta.CuspForm.Δ z = 0 := congrFun h z
  rcases mul_eq_zero.mp hz with h0 | h0
  · norm_num at h0
  · simpa using h0

/-- **The Rankin–Selberg pole for `Δ`.** The Dirichlet series `D(w) = Σ |a(n)|² n^{-w}` of the
normalised discriminant agrees with its continuation `rsDcont` for `w > 13`, and
`(w − 12) · rsDcont(w)` tends, as `w → 12⁺` along the reals, to the positive number
`(4π)^{12}/Γ(12) · (3/π) ∫_𝒟 y^{12} |fΔ|²`. -/
theorem rankinSelberg_pole_Delta :
    (∀ σ : ℝ, ((12 : ℤ) : ℝ) + 1 < σ → (rsDcont 12 fΔ σ : ℂ) = rsD fΔ (σ : ℂ)) ∧
    Tendsto (fun σ : ℝ => (σ - ((12 : ℤ) : ℝ)) * rsDcont 12 fΔ σ) (𝓝[>] ((12 : ℤ) : ℝ))
      (𝓝 ((4 * Real.pi) ^ (12 : ℤ) / Real.Gamma ((12 : ℤ) : ℝ) *
        (3 / Real.pi * ∫ z in (𝒟 : Set UpperHalfPlane), phi 12 fΔ z))) ∧
    0 < (4 * Real.pi) ^ (12 : ℤ) / Real.Gamma ((12 : ℤ) : ℝ) *
        (3 / Real.pi * ∫ z in (𝒟 : Set UpperHalfPlane), phi 12 fΔ z) :=
  rsD_simplePole 12 fΔ (by norm_num) fΔ_ne_zero

/-- **A zero-free region for the Rankin–Selberg square of `Δ`.** There are constants `C > 0` and
`t₀ ≥ 3` such that every zero `β + iγ` of `G = Gfull 12 fΔ` with `3/4 < β < 1` and `|γ| ≥ t₀`
satisfies `β ≤ 1 − 1/(160 C log |γ|)`. -/
theorem zero_free_region_Delta :
    ∃ C t₀ : ℝ, 0 < C ∧ 3 ≤ t₀ ∧ ∀ β γ : ℝ, 3 / 4 < β → β < 1 → t₀ ≤ |γ| →
      Gfull 12 fΔ ((β : ℂ) + Complex.I * γ) = 0 →
      β ≤ 1 - 1 / (20 * (8 * C) * Real.log |γ|) :=
  rs_zero_free_region 12 fΔ (by norm_num) isHeckeEigenCoeffs_rsCoeff_fΔ

/-- **The explicit formula for the Rankin–Selberg square of `Δ`.** For `1 < σ < 2` and a smooth
compactly supported `g : ℝ → ℂ`, the sum of `ĝ` over the zeros of the entire function
`rsHent 12 fΔ = (s − 1) G(s)` in the strip `1 − σ ≤ Re s ≤ σ`, counted with multiplicity by the
divisor, converges and equals `ĝ(1)` minus the two prime sums `Σ Λ_G(n) g(log n)` and
`Σ Λ_G(n) g(−log n)/n`, minus the archimedean integral. -/
theorem explicit_formula_Delta {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ < 2) (g : ℝ → ℂ)
    (hg : ContDiff ℝ ∞ g) (hgs : HasCompactSupport g) :
    ∑' u, ((MeromorphicOn.divisor (rsHent 12 fΔ) (ZeroSum.strip σ)) u : ℂ) * ghat g u
      = ghat g 1
        - ∑' n, (if 2 ≤ n then (rsVonMangoldt (rsCoeff fΔ) 12 n : ℂ) * g (Real.log n) else 0)
        - ∑' n, (if 2 ≤ n then (rsVonMangoldt (rsCoeff fΔ) 12 n : ℂ) * (g (-(Real.log n)) / n)
            else 0)
        - (1 / (2 * Real.pi)) * ∫ t : ℝ, (logDeriv (rsPre 12) ((σ : ℂ) - t * Complex.I)
            + logDeriv (rsPre 12) (((1 - σ : ℝ) : ℂ) + t * Complex.I))
            * ghat g (((1 - σ : ℝ) : ℂ) + t * Complex.I) :=
  explicitFormula_Gfull_tsum_of_smooth 12 fΔ (by norm_num) isHeckeEigenCoeffs_rsCoeff_fΔ hσ1 hσ2 g
    hg hgs

/-- Witness that the hypotheses of `explicit_formula_Delta` can all hold, with a test function that
is not identically zero: `σ = 3/2` and a smooth bump `g` with `g 0 = 1`. -/
theorem explicit_formula_Delta_hyps_satisfiable :
    ∃ (σ : ℝ) (g : ℝ → ℂ), 1 < σ ∧ σ < 2 ∧ ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ g 0 = 1 :=
  explicitFormula_Gfull_tsum_hyps_satisfiable

end

end RankinSelbergDelta.Delta
