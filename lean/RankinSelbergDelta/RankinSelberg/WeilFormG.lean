import RankinSelbergDelta.RankinSelberg.ArchimedeanKernel
import RankinSelbergDelta.RankinSelberg.WeilForm

/-!
# The self-dual Weil form of `G`

`weilForm_Gfull`: the explicit formula applied to `h = g ⋆ g♯`. And
`weilForm_Gfull_nonneg_of_line`: if every zero of `G` lies on the critical line, the zero side is
nonnegative.
-/

open MeasureTheory Filter
open scoped NNReal MatrixGroups Pointwise

noncomputable section

namespace RankinSelbergDelta.RankinSelberg

open Complex UpperHalfPlane MeasureTheory Set Filter RankinSelbergDelta.Eisenstein RankinSelbergDelta.ArgPrinciple
open scoped Real Topology Modular FourierTransform ComplexConjugate

variable {F : Type*} [FunLike F ℍ ℂ] (k : ℤ)
  [cf : CuspFormClass F (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma 1)) k]

/-- The Weil-form `ghat` agrees with `RankinSelbergDelta.RankinSelberg.ghat`. -/
lemma WeilForm.ghat_eq (g : ℝ → ℂ) : WeilForm.ghat g = ghat g := rfl

include cf in
/-- **The self-dual Weil form of `G`**: `explicitFormula_Gfull` applied to
`h = g ⋆ g♯` (`WeilForm.selfDual g`), with `ĥ(u) = ĝ(u) · conj(ĝ(1 − conj u))` on the zero side and
`ĥ(1) = ĝ(1) · conj(ĝ(0))` in the pole term. The hypotheses are those of `explicitFormula_Gfull`
for `h` (continuity of `h` is derived; the Laplace-inversion, decay and archimedean-integrability
hypotheses are carried, as for any test function). Support: `supp g ⊆ [−L, L]` gives
`supp h ⊆ [−2L, 2L]`, so the prime terms present are those with `log n ≤ 2L`. -/
theorem weilForm_Gfull (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k) {σ : ℝ}
    (hσ1 : 1 < σ) (hσ2 : σ < 2) (g : ℝ → ℂ) (hc : Continuous g) (hs : HasCompactSupport g)
    (hga : ∀ s : ℂ, AnalyticAt ℂ (ghat (WeilForm.selfDual g)) s)
    (hg : Integrable (fun x : ℝ => WeilForm.selfDual g x * Complex.exp (σ * x)))
    (hF : Integrable (𝓕 (fun x : ℝ => WeilForm.selfDual g x * Complex.exp (σ * x))))
    (hg' : Integrable (fun x : ℝ => WeilForm.selfDual g (-x) * Complex.exp (-(x : ℂ))
      * Complex.exp (σ * x)))
    (hF' : Integrable (𝓕 (fun x : ℝ => WeilForm.selfDual g (-x) * Complex.exp (-(x : ℂ))
      * Complex.exp (σ * x))))
    (hdec : ∃ B : ℝ, ∀ s : ℂ, 1 - σ ≤ s.re → s.re ≤ σ → 1 ≤ |s.im| →
      ‖ghat (WeilForm.selfDual g) s‖ * s.im ^ 2 ≤ B)
    (hArch : Integrable (fun t : ℝ =>
      (logDeriv (rsPre k) ((σ : ℂ) - t * Complex.I)
          + logDeriv (rsPre k) (((1 - σ : ℝ) : ℂ) + t * Complex.I))
        * ghat (WeilForm.selfDual g) (((1 - σ : ℝ) : ℂ) + t * Complex.I))) :
    ∃ T : ℕ → ℝ, (∀ j : ℕ, (j : ℝ) ≤ T j ∧ T j ≤ j + 1) ∧
      Tendsto (fun j : ℕ => ∑ᶠ u, ((MeromorphicOn.divisor (rsHent k f)
          (closedRect ⟨1 - σ, -(T j)⟩ ⟨σ, T j⟩)) u : ℂ) * (ghat g u * conj (ghat g (1 - conj u)))) atTop
        (𝓝 (ghat g 1 * conj (ghat g 0)
          - ∑' n, (if 2 ≤ n then (rsVonMangoldt (rsCoeff f) k n : ℂ) * WeilForm.selfDual g (Real.log n)
              else 0)
          - ∑' n, (if 2 ≤ n then (rsVonMangoldt (rsCoeff f) k n : ℂ)
              * (WeilForm.selfDual g (-(Real.log n)) / n) else 0)
          - (1 / (2 * Real.pi)) * ∫ t : ℝ, (logDeriv (rsPre k) ((σ : ℂ) - t * Complex.I)
              + logDeriv (rsPre k) (((1 - σ : ℝ) : ℂ) + t * Complex.I))
              * ghat (WeilForm.selfDual g) (((1 - σ : ℝ) : ℂ) + t * Complex.I))) := by
  have hhc : Continuous (WeilForm.selfDual g) := WeilForm.continuous_selfDual g hc hs
  obtain ⟨T, hT, hlim⟩ := explicitFormula_Gfull k f hk hf hσ1 hσ2 (WeilForm.selfDual g) hhc hga
    hg hF hg' hF' hdec hArch
  refine ⟨T, hT, ?_⟩
  have hpt : ∀ u : ℂ, ghat (WeilForm.selfDual g) u = ghat g u * conj (ghat g (1 - conj u)) :=
    fun u => WeilForm.ghat_selfDual_eq g hc hs u
  have h1 : ghat (WeilForm.selfDual g) 1 = ghat g 1 * conj (ghat g 0) := by
    rw [hpt]; simp
  rw [h1] at hlim
  refine hlim.congr fun j => ?_
  refine finsum_congr fun u => ?_
  rw [hpt]

include cf in
/-- **Weil positivity for `G` follows from the Riemann hypothesis for `G`** (the easy direction, stated through the
divisor of the entire `(s − 1)G`): if every zero of the continuation lies on `Re s = 1/2`, the
arithmetic side of the self-dual Weil form is a nonnegative real number. -/
theorem weilForm_Gfull_nonneg_of_line (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k)
    {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ < 2) (g : ℝ → ℂ) (hc : Continuous g) (hs : HasCompactSupport g)
    (hga : ∀ s : ℂ, AnalyticAt ℂ (ghat (WeilForm.selfDual g)) s)
    (hg : Integrable (fun x : ℝ => WeilForm.selfDual g x * Complex.exp (σ * x)))
    (hF : Integrable (𝓕 (fun x : ℝ => WeilForm.selfDual g x * Complex.exp (σ * x))))
    (hg' : Integrable (fun x : ℝ => WeilForm.selfDual g (-x) * Complex.exp (-(x : ℂ))
      * Complex.exp (σ * x)))
    (hF' : Integrable (𝓕 (fun x : ℝ => WeilForm.selfDual g (-x) * Complex.exp (-(x : ℂ))
      * Complex.exp (σ * x))))
    (hdec : ∃ B : ℝ, ∀ s : ℂ, 1 - σ ≤ s.re → s.re ≤ σ → 1 ≤ |s.im| →
      ‖ghat (WeilForm.selfDual g) s‖ * s.im ^ 2 ≤ B)
    (hArch : Integrable (fun t : ℝ =>
      (logDeriv (rsPre k) ((σ : ℂ) - t * Complex.I)
          + logDeriv (rsPre k) (((1 - σ : ℝ) : ℂ) + t * Complex.I))
        * ghat (WeilForm.selfDual g) (((1 - σ : ℝ) : ℂ) + t * Complex.I)))
    (hline : ∀ z w u : ℂ, (MeromorphicOn.divisor (rsHent k f) (closedRect z w)) u ≠ 0 →
      u.re = 1 / 2) :
    0 ≤ (ghat g 1 * conj (ghat g 0)
          - ∑' n, (if 2 ≤ n then (rsVonMangoldt (rsCoeff f) k n : ℂ) * WeilForm.selfDual g (Real.log n)
              else 0)
          - ∑' n, (if 2 ≤ n then (rsVonMangoldt (rsCoeff f) k n : ℂ)
              * (WeilForm.selfDual g (-(Real.log n)) / n) else 0)
          - (1 / (2 * Real.pi)) * ∫ t : ℝ, (logDeriv (rsPre k) ((σ : ℂ) - t * Complex.I)
              + logDeriv (rsPre k) (((1 - σ : ℝ) : ℂ) + t * Complex.I))
              * ghat (WeilForm.selfDual g) (((1 - σ : ℝ) : ℂ) + t * Complex.I)).re ∧
    (ghat g 1 * conj (ghat g 0)
          - ∑' n, (if 2 ≤ n then (rsVonMangoldt (rsCoeff f) k n : ℂ) * WeilForm.selfDual g (Real.log n)
              else 0)
          - ∑' n, (if 2 ≤ n then (rsVonMangoldt (rsCoeff f) k n : ℂ)
              * (WeilForm.selfDual g (-(Real.log n)) / n) else 0)
          - (1 / (2 * Real.pi)) * ∫ t : ℝ, (logDeriv (rsPre k) ((σ : ℂ) - t * Complex.I)
              + logDeriv (rsPre k) (((1 - σ : ℝ) : ℂ) + t * Complex.I))
              * ghat (WeilForm.selfDual g) (((1 - σ : ℝ) : ℂ) + t * Complex.I)).im = 0 := by
  have hhc : Continuous (WeilForm.selfDual g) := WeilForm.continuous_selfDual g hc hs
  obtain ⟨T, hT, hlim⟩ := explicitFormula_Gfull k f hk hf hσ1 hσ2 (WeilForm.selfDual g) hhc hga
    hg hF hg' hF' hdec hArch
  have h1 : ghat (WeilForm.selfDual g) 1 = ghat g 1 * conj (ghat g 0) := by
    have := WeilForm.ghat_selfDual_eq g hc hs 1
    simp only [map_one, sub_self] at this
    exact this
  rw [h1] at hlim
  -- each finsum is a nonnegative real
  have hreal : ∀ j : ℕ, ∃ r : ℝ, 0 ≤ r ∧
      (∑ᶠ u, ((MeromorphicOn.divisor (rsHent k f) (closedRect ⟨1 - σ, -(T j)⟩ ⟨σ, T j⟩)) u : ℂ)
        * ghat (WeilForm.selfDual g) u) = (r : ℂ) := by
    intro j
    set D := MeromorphicOn.divisor (rsHent k f) (closedRect ⟨1 - σ, -(T j)⟩ ⟨σ, T j⟩) with hD
    have hfa : AnalyticOnNhd ℂ (rsHent k f) (closedRect ⟨1 - σ, -(T j)⟩ ⟨σ, T j⟩) :=
      fun s _ => analyticAt_rsHent k f hk s
    have hD0 : ∀ u, 0 ≤ D u := fun u => by
      have := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfa u
      simpa using this
    have hDfin : (Function.support (fun u => D u)).Finite :=
      (MeromorphicOn.divisor (rsHent k f) (closedRect ⟨1 - σ, -(T j)⟩ ⟨σ, T j⟩)).finiteSupport
        (isCompact_closedRect _ _)
    obtain ⟨heq, hnn⟩ := WeilForm.finsum_divisor_ghat_selfDual_nonneg g hc hs (fun u => D u) hD0
      hDfin (fun u hu => hline _ _ u hu)
    exact ⟨_, hnn, heq⟩
  choose r hr using hreal
  have hlim' : Tendsto (fun j : ℕ => ((r j : ℝ) : ℂ)) atTop (𝓝 _) :=
    hlim.congr fun j => (hr j).2
  constructor
  · have := (Complex.continuous_re.tendsto _).comp hlim'
    refine ge_of_tendsto' this fun j => ?_
    simp only [Function.comp, Complex.ofReal_re]
    exact (hr j).1
  · have := (Complex.continuous_im.tendsto _).comp hlim'
    have h0 : Tendsto (fun j : ℕ => (((r j : ℝ) : ℂ)).im) atTop (𝓝 0) := by
      simp only [Complex.ofReal_im]; exact tendsto_const_nhds
    exact tendsto_nhds_unique this h0

end RankinSelbergDelta.RankinSelberg
