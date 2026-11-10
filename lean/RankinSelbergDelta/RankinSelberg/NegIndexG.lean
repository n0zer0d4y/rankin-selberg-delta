import RankinSelbergDelta.RankinSelberg.DefectLadderG
import RankinSelbergDelta.RankinSelberg.NegIndex

/-!
# The negative index of the zero side of the Weil form of `G`

The zero side of the self-dual Weil form of `G`, restricted to a finite-dimensional space of test
functions, has negative index at most twice the number of zeros off the critical line
(`negIndex_zeroSumForm_ghatLin_le`).
-/

open MeasureTheory Filter
open scoped NNReal MatrixGroups Pointwise

noncomputable section

namespace RankinSelbergDelta.RankinSelberg.WeilForm

open MeasureTheory Complex
open scoped ComplexConjugate

/-! #### The wrapper: rank control on the concrete self-dual Weil form of `G`

A finite-dimensional real subspace `T` of test functions `ℝ → ℂ`, all continuous with compact
support, carries the real-linear maps `ghatLin T hc hs s : T →ₗ[ℝ] ℂ`, `g ↦ ĝ(s)`. With the
divisor multiplicities `D ≥ 0` (symmetric under `u ↦ 1 − conj u` by the functional equation),
`RankinSelbergDelta.RankinSelberg.NegIndex.zeroSumForm (ghatLin T hc hs) D Z` evaluated at `(g, g)` is exactly the
real part of the zero side `∑ D u · ĥ(u) = ∑ D u · ĝ(u) · conj ĝ(1 − conj u)`
(`ghat_selfDual_eq`), and `negIndex_zeroSumForm_le` bounds its negative index by twice the
number of zeros off the critical line. -/

/-- `g ↦ ĝ(s)` as a real-linear map on a space `T` of continuous, compactly supported test
functions (linearity of the integral needs integrability, which continuity and compact support
provide). -/
noncomputable def ghatLin (T : Submodule ℝ (ℝ → ℂ)) (hc : ∀ g ∈ T, Continuous g)
    (hs : ∀ g ∈ T, HasCompactSupport g) (s : ℂ) : T →ₗ[ℝ] ℂ where
  toFun g := ghat g s
  map_add' g₁ g₂ := by
    have h1 : Integrable (fun x : ℝ => (g₁ : ℝ → ℂ) x * Complex.exp (s * x)) :=
      ((hc g₁ g₁.2).mul (by fun_prop)).integrable_of_hasCompactSupport (hs g₁ g₁.2).mul_right
    have h2 : Integrable (fun x : ℝ => (g₂ : ℝ → ℂ) x * Complex.exp (s * x)) :=
      ((hc g₂ g₂.2).mul (by fun_prop)).integrable_of_hasCompactSupport (hs g₂ g₂.2).mul_right
    simp only [Submodule.coe_add]
    unfold ghat
    rw [← integral_add h1 h2]
    congr 1
    funext x
    simp only [Pi.add_apply]
    ring
  map_smul' c g := by
    simp only [Submodule.coe_smul, RingHom.id_apply]
    unfold ghat
    rw [← integral_smul]
    congr 1
    funext x
    simp only [Pi.smul_apply, Complex.real_smul]
    ring

@[simp] lemma ghatLin_apply (T : Submodule ℝ (ℝ → ℂ)) (hc : ∀ g ∈ T, Continuous g)
    (hs : ∀ g ∈ T, HasCompactSupport g) (s : ℂ) (g : T) : ghatLin T hc hs s g = ghat g s := rfl

/-- **The zero-sum form IS the real part of the zero side.** For `g ∈ T`,
`zeroSumForm (ghatLin) D Z (g, g) = Re (∑_{u ∈ Z} D u · ĥ(u))` with `ĥ = ĝ · conj ĝ(1 − conj ·)`. -/
theorem zeroSumForm_ghatLin_apply_self (T : Submodule ℝ (ℝ → ℂ)) [FiniteDimensional ℝ T]
    (hc : ∀ g ∈ T, Continuous g)
    (hs : ∀ g ∈ T, HasCompactSupport g) (D : ℂ → ℤ) (Z : Finset ℂ) (g : T) :
    RankinSelbergDelta.RankinSelberg.NegIndex.zeroSumForm (ghatLin T hc hs) (fun u => (D u : ℝ)) Z g g
      = (∑ u ∈ Z, (D u : ℂ) * ghat (selfDual g) u).re := by
  unfold RankinSelbergDelta.RankinSelberg.NegIndex.zeroSumForm
  rw [LinearMap.sum_apply, LinearMap.sum_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul,
    RankinSelbergDelta.RankinSelberg.NegIndex.hermTerm_apply, ghatLin_apply, ghatLin_apply,
    ghat_selfDual_eq g (hc g g.2) (hs g g.2) u]
  have e : ((D u : ℤ) : ℂ) = ((D u : ℝ) : ℂ) := by norm_cast
  rw [e, Complex.re_ofReal_mul]
  rfl

/-- The same with RSPole's `finsum` over a divisor supported in `Z`. -/
theorem zeroSumForm_ghatLin_apply_self_finsum (T : Submodule ℝ (ℝ → ℂ)) [FiniteDimensional ℝ T]
    (hc : ∀ g ∈ T, Continuous g) (hs : ∀ g ∈ T, HasCompactSupport g) (D : ℂ → ℤ)
    (Z : Finset ℂ) (hZ : Function.support D ⊆ (Z : Set ℂ)) (g : T) :
    RankinSelbergDelta.RankinSelberg.NegIndex.zeroSumForm (ghatLin T hc hs) (fun u => (D u : ℝ)) Z g g
      = (∑ᶠ u, (D u : ℂ) * ghat (selfDual g) u).re := by
  rw [zeroSumForm_ghatLin_apply_self]
  congr 1
  symm
  apply finsum_eq_sum_of_support_subset
  intro u hu
  rw [Function.mem_support] at hu
  have : D u ≠ 0 := fun h => hu (by rw [h]; simp)
  exact hZ this

/-- **Rank control on the concrete Weil form of `G` (, landed).** For a divisor `D ≥ 0`
symmetric under `u ↦ 1 − conj u`, zeros `Zon` on the line and off-line pairs represented by `R`,
the real quadratic form `g ↦ Re (∑ D u · ĥ(u))` on the test space `T` has negative index at
most `2 · #R`: one complex dimension per off-line pair, none per zero on the line, uniformly
in `T` (hence in the support `L` of the test functions). -/
theorem negIndex_zeroSumForm_ghatLin_le (T : Submodule ℝ (ℝ → ℂ)) [FiniteDimensional ℝ T]
    (hc : ∀ g ∈ T, Continuous g) (hs : ∀ g ∈ T, HasCompactSupport g) (D : ℂ → ℤ)
    (hD : ∀ u, 0 ≤ D u) (hDsymm : ∀ u, D (1 - conj u) = D u) (Zon R : Finset ℂ)
    (hon : ∀ ρ ∈ Zon, ρ.re = 1 / 2)
    (h₁ : Disjoint R (R.image RankinSelbergDelta.RankinSelberg.NegIndex.refl))
    (h₂ : Disjoint Zon (R ∪ R.image RankinSelbergDelta.RankinSelberg.NegIndex.refl)) :
    RankinSelbergDelta.RankinSelberg.NegIndex.negIndex (RankinSelbergDelta.RankinSelberg.NegIndex.zeroSumForm (ghatLin T hc hs)
      (fun u => (D u : ℝ)) (Zon ∪ (R ∪ R.image RankinSelbergDelta.RankinSelberg.NegIndex.refl))) ≤ 2 * R.card :=
  RankinSelbergDelta.RankinSelberg.NegIndex.negIndex_zeroSumForm_le _ _ (fun u => by exact_mod_cast hD u) Zon R
    (fun ρ hρ => (RankinSelbergDelta.RankinSelberg.NegIndex.refl_eq_self_iff ρ).2 (hon ρ hρ))
    (fun ρ _ => by simp only [RankinSelbergDelta.RankinSelberg.NegIndex.refl, hDsymm]) h₁ h₂

/-- Satisfiability witness: a nonzero finite-dimensional test space of continuous, compactly
supported functions exists (the span of the tent function `x ↦ max 0 (1 − |x|)`). -/
example : ∃ T : Submodule ℝ (ℝ → ℂ), FiniteDimensional ℝ T ∧ (∀ g ∈ T, Continuous g) ∧
    (∀ g ∈ T, HasCompactSupport g) ∧ T ≠ ⊥ := by
  let tent : ℝ → ℂ := fun x => ((max 0 (1 - |x|) : ℝ) : ℂ)
  have hcont : Continuous tent :=
    Complex.continuous_ofReal.comp (continuous_const.max (continuous_const.sub continuous_abs))
  have hsupp : HasCompactSupport tent := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hx'
    apply hx
    rw [Set.mem_Icc] at hx'
    have h1 : 1 ≤ |x| := by
      rcases le_or_gt 0 x with h | h
      · rw [abs_of_nonneg h]
        by_contra h'
        exact hx' ⟨by linarith, by linarith⟩
      · rw [abs_of_neg h]
        by_contra h'
        exact hx' ⟨by linarith, by linarith⟩
    simp only [tent, Complex.ofReal_eq_zero]
    exact max_eq_left (by linarith)
  refine ⟨Submodule.span ℝ {tent}, inferInstance, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hg
    exact hcont.const_smul c
  · intro g hg
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hg
    exact hsupp.mono (Function.support_const_smul_subset c tent)
  · rw [Ne, Submodule.span_singleton_eq_bot]
    intro h
    have := congrFun h 0
    simp [tent] at this

end RankinSelbergDelta.RankinSelberg.WeilForm
