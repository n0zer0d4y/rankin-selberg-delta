import RankinSelbergDelta.RankinSelberg.PrimeSideLimit

/-!
# The explicit formula for `G`

Heights that avoid the zeros of `G` by a fixed margin, the logarithmic-derivative bound on the
horizontal edges, the vanishing of the edge integrals, and the explicit formula
`explicitFormula_Gfull` for test functions with an entire transform and the stated decay.
-/

open MeasureTheory Filter
open scoped NNReal MatrixGroups Pointwise

noncomputable section


/-! ### The last two edges of the explicit formula, and `explicitFormula_Gfull`

(ii) Horizontal-edge vanishing along zero-avoiding heights: the complex Davenport/Backlund
expansion of the logarithmic derivative (namespace `RankinSelbergDelta.LogDerivExpansion`), a
pigeonhole choice of heights, and the generic `exists_zeroAvoiding_heights`. (iii) The left edge via the functional equation: the entire `(s − 1)G` through `s = 0`,
the rectangle identity on any rectangle, `logDeriv_Gfull_one_sub`, the reversed test function.
Then `explicitFormula_Gfull` as a limit along the heights `T_j`. -/

namespace RankinSelbergDelta.LogDerivExpansion

open Complex Metric Set Filter Topology RankinSelbergDelta.BorelCaratheodory

/-- **Davenport's Lemma (§13), complex form (Backlund's expansion), zeros with multiplicity.**
If `f` is holomorphic on `ball z₀ (2R)`, `f z₀ ≠ 0` and `‖f z‖ ≤ e^M ‖f z₀‖` there, then for
`‖z − z₀‖ ≤ R/4` with `f z ≠ 0`: `‖f′/f(z) − Σ_ρ m_ρ/(z − ρ)‖ ≤ 48 M / R`, the sum over the zeros
`ρ` of `f` in `ball z₀ (R/2)` with multiplicities `m_ρ ≥ 1`. -/
theorem norm_logDeriv_sub_sum_le {f : ℂ → ℂ} {z₀ : ℂ} {R M : ℝ} (hR : 0 < R) (hM : 0 < M)
    (hf : DifferentiableOn ℂ f (ball z₀ (2 * R))) (h0 : f z₀ ≠ 0)
    (hbound : ∀ z ∈ ball z₀ (2 * R), ‖f z‖ ≤ Real.exp M * ‖f z₀‖) :
    ∃ (S : Finset ℂ) (m : ℂ → ℤ),
      (∀ u ∈ S, u ∈ ball z₀ (R / 2) ∧ f u = 0 ∧ 1 ≤ m u) ∧
      (∀ u ∈ ball z₀ (R / 2), f u = 0 → u ∈ S) ∧
      ∀ z ∈ closedBall z₀ (R / 4), f z ≠ 0 →
        ‖logDeriv f z - ∑ u ∈ S, (m u : ℂ) / (z - u)‖ ≤ 48 * M / R := by
  classical
  -- the big disc `B`, the half disc `U`
  set B : Set ℂ := ball z₀ (2 * R) with hB
  set U : Set ℂ := ball z₀ (R / 2) with hU
  have hUB : U ⊆ B := ball_subset_ball (by linarith)
  have hUo : IsOpen U := isOpen_ball
  have hBo : IsOpen B := isOpen_ball
  have hz₀U : z₀ ∈ U := mem_ball_self (by positivity)
  have hz₀B : z₀ ∈ B := mem_ball_self (by positivity)
  have hfa : AnalyticOnNhd ℂ f B := hf.analyticOnNhd hBo
  have hfaU : AnalyticOnNhd ℂ f U := hfa.mono hUB
  -- the order of `f` is finite everywhere on `B` (identity theorem, `f z₀ ≠ 0`)
  have hord : ∀ u ∈ B, meromorphicOrderAt f u ≠ ⊤ := by
    intro u hu h
    rw [meromorphicOrderAt_eq_top_iff] at h
    have : EqOn f 0 B :=
      hfa.eqOn_zero_of_preconnected_of_frequently_eq_zero (convex_ball z₀ (2 * R)).isPreconnected
        hu h.frequently
    exact h0 (this hz₀B)
  -- the divisor on `U` and its finite support
  set D := MeromorphicOn.divisor f U with hDdef
  have hfm : MeromorphicOn f U := AnalyticOnNhd.meromorphicOn hfaU
  have hD0 : ∀ u, 0 ≤ D u := fun u => by
    have := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfaU u
    simpa using this
  have hDapply : ∀ u ∈ U, D u = (meromorphicOrderAt f u).untop₀ := fun u hu =>
    MeromorphicOn.divisor_apply hfm hu
  have hDfin : D.support.Finite := by
    have hK : IsCompact (closedBall z₀ (R / 2)) := isCompact_closedBall _ _
    have hfK : MeromorphicOn f (closedBall z₀ (R / 2)) :=
      (hfa.mono (closedBall_subset_ball (by linarith))).meromorphicOn
    have hfin := (MeromorphicOn.divisor f (closedBall z₀ (R / 2))).finiteSupport hK
    refine hfin.subset fun u hu => ?_
    have huU : u ∈ U := D.supportWithinDomain hu
    rw [Function.mem_support] at hu ⊢
    rwa [MeromorphicOn.divisor_apply hfK (ball_subset_closedBall huU), ← hDapply u huU]
  -- the zeros of `f` in `U` are exactly the support of `D`, each with `D u ≥ 1`
  have hzero : ∀ u ∈ U, (f u = 0 ↔ D u ≠ 0) := by
    intro u hu
    have hne : meromorphicOrderAt f u ≠ ⊤ := hord u (hUB hu)
    have hm := (hfaU u hu).meromorphicOrderAt_eq
    have h0' : analyticOrderAt f u = 0 ↔ f u ≠ 0 := by
      rw [analyticOrderAt_eq_zero]
      exact ⟨fun h => h.resolve_left (not_not.mpr (hfaU u hu)), Or.inr⟩
    rcases hn : analyticOrderAt f u with _ | n
    · exfalso; apply hne; rw [hm, hn]; rfl
    · have hDn : D u = n := by
        rw [hDapply u hu, hm, hn]
        first | rfl | simp [WithTop.map_coe, ENat.map_coe, WithTop.untop₀_coe]
      rw [hDn]
      rw [hn] at h0'
      have key : n = 0 ↔ f u ≠ 0 := by
        rw [← h0']
        first | exact WithTop.coe_eq_zero.symm | simp
      constructor
      · intro hfu hD
        exact key.mp (by exact_mod_cast hD) hfu
      · intro hD
        by_contra hfu
        exact hD (by exact_mod_cast key.mpr hfu)
  -- extract the zeros: `f = P • g` on `U` with `g` analytic and nonvanishing
  obtain ⟨g, hga, hg0, hfg⟩ := hfm.extract_zeros_poles (fun u => hord u (hUB u.2)) hDfin
  set P : ℂ → ℂ := ∏ᶠ u, (· - u) ^ D u with hPdef
  have hPa : AnalyticOnNhd ℂ P univ := fun x _ =>
    Function.FactorizedRational.analyticAt (hD0 x)
  have hPne : ∀ x, x ∉ U → P x ≠ 0 := fun x hx =>
    Function.FactorizedRational.ne_zero (by
      by_contra h
      exact hx (D.supportWithinDomain (Function.mem_support.mpr h)))
  -- equality `f = P g` on all of `U`
  have hfPg : EqOn f (fun z => P z * g z) U := by
    refine AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hfaU
      ((hPa.mono (subset_univ _)).mul hga) (convex_ball z₀ (R / 2)).isPreconnected hz₀U ?_
    have h1 : {x | f x = (P • g) x} ∪ Uᶜ ∈ 𝓝[≠] z₀ :=
      (mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hfg) z₀ hz₀U
    have h2 : U ∈ 𝓝[≠] z₀ := nhdsWithin_le_nhds (hUo.mem_nhds hz₀U)
    have h4 : ∀ᶠ x in 𝓝[≠] z₀, f x = P x * g x := by
      filter_upwards [h1, h2] with x hx1 hx2
      rcases hx1 with hx1 | hx1
      · simpa [Pi.smul_apply, smul_eq_mul] using hx1
      · exact absurd hx2 hx1
    exact h4.frequently
  -- the glued function `G`
  set G : ℂ → ℂ := fun z => if z ∈ U then g z else f z / P z with hGdef
  have hGU : ∀ z ∈ U, G z = g z := fun z hz => by
    show (if z ∈ U then g z else f z / P z) = g z
    rw [if_pos hz]
  have hGne : ∀ z ∈ U, G z ≠ 0 := fun z hz => by rw [hGU z hz]; exact hg0 ⟨z, hz⟩
  have hPz₀ : P z₀ ≠ 0 := Function.FactorizedRational.ne_zero (by
    by_contra h
    exact h0 ((hzero z₀ hz₀U).mpr h))
  have hGz₀ : G z₀ = f z₀ / P z₀ := by
    rw [hGU z₀ hz₀U, eq_div_iff hPz₀, mul_comm]
    exact (hfPg hz₀U).symm
  have hGz₀ne : G z₀ ≠ 0 := by rw [hGz₀]; exact div_ne_zero h0 hPz₀
  -- `G` is analytic on `B`
  have hGa : AnalyticOnNhd ℂ G B := by
    intro x hx
    by_cases hxU : x ∈ U
    · refine (hga x hxU).congr ?_
      filter_upwards [hUo.mem_nhds hxU] with y hy
      exact (hGU y hy).symm
    · -- near `x`, `P ≠ 0` (the finite support of `D` is closed and misses `x`)
      have hxS : x ∉ D.support := fun h => hxU (D.supportWithinDomain h)
      have hopen : IsOpen (D.supportᶜ) := hDfin.isClosed.isOpen_compl
      have hnhds : D.supportᶜ ∈ 𝓝 x := hopen.mem_nhds hxS
      have hfP : AnalyticAt ℂ (fun z => f z / P z) x :=
        (hfa x hx).div (hPa x (mem_univ _)) (hPne x hxU)
      refine hfP.congr ?_
      filter_upwards [hnhds] with y hy
      by_cases hyU : y ∈ U
      · have hPy : P y ≠ 0 := Function.FactorizedRational.ne_zero (by simpa using hy)
        rw [hGU y hyU, div_eq_iff hPy, hfPg hyU]
        show P y * g y = g y * P y
        ring
      · show f y / P y = (if y ∈ U then g y else f y / P y)
        rw [if_neg hyU]
  -- maximum modulus: `‖G‖ ≤ e^M ‖G z₀‖` on `closedBall z₀ R`
  have hGbound : ∀ z ∈ closedBall z₀ R, ‖G z‖ ≤ Real.exp M * ‖G z₀‖ := by
    have hball : closure (ball z₀ R) = closedBall z₀ R := closure_ball z₀ hR.ne'
    intro z hz
    rw [← hball] at hz
    have hGd : DifferentiableOn ℂ G B := hGa.differentiableOn
    have hdc : DiffContOnCl ℂ G (ball z₀ R) := by
      refine DifferentiableOn.diffContOnCl (hGd.mono ?_)
      rw [hball]
      exact closedBall_subset_ball (by linarith)
    refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc ?_ hz
    · intro w hw
      rw [frontier_ball z₀ hR.ne', mem_sphere, Complex.dist_eq] at hw
      have hwU : w ∉ U := by
        intro h
        have h' : dist w z₀ < R / 2 := h
        rw [Complex.dist_eq] at h'
        linarith
      have hwB : w ∈ B := by rw [hB, mem_ball, Complex.dist_eq, hw]; linarith
      have hPw : P w ≠ 0 := hPne w hwU
      have hGw : G w = f w / P w := by
        show (if w ∈ U then g w else f w / P w) = f w / P w
        rw [if_neg hwU]
      -- `‖P z₀‖ ≤ ‖P w‖`
      have hPle : ‖P z₀‖ ≤ ‖P w‖ := by
        rw [hPdef, finprod_eq_finset_prod hDfin, finprod_eq_finset_prod hDfin, norm_prod, norm_prod]
        refine Finset.prod_le_prod (fun u _ => norm_nonneg _) fun u hu => ?_
        have huU : u ∈ U := D.supportWithinDomain (by simpa using hu)
        refine norm_zpow_le_norm_zpow (hD0 u) ?_
        rw [hU, mem_ball, Complex.dist_eq] at huU
        have h1 : ‖w - u‖ ≥ ‖w - z₀‖ - ‖u - z₀‖ := by
          have := norm_sub_norm_le (w - z₀) (u - z₀)
          rwa [sub_sub_sub_cancel_right] at this
        rw [hw] at h1
        have h2 : ‖z₀ - u‖ = ‖u - z₀‖ := norm_sub_rev _ _
        calc ‖z₀ - u‖ = ‖u - z₀‖ := h2
          _ ≤ R - ‖u - z₀‖ := by linarith
          _ ≤ ‖w - u‖ := h1
      rw [hGw, hGz₀, norm_div, norm_div]
      have hPz₀pos : 0 < ‖P z₀‖ := norm_pos_iff.mpr hPz₀
      calc ‖f w‖ / ‖P w‖ ≤ ‖f w‖ / ‖P z₀‖ :=
            div_le_div_of_nonneg_left (norm_nonneg _) hPz₀pos hPle
        _ ≤ (Real.exp M * ‖f z₀‖) / ‖P z₀‖ := by
            gcongr
            exact hbound w hwB
        _ = Real.exp M * (‖f z₀‖ / ‖P z₀‖) := by ring
  -- a primitive `F` of `G′/G` on `U`, normalised by `F z₀ = 0`
  have hGdU : DifferentiableOn ℂ G U := (hGa.mono hUB).differentiableOn
  have hGderiv : DifferentiableOn ℂ (deriv G) U := ((hGa.mono hUB).deriv).differentiableOn
  have hlog : DifferentiableOn ℂ (fun z => deriv G z / G z) U := hGderiv.div hGdU hGne
  obtain ⟨F₀, hF₀⟩ := hlog.isExactOn_ball
  set F : ℂ → ℂ := fun z => F₀ z - F₀ z₀ with hFdef
  have hF : ∀ z ∈ U, HasDerivAt F (deriv G z / G z) z := fun z hz => (hF₀ z hz).sub_const _
  have hFz₀ : F z₀ = 0 := sub_self _
  have hFd : DifferentiableOn ℂ F U := fun z hz => (hF z hz).differentiableAt.differentiableWithinAt
  -- `G = G z₀ · exp F` on `U`
  have hGexp : ∀ z ∈ U, G z = G z₀ * Complex.exp (F z) := by
    have hQ : ∀ z ∈ U, HasDerivAt (fun w => G w * Complex.exp (-F w)) 0 z := by
      intro z hz
      have h1 : HasDerivAt G (deriv G z) z :=
        ((hGa.mono hUB) z hz).differentiableAt.hasDerivAt
      have h2 : HasDerivAt (fun w => Complex.exp (-F w))
          (Complex.exp (-F z) * -(deriv G z / G z)) z :=
        (Complex.hasDerivAt_exp _).comp z (hF z hz).neg
      have := h1.mul h2
      convert this using 1
      field_simp [hGne z hz]
      ring
    have hconst : ∀ z ∈ U, G z * Complex.exp (-F z) = G z₀ * Complex.exp (-F z₀) :=
      fun z hz => hUo.is_const_of_deriv_eq_zero (convex_ball z₀ (R / 2)).isPreconnected
        (fun w hw => (hQ w hw).differentiableAt.differentiableWithinAt)
        (fun w hw => (hQ w hw).deriv) hz hz₀U
    intro z hz
    have h := hconst z hz
    rw [hFz₀, neg_zero, Complex.exp_zero, mul_one] at h
    rw [← h, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
  -- hence `Re F ≤ M` on `U`
  have hFre : ∀ z ∈ U, (F z).re ≤ M := by
    intro z hz
    have h1 := hGbound z (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)) hz)
    rw [hGexp z hz, norm_mul, Complex.norm_exp] at h1
    have hG0 : 0 < ‖G z₀‖ := norm_pos_iff.mpr hGz₀ne
    have h2 : Real.exp (F z).re ≤ Real.exp M :=
      le_of_mul_le_mul_left (by linarith [h1] : ‖G z₀‖ * Real.exp (F z).re ≤ ‖G z₀‖ * Real.exp M) hG0
    exact Real.exp_le_exp.mp h2
  -- Borel–Carathéodory on `U`: `‖F‖ ≤ 6M` on `closedBall z₀ (3R/8)`
  have hF6 : ∀ z ∈ closedBall z₀ (3 * R / 8), ‖F z‖ ≤ 6 * M := by
    intro z hz
    have hzU : z ∈ U := by
      rw [hU, mem_ball]; rw [mem_closedBall] at hz; linarith
    have := norm_le_of_re_le (by positivity : (0 : ℝ) < R / 2) hM hFd hFz₀ hFre hzU
    rw [mem_closedBall] at hz
    have hd0 : 0 ≤ dist z z₀ := dist_nonneg
    have hden : R / 8 ≤ R / 2 - dist z z₀ := by linarith
    calc ‖F z‖ ≤ 2 * M * dist z z₀ / (R / 2 - dist z z₀) := this
      _ ≤ 2 * M * (3 * R / 8) / (R / 8) := by
          gcongr
      _ = 6 * M := by field_simp; ring
  -- Cauchy: `‖F′ z‖ ≤ 48 M / R` on `closedBall z₀ (R/4)`
  have hF' : ∀ z ∈ closedBall z₀ (R / 4), ‖deriv F z‖ ≤ 48 * M / R := by
    intro z hz
    rw [mem_closedBall] at hz
    have hsub : closedBall z (R / 8) ⊆ closedBall z₀ (3 * R / 8) := by
      intro w hw
      rw [mem_closedBall] at hw ⊢
      calc dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
        _ ≤ R / 8 + R / 4 := by linarith
        _ = 3 * R / 8 := by ring
    have hsubU : closedBall z (R / 8) ⊆ U := by
      intro w hw
      have := hsub hw
      rw [hU, mem_ball]; rw [mem_closedBall] at this; linarith
    have hdc : DiffContOnCl ℂ F (ball z (R / 8)) := by
      refine DifferentiableOn.diffContOnCl ?_
      rw [closure_ball z (by positivity : R / 8 ≠ 0)]
      exact hFd.mono hsubU
    have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity : (0 : ℝ) < R / 8) hdc
      (fun w hw => hF6 w (hsub (sphere_subset_closedBall hw)))
    calc ‖deriv F z‖ ≤ 6 * M / (R / 8) := this
      _ = 48 * M / R := by field_simp; ring
  -- the zero set and multiplicities
  refine ⟨hDfin.toFinset, fun u => D u, ?_, ?_, ?_⟩
  · intro u hu
    have hu' : D u ≠ 0 := by simpa using hu
    have huU : u ∈ U := D.supportWithinDomain (Function.mem_support.mpr hu')
    refine ⟨huU, (hzero u huU).mpr hu', ?_⟩
    have := hD0 u
    show 1 ≤ D u
    omega
  · intro u hu hfu
    simpa using (hzero u hu).mp hfu
  -- the inequality
  intro z hz hfz
  have hzU : z ∈ U := by
    rw [hU, mem_ball]; rw [mem_closedBall] at hz; linarith
  have hPz : P z ≠ 0 := by
    intro h
    have := hfPg hzU
    simp only at this
    rw [h, zero_mul] at this
    exact hfz this
  -- `logDeriv f z = logDeriv P z + logDeriv G z`
  have hfeq : f =ᶠ[𝓝 z] fun w => P w * G w := by
    filter_upwards [hUo.mem_nhds hzU] with w hw
    rw [hfPg hw, hGU w hw]
  have hlogf : logDeriv f z = logDeriv P z + logDeriv G z := by
    rw [show logDeriv f z = logDeriv (fun w => P w * G w) z by
      simp only [logDeriv_apply]
      rw [hfeq.deriv_eq, hfeq.eq_of_nhds]]
    exact logDeriv_mul z hPz (hGne z hzU) (hPa z (mem_univ _)).differentiableAt
      ((hGa.mono hUB) z hzU).differentiableAt
  -- `logDeriv G z = deriv F z`
  have hlogG : logDeriv G z = deriv F z := by
    rw [logDeriv_apply, (hF z hzU).deriv]
  -- `logDeriv P z = Σ D u / (z − u)`
  have hlogP : logDeriv P z = ∑ u ∈ hDfin.toFinset, (D u : ℂ) / (z - u) := by
    have hPeq : P = fun x => ∏ u ∈ hDfin.toFinset, (x - u) ^ D u := by
      funext x; exact finprod_eq_finset_prod hDfin x
    have hne : ∀ u ∈ hDfin.toFinset, z - u ≠ 0 := by
      intro u hu h
      have hu' : D u ≠ 0 := by simpa using hu
      have hzu : z = u := sub_eq_zero.mp h
      subst hzu
      exact hfz ((hzero z hzU).mpr hu')
    have hprod := logDeriv_prod (f := fun u x => (x - u) ^ D u) (x := z) (s := hDfin.toFinset)
      (fun u hu => zpow_ne_zero _ (hne u hu))
      (fun u _ => (differentiableAt_id.sub_const u).zpow (Or.inr (hD0 u)))
    beta_reduce at hprod
    rw [hPeq, hprod]
    refine Finset.sum_congr rfl fun u hu => ?_
    have hz := logDeriv_fun_zpow (f := fun x => x - u) (x := z) (differentiableAt_id.sub_const u) (D u)
    beta_reduce at hz
    rw [hz, logDeriv_apply, deriv_sub_const, deriv_id'']
    ring
  show ‖logDeriv f z - ∑ u ∈ hDfin.toFinset, (D u : ℂ) / (z - u)‖ ≤ 48 * M / R
  rw [hlogf, hlogG, hlogP, add_sub_cancel_left]
  exact hF' z hz


end RankinSelbergDelta.LogDerivExpansion

namespace RankinSelbergDelta.ZeroAvoid

open Finset

/-- **Pigeonhole for zero-avoiding heights.** -/
theorem exists_avoid (Z : Finset ℝ) {δ : ℝ} (hδ : 0 < δ) (hn : 2 * δ * Z.card ≤ 1) (j : ℝ) :
    ∃ t : ℝ, j ≤ t ∧ t ≤ j + 1 ∧ ∀ z ∈ Z, δ ≤ |t - z| := by
  classical
  by_contra hcon
  push_neg at hcon
  -- every grid point `t_i = j + 2 δ i`, `i ≤ |Z|`, is within `δ` of some element of `Z`
  have hpt : ∀ i ∈ range (Z.card + 1), ∃ z ∈ Z, |(j + 2 * δ * i) - z| < δ := by
    intro i hi
    rw [mem_range] at hi
    have hi' : (i : ℝ) ≤ Z.card := by exact_mod_cast Nat.lt_succ_iff.mp hi
    have hδi : 0 ≤ 2 * δ * i := by positivity
    refine hcon (j + 2 * δ * i) (by linarith) ?_
    have : 2 * δ * i ≤ 2 * δ * Z.card := by gcongr
    linarith
  choose! zf hzf using hpt
  -- the choice `i ↦ z_i` is injective on the grid: two grid points within `δ` of the same `z`
  -- are less than `2 δ` apart, so they coincide
  have hinj : Set.InjOn zf (range (Z.card + 1) : Set ℕ) := by
    intro a ha b hb hab
    have h1 := (hzf a ha).2
    have h2 := (hzf b hb).2
    rw [hab] at h1
    have h3 : |(j + 2 * δ * a) - (j + 2 * δ * b)| < 2 * δ := by
      calc |(j + 2 * δ * a) - (j + 2 * δ * b)|
          ≤ |(j + 2 * δ * a) - zf b| + |zf b - (j + 2 * δ * b)| := abs_sub_le _ _ _
        _ = |(j + 2 * δ * a) - zf b| + |(j + 2 * δ * b) - zf b| := by rw [abs_sub_comm (zf b)]
        _ < δ + δ := add_lt_add h1 h2
        _ = 2 * δ := by ring
    have h4 : |(j + 2 * δ * a) - (j + 2 * δ * b)| = 2 * δ * |(a : ℝ) - b| := by
      rw [show (j + 2 * δ * a) - (j + 2 * δ * b) = 2 * δ * ((a : ℝ) - b) by ring, abs_mul,
        abs_of_pos (by positivity : (0 : ℝ) < 2 * δ)]
    rw [h4] at h3
    have h5 : |(a : ℝ) - b| < 1 := by
      by_contra h
      push_neg at h
      have : 2 * δ * 1 ≤ 2 * δ * |(a : ℝ) - b| := by gcongr
      linarith
    rw [abs_lt] at h5
    have h6 : a < b + 1 := by exact_mod_cast (by linarith [h5.2] : (a : ℝ) < b + 1)
    have h7 : b < a + 1 := by exact_mod_cast (by linarith [h5.1] : (b : ℝ) < a + 1)
    omega
  have hmaps : Set.MapsTo zf (range (Z.card + 1) : Set ℕ) (Z : Set ℝ) := fun i hi =>
    (hzf i (by simpa using hi)).1
  have := Finset.card_le_card_of_injOn zf hmaps hinj
  simp at this

end RankinSelbergDelta.ZeroAvoid

/-! ### The generic theorem: zero-avoiding heights and the `O(log² T)` bound on `f′/f` -/

namespace RankinSelbergDelta.HorizontalEdge

open Complex Metric Set Filter Topology RankinSelbergDelta.ZeroCount

/-- **The complex expansion of `f′/f` near height `τ`** (the argument of `logDeriv_bound_setup`,
with the disc radius `R = 4(σ₀ + 1)`, so that the conclusion covers `−1 ≤ Re z`).
For `|τ| ≥ 8σ₀ + 10` and `z₀ = σ₀ + iτ`: the zeros `S` of `f` in `ball z₀ (2(σ₀+1))` with
multiplicities `m ≥ 1` satisfy `‖f′/f(z) − Σ_{u ∈ S} m_u/(z − u)‖ ≤ C′ log|τ|` on
`closedBall z₀ (σ₀ + 1)` wherever `f z ≠ 0`. -/
theorem expansion_setup {f : ℂ → ℂ} {σ₀ C c : ℝ} {N : ℕ} (hσ₀ : 2 ≤ σ₀) (hC : 0 < C) (hc : 0 < c)
    (hf : ∀ z : ℂ, 1 ≤ |z.im| → AnalyticAt ℂ f z)
    (hgrow : ∀ z : ℂ, -(8 * σ₀ + 8) ≤ z.re → 1 ≤ |z.im| → ‖f z‖ ≤ C * (1 + |z.im|) ^ N)
    (hlow : ∀ t : ℝ, c ≤ ‖f ((σ₀ : ℂ) + Complex.I * t)‖) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ τ : ℝ, 8 * σ₀ + 10 ≤ |τ| →
      ∃ (S : Finset ℂ) (m : ℂ → ℤ),
        (∀ u ∈ S, u ∈ ball ((σ₀ : ℂ) + Complex.I * τ) (2 * (σ₀ + 1)) ∧ f u = 0 ∧ 1 ≤ m u) ∧
        (∀ u ∈ ball ((σ₀ : ℂ) + Complex.I * τ) (2 * (σ₀ + 1)), f u = 0 → u ∈ S) ∧
        ∀ z ∈ closedBall ((σ₀ : ℂ) + Complex.I * τ) (σ₀ + 1), f z ≠ 0 →
          ‖logDeriv f z - ∑ u ∈ S, (m u : ℂ) / (z - u)‖ ≤ C' * Real.log |τ| := by
  set R : ℝ := 4 * (σ₀ + 1) with hR
  have hRpos : 0 < R := by rw [hR]; linarith
  set K : ℝ := 2 * R + 2 with hK
  have hK1 : 1 ≤ K := by rw [hK]; linarith
  set c₀ : ℝ := |Real.log (C / c)| + N * Real.log K + 1 with hc₀
  have hc₀1 : 1 ≤ c₀ := by
    rw [hc₀]
    have := abs_nonneg (Real.log (C / c))
    have := mul_nonneg (Nat.cast_nonneg N : (0:ℝ) ≤ N) (Real.log_nonneg hK1)
    linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(48 / R) * (c₀ / Real.log 2 + N), by positivity, fun τ hτ => ?_⟩
  set z₀ : ℂ := (σ₀ : ℂ) + Complex.I * τ with hz₀
  have hz₀re : z₀.re = σ₀ := by simp [hz₀]
  have hz₀im : z₀.im = τ := by simp [hz₀]
  have hτ2 : 2 ≤ |τ| := by linarith
  have hτ1 : 1 ≤ |τ| := by linarith
  have hball : ∀ w ∈ ball z₀ (2 * R), 2 ≤ |w.im| ∧ -(8 * σ₀ + 8) ≤ w.re ∧ |w.im| ≤ |τ| + 2 * R := by
    intro w hw
    rw [mem_ball, Complex.dist_eq] at hw
    have hre := Complex.abs_re_le_norm (w - z₀)
    have him := Complex.abs_im_le_norm (w - z₀)
    rw [Complex.sub_re, hz₀re] at hre
    rw [Complex.sub_im, hz₀im] at him
    rw [abs_le] at hre him
    have h1 : |τ| - 2 * R ≤ |w.im| := by
      have := abs_sub_abs_le_abs_sub τ w.im
      rw [abs_sub_comm] at this
      have h2 : |w.im - τ| ≤ 2 * R := by rw [abs_le]; constructor <;> linarith
      linarith
    have h3 : |w.im| ≤ |τ| + 2 * R := by
      have := abs_sub_abs_le_abs_sub w.im τ
      have h2 : |w.im - τ| ≤ 2 * R := by rw [abs_le]; constructor <;> linarith
      linarith
    refine ⟨by linarith, by linarith, h3⟩
  have hdiff : DifferentiableOn ℂ f (ball z₀ (2 * R)) := by
    intro w hw
    obtain ⟨him, -, -⟩ := hball w hw
    exact (hf w (by linarith)).differentiableAt.differentiableWithinAt
  set M : ℝ := c₀ + N * Real.log |τ| with hM
  have hMpos : 0 < M := by
    rw [hM]
    have := mul_nonneg (Nat.cast_nonneg N : (0:ℝ) ≤ N) (Real.log_nonneg hτ1)
    linarith
  have hfz₀ : c ≤ ‖f z₀‖ := hlow τ
  have hfz₀ne : f z₀ ≠ 0 := by
    intro h; rw [h, norm_zero] at hfz₀; linarith
  have hbound : ∀ w ∈ ball z₀ (2 * R), ‖f w‖ ≤ Real.exp M * ‖f z₀‖ := by
    intro w hw
    obtain ⟨him, hreA, himle⟩ := hball w hw
    have hfw := hgrow w hreA (by linarith)
    have h1K : 1 + |w.im| ≤ K * |τ| := by
      rw [hK]
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * R + 1) (by linarith : (0 : ℝ) ≤ |τ| - 1)]
    have hpow : (1 + |w.im|) ^ N ≤ (K * |τ|) ^ N :=
      pow_le_pow_left₀ (by positivity) h1K N
    have hexp : C * (K * |τ|) ^ N ≤ c * Real.exp M := by
      have hCc : 0 < C / c := by positivity
      have hKpos : 0 < K := by linarith
      have hτpos : 0 < |τ| := by linarith
      have hlogM : Real.log (C / c * (K * |τ|) ^ N) ≤ M := by
        rw [Real.log_mul hCc.ne' (by positivity), Real.log_pow, Real.log_mul hKpos.ne' hτpos.ne',
          hM, hc₀]
        have := le_abs_self (Real.log (C / c))
        have hdistr : (N : ℝ) * (Real.log K + Real.log |τ|)
            = N * Real.log K + N * Real.log |τ| := by ring
        linarith
      have := Real.exp_le_exp.mpr hlogM
      rw [Real.exp_log (by positivity)] at this
      rw [div_mul_eq_mul_div, div_le_iff₀ hc] at this
      linarith
    calc ‖f w‖ ≤ C * (1 + |w.im|) ^ N := hfw
      _ ≤ C * (K * |τ|) ^ N := mul_le_mul_of_nonneg_left hpow hC.le
      _ ≤ c * Real.exp M := hexp
      _ ≤ Real.exp M * ‖f z₀‖ := by nlinarith [Real.exp_pos M]
  obtain ⟨S, m, hS1, hS2, hineq⟩ :=
    RankinSelbergDelta.LogDerivExpansion.norm_logDeriv_sub_sum_le hRpos hMpos hdiff hfz₀ne hbound
  have hR2 : R / 2 = 2 * (σ₀ + 1) := by rw [hR]; ring
  have hR4 : R / 4 = σ₀ + 1 := by rw [hR]; ring
  rw [hR2] at hS1 hS2
  rw [hR4] at hineq
  refine ⟨S, m, hS1, hS2, fun z hz hz0 => ?_⟩
  have := hineq z hz hz0
  have hlogτ : Real.log 2 ≤ Real.log |τ| := Real.log_le_log (by norm_num) hτ2
  have hMle : 48 * M / R ≤ (48 / R) * (c₀ / Real.log 2 + N) * Real.log |τ| := by
    rw [hM]
    have hc : c₀ ≤ c₀ / Real.log 2 * Real.log |τ| := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
      nlinarith
    have h48 : 0 < 48 / R := by positivity
    calc 48 * (c₀ + N * Real.log |τ|) / R = (48 / R) * (c₀ + N * Real.log |τ|) := by ring
      _ ≤ (48 / R) * (c₀ / Real.log 2 * Real.log |τ| + N * Real.log |τ|) := by gcongr
      _ = (48 / R) * (c₀ / Real.log 2 + N) * Real.log |τ| := by ring
  linarith

/-- **The multiplicities of the zeros in the Davenport disc sum to `O(log |τ|)`**: at the centre
`z₀`, `Re Σ m_u/(z₀ − u) ≥ Σ m_u · (σ₀ − 1)/(4(σ₀+1)²)` (every zero has `Re u ≤ 1`), while
`‖Σ m_u/(z₀ − u)‖ ≤ ‖f′/f(z₀)‖ + C′ log|τ| ≤ L + C′ log|τ|`. -/
theorem sum_mult_le {f : ℂ → ℂ} {σ₀ L : ℝ} (hσ₀ : 2 ≤ σ₀)
    (hL : ∀ t : ℝ, ‖logDeriv f ((σ₀ : ℂ) + Complex.I * t)‖ ≤ L)
    (hne : ∀ z : ℂ, 1 < z.re → f z ≠ 0) {C' : ℝ} (hC' : 0 < C') {τ : ℝ} (hτ : 2 ≤ |τ|)
    {S : Finset ℂ} {m : ℂ → ℤ}
    (hS1 : ∀ u ∈ S, u ∈ ball ((σ₀ : ℂ) + Complex.I * τ) (2 * (σ₀ + 1)) ∧ f u = 0 ∧ 1 ≤ m u)
    (hineq : ∀ z ∈ closedBall ((σ₀ : ℂ) + Complex.I * τ) (σ₀ + 1), f z ≠ 0 →
      ‖logDeriv f z - ∑ u ∈ S, (m u : ℂ) / (z - u)‖ ≤ C' * Real.log |τ|) :
    ∑ u ∈ S, (m u : ℝ)
      ≤ (4 * (σ₀ + 1) ^ 2 / (σ₀ - 1)) * (L / Real.log 2 + C') * Real.log |τ| := by
  set z₀ : ℂ := (σ₀ : ℂ) + Complex.I * τ with hz₀
  have hz₀re : z₀.re = σ₀ := by simp [hz₀]
  have hz₀ne : f z₀ ≠ 0 := hne z₀ (by rw [hz₀re]; linarith)
  have hz₀mem : z₀ ∈ closedBall z₀ (σ₀ + 1) := mem_closedBall_self (by linarith)
  have h1 := hineq z₀ hz₀mem hz₀ne
  have hLz : ‖logDeriv f z₀‖ ≤ L := hL τ
  have hsum_norm : ‖∑ u ∈ S, (m u : ℂ) / (z₀ - u)‖ ≤ L + C' * Real.log |τ| := by
    calc ‖∑ u ∈ S, (m u : ℂ) / (z₀ - u)‖
        = ‖logDeriv f z₀ - (logDeriv f z₀ - ∑ u ∈ S, (m u : ℂ) / (z₀ - u))‖ := by congr 1; ring
      _ ≤ ‖logDeriv f z₀‖ + ‖logDeriv f z₀ - ∑ u ∈ S, (m u : ℂ) / (z₀ - u)‖ := norm_sub_le _ _
      _ ≤ L + C' * Real.log |τ| := add_le_add hLz h1
  have hterm : ∀ u ∈ S, (m u : ℝ) * ((σ₀ - 1) / (4 * (σ₀ + 1) ^ 2))
      ≤ ((m u : ℂ) / (z₀ - u)).re := by
    intro u hu
    obtain ⟨humem, hu0, hm1⟩ := hS1 u hu
    have hure : u.re ≤ 1 := by
      by_contra hcon; push_neg at hcon; exact hne u hcon hu0
    have hdist : ‖z₀ - u‖ < 2 * (σ₀ + 1) := by
      rw [mem_ball, Complex.dist_eq] at humem; rw [norm_sub_rev]; exact humem
    have hre : σ₀ - 1 ≤ (z₀ - u).re := by rw [Complex.sub_re, hz₀re]; linarith
    have hnormSq : Complex.normSq (z₀ - u) ≤ 4 * (σ₀ + 1) ^ 2 := by
      rw [Complex.normSq_eq_norm_sq]
      have h0 : 0 ≤ ‖z₀ - u‖ := norm_nonneg _
      nlinarith
    have hnormSq_pos : 0 < Complex.normSq (z₀ - u) := by
      rw [Complex.normSq_pos]
      intro h
      have huz : u = z₀ := (sub_eq_zero.mp h).symm
      rw [huz] at hu0
      exact hz₀ne hu0
    have hm0 : (0 : ℝ) ≤ m u := by exact_mod_cast (by omega : (0 : ℤ) ≤ m u)
    have hre' : ((m u : ℂ) / (z₀ - u)).re
        = (m u : ℝ) * ((z₀ - u).re / Complex.normSq (z₀ - u)) := by
      rw [div_eq_mul_inv, ← Complex.ofReal_intCast, Complex.re_ofReal_mul, Complex.inv_re]
    rw [hre']
    apply mul_le_mul_of_nonneg_left _ hm0
    rw [div_le_div_iff₀ (by positivity) hnormSq_pos]
    calc (σ₀ - 1) * Complex.normSq (z₀ - u) ≤ (σ₀ - 1) * (4 * (σ₀ + 1) ^ 2) :=
          mul_le_mul_of_nonneg_left hnormSq (by linarith)
      _ ≤ (z₀ - u).re * (4 * (σ₀ + 1) ^ 2) := mul_le_mul_of_nonneg_right hre (by positivity)
  have hsum_re : ∑ u ∈ S, (m u : ℝ) * ((σ₀ - 1) / (4 * (σ₀ + 1) ^ 2))
      ≤ (∑ u ∈ S, (m u : ℂ) / (z₀ - u)).re := by
    rw [Complex.re_sum]; exact Finset.sum_le_sum hterm
  have hre_le : (∑ u ∈ S, (m u : ℂ) / (z₀ - u)).re ≤ L + C' * Real.log |τ| :=
    (Complex.re_le_norm _).trans hsum_norm
  rw [← Finset.sum_mul] at hsum_re
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogτ : Real.log 2 ≤ Real.log |τ| := Real.log_le_log (by norm_num) hτ
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  have hL' : L ≤ L / Real.log 2 * Real.log |τ| := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]; nlinarith
  have hq : 0 < (σ₀ - 1) / (4 * (σ₀ + 1) ^ 2) := div_pos (by linarith) (by positivity)
  have hmain : (∑ u ∈ S, (m u : ℝ)) * ((σ₀ - 1) / (4 * (σ₀ + 1) ^ 2))
      ≤ L + C' * Real.log |τ| := hsum_re.trans hre_le
  rw [← le_div_iff₀ hq] at hmain
  have hσ1 : σ₀ - 1 ≠ 0 := by linarith
  calc ∑ u ∈ S, (m u : ℝ) ≤ (L + C' * Real.log |τ|) / ((σ₀ - 1) / (4 * (σ₀ + 1) ^ 2)) := hmain
    _ = (4 * (σ₀ + 1) ^ 2 / (σ₀ - 1)) * (L + C' * Real.log |τ|) := by
        rw [div_div_eq_mul_div]; ring
    _ ≤ (4 * (σ₀ + 1) ^ 2 / (σ₀ - 1)) * (L / Real.log 2 * Real.log |τ| + C' * Real.log |τ|) :=
        mul_le_mul_of_nonneg_left (by linarith) (le_of_lt (div_pos (by positivity) (by linarith)))
    _ = (4 * (σ₀ + 1) ^ 2 / (σ₀ - 1)) * (L / Real.log 2 + C') * Real.log |τ| := by ring

/-- **Zero-avoiding heights and the `O(log² T)` bound (Backlund).** For `f` analytic on
`|Im z| ≥ 1`, of polynomial growth on `Re z ≥ −(8σ₀+8)`, bounded below by `c > 0` and with
`‖f′/f‖ ≤ L` on the line `Re z = σ₀ ≥ 2`, and nonvanishing on `Re z > 1`: there are `j₀` and
`C₂` such that every `j ≥ j₀` admits a height `T ∈ [j, j+1]` with `f(x ± iT) ≠ 0` and
`‖f′/f(x ± iT)‖ ≤ C₂ log² j` for all `−1 ≤ x ≤ 2`. The height is chosen by pigeonhole among the
`O(log j)` zero ordinates near height `±(j + 1/2)` (Jensen's disc count), so that every zero of the
Davenport disc is at distance `≥ c₁/log j` from the line `Im z = ±T`; the expansion
`f′/f = Σ m_u/(z − u) + O(log T)` with `Σ m_u = O(log T)` then gives `O(log² T)`. -/
theorem exists_zeroAvoiding_heights {f : ℂ → ℂ} {σ₀ C c L : ℝ} {N : ℕ} (hσ₀ : 2 ≤ σ₀)
    (hC : 0 < C) (hc : 0 < c)
    (hf : ∀ z : ℂ, 1 ≤ |z.im| → AnalyticAt ℂ f z)
    (hgrow : ∀ z : ℂ, -(8 * σ₀ + 8) ≤ z.re → 1 ≤ |z.im| → ‖f z‖ ≤ C * (1 + |z.im|) ^ N)
    (hlow : ∀ t : ℝ, c ≤ ‖f ((σ₀ : ℂ) + Complex.I * t)‖)
    (hL : ∀ t : ℝ, ‖logDeriv f ((σ₀ : ℂ) + Complex.I * t)‖ ≤ L)
    (hne : ∀ z : ℂ, 1 < z.re → f z ≠ 0) :
    ∃ (j₀ : ℕ) (C₂ : ℝ), 0 < C₂ ∧ ∀ j : ℕ, j₀ ≤ j → ∃ T : ℝ, (j : ℝ) ≤ T ∧ T ≤ j + 1 ∧
      ∀ x : ℝ, -1 ≤ x → x ≤ 2 →
        (f ((x : ℂ) + T * Complex.I) ≠ 0 ∧
          ‖logDeriv f ((x : ℂ) + T * Complex.I)‖ ≤ C₂ * Real.log j ^ 2) ∧
        (f ((x : ℂ) - T * Complex.I) ≠ 0 ∧
          ‖logDeriv f ((x : ℂ) - T * Complex.I)‖ ≤ C₂ * Real.log j ^ 2) := by
  classical
  obtain ⟨C', hC', hexp⟩ := expansion_setup hσ₀ hC hc hf hgrow hlow
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set K₁ : ℝ := (4 * (σ₀ + 1) ^ 2 / (σ₀ - 1)) * (L / Real.log 2 + C') with hK₁
  have hK₁0 : 0 ≤ K₁ := by
    rw [hK₁]
    exact mul_nonneg (div_nonneg (by positivity) (by linarith))
      (add_nonneg (div_nonneg hL0 hlog2.le) hC'.le)
  -- the disc count at height `±(j + 1/2)`: radius `ρ = 2σ₀ + 3 = R'/2`
  set R' : ℝ := 4 * σ₀ + 6 with hR'
  set ρ : ℝ := 2 * σ₀ + 3 with hρ
  have hρR : R' / 2 = ρ := by rw [hR', hρ]; ring
  have hR'pos : 0 < R' := by rw [hR']; linarith
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have hlR : 0 ≤ Real.log (R' + 2) := Real.log_nonneg (by linarith)
  set K₂ : ℝ := (|Real.log (max C 1)| + |Real.log c| + N * Real.log (R' + 2) + N) / Real.log 2
    with hK₂
  have hA0 : 0 ≤ |Real.log (max C 1)| + |Real.log c| + N * Real.log (R' + 2) :=
    add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (mul_nonneg hN0 hlR)
  have hK₂0 : 0 ≤ K₂ := by
    rw [hK₂]
    exact div_nonneg (by linarith) hlog2.le
  set c₁ : ℝ := 1 / (4 * (K₂ + 1)) with hc₁
  have hc₁pos : 0 < c₁ := by rw [hc₁]; positivity
  set j₀ : ℕ := ⌈8 * σ₀⌉₊ + 10 with hj₀
  refine ⟨j₀, 2 * C' + 2 * K₁ / c₁, by positivity, fun j hj => ?_⟩
  have hjR : 8 * σ₀ + 10 ≤ (j : ℝ) := by
    have h1 := Nat.le_ceil (8 * σ₀)
    have h2 : (j₀ : ℝ) ≤ j := by exact_mod_cast hj
    rw [hj₀] at h2; push_cast at h2; linarith
  have hj3 : (3 : ℝ) ≤ j := by linarith
  have hjpos : (0:ℝ) < j := by linarith
  have hlogj1 : 1 ≤ Real.log j := by
    have h : Real.exp 1 ≤ (j : ℝ) := by
      have := Real.exp_one_lt_d9; linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log j := Real.log_le_log (Real.exp_pos 1) h
  have hlogj0 : 0 < Real.log j := by linarith
  -- the per-disc count
  have hcount : ∀ t : ℝ, R' + 1 ≤ |t| →
      ((zerosIn f (closedBall (pt σ₀ t) ρ)).ncard : ℝ) * Real.log 2
        ≤ Real.log (max C 1) + N * Real.log (1 + |t| + R') - Real.log c := by
    intro t ht
    rw [← hρR]
    refine disc_count_le hR'pos hC hc hf ?_ ?_ t ht
    · intro z hz hzim
      exact hgrow z (by linarith) hzim
    · intro t'
      have hpt : pt σ₀ t' = (σ₀ : ℂ) + Complex.I * t' := by apply Complex.ext <;> simp [pt]
      rw [hpt]; exact hlow t'
  have hcount' : ∀ t : ℝ, |t| = j + 1 / 2 →
      ((zerosIn f (closedBall (pt σ₀ t) ρ)).ncard : ℝ) ≤ K₂ * Real.log j := by
    intro t ht
    have h := hcount t (by rw [ht]; linarith)
    have hlogb : Real.log (1 + |t| + R') ≤ Real.log (R' + 2) + Real.log j := by
      rw [← Real.log_mul (by linarith) hjpos.ne']
      apply Real.log_le_log (by rw [ht]; linarith)
      rw [ht]; nlinarith
    have hla := le_abs_self (Real.log (max C 1))
    have hlc := neg_abs_le (Real.log c)
    have hNd := mul_le_mul_of_nonneg_left hlogb hN0
    have hdistr : (N : ℝ) * (Real.log (R' + 2) + Real.log j)
        = N * Real.log (R' + 2) + N * Real.log j := by ring
    rw [hK₂, div_mul_eq_mul_div, le_div_iff₀ hlog2]
    have h2 : ((zerosIn f (closedBall (pt σ₀ t) ρ)).ncard : ℝ) * Real.log 2
        ≤ |Real.log (max C 1)| + |Real.log c| + N * Real.log (R' + 2) + N * Real.log j := by
      linarith
    calc _ ≤ |Real.log (max C 1)| + |Real.log c| + N * Real.log (R' + 2) + N * Real.log j := h2
      _ ≤ (|Real.log (max C 1)| + |Real.log c| + N * Real.log (R' + 2) + N) * Real.log j := by
          nlinarith [mul_nonneg hA0 (by linarith : (0:ℝ) ≤ Real.log j - 1)]
  -- the zero sets near height `±(j + 1/2)` are finite
  have hfin : ∀ t : ℝ, R' + 1 ≤ |t| → (zerosIn f (closedBall (pt σ₀ t) ρ)).Finite := by
    intro t ht
    have hρ0 : 0 ≤ ρ := by rw [hρ]; linarith
    have hfa : AnalyticOnNhd ℂ f (closedBall (pt σ₀ t) ρ) := by
      intro z hz
      have := mem_closedBall_pt_bounds hz
      exact hf z (by linarith [this.2.2.1])
    have hcen : f (pt σ₀ t) ≠ 0 := by
      intro h
      have hpt : pt σ₀ t = (σ₀ : ℂ) + Complex.I * t := by apply Complex.ext <;> simp [pt]
      have := hlow t
      rw [← hpt, h, norm_zero] at this
      linarith
    exact zerosIn_finite (isCompact_closedBall _ _) hfa
      (fun u hu => analyticOrderAt_ne_top_of_ne_zero_center hρ0 hfa hcen hu)
  have htU : R' + 1 ≤ |(j : ℝ) + 1 / 2| := by rw [abs_of_pos (by linarith)]; linarith
  have htD : R' + 1 ≤ |-((j : ℝ) + 1 / 2)| := by rw [abs_neg, abs_of_pos (by linarith)]; linarith
  set ZU : Finset ℝ := (hfin ((j : ℝ) + 1 / 2) htU).toFinset.image Complex.im with hZU
  set ZD : Finset ℝ := (hfin (-((j : ℝ) + 1 / 2)) htD).toFinset.image (fun u : ℂ => -u.im) with hZD
  set Z : Finset ℝ := ZU ∪ ZD with hZ
  have hZcard : (Z.card : ℝ) ≤ 2 * (K₂ * Real.log j) := by
    have h1 : (ZU.card : ℝ) ≤ K₂ * Real.log j := by
      have := hcount' ((j:ℝ) + 1 / 2) (abs_of_pos (by linarith))
      rw [Set.ncard_eq_toFinset_card _ (hfin ((j : ℝ) + 1 / 2) htU)] at this
      refine le_trans ?_ this
      exact_mod_cast Finset.card_image_le
    have h2 : (ZD.card : ℝ) ≤ K₂ * Real.log j := by
      have := hcount' (-((j:ℝ) + 1 / 2)) (by rw [abs_neg, abs_of_pos (by linarith)])
      rw [Set.ncard_eq_toFinset_card _ (hfin (-((j : ℝ) + 1 / 2)) htD)] at this
      refine le_trans ?_ this
      exact_mod_cast Finset.card_image_le
    have h3 : (Z.card : ℝ) ≤ ZU.card + ZD.card := by exact_mod_cast Finset.card_union_le _ _
    linarith
  set δ : ℝ := c₁ / Real.log j with hδ
  have hδpos : 0 < δ := by rw [hδ]; exact div_pos hc₁pos hlogj0
  have h2δ : 2 * δ * Z.card ≤ 1 := by
    have hlj : Real.log j ≠ 0 := hlogj0.ne'
    have hK₂1 : K₂ + 1 ≠ 0 := by linarith
    have hq0 : 0 ≤ 2 * δ := by linarith
    calc 2 * δ * Z.card ≤ 2 * δ * (2 * (K₂ * Real.log j)) := mul_le_mul_of_nonneg_left hZcard hq0
      _ = K₂ / (K₂ + 1) := by rw [hδ, hc₁]; field_simp; ring
      _ ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  obtain ⟨T, hTj, hTj1, hTavoid⟩ := RankinSelbergDelta.ZeroAvoid.exists_avoid Z hδpos h2δ j
  refine ⟨T, hTj, hTj1, fun x hx1 hx2 => ?_⟩
  -- the common argument for one sign
  have key : ∀ τ tc : ℝ, |τ| = T → |τ - tc| ≤ 1 / 2 →
      (∀ u ∈ zerosIn f (closedBall (pt σ₀ tc) ρ), δ ≤ |τ - u.im|) →
      f ((x : ℂ) + τ * Complex.I) ≠ 0 ∧
        ‖logDeriv f ((x : ℂ) + τ * Complex.I)‖ ≤ (2 * C' + 2 * K₁ / c₁) * Real.log j ^ 2 := by
    intro τ tc hτT hτc havoid
    have hτabs : 8 * σ₀ + 10 ≤ |τ| := by rw [hτT]; linarith
    have hτ2 : 2 ≤ |τ| := by linarith
    obtain ⟨S, m, hS1, hS2, hineq⟩ := hexp τ hτabs
    have hsum := sum_mult_le hσ₀ hL hne hC' hτ2 hS1 hineq
    set z₀ : ℂ := (σ₀ : ℂ) + Complex.I * τ with hz₀
    set z : ℂ := (x : ℂ) + τ * Complex.I with hz
    have hzim : z.im = τ := by simp [hz]
    have hzmem : z ∈ closedBall z₀ (σ₀ + 1) := by
      rw [mem_closedBall, Complex.dist_eq]
      have : z - z₀ = ((x - σ₀ : ℝ) : ℂ) := by apply Complex.ext <;> simp [hz, hz₀]
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]; constructor <;> linarith
    have hfar : ∀ u ∈ S, δ ≤ |τ - u.im| := by
      intro u hu
      obtain ⟨humem, hu0, -⟩ := hS1 u hu
      apply havoid u
      refine ⟨?_, hu0⟩
      rw [mem_closedBall, dist_eq_norm]
      rw [mem_ball, dist_eq_norm] at humem
      have hpt : pt σ₀ tc = z₀ + ((tc - τ : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp [pt, hz₀]
      calc ‖u - pt σ₀ tc‖ = ‖(u - z₀) - ((tc - τ : ℝ) : ℂ) * Complex.I‖ := by
            rw [hpt]; congr 1; ring
        _ ≤ ‖u - z₀‖ + ‖((tc - τ : ℝ) : ℂ) * Complex.I‖ := norm_sub_le _ _
        _ ≤ 2 * (σ₀ + 1) + 1 / 2 := by
            apply add_le_add humem.le
            rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
              abs_sub_comm]
            exact hτc
        _ ≤ ρ := by rw [hρ]; linarith
    have hz0 : f z ≠ 0 := by
      intro h
      have hzS : z ∈ S := hS2 z (by
        rw [mem_ball]; rw [mem_closedBall] at hzmem; linarith) h
      have := hfar z hzS
      rw [hzim, sub_self, abs_zero] at this
      linarith
    refine ⟨hz0, ?_⟩
    have h1 := hineq z hzmem hz0
    have hsumnorm : ‖∑ u ∈ S, (m u : ℂ) / (z - u)‖ ≤ (∑ u ∈ S, (m u : ℝ)) / δ := by
      rw [Finset.sum_div]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u hu => ?_)
      obtain ⟨-, -, hm1⟩ := hS1 u hu
      have hm0 : (0:ℝ) < m u := by exact_mod_cast (by omega : (0:ℤ) < m u)
      have hzu : δ ≤ ‖z - u‖ := by
        calc δ ≤ |τ - u.im| := hfar u hu
          _ = |(z - u).im| := by rw [Complex.sub_im, hzim]
          _ ≤ ‖z - u‖ := Complex.abs_im_le_norm _
      rw [norm_div, show ((m u : ℤ) : ℂ) = ((m u : ℝ) : ℂ) from (Complex.ofReal_intCast _).symm,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm0]
      exact div_le_div_of_nonneg_left hm0.le hδpos hzu
    have hlogT : Real.log |τ| ≤ 2 * Real.log j := by
      rw [hτT]
      have hT1 : Real.log T ≤ Real.log ((j : ℝ) + 1) := Real.log_le_log (by linarith) hTj1
      have hsq : Real.log ((j : ℝ) ^ 2) = 2 * Real.log j := by rw [Real.log_pow]; norm_num
      have h2 : Real.log ((j:ℝ) + 1) ≤ 2 * Real.log j := by
        rw [← hsq]
        apply Real.log_le_log (by linarith)
        nlinarith
      linarith
    have hsumle : ∑ u ∈ S, (m u : ℝ) ≤ K₁ * (2 * Real.log j) :=
      hsum.trans (mul_le_mul_of_nonneg_left hlogT hK₁0)
    have hlogsq : Real.log j ≤ Real.log j ^ 2 := by nlinarith
    have hlj : Real.log j ≠ 0 := hlogj0.ne'
    have hc₁ne : c₁ ≠ 0 := hc₁pos.ne'
    calc ‖logDeriv f z‖
        = ‖(logDeriv f z - ∑ u ∈ S, (m u : ℂ) / (z - u)) + ∑ u ∈ S, (m u : ℂ) / (z - u)‖ := by
          congr 1; ring
      _ ≤ ‖logDeriv f z - ∑ u ∈ S, (m u : ℂ) / (z - u)‖ + ‖∑ u ∈ S, (m u : ℂ) / (z - u)‖ :=
          norm_add_le _ _
      _ ≤ C' * Real.log |τ| + (∑ u ∈ S, (m u : ℝ)) / δ := add_le_add h1 hsumnorm
      _ ≤ C' * (2 * Real.log j) + (K₁ * (2 * Real.log j)) / δ :=
          add_le_add (mul_le_mul_of_nonneg_left hlogT hC'.le)
            (div_le_div_of_nonneg_right hsumle hδpos.le)
      _ = 2 * C' * Real.log j + 2 * K₁ / c₁ * Real.log j ^ 2 := by
          rw [hδ]; field_simp
      _ ≤ (2 * C' + 2 * K₁ / c₁) * Real.log j ^ 2 := by
          nlinarith [mul_le_mul_of_nonneg_left hlogsq (by positivity : (0:ℝ) ≤ 2 * C')]
  have hZU_sub : ∀ u ∈ zerosIn f (closedBall (pt σ₀ ((j:ℝ) + 1 / 2)) ρ), δ ≤ |T - u.im| := by
    intro u hu
    apply hTavoid
    rw [hZ]; apply Finset.mem_union_left
    rw [hZU, Finset.mem_image]
    exact ⟨u, (hfin ((j : ℝ) + 1 / 2) htU).mem_toFinset.mpr hu, rfl⟩
  have hZD_sub : ∀ u ∈ zerosIn f (closedBall (pt σ₀ (-((j:ℝ) + 1 / 2))) ρ),
      δ ≤ |-T - u.im| := by
    intro u hu
    have := hTavoid (-u.im) (by
      rw [hZ]; apply Finset.mem_union_right
      rw [hZD, Finset.mem_image]
      exact ⟨u, (hfin (-((j : ℝ) + 1 / 2)) htD).mem_toFinset.mpr hu, rfl⟩)
    rwa [show -T - u.im = -(T - -u.im) by ring, abs_neg]
  have hT0 : 0 ≤ T := by linarith
  refine ⟨key T ((j:ℝ) + 1 / 2) (abs_of_nonneg hT0) ?_ hZU_sub, ?_⟩
  · rw [abs_le]; constructor <;> linarith
  · have hk := key (-T) (-((j:ℝ) + 1 / 2)) (by rw [abs_neg, abs_of_nonneg hT0])
      (by rw [show -T - -((j:ℝ) + 1 / 2) = -(T - (j + 1 / 2)) by ring, abs_neg, abs_le]
          constructor <;> linarith) hZD_sub
    have e : ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) = (x : ℂ) - T * Complex.I := by
      push_cast; ring
    rw [e] at hk
    exact hk

end RankinSelbergDelta.HorizontalEdge


namespace RankinSelbergDelta.RankinSelberg

open Complex UpperHalfPlane MeasureTheory Set Filter RankinSelbergDelta.Eisenstein RankinSelbergDelta.ArgPrinciple
open scoped Real Topology Modular FourierTransform

variable {F : Type*} [FunLike F ℍ ℂ] (k : ℤ)
  [cf : CuspFormClass F (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma 1)) k]

/-! #### A. The entire pole-free function `(s − 1) G(s)`, continued through `s = 0`

Lean's `Gfull k f 0 = 0` literally (`Complex.Gamma 0 = 0`, `1/0 = 0`), while the true continuation
`G(0) = rsPre′(0) · (−∫_𝒟 Φ)` is finite: `rsHfull` is not continuous at `0`. The entire
`rsHent(s) = (rsPre(s)/s) · (s(s−1) rsJ(s) + ∫_𝒟 Φ)` equals `(s − 1) G(s)` off `{0, 1}`, with
`rsPre(s)/s = (4π)^{s+k−1} π^s / (2 Γ(s+k−1) Γ(s+1))` entire. -/

lemma rsPre_zero : rsPre k 0 = 0 := by
  unfold rsPre; simp [Complex.Gamma_zero]

include cf in
lemma Gfull_zero (f : F) : Gfull k f 0 = 0 := by
  unfold Gfull
  rw [if_pos (by simp), rsG_eq_rsPre_mul_rsLambda, rsPre_zero, zero_mul]

/-- `rsPre(s)/s`, entire: `(4π)^{s+k−1} π^s / (2 Γ(s+k−1) Γ(s+1))`. -/
noncomputable def rsPreS (s : ℂ) : ℂ :=
  ((4 * Real.pi : ℝ) : ℂ) ^ (s + k - 1) * (Real.pi : ℂ) ^ s
    * ((Complex.Gamma (s + k - 1))⁻¹ * (Complex.Gamma (s + 1))⁻¹) / 2

lemma differentiable_rsPreS : Differentiable ℂ (rsPreS k) := by
  have h4 : (((4 * Real.pi : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hπ : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h1 : Differentiable ℂ fun s : ℂ => ((4 * Real.pi : ℝ) : ℂ) ^ (s + k - 1) := fun s =>
    ((differentiableAt_id.add_const _).sub_const _).const_cpow (Or.inl h4)
  have h2 : Differentiable ℂ fun s : ℂ => (Real.pi : ℂ) ^ s := fun s =>
    differentiableAt_id.const_cpow (Or.inl hπ)
  have h3 : Differentiable ℂ fun s : ℂ => (Complex.Gamma (s + k - 1))⁻¹ :=
    Complex.differentiable_one_div_Gamma.comp ((differentiable_id.add_const _).sub_const _)
  have h4' : Differentiable ℂ fun s : ℂ => (Complex.Gamma (s + 1))⁻¹ :=
    Complex.differentiable_one_div_Gamma.comp (differentiable_id.add_const _)
  exact ((h1.mul h2).mul (h3.mul h4')).div_const 2

lemma rsPre_eq_mul_rsPreS (s : ℂ) : rsPre k s = s * rsPreS k s := by
  unfold rsPre rsPreS
  by_cases hs : s = 0
  · subst hs; simp [Complex.Gamma_zero]
  · rw [Complex.Gamma_add_one s hs, mul_inv]
    have h1 : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    linear_combination (-(((4 * Real.pi : ℝ) : ℂ) ^ (s + k - 1) * (Real.pi : ℂ) ^ s
      * ((Complex.Gamma (s + k - 1))⁻¹ * (Complex.Gamma s)⁻¹) / 2)) * h1

include cf in
/-- The entire function `(s − 1) G(s)`: `rsHent(s) = rsPreS(s) · (s (s − 1) rsJ(s) + ∫_𝒟 Φ)`. -/
noncomputable def rsHent (f : F) (s : ℂ) : ℂ :=
  rsPreS k s * (s * (s - 1) * rsJ k f s + ((∫ z in (𝒟 : Set ℍ), phi k f z : ℝ) : ℂ))

include cf in
lemma rsHent_eq (f : F) (hk : 0 < k) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    rsHent k f s = (s - 1) * Gfull k f s := by
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  rw [Gfull_eq_rsG k f hk, rsG_eq_rsPre_mul_rsLambda, rsPre_eq_mul_rsPreS]
  unfold rsLambda rsHent
  field_simp
  ring

include cf in
lemma differentiable_rsHent (f : F) (hk : 0 < k) : Differentiable ℂ (rsHent k f) := by
  have h1 : Differentiable ℂ (fun s : ℂ => s * (s - 1) * rsJ k f s) :=
    (differentiable_id.mul (differentiable_id.sub_const 1)).mul (differentiable_rsJ k f hk)
  exact (differentiable_rsPreS k).mul (h1.add_const _)

include cf in
lemma analyticAt_rsHent (f : F) (hk : 0 < k) (s : ℂ) : AnalyticAt ℂ (rsHent k f) s :=
  (differentiable_rsHent k f hk).analyticAt s

include cf in
/-- Off `{0, 1}`, where `G ≠ 0`: `H′/H = G′/G + 1/(s − 1)`. -/
lemma logDeriv_rsHent_eq (f : F) (hk : 0 < k) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hG : Gfull k f s ≠ 0) :
    logDeriv (rsHent k f) s = logDeriv (Gfull k f) s + (s - 1)⁻¹ := by
  have hev : rsHent k f =ᶠ[𝓝 s] fun t => (t - 1) * Gfull k f t := by
    filter_upwards [eventually_ne_nhds hs0, eventually_ne_nhds hs1] with t ht0 ht1
    exact rsHent_eq k f hk ht0 ht1
  rw [show logDeriv (rsHent k f) s = logDeriv (fun t => (t - 1) * Gfull k f t) s from
    (by rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds])]
  rw [logDeriv_mul (f := fun t => t - 1) (g := Gfull k f) s (sub_ne_zero.mpr hs1) hG
    (differentiableAt_id.sub_const 1) (differentiableAt_Gfull k f hk hs0 hs1), add_comm]
  congr 1
  rw [logDeriv_apply, deriv_sub_const, deriv_id'', one_div]

open scoped Classical in
include cf in
/-- **The truncated explicit formula on any rectangle** (through `s = 0`): for a closed rectangle
`K` on whose boundary `G ≠ 0` (which excludes `0`, where Lean's `G` vanishes) and `s ≠ 1`, and `h`
analytic on a neighbourhood of `K`: `2πi ∑_ρ m_ρ h(ρ) = ∮_{∂K} (G′/G)·h + 2πi·h(1)·[1 ∈ K]`, the sum
over the divisor of the entire `rsHent = (s − 1)G` on `K` (the zeros of the continuation of `G`,
with multiplicity; `rsHent 1 ≠ 0`). -/
theorem explicitFormula_Gfull_rect' (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k)
    (z w : ℂ) (hzw : z.re < w.re ∧ z.im < w.im) (h : ℂ → ℂ)
    (hh : AnalyticOnNhd ℂ h (closedRect z w))
    (hne : ∀ s ∈ rectBoundary z w, Gfull k f s ≠ 0) (h1 : (1 : ℂ) ∉ rectBoundary z w) :
    2 * Real.pi * Complex.I * ∑ᶠ u, ((MeromorphicOn.divisor (rsHent k f) (closedRect z w)) u : ℂ) * h u
      = rectBoundaryIntegral (fun s => logDeriv (Gfull k f) s * h s) z w
        + (if (1 : ℂ) ∈ closedRect z w then 2 * Real.pi * Complex.I * h 1 else 0) := by
  have hs0 : ∀ s ∈ rectBoundary z w, s ≠ 0 := by
    intro s hs heq
    apply hne s hs
    rw [heq]; exact Gfull_zero k f
  have hfa : AnalyticOnNhd ℂ (rsHent k f) (closedRect z w) := fun s _ => analyticAt_rsHent k f hk s
  have hneH : ∀ s ∈ rectBoundary z w, rsHent k f s ≠ 0 := by
    intro s hs
    have hs1 : s ≠ 1 := fun heq => h1 (heq ▸ hs)
    rw [rsHent_eq k f hk (hs0 s hs) hs1]
    exact mul_ne_zero (sub_ne_zero.mpr hs1) (hne s hs)
  rw [← rectBoundaryIntegral_logDeriv_mul (rsHent k f) h z w hzw hfa hh hneH]
  have hsplit : ∀ s ∈ rectBoundary z w, logDeriv (rsHent k f) s * h s
      = logDeriv (Gfull k f) s * h s + h s / (s - 1) := by
    intro s hs
    have hs1 : s ≠ 1 := fun heq => h1 (heq ▸ hs)
    rw [logDeriv_rsHent_eq k f hk (hs0 s hs) hs1 (hne s hs)]
    rw [div_eq_mul_inv]; ring
  have hE1 : EdgeIntegrable (fun s => logDeriv (Gfull k f) s * h s) z w := by
    refine EdgeIntegrable.of_continuousOn ?_
    intro s hs
    have hs1 : s ≠ 1 := fun heq => h1 (heq ▸ hs)
    have hG := analyticAt_Gfull k f hk (hs0 s hs) hs1
    apply ContinuousAt.continuousWithinAt
    exact (hG.deriv.continuousAt.div hG.continuousAt (hne s hs)).mul (hh s hs.1).continuousAt
  have hE2 : EdgeIntegrable (fun s => h s / (s - 1)) z w := by
    refine EdgeIntegrable.of_continuousOn ?_
    refine (hh.continuousOn.mono (rectBoundary_subset z w)).div
      (continuousOn_id.sub continuousOn_const) ?_
    intro s hs
    exact sub_ne_zero.mpr fun heq => h1 (heq ▸ hs)
  rw [rectBoundaryIntegral_congr hsplit, rectBoundaryIntegral_add hE1 hE2]
  congr 1
  by_cases hK : (1 : ℂ) ∈ closedRect z w
  · rw [if_pos hK]
    have hint : z.re < (1 : ℂ).re ∧ (1 : ℂ).re < w.re ∧ z.im < (1 : ℂ).im ∧ (1 : ℂ).im < w.im := by
      have hK' := hK
      rw [closedRect, Complex.mem_reProdIm, Set.uIcc_of_le hzw.1.le, Set.uIcc_of_le hzw.2.le] at hK'
      obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ := hK'
      refine ⟨lt_of_le_of_ne a1 ?_, lt_of_le_of_ne a2 ?_, lt_of_le_of_ne a3 ?_, lt_of_le_of_ne a4 ?_⟩
      · exact fun e => h1 ⟨hK, Or.inl e.symm⟩
      · exact fun e => h1 ⟨hK, Or.inr (Or.inl e)⟩
      · exact fun e => h1 ⟨hK, Or.inr (Or.inr (Or.inl e.symm))⟩
      · exact fun e => h1 ⟨hK, Or.inr (Or.inr (Or.inr e))⟩
    exact rectBoundaryIntegral_div_sub hh hint
  · rw [if_neg hK]
    exact rectBoundaryIntegral_div_sub_of_notMem hh hK

/-! #### B. The functional equation for the logarithmic derivative -/

lemma rsPre_ne_zero_of_not_int (hk : 0 < k) {s : ℂ} (h1 : ∀ m : ℕ, s ≠ -(m : ℂ))
    (h2 : ∀ m : ℕ, s + k - 1 ≠ -(m : ℂ)) : rsPre k s ≠ 0 := by
  have h4π : ((4 * Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hP1 : ((4 * Real.pi : ℝ) : ℂ) ^ (s + k - 1) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; push_neg; intro h; exact absurd h h4π
  have hP2 : (Real.pi : ℂ) ^ s ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; push_neg; intro h; exact absurd h hπ
  have hΓ1 : Complex.Gamma (s + k - 1) ≠ 0 := Complex.Gamma_ne_zero h2
  have hΓ2 : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero h1
  unfold rsPre
  exact div_ne_zero (mul_ne_zero (mul_ne_zero hP1 hP2)
    (mul_ne_zero (inv_ne_zero hΓ1) (inv_ne_zero hΓ2))) two_ne_zero

/-- On the line `Re s = 1 − σ`, `1 < σ < 2`: `rsPre(s) ≠ 0`. -/
lemma rsPre_ne_zero_left (hk : 0 < k) {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ < 2) (y : ℝ) :
    rsPre k (((1 - σ : ℝ) : ℂ) + y * Complex.I) ≠ 0 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  refine rsPre_ne_zero_of_not_int k hk ?_ ?_
  · intro m h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, Complex.neg_re, Complex.natCast_re] at hre
    rcases Nat.eq_zero_or_pos m with hm | hm
    · have : (m : ℝ) = 0 := by exact_mod_cast hm
      rw [this] at hre; linarith
    · have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      linarith
  · intro m h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, Complex.neg_re,
      Complex.natCast_re, Complex.intCast_re, Complex.one_re] at hre
    rcases Nat.eq_zero_or_pos m with hm | hm
    · have : (m : ℝ) = 0 := by exact_mod_cast hm
      rw [this] at hre
      rcases le_or_gt k 1 with hk' | hk'
      · have : (k : ℝ) ≤ 1 := by exact_mod_cast hk'
        linarith
      · have h2 : (2 : ℤ) ≤ k := by omega
        have : (2 : ℝ) ≤ k := by exact_mod_cast h2
        linarith
    · have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      linarith

include cf in
/-- The functional equation of `G`: `G(1 − s) = (rsPre(1−s)/rsPre(s)) · G(s)` when `rsPre(s) ≠ 0`. -/
lemma Gfull_one_sub (f : F) (hk : 0 < k) {s : ℂ} (hP : rsPre k s ≠ 0) :
    Gfull k f (1 - s) = rsPre k (1 - s) / rsPre k s * Gfull k f s := by
  rw [Gfull_eq_rsG k f hk, Gfull_eq_rsG k f hk, div_mul_eq_mul_div, eq_div_iff hP, mul_comm]
  exact (rsG_functional_equation k f s).symm

include cf in
/-- `G ≠ 0` on the line `Re s = 1 − σ`, `1 < σ < 2` (by the functional equation). -/
lemma Gfull_ne_zero_left (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k) {σ : ℝ}
    (hσ1 : 1 < σ) (hσ2 : σ < 2) (y : ℝ) :
    Gfull k f (((1 - σ : ℝ) : ℂ) + y * Complex.I) ≠ 0 := by
  have e : (((1 - σ : ℝ) : ℂ) + y * Complex.I) = 1 - ((σ : ℂ) - y * Complex.I) := by
    push_cast; ring
  have hP : rsPre k ((σ : ℂ) - y * Complex.I) ≠ 0 := rsPre_ne_zero k hk (by simp; linarith)
  rw [e, Gfull_one_sub k f hk hP, ← e]
  exact mul_ne_zero (div_ne_zero (rsPre_ne_zero_left k hk hσ1 hσ2 y) hP)
    (Gfull_ne_zero_of_one_lt k f hk hf (by simp; linarith))

include cf in
/-- **The functional equation for the logarithmic derivative**:
`(G′/G)(1 − s) = (rsPre′/rsPre)(s) + (rsPre′/rsPre)(1 − s) − (G′/G)(s)`. -/
theorem logDeriv_Gfull_one_sub (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k) {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hP : rsPre k s ≠ 0) (hP' : rsPre k (1 - s) ≠ 0)
    (hG : Gfull k f s ≠ 0) :
    logDeriv (Gfull k f) (1 - s)
      = logDeriv (rsPre k) s + logDeriv (rsPre k) (1 - s) - logDeriv (Gfull k f) s := by
  have h1s0 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have h1s1 : (1 : ℂ) - s ≠ 1 := by
    intro h; apply hs0; linear_combination -h
  have hG' : Gfull k f (1 - s) ≠ 0 := by
    rw [Gfull_one_sub k f hk hP]; exact mul_ne_zero (div_ne_zero hP' hP) hG
  have hP1 : HasDerivAt (rsPre k) (deriv (rsPre k) s) s := (differentiable_rsPre k s).hasDerivAt
  have hP2 : HasDerivAt (fun w => rsPre k (1 - w)) (-(deriv (rsPre k) (1 - s))) s := by
    have := (differentiable_rsPre k (1 - s)).hasDerivAt.comp s ((hasDerivAt_id s).const_sub 1)
    simpa using this
  have hG1 : HasDerivAt (Gfull k f) (deriv (Gfull k f) s) s :=
    (differentiableAt_Gfull k f hk hs0 hs1).hasDerivAt
  have hG2 : HasDerivAt (fun w => Gfull k f (1 - w)) (-(deriv (Gfull k f) (1 - s))) s := by
    have := (differentiableAt_Gfull k f hk h1s0 h1s1).hasDerivAt.comp s
      ((hasDerivAt_id s).const_sub 1)
    simpa using this
  have hL : HasDerivAt (fun w => rsPre k (1 - w) * Gfull k f w)
      (-(deriv (rsPre k) (1 - s)) * Gfull k f s + rsPre k (1 - s) * deriv (Gfull k f) s) s :=
    hP2.mul hG1
  have hR : HasDerivAt (fun w => rsPre k w * Gfull k f (1 - w))
      (deriv (rsPre k) s * Gfull k f (1 - s) + rsPre k s * -(deriv (Gfull k f) (1 - s))) s :=
    hP1.mul hG2
  have hLR : (fun w => rsPre k (1 - w) * Gfull k f w) = fun w => rsPre k w * Gfull k f (1 - w) := by
    funext w
    rw [Gfull_eq_rsG k f hk, Gfull_eq_rsG k f hk]
    exact rsG_functional_equation k f w
  rw [hLR] at hL
  have hderiv := hL.unique hR
  have hD : Gfull k f (1 - s) = rsPre k (1 - s) * Gfull k f s / rsPre k s := by
    rw [Gfull_one_sub k f hk hP]; ring
  have hD' : deriv (Gfull k f) (1 - s)
      = (deriv (rsPre k) s * Gfull k f (1 - s) + deriv (rsPre k) (1 - s) * Gfull k f s
          - rsPre k (1 - s) * deriv (Gfull k f) s) / rsPre k s := by
    rw [eq_div_iff hP]; linear_combination hderiv
  simp only [logDeriv_apply]
  rw [hD', hD]
  field_simp

/-! #### C. A uniform bound on `G′/G` to the right of `Re s = 2` -/

include cf in
lemma exists_norm_logDeriv_Gfull_le (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k) :
    ∃ L : ℝ, ∀ s : ℂ, 2 ≤ s.re → ‖logDeriv (Gfull k f) s‖ ≤ L := by
  set Λ := rsVonMangoldt (rsCoeff f) k with hΛdef
  have hΛ : ∀ n, 0 ≤ Λ n := rsVonMangoldt_nonneg _ _
  set M : ℕ → ℝ := fun n => (2 / (1 : ℝ)) * ‖dlvpTerm Λ ((1 + 1 / 2 : ℝ) : ℂ) n‖ with hM
  have hMsum : Summable M :=
    (summable_norm_iff.mpr (summable_dlvpTerm_rs k f hk hf (s := ((1 + 1 / 2 : ℝ) : ℂ))
      (by simp only [Complex.ofReal_re]; linarith))).mul_left _
  refine ⟨∑' n, M n, fun s hs => ?_⟩
  rw [logDeriv_Gfull_eq_neg_tsum k f hk hf (by linarith), norm_neg]
  have hvm : ∀ n, ‖vmTerm Λ s n‖ ≤ M n := fun n =>
    norm_vmTerm_le_majorant Λ hΛ (ε := 1) (by norm_num) (by linarith) n
  have hsum : Summable fun n => ‖vmTerm Λ s n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hvm hMsum
  exact (norm_tsum_le_tsum_norm hsum).trans (hsum.tsum_le_tsum hvm hMsum)

/-! #### D. Zero-avoiding heights for `G` -/

include cf in
/-- **Zero-avoiding heights for `G = Gfull k f`** (the generic theorem instantiated with the growth
`exists_norm_Gfull_le_halfStrip`, the lower bound `exists_norm_Gfull_ge` and the uniform bound on
`G′/G` far to the right): heights `T_j ∈ [j, j+1]` with `G(x ± iT_j) ≠ 0` and
`‖G′/G(x ± iT_j)‖ ≤ C₂ log² j` for `−1 ≤ x ≤ 2`. -/
theorem exists_zeroAvoiding_heights_Gfull (f : F) (hk : 0 < k)
    (hf : IsHeckeEigenCoeffs (rsCoeff f) k) :
    ∃ (j₀ : ℕ) (C₂ : ℝ), 0 < C₂ ∧ ∀ j : ℕ, j₀ ≤ j → ∃ T : ℝ, (j : ℝ) ≤ T ∧ T ≤ j + 1 ∧
      ∀ x : ℝ, -1 ≤ x → x ≤ 2 →
        (Gfull k f ((x : ℂ) + T * Complex.I) ≠ 0 ∧
          ‖logDeriv (Gfull k f) ((x : ℂ) + T * Complex.I)‖ ≤ C₂ * Real.log j ^ 2) ∧
        (Gfull k f ((x : ℂ) - T * Complex.I) ≠ 0 ∧
          ‖logDeriv (Gfull k f) ((x : ℂ) - T * Complex.I)‖ ≤ C₂ * Real.log j ^ 2) := by
  obtain ⟨σ₀, hσ₀, hlow⟩ := exists_norm_Gfull_ge k f hk hf
  obtain ⟨C, N, hC, hgrow⟩ := exists_norm_Gfull_le_halfStrip k f hk (⌈8 * σ₀⌉₊ + 8)
  obtain ⟨L, hL⟩ := exists_norm_logDeriv_Gfull_le k f hk hf
  refine RankinSelbergDelta.HorizontalEdge.exists_zeroAvoiding_heights (f := Gfull k f) (σ₀ := σ₀)
    (C := C) (c := 3 / 8) (L := L) (N := N) hσ₀ hC (by norm_num)
    (fun z hz => analyticAt_Gfull_of_one_le_abs_im k f hk hz) ?_ hlow ?_
    (fun z hz => Gfull_ne_zero_of_one_lt k f hk hf hz)
  · intro z hz hzim
    apply hgrow z _ hzim
    have := Nat.le_ceil (8 * σ₀)
    push_cast
    linarith
  · intro t
    exact hL _ (by simp; linarith)

/-! #### E. The reversed test function and the rectangle with explicit corners -/

/-- `ĝ_rev(w) = ĝ(1 − w)` for `g_rev(y) = g(−y) e^{−y}`. -/
lemma ghat_rev (g : ℝ → ℂ) (w : ℂ) :
    ghat (fun y : ℝ => g (-y) * Complex.exp (-(y : ℂ))) w = ghat g (1 - w) := by
  unfold ghat
  rw [← MeasureTheory.integral_neg_eq_self (fun x : ℝ => g x * Complex.exp ((1 - w) * x))]
  congr 1
  funext y
  simp only [neg_neg]
  push_cast
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  ring

lemma rectBoundaryIntegral_mk (f : ℂ → ℂ) (a b c d : ℝ) :
    rectBoundaryIntegral f ⟨a, c⟩ ⟨b, d⟩
      = (∫ x : ℝ in a..b, f (x + c * Complex.I)) - (∫ x : ℝ in a..b, f (x + d * Complex.I))
        + Complex.I • (∫ y : ℝ in c..d, f (b + y * Complex.I))
        - Complex.I • (∫ y : ℝ in c..d, f (a + y * Complex.I)) := rfl

/-! #### F. The explicit formula as a limit along zero-avoiding heights -/

include cf in
/-- **The explicit formula for the Rankin–Selberg square `G = Gfull k f`.** For `1 < σ < 2` and a
test function `g` with `ĝ(s) = ∫ g(x) e^{sx} dx` entire, the Laplace-inversion hypotheses on the
two lines `Re s = σ` (for `g`) and (for `g_rev(y) = g(−y)e^{−y}`, i.e. the line `Re s = 1 − σ`),
the horizontal decay `‖ĝ(s)‖ ≤ B/(Im s)²` on the strip `1 − σ ≤ Re s ≤ σ`, and the archimedean
kernel `(rsPre′/rsPre(σ − it) + rsPre′/rsPre(1 − σ + it)) ĝ(1 − σ + it)` integrable on `ℝ` —
all satisfied by `g ∈ C_c^∞` — there are heights `T_j ∈ [j, j+1]` such that
`∑_{ρ ∈ K_j} m_ρ ĝ(ρ) → ĝ(1) − ∑_n Λ_G(n) g(log n) − ∑_n Λ_G(n) g(−log n)/n − (1/2π) ∫ (kernel)`,
the sum over the zeros `ρ` (with multiplicity, as the divisor of the entire `(s − 1)G`) of `G` in the
rectangle `K_j = [1 − σ, σ] × [−T_j, T_j]`. -/
theorem explicitFormula_Gfull (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k) {σ : ℝ}
    (hσ1 : 1 < σ) (hσ2 : σ < 2) (g : ℝ → ℂ) (hgc : Continuous g)
    (hga : ∀ s : ℂ, AnalyticAt ℂ (ghat g) s)
    (hg : Integrable (fun x : ℝ => g x * Complex.exp (σ * x)))
    (hF : Integrable (𝓕 (fun x : ℝ => g x * Complex.exp (σ * x))))
    (hg' : Integrable (fun x : ℝ => g (-x) * Complex.exp (-(x : ℂ)) * Complex.exp (σ * x)))
    (hF' : Integrable (𝓕 (fun x : ℝ => g (-x) * Complex.exp (-(x : ℂ)) * Complex.exp (σ * x))))
    (hdec : ∃ B : ℝ, ∀ s : ℂ, 1 - σ ≤ s.re → s.re ≤ σ → 1 ≤ |s.im| → ‖ghat g s‖ * s.im ^ 2 ≤ B)
    (hArch : Integrable (fun t : ℝ =>
      (logDeriv (rsPre k) ((σ : ℂ) - t * Complex.I)
          + logDeriv (rsPre k) (((1 - σ : ℝ) : ℂ) + t * Complex.I))
        * ghat g (((1 - σ : ℝ) : ℂ) + t * Complex.I))) :
    ∃ T : ℕ → ℝ, (∀ j : ℕ, (j : ℝ) ≤ T j ∧ T j ≤ j + 1) ∧
      Tendsto (fun j : ℕ => ∑ᶠ u, ((MeromorphicOn.divisor (rsHent k f)
          (closedRect ⟨1 - σ, -(T j)⟩ ⟨σ, T j⟩)) u : ℂ) * ghat g u) atTop
        (𝓝 (ghat g 1
          - ∑' n, (if 2 ≤ n then (rsVonMangoldt (rsCoeff f) k n : ℂ) * g (Real.log n) else 0)
          - ∑' n, (if 2 ≤ n then (rsVonMangoldt (rsCoeff f) k n : ℂ) * (g (-(Real.log n)) / n)
              else 0)
          - (1 / (2 * Real.pi)) * ∫ t : ℝ, (logDeriv (rsPre k) ((σ : ℂ) - t * Complex.I)
              + logDeriv (rsPre k) (((1 - σ : ℝ) : ℂ) + t * Complex.I))
              * ghat g (((1 - σ : ℝ) : ℂ) + t * Complex.I))) := by
  classical
  obtain ⟨j₀, C₂, hC₂, hT⟩ := exists_zeroAvoiding_heights_Gfull k f hk hf
  choose! T₀ hT₀ using hT
  set T : ℕ → ℝ := fun j => if j₀ ≤ j then T₀ j else j with hTdef
  have hTb : ∀ j : ℕ, (j : ℝ) ≤ T j ∧ T j ≤ j + 1 := by
    intro j
    by_cases hj : j₀ ≤ j
    · simp only [hTdef, if_pos hj]; exact ⟨(hT₀ j hj).1, (hT₀ j hj).2.1⟩
    · simp only [hTdef, if_neg hj]; exact ⟨le_rfl, by linarith⟩
  have hTspec : ∀ j : ℕ, j₀ ≤ j → ∀ x : ℝ, -1 ≤ x → x ≤ 2 →
      (Gfull k f ((x : ℂ) + T j * Complex.I) ≠ 0 ∧
        ‖logDeriv (Gfull k f) ((x : ℂ) + T j * Complex.I)‖ ≤ C₂ * Real.log j ^ 2) ∧
      (Gfull k f ((x : ℂ) - T j * Complex.I) ≠ 0 ∧
        ‖logDeriv (Gfull k f) ((x : ℂ) - T j * Complex.I)‖ ≤ C₂ * Real.log j ^ 2) := by
    intro j hj
    simp only [hTdef, if_pos hj]
    exact (hT₀ j hj).2.2
  refine ⟨T, hTb, ?_⟩
  have hTtop : Tendsto T atTop atTop :=
    tendsto_atTop_mono (fun j => (hTb j).1) tendsto_natCast_atTop_atTop
  have hTbot : Tendsto (fun j => -T j) atTop atBot := tendsto_neg_atTop_atBot.comp hTtop
  have hghc : Continuous (ghat g) := continuous_iff_continuousAt.mpr fun s => (hga s).continuousAt
  -- the right edge
  have hright : Tendsto (fun j => ∫ y in (-T j)..(T j),
      logDeriv (Gfull k f) ((σ : ℂ) + y * Complex.I) * ghat g ((σ : ℂ) + y * Complex.I)) atTop
      (𝓝 (-∑' n, if 2 ≤ n then (rsVonMangoldt (rsCoeff f) k n : ℂ) * (2 * Real.pi * g (Real.log n))
        else 0)) :=
    (prime_side_Gfull k f hk hf hσ1 g hgc hghc hg hF).comp hTtop
  -- the reversed test function and its prime side
  have hgrc : Continuous (fun y : ℝ => g (-y) * Complex.exp (-(y : ℂ))) := by fun_prop
  have hghrc : Continuous (ghat (fun y : ℝ => g (-y) * Complex.exp (-(y : ℂ)))) := by
    have : ghat (fun y : ℝ => g (-y) * Complex.exp (-(y : ℂ))) = fun w => ghat g (1 - w) :=
      funext fun w => ghat_rev g w
    rw [this]; exact hghc.comp (continuous_const.sub continuous_id)
  have hleftP : Tendsto (fun j => ∫ y in (-T j)..(T j),
      logDeriv (Gfull k f) ((σ : ℂ) + y * Complex.I)
        * ghat (fun y : ℝ => g (-y) * Complex.exp (-(y : ℂ))) ((σ : ℂ) + y * Complex.I)) atTop
      (𝓝 (-∑' n, if 2 ≤ n then (rsVonMangoldt (rsCoeff f) k n : ℂ)
        * (2 * Real.pi * (g (-(Real.log n)) * Complex.exp (-((Real.log n : ℝ) : ℂ)))) else 0)) :=
    (prime_side_Gfull k f hk hf hσ1 (fun y : ℝ => g (-y) * Complex.exp (-(y : ℂ))) hgrc hghrc
      hg' hF').comp hTtop
  -- the left edge, pointwise, by the functional equation
  have hleft_pt : ∀ y : ℝ,
      logDeriv (Gfull k f) (((1 - σ : ℝ) : ℂ) + y * Complex.I)
          * ghat g (((1 - σ : ℝ) : ℂ) + y * Complex.I)
      = (logDeriv (rsPre k) ((σ : ℂ) - y * Complex.I)
            + logDeriv (rsPre k) (((1 - σ : ℝ) : ℂ) + y * Complex.I))
          * ghat g (((1 - σ : ℝ) : ℂ) + y * Complex.I)
        - logDeriv (Gfull k f) ((σ : ℂ) - y * Complex.I)
          * ghat g (((1 - σ : ℝ) : ℂ) + y * Complex.I) := by
    intro y
    have e : (1 : ℂ) - ((σ : ℂ) - y * Complex.I) = ((1 - σ : ℝ) : ℂ) + y * Complex.I := by
      push_cast; ring
    have hs0 : ((σ : ℂ) - y * Complex.I) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hs1 : ((σ : ℂ) - y * Complex.I) ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hP : rsPre k ((σ : ℂ) - y * Complex.I) ≠ 0 := rsPre_ne_zero k hk (by simp; linarith)
    have hP' : rsPre k (1 - ((σ : ℂ) - y * Complex.I)) ≠ 0 := by
      rw [e]; exact rsPre_ne_zero_left k hk hσ1 hσ2 y
    have hGs : Gfull k f ((σ : ℂ) - y * Complex.I) ≠ 0 :=
      Gfull_ne_zero_of_one_lt k f hk hf (by simp; linarith)
    have hfe := logDeriv_Gfull_one_sub k f hk hf hs0 hs1 hP hP' hGs
    rw [e] at hfe
    rw [hfe]; ring
  -- continuity on the two lines
  have hcontψ : ∀ s : ℂ, rsPre k s ≠ 0 → ContinuousAt (logDeriv (rsPre k)) s := by
    intro s hs
    have hd : ContinuousAt (deriv (rsPre k)) s :=
      ((differentiable_rsPre k).analyticAt s).deriv.continuousAt
    have hc : ContinuousAt (rsPre k) s := (differentiable_rsPre k s).continuousAt
    have : logDeriv (rsPre k) = fun w => deriv (rsPre k) w / rsPre k w :=
      funext fun w => logDeriv_apply _ _
    rw [this]; exact hd.div hc hs
  have hcontG : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → Gfull k f s ≠ 0 → ContinuousAt (logDeriv (Gfull k f)) s := by
    intro s hs0 hs1 hGs
    have hA := analyticAt_Gfull k f hk hs0 hs1
    have : logDeriv (Gfull k f) = fun w => deriv (Gfull k f) w / Gfull k f w :=
      funext fun w => logDeriv_apply _ _
    rw [this]; exact hA.deriv.continuousAt.div hA.continuousAt hGs
  have hψR : Continuous (fun y : ℝ => logDeriv (rsPre k) ((σ : ℂ) - y * Complex.I)) :=
    continuous_iff_continuousAt.mpr fun y =>
      (hcontψ _ (rsPre_ne_zero k hk (by simp; linarith))).comp
        (f := fun y : ℝ => (σ : ℂ) - y * Complex.I) (by fun_prop)
  have hψL : Continuous (fun y : ℝ => logDeriv (rsPre k) (((1 - σ : ℝ) : ℂ) + y * Complex.I)) :=
    continuous_iff_continuousAt.mpr fun y =>
      (hcontψ _ (rsPre_ne_zero_left k hk hσ1 hσ2 y)).comp
        (f := fun y : ℝ => ((1 - σ : ℝ) : ℂ) + y * Complex.I) (by fun_prop)
  have hGR : Continuous (fun y : ℝ => logDeriv (Gfull k f) ((σ : ℂ) - y * Complex.I)) :=
    continuous_iff_continuousAt.mpr fun y =>
      (hcontG _ (by intro h; have := congrArg Complex.re h; simp at this; linarith)
        (by intro h; have := congrArg Complex.re h; simp at this; linarith)
        (Gfull_ne_zero_of_one_lt k f hk hf (by simp; linarith))).comp
        (f := fun y : ℝ => (σ : ℂ) - y * Complex.I) (by fun_prop)
  have hĝL : Continuous (fun y : ℝ => ghat g (((1 - σ : ℝ) : ℂ) + y * Complex.I)) :=
    hghc.comp (by fun_prop)
  have hcontA : Continuous (fun y : ℝ => (logDeriv (rsPre k) ((σ : ℂ) - y * Complex.I)
      + logDeriv (rsPre k) (((1 - σ : ℝ) : ℂ) + y * Complex.I))
      * ghat g (((1 - σ : ℝ) : ℂ) + y * Complex.I)) := (hψR.add hψL).mul hĝL
  have hcontB : Continuous (fun y : ℝ => logDeriv (Gfull k f) ((σ : ℂ) - y * Complex.I)
      * ghat g (((1 - σ : ℝ) : ℂ) + y * Complex.I)) := hGR.mul hĝL
  have hleft_eq : ∀ j : ℕ, (∫ y in (-T j)..(T j), logDeriv (Gfull k f) (((1 - σ : ℝ) : ℂ) + y * Complex.I)
        * ghat g (((1 - σ : ℝ) : ℂ) + y * Complex.I))
      = (∫ y in (-T j)..(T j), (logDeriv (rsPre k) ((σ : ℂ) - y * Complex.I)
            + logDeriv (rsPre k) (((1 - σ : ℝ) : ℂ) + y * Complex.I))
          * ghat g (((1 - σ : ℝ) : ℂ) + y * Complex.I))
        - ∫ y in (-T j)..(T j), logDeriv (Gfull k f) ((σ : ℂ) - y * Complex.I)
          * ghat g (((1 - σ : ℝ) : ℂ) + y * Complex.I) := by
    intro j
    rw [← intervalIntegral.integral_sub (hcontA.intervalIntegrable _ _)
      (hcontB.intervalIntegrable _ _)]
    exact intervalIntegral.integral_congr fun y _ => hleft_pt y
  have hsub_eq : ∀ j : ℕ, (∫ y in (-T j)..(T j), logDeriv (Gfull k f) ((σ : ℂ) - y * Complex.I)
        * ghat g (((1 - σ : ℝ) : ℂ) + y * Complex.I))
      = ∫ y in (-T j)..(T j), logDeriv (Gfull k f) ((σ : ℂ) + y * Complex.I)
          * ghat (fun y : ℝ => g (-y) * Complex.exp (-(y : ℂ))) ((σ : ℂ) + y * Complex.I) := by
    intro j
    have := intervalIntegral.integral_comp_neg (a := -T j) (b := T j)
      (fun y : ℝ => logDeriv (Gfull k f) ((σ : ℂ) + y * Complex.I)
        * ghat (fun y : ℝ => g (-y) * Complex.exp (-(y : ℂ))) ((σ : ℂ) + y * Complex.I))
    rw [neg_neg] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun y _ => ?_
    beta_reduce
    rw [ghat_rev]
    have e1 : ((σ : ℂ) - y * Complex.I) = (σ : ℂ) + ((-y : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    have e2 : (((1 - σ : ℝ) : ℂ) + y * Complex.I) = 1 - ((σ : ℂ) + ((-y : ℝ) : ℂ) * Complex.I) := by
      push_cast; ring
    rw [e1, e2]
  have hA : Tendsto (fun j : ℕ => ∫ y in (-T j)..(T j), (logDeriv (rsPre k) ((σ : ℂ) - y * Complex.I)
        + logDeriv (rsPre k) (((1 - σ : ℝ) : ℂ) + y * Complex.I))
        * ghat g (((1 - σ : ℝ) : ℂ) + y * Complex.I)) atTop
      (𝓝 (∫ t : ℝ, (logDeriv (rsPre k) ((σ : ℂ) - t * Complex.I)
        + logDeriv (rsPre k) (((1 - σ : ℝ) : ℂ) + t * Complex.I))
        * ghat g (((1 - σ : ℝ) : ℂ) + t * Complex.I))) :=
    intervalIntegral_tendsto_integral hArch hTbot hTtop
  have hleft : Tendsto (fun j : ℕ => ∫ y in (-T j)..(T j),
      logDeriv (Gfull k f) (((1 - σ : ℝ) : ℂ) + y * Complex.I)
        * ghat g (((1 - σ : ℝ) : ℂ) + y * Complex.I)) atTop
      (𝓝 ((∫ t : ℝ, (logDeriv (rsPre k) ((σ : ℂ) - t * Complex.I)
        + logDeriv (rsPre k) (((1 - σ : ℝ) : ℂ) + t * Complex.I))
        * ghat g (((1 - σ : ℝ) : ℂ) + t * Complex.I))
        - (-∑' n, if 2 ≤ n then (rsVonMangoldt (rsCoeff f) k n : ℂ)
          * (2 * Real.pi * (g (-(Real.log n)) * Complex.exp (-((Real.log n : ℝ) : ℂ)))) else 0))) := by
    refine (hA.sub hleftP).congr' (Eventually.of_forall fun j => ?_)
    beta_reduce
    rw [hleft_eq j, hsub_eq j]
  -- the horizontal edges
  obtain ⟨B, hB⟩ := hdec
  have hB0 : 0 ≤ B := by
    have := hB ⟨1 - σ, 1⟩ le_rfl (by show 1 - σ ≤ σ; linarith) (by show (1 : ℝ) ≤ |1|; simp)
    change ‖ghat g ⟨1 - σ, 1⟩‖ * (1 : ℝ) ^ 2 ≤ B at this
    rw [one_pow, mul_one] at this
    exact (norm_nonneg _).trans this
  have hlog : Tendsto (fun j : ℕ => Real.log j ^ 2 / (j : ℝ) ^ 2) atTop (𝓝 0) := by
    have h := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.pow 2).comp
      tendsto_natCast_atTop_atTop
    have h0 : ((0 : ℝ) ^ 2) = 0 := by norm_num
    rw [h0] at h
    refine h.congr fun j => ?_
    simp [Function.comp, div_pow]
  have ha : Tendsto (fun j : ℕ => C₂ * B * (2 * σ - 1) * (Real.log j ^ 2 / (j : ℝ) ^ 2)) atTop
      (𝓝 0) := by
    have := hlog.const_mul (C₂ * B * (2 * σ - 1)); rwa [mul_zero] at this
  have hedgeBound : ∀ j : ℕ, j₀ ≤ j → 1 ≤ j → ∀ τ : ℝ, τ = T j ∨ τ = -(T j) →
      ‖∫ x in (1 - σ)..σ, logDeriv (Gfull k f) ((x : ℂ) + τ * Complex.I)
          * ghat g ((x : ℂ) + τ * Complex.I)‖
        ≤ C₂ * B * (2 * σ - 1) * (Real.log j ^ 2 / (j : ℝ) ^ 2) := by
    intro j hj hj1 τ hτ
    have hTj := hTb j
    have hj1' : (1:ℝ) ≤ j := by exact_mod_cast hj1
    have hT1 : 1 ≤ T j := by linarith [hTj.1]
    have hτabs : |τ| = T j := by
      rcases hτ with h | h <;> rw [h] <;> simp [abs_of_pos (by linarith : (0:ℝ) < T j)]
    have hτsq : τ ^ 2 = T j ^ 2 := by rcases hτ with h | h <;> rw [h] <;> ring
    have hpt : ∀ x : ℝ, x ∈ Set.uIoc (1 - σ) σ →
        ‖logDeriv (Gfull k f) ((x : ℂ) + τ * Complex.I) * ghat g ((x : ℂ) + τ * Complex.I)‖
          ≤ C₂ * Real.log j ^ 2 * (B / T j ^ 2) := by
      intro x hx
      rw [Set.uIoc_of_le (by linarith), Set.mem_Ioc] at hx
      have hx1 : -1 ≤ x := by linarith
      have hx2 : x ≤ 2 := by linarith
      have hld : ‖logDeriv (Gfull k f) ((x : ℂ) + τ * Complex.I)‖ ≤ C₂ * Real.log j ^ 2 := by
        rcases hτ with h | h
        · rw [h]; exact (hTspec j hj x hx1 hx2).1.2
        · rw [h]
          have e : ((x : ℂ) + ((-(T j) : ℝ) : ℂ) * Complex.I) = (x : ℂ) - T j * Complex.I := by
            push_cast; ring
          rw [e]; exact (hTspec j hj x hx1 hx2).2.2
      have hĝ : ‖ghat g ((x : ℂ) + τ * Complex.I)‖ ≤ B / T j ^ 2 := by
        have h := hB ((x : ℂ) + τ * Complex.I) (by simp; linarith) (by simp; linarith)
          (by simp [hτabs]; linarith)
        rw [le_div_iff₀ (by positivity)]
        simpa [hτsq] using h
      rw [norm_mul]
      exact mul_le_mul hld hĝ (norm_nonneg _) (by positivity)
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    rw [abs_of_pos (by linarith : (0:ℝ) < σ - (1 - σ))] at h1
    refine h1.trans ?_
    have hT2 : (j : ℝ) ^ 2 ≤ T j ^ 2 := by nlinarith [hTj.1]
    have hdiv : B / T j ^ 2 ≤ B / (j : ℝ) ^ 2 := div_le_div_of_nonneg_left hB0 (by positivity) hT2
    calc C₂ * Real.log j ^ 2 * (B / T j ^ 2) * (σ - (1 - σ))
        ≤ C₂ * Real.log j ^ 2 * (B / (j:ℝ) ^ 2) * (σ - (1 - σ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdiv (by positivity)) (by linarith)
      _ = C₂ * B * (2 * σ - 1) * (Real.log j ^ 2 / (j : ℝ) ^ 2) := by ring
  have hbot : Tendsto (fun j : ℕ => ∫ x in (1 - σ)..σ,
      logDeriv (Gfull k f) ((x : ℂ) + ((-(T j) : ℝ) : ℂ) * Complex.I)
        * ghat g ((x : ℂ) + ((-(T j) : ℝ) : ℂ) * Complex.I)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ ha
    filter_upwards [eventually_ge_atTop j₀, eventually_ge_atTop 1] with j hj hj1
    exact hedgeBound j hj hj1 _ (Or.inr rfl)
  have htop : Tendsto (fun j : ℕ => ∫ x in (1 - σ)..σ,
      logDeriv (Gfull k f) ((x : ℂ) + (T j : ℝ) * Complex.I)
        * ghat g ((x : ℂ) + (T j : ℝ) * Complex.I)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ ha
    filter_upwards [eventually_ge_atTop j₀, eventually_ge_atTop 1] with j hj hj1
    exact hedgeBound j hj hj1 _ (Or.inl rfl)
  -- the identity for large `j`
  have h2πI : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero
    exact_mod_cast Real.pi_ne_zero
  have hid : ∀ᶠ j : ℕ in atTop,
      (∑ᶠ u, ((MeromorphicOn.divisor (rsHent k f) (closedRect ⟨1 - σ, -(T j)⟩ ⟨σ, T j⟩)) u : ℂ)
          * ghat g u)
      = ghat g 1 + (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ((∫ x in (1 - σ)..σ, logDeriv (Gfull k f) ((x : ℂ) + ((-(T j) : ℝ) : ℂ) * Complex.I)
            * ghat g ((x : ℂ) + ((-(T j) : ℝ) : ℂ) * Complex.I))
          - (∫ x in (1 - σ)..σ, logDeriv (Gfull k f) ((x : ℂ) + (T j : ℝ) * Complex.I)
            * ghat g ((x : ℂ) + (T j : ℝ) * Complex.I))
          + Complex.I • (∫ y in (-T j)..(T j), logDeriv (Gfull k f) ((σ : ℂ) + y * Complex.I)
            * ghat g ((σ : ℂ) + y * Complex.I))
          - Complex.I • (∫ y in (-T j)..(T j),
            logDeriv (Gfull k f) (((1 - σ : ℝ) : ℂ) + y * Complex.I)
              * ghat g (((1 - σ : ℝ) : ℂ) + y * Complex.I))) := by
    filter_upwards [eventually_ge_atTop j₀, eventually_ge_atTop 1] with j hj hj1
    have hTj := hTb j
    have hj1' : (1:ℝ) ≤ j := by exact_mod_cast hj1
    have hT1 : 1 ≤ T j := by linarith [hTj.1]
    have hzw : (⟨1 - σ, -(T j)⟩ : ℂ).re < (⟨σ, T j⟩ : ℂ).re ∧
        (⟨1 - σ, -(T j)⟩ : ℂ).im < (⟨σ, T j⟩ : ℂ).im :=
      ⟨by show 1 - σ < σ; linarith, by show -(T j) < T j; linarith⟩
    have hne : ∀ s ∈ rectBoundary (⟨1 - σ, -(T j)⟩ : ℂ) ⟨σ, T j⟩, Gfull k f s ≠ 0 := by
      intro s hs
      obtain ⟨hsK, hcase⟩ := hs
      rw [closedRect, Complex.mem_reProdIm, Set.uIcc_of_le hzw.1.le, Set.uIcc_of_le hzw.2.le] at hsK
      obtain ⟨⟨hre1, hre2⟩, ⟨him1, him2⟩⟩ := hsK
      change 1 - σ ≤ s.re at hre1
      change s.re ≤ σ at hre2
      change -(T j) ≤ s.im at him1
      change s.im ≤ T j at him2
      rcases hcase with h | h | h | h
      · change s.re = 1 - σ at h
        have e : s = ((1 - σ : ℝ) : ℂ) + s.im * Complex.I := by
          apply Complex.ext <;> simp [h]
        rw [e]; exact Gfull_ne_zero_left k f hk hf hσ1 hσ2 s.im
      · change s.re = σ at h
        exact Gfull_ne_zero_of_one_lt k f hk hf (by rw [h]; exact hσ1)
      · change s.im = -(T j) at h
        have e : s = (s.re : ℂ) - T j * Complex.I := by
          apply Complex.ext <;> simp [h]
        rw [e]; exact (hTspec j hj s.re (by linarith) (by linarith)).2.1
      · change s.im = T j at h
        have e : s = (s.re : ℂ) + T j * Complex.I := by
          apply Complex.ext <;> simp [h]
        rw [e]; exact (hTspec j hj s.re (by linarith) (by linarith)).1.1
    have h1 : (1 : ℂ) ∉ rectBoundary (⟨1 - σ, -(T j)⟩ : ℂ) ⟨σ, T j⟩ := by
      intro hs
      obtain ⟨-, hcase⟩ := hs
      rcases hcase with h | h | h | h
      · change (1:ℂ).re = 1 - σ at h; rw [Complex.one_re] at h; linarith
      · change (1:ℂ).re = σ at h; rw [Complex.one_re] at h; linarith
      · change (1:ℂ).im = -(T j) at h; rw [Complex.one_im] at h; linarith
      · change (1:ℂ).im = T j at h; rw [Complex.one_im] at h; linarith
    have hK1 : (1 : ℂ) ∈ closedRect (⟨1 - σ, -(T j)⟩ : ℂ) ⟨σ, T j⟩ := by
      rw [closedRect, Complex.mem_reProdIm, Set.uIcc_of_le hzw.1.le, Set.uIcc_of_le hzw.2.le]
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · show 1 - σ ≤ (1:ℂ).re; rw [Complex.one_re]; linarith
      · show (1:ℂ).re ≤ σ; rw [Complex.one_re]; linarith
      · show -(T j) ≤ (1:ℂ).im; rw [Complex.one_im]; linarith
      · show (1:ℂ).im ≤ T j; rw [Complex.one_im]; linarith
    have hrect := explicitFormula_Gfull_rect' k f hk hf ⟨1 - σ, -(T j)⟩ ⟨σ, T j⟩ hzw (ghat g)
      (fun s _ => hga s) hne h1
    rw [if_pos hK1] at hrect
    have hmul := congrArg (fun w => (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * w) hrect
    beta_reduce at hmul
    rw [inv_mul_cancel_left₀ h2πI] at hmul
    rw [hmul, rectBoundaryIntegral_mk]
    beta_reduce
    rw [mul_add, inv_mul_cancel_left₀ h2πI]
    ring
  -- the limit
  have hlim := tendsto_const_nhds (x := ghat g 1) |>.add
    ((((hbot.sub htop).add (hright.const_smul Complex.I)).sub (hleft.const_smul Complex.I)).const_mul
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹)
  have hfinal := hlim.congr' (hid.mono fun j hj => hj.symm)
  -- the value of the limit
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI := Complex.I_ne_zero
  have hS1 : (∑' n, if 2 ≤ n then (rsVonMangoldt (rsCoeff f) k n : ℂ) * (2 * Real.pi * g (Real.log n))
      else 0) = (2 * Real.pi : ℂ) * ∑' n, (if 2 ≤ n then (rsVonMangoldt (rsCoeff f) k n : ℂ)
        * g (Real.log n) else 0) := by
    rw [← tsum_mul_left]
    congr 1; funext n; split_ifs <;> ring
  have hS2 : (∑' n, if 2 ≤ n then (rsVonMangoldt (rsCoeff f) k n : ℂ)
      * (2 * Real.pi * (g (-(Real.log n)) * Complex.exp (-((Real.log n : ℝ) : ℂ)))) else 0)
      = (2 * Real.pi : ℂ) * ∑' n, (if 2 ≤ n then (rsVonMangoldt (rsCoeff f) k n : ℂ)
        * (g (-(Real.log n)) / n) else 0) := by
    rw [← tsum_mul_left]
    congr 1; funext n
    split_ifs with hn
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hexp : Complex.exp (-((Real.log n : ℝ) : ℂ)) = ((n : ℂ))⁻¹ := by
        rw [Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log hn0]
        push_cast; rfl
      rw [hexp]; ring
    · ring
  have hval : ghat g 1 + (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      (0 - 0 + Complex.I • (-∑' n, if 2 ≤ n then (rsVonMangoldt (rsCoeff f) k n : ℂ)
          * (2 * Real.pi * g (Real.log n)) else 0)
        - Complex.I • ((∫ t : ℝ, (logDeriv (rsPre k) ((σ : ℂ) - t * Complex.I)
            + logDeriv (rsPre k) (((1 - σ : ℝ) : ℂ) + t * Complex.I))
            * ghat g (((1 - σ : ℝ) : ℂ) + t * Complex.I))
          - (-∑' n, if 2 ≤ n then (rsVonMangoldt (rsCoeff f) k n : ℂ)
            * (2 * Real.pi * (g (-(Real.log n)) * Complex.exp (-((Real.log n : ℝ) : ℂ)))) else 0)))
      = ghat g 1
          - ∑' n, (if 2 ≤ n then (rsVonMangoldt (rsCoeff f) k n : ℂ) * g (Real.log n) else 0)
          - ∑' n, (if 2 ≤ n then (rsVonMangoldt (rsCoeff f) k n : ℂ) * (g (-(Real.log n)) / n)
              else 0)
          - (1 / (2 * Real.pi)) * ∫ t : ℝ, (logDeriv (rsPre k) ((σ : ℂ) - t * Complex.I)
              + logDeriv (rsPre k) (((1 - σ : ℝ) : ℂ) + t * Complex.I))
              * ghat g (((1 - σ : ℝ) : ℂ) + t * Complex.I) := by
    rw [hS1, hS2]
    simp only [smul_eq_mul]
    field_simp
    ring
  rw [hval] at hfinal
  exact hfinal

end RankinSelbergDelta.RankinSelberg
