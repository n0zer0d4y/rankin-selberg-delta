import RankinSelbergDelta.RankinSelberg.StripGrowth

/-!
# Bounds for the logarithmic derivative of `G`

The Borel–Carathéodory inequality, Davenport's disc lemma, the de la Vallée Poussin bounds
`−Re(G′/G)(σ + iγ) ≤ C log |γ|`, and the bound near the simple pole at `s = 1`.
-/

open MeasureTheory Filter
open scoped NNReal MatrixGroups Pointwise

noncomputable section


/-! ### Borel-Caratheodory and Davenport's disc lemma -/

/-!
# The Hadamard–Borel–Carathéodory bound for the logarithmic derivative (Davenport §13, Lemma)


If `f` is holomorphic on `ball z₀ (2R)`, `f z₀ ≠ 0` and `‖f z‖ ≤ e^M ‖f z₀‖` there, then for
`‖z − z₀‖ ≤ R/4` with `f z ≠ 0`,
`−Re (f′/f)(z) ≤ 48 M / R − Σ_ρ m_ρ · Re (1/(z − ρ))`,
the sum over the zeros `ρ` of `f` in `ball z₀ (R/2)` with multiplicities `m_ρ ≥ 1`.

Route: strip the zeros with Mathlib's `MeromorphicOn.extract_zeros_poles` (`f = P · g`, `P` the
factorized rational function of the divisor, `g` analytic and nonvanishing on the half-disc), glue
`G = g` on the half-disc and `G = f/P` outside into an analytic function on the big disc, bound
`‖G/G(z₀)‖ ≤ e^M` by the maximum principle (`‖P‖` is larger on the big circle than at `z₀`), take a
primitive `F` of `G′/G` on the half-disc (`DifferentiableOn.isExactOn_ball`), identify
`G = G(z₀) e^F` so `Re F = log ‖G/G(z₀)‖ ≤ M`, apply Borel–Carathéodory to `F` and the Cauchy
estimate to `F′ = G′/G`; finally `f′/f = P′/P + G′/G` with `P′/P = Σ m_ρ/(z − ρ)` (`logDeriv_prod`).

Not in Mathlib (8f9d9cff); built from scratch on the pieces above.
-/

namespace RankinSelbergDelta.BorelCaratheodory

open Complex Metric Set Filter Topology

/-! ### Borel–Carathéodory (as in `BorelCaratheodory.lean`) -/

lemma le_of_sq_le_sq'' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  calc a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha).symm
    _ ≤ Real.sqrt (b ^ 2) := Real.sqrt_le_sqrt h
    _ = b := Real.sqrt_sq hb

lemma norm_le_norm_two_mul_sub {w : ℂ} {A : ℝ} (hA : 0 ≤ A) (hw : w.re ≤ A) :
    ‖w‖ ≤ ‖2 * (A : ℂ) - w‖ := by
  refine le_of_sq_le_sq'' (norm_nonneg _) (norm_nonneg _) ?_
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.re_ofNat,
    Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im]
  nlinarith

lemma two_mul_sub_ne_zero {w : ℂ} {A : ℝ} (hA : 0 < A) (hw : w.re ≤ A) : 2 * (A : ℂ) - w ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re,
    Complex.ofReal_im, Complex.zero_re] at this
  linarith

/-- **Borel–Carathéodory.** -/
theorem norm_le_of_re_le {f : ℂ → ℂ} {c : ℂ} {R A : ℝ} (hR : 0 < R) (hA : 0 < A)
    (hf : DifferentiableOn ℂ f (ball c R)) (h0 : f c = 0)
    (hre : ∀ z ∈ ball c R, (f z).re ≤ A) {z : ℂ} (hz : z ∈ ball c R) :
    ‖f z‖ ≤ 2 * A * dist z c / (R - dist z c) := by
  set φ : ℂ → ℂ := fun w => f w / (2 * (A : ℂ) - f w) with hφ
  have hden : ∀ w ∈ ball c R, 2 * (A : ℂ) - f w ≠ 0 := fun w hw => two_mul_sub_ne_zero hA (hre w hw)
  have hφd : DifferentiableOn ℂ φ (ball c R) :=
    hf.div ((differentiableOn_const _).sub hf) hden
  have hφc : φ c = 0 := by simp [hφ, h0]
  have hmaps : MapsTo φ (ball c R) (closedBall (φ c) 1) := by
    intro w hw
    rw [hφc, mem_closedBall, dist_zero_right, hφ]
    show ‖f w / (2 * (A : ℂ) - f w)‖ ≤ 1
    rw [norm_div, div_le_one (norm_pos_iff.mpr (hden w hw))]
    exact norm_le_norm_two_mul_sub hA.le (hre w hw)
  have hS := Complex.dist_le_div_mul_dist_of_mapsTo_ball hφd hmaps hz
  rw [hφc, dist_zero_right] at hS
  set d : ℝ := dist z c with hd
  have hdR : d < R := by rwa [mem_ball] at hz
  have hd0 : 0 ≤ d := dist_nonneg
  have hφz : ‖φ z‖ ≤ d / R := by rw [one_div, inv_mul_eq_div] at hS; exact hS
  have hdenz := hden z hz
  have hone : 1 + φ z ≠ 0 := by
    intro h
    have h1 : ‖φ z‖ = 1 := by
      have : φ z = -1 := by linear_combination h
      rw [this, norm_neg, norm_one]
    have : d / R < 1 := by rw [div_lt_one hR]; exact hdR
    linarith
  have hfz : f z = 2 * (A : ℂ) * φ z / (1 + φ z) := by
    rw [eq_div_iff hone, hφ]
    field_simp
    ring
  have hnorm1 : 1 - d / R ≤ ‖1 + φ z‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-(φ z))
    rw [norm_one, norm_neg, sub_neg_eq_add] at this
    linarith
  have hpos : 0 < 1 - d / R := by
    have : d / R < 1 := by rw [div_lt_one hR]; exact hdR
    linarith
  have hRd : 0 ≤ R - d := by linarith
  have h2Ad : 0 ≤ 2 * A * d := mul_nonneg (by positivity) hd0
  rw [hfz, norm_div, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_of_nonneg hA.le, div_le_div_iff₀ (norm_pos_iff.mpr hone) (by linarith)]
  calc 2 * A * ‖φ z‖ * (R - d) ≤ 2 * A * (d / R) * (R - d) := by gcongr
    _ = 2 * A * d * (1 - d / R) := by field_simp
    _ ≤ 2 * A * d * ‖1 + φ z‖ := by gcongr

/-! ### Auxiliary facts -/

lemma norm_zpow_le_norm_zpow {a b : ℂ} {n : ℤ} (hn : 0 ≤ n) (h : ‖a‖ ≤ ‖b‖) :
    ‖a ^ n‖ ≤ ‖b ^ n‖ := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  rw [zpow_natCast, zpow_natCast, norm_pow, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h k

/-- The factorized rational function of a finitely supported `d ≥ 0`, as a `Finset` product. -/
lemma finprod_eq_finset_prod {d : ℂ → ℤ} (hd : d.support.Finite) (x : ℂ) :
    (∏ᶠ u, (· - u) ^ d u) x = ∏ u ∈ hd.toFinset, (x - u) ^ d u := by
  rw [finprod_eq_prod_of_mulSupport_subset (s := hd.toFinset)]
  · rw [Finset.prod_apply]
    rfl
  · rw [Function.FactorizedRational.mulSupport]
    intro u hu
    simpa using hu

/-! ### The disc lemma -/

/-- **Davenport's Lemma (§13), with the zeros counted with multiplicity.** -/
theorem neg_re_logDeriv_le {f : ℂ → ℂ} {z₀ : ℂ} {R M : ℝ} (hR : 0 < R) (hM : 0 < M)
    (hf : DifferentiableOn ℂ f (ball z₀ (2 * R))) (h0 : f z₀ ≠ 0)
    (hbound : ∀ z ∈ ball z₀ (2 * R), ‖f z‖ ≤ Real.exp M * ‖f z₀‖) :
    ∃ (S : Finset ℂ) (m : ℂ → ℤ),
      (∀ u ∈ S, u ∈ ball z₀ (R / 2) ∧ f u = 0 ∧ 1 ≤ m u) ∧
      (∀ u ∈ ball z₀ (R / 2), f u = 0 → u ∈ S) ∧
      ∀ z ∈ closedBall z₀ (R / 4), f z ≠ 0 →
        -(logDeriv f z).re ≤ 48 * M / R - ∑ u ∈ S, (m u : ℝ) * (1 / (z - u)).re := by
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
  have hre : (∑ u ∈ hDfin.toFinset, (D u : ℂ) / (z - u)).re
      = ∑ u ∈ hDfin.toFinset, (D u : ℝ) * (1 / (z - u)).re := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [div_eq_mul_one_div]
    simp [Complex.mul_re]
  have hFz := hF' z hz
  have hre' : -(deriv F z).re ≤ 48 * M / R := by
    have := Complex.abs_re_le_norm (deriv F z)
    rw [abs_le] at this
    linarith
  rw [hlogf, hlogG, Complex.add_re, hlogP, hre]
  beta_reduce
  linarith

end RankinSelbergDelta.BorelCaratheodory

/-! ### the de la Vallée Poussin log-derivative bounds for `G = Gfull k f`: (A) `−Re(G′/G)(σ + 2iγ) ≤ C′ log|γ|` and (B) the same with the
term `−1/(σ − β)` of a zero `β + iγ`, from Davenport's disc lemma `neg_re_logDeriv_le` (above, in
`RankinSelbergDelta.BorelCaratheodory`), the growth `exists_norm_Gfull_le_halfStrip`, the nonvanishing
`Gfull_ne_zero_of_one_lt` and a lower bound `‖G(σ₀ + it)‖ ≥ 3/8` far to the right. -/

namespace RankinSelbergDelta.RankinSelberg

open Complex UpperHalfPlane MeasureTheory Set Filter RankinSelbergDelta.Eisenstein
open scoped Real Topology Modular

/-! #### Tails of nonnegative series -/

lemma tsum_shift_two_le {h : ℕ → ℝ} (h0 : ∀ n, 0 ≤ h n) (hs : Summable h) :
    ∑' n, h (n + 2) ≤ ∑' n, h n := by
  have h1 : Summable fun n => h (n + 1) := (summable_nat_add_iff 1).mpr hs
  have h2 : Summable fun n => h (n + 2) := (summable_nat_add_iff 2).mpr hs
  rw [hs.tsum_eq_zero_add, h1.tsum_eq_zero_add]
  have : ∑' n, h (n + 1 + 1) = ∑' n, h (n + 2) := by congr 1
  rw [this]
  linarith [h0 0, h0 1]

lemma tsum_eq_zero_add_two {g : ℕ → ℂ} (hg : Summable g) :
    ∑' n, g n = g 0 + (g 1 + ∑' n, g (n + 2)) := by
  have h1 : Summable fun n => g (n + 1) := (summable_nat_add_iff 1).mpr hg
  rw [hg.tsum_eq_zero_add, h1.tsum_eq_zero_add]

lemma tsum_eq_zero_add_two_real {g : ℕ → ℝ} (hg : Summable g) :
    ∑' n, g n = g 0 + (g 1 + ∑' n, g (n + 2)) := by
  have h1 : Summable fun n => g (n + 1) := (summable_nat_add_iff 1).mpr hg
  rw [hg.tsum_eq_zero_add, h1.tsum_eq_zero_add]

/-! #### `ζ(u)` is at least `5/6` for `Re u ≥ 4` -/

lemma tsum_one_div_add_two_sq : ∑' n : ℕ, (1 : ℝ) / ((n + 2 : ℕ) : ℝ) ^ 2 = π ^ 2 / 6 - 1 := by
  have h := hasSum_zeta_two
  have hs : Summable fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2 := h.summable
  have e := tsum_eq_zero_add_two_real hs
  rw [h.tsum_eq] at e
  simp only [Nat.cast_zero, Nat.cast_one, one_pow, div_one] at e
  rw [zero_pow two_ne_zero, div_zero, zero_add] at e
  linarith

lemma pi_sq_lt_ten : π ^ 2 < 10 := by
  have := Real.pi_lt_d2
  have h0 := Real.pi_pos
  nlinarith

lemma norm_zeta_sub_one_le {u : ℂ} (hu : 4 ≤ u.re) : ‖riemannZeta u - 1‖ ≤ 1 / 6 := by
  have hu1 : 1 < u.re := by linarith
  have hu0 : u ≠ 0 := Complex.ne_zero_of_one_lt_re hu1
  rw [zeta_eq_tsum_one_div_nat_cpow hu1]
  have hsum : Summable fun n : ℕ => 1 / (n : ℂ) ^ u := by
    rw [Complex.summable_one_div_nat_cpow]; exact hu1
  rw [tsum_eq_zero_add_two hsum]
  simp only [Nat.cast_zero, zero_cpow hu0, div_zero, Nat.cast_one, one_cpow, div_one, zero_add,
    add_sub_cancel_left]
  -- the tail
  have hterm : ∀ n : ℕ, ‖1 / ((n + 2 : ℕ) : ℂ) ^ u‖ ≤ (1 / 4) * (1 / ((n + 2 : ℕ) : ℝ) ^ 2) := by
    intro n
    rw [norm_one_div_natCast_cpow hu1]
    have hn2 : (2 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    have hpos : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by linarith
    have h4 : ((n + 2 : ℕ) : ℝ) ^ (4 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) ^ u.re :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hu
    have h4' : ((n + 2 : ℕ) : ℝ) ^ (4 : ℝ) = (((n + 2 : ℕ) : ℝ) ^ 2) ^ 2 := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      ring
    have hsq : (4 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) ^ 2 := by nlinarith
    calc 1 / ((n + 2 : ℕ) : ℝ) ^ u.re ≤ 1 / ((n + 2 : ℕ) : ℝ) ^ (4 : ℝ) :=
          one_div_le_one_div_of_le (by positivity) h4
      _ = 1 / ((((n + 2 : ℕ) : ℝ) ^ 2) ^ 2) := by rw [h4']
      _ ≤ 1 / (4 * ((n + 2 : ℕ) : ℝ) ^ 2) := by
          apply one_div_le_one_div_of_le (by positivity)
          nlinarith
      _ = (1 / 4) * (1 / ((n + 2 : ℕ) : ℝ) ^ 2) := by field_simp
  have hs2 : Summable fun n : ℕ => (1 / 4) * (1 / ((n + 2 : ℕ) : ℝ) ^ 2) :=
    ((summable_nat_add_iff 2).mpr hasSum_zeta_two.summable).mul_left (1 / 4)
  have hnorm : Summable fun n : ℕ => ‖1 / ((n + 2 : ℕ) : ℂ) ^ u‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hs2
  calc ‖∑' n : ℕ, 1 / ((n + 2 : ℕ) : ℂ) ^ u‖ ≤ ∑' n : ℕ, ‖1 / ((n + 2 : ℕ) : ℂ) ^ u‖ :=
        norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, (1 / 4) * (1 / ((n + 2 : ℕ) : ℝ) ^ 2) := hnorm.tsum_le_tsum hterm hs2
    _ = (1 / 4) * (π ^ 2 / 6 - 1) := by rw [tsum_mul_left, tsum_one_div_add_two_sq]
    _ ≤ 1 / 6 := by linarith [pi_sq_lt_ten]

lemma norm_zeta_ge {u : ℂ} (hu : 4 ≤ u.re) : 5 / 6 ≤ ‖riemannZeta u‖ := by
  have h := norm_zeta_sub_one_le hu
  have := norm_sub_norm_le (1 : ℂ) (riemannZeta u)
  rw [norm_one, norm_sub_rev] at this
  linarith

variable {F : Type*} [FunLike F ℍ ℂ] (k : ℤ)
  [cf : CuspFormClass F (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma 1)) k]

/-! #### `D(w)` is at least `1/2` far to the right (eigenform: `a₁ = 1`) -/

include cf in
lemma norm_rsD_sub_one_le (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k) {w : ℂ}
    (hw : (k : ℝ) < w.re) :
    ‖rsD f w - 1‖ ≤ ∑' n : ℕ, ‖(ModularFormClass.qExpansion 1 f).coeff (n + 2)‖ ^ 2
      / ((n + 2 : ℕ) : ℝ) ^ w.re := by
  have hnorm : Summable fun n : ℕ =>
      ‖((‖(ModularFormClass.qExpansion 1 f).coeff n‖ : ℂ)) ^ 2 / (n : ℂ) ^ w‖ :=
    (summable_rsDirichlet' k f hk hw).congr fun n => (norm_rsD_term k f w n).symm
  have hsum : Summable fun n : ℕ =>
      ((‖(ModularFormClass.qExpansion 1 f).coeff n‖ : ℂ)) ^ 2 / (n : ℂ) ^ w := hnorm.of_norm
  unfold rsD
  rw [tsum_eq_zero_add_two hsum]
  have h0 : (ModularFormClass.qExpansion 1 f).coeff 0 = 0 :=
    RankinSelbergDelta.CuspForm.qExpansion_coeff_zero_cusp f
  have h1 : (ModularFormClass.qExpansion 1 f).coeff 1 = 1 := hf.one
  simp only [h0, h1, norm_zero, norm_one, Complex.ofReal_zero, Complex.ofReal_one, Nat.cast_zero,
    Nat.cast_one, one_cpow, div_one, one_pow, zero_pow two_ne_zero, zero_div, zero_add,
    add_sub_cancel_left]
  have hnorm2 : Summable fun n : ℕ =>
      ‖((‖(ModularFormClass.qExpansion 1 f).coeff (n + 2)‖ : ℂ)) ^ 2 / ((n + 2 : ℕ) : ℂ) ^ w‖ :=
    (summable_nat_add_iff 2).mpr hnorm
  refine (norm_tsum_le_tsum_norm hnorm2).trans (le_of_eq (tsum_congr fun n => ?_))
  exact norm_rsD_term k f w (n + 2)

include cf in
/-- The tail is at most `2^{−N} D(k+1)` for `Re w ≥ k + 1 + N`. -/
lemma tail_rsD_le (f : F) (hk : 0 < k) (N : ℕ) {σ : ℝ} (hσ : (k : ℝ) + 1 + N ≤ σ) :
    ∑' n : ℕ, ‖(ModularFormClass.qExpansion 1 f).coeff (n + 2)‖ ^ 2 / ((n + 2 : ℕ) : ℝ) ^ σ
      ≤ (1 / 2 ^ N) * rsDbound f ((k : ℝ) + 1) := by
  set a : ℕ → ℝ := fun n => ‖(ModularFormClass.qExpansion 1 f).coeff n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + 1)
    with ha
  have ha0 : ∀ n, 0 ≤ a n := fun n => by positivity
  have has : Summable a := summable_rsDirichlet' k f hk (by linarith)
  have hterm : ∀ n : ℕ, ‖(ModularFormClass.qExpansion 1 f).coeff (n + 2)‖ ^ 2 / ((n + 2 : ℕ) : ℝ) ^ σ
      ≤ (1 / 2 ^ N) * a (n + 2) := by
    intro n
    have hn2 : (2 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    have hpos : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by linarith
    have hsplit : ((n + 2 : ℕ) : ℝ) ^ σ
        = ((n + 2 : ℕ) : ℝ) ^ ((k : ℝ) + 1) * ((n + 2 : ℕ) : ℝ) ^ (σ - ((k : ℝ) + 1)) := by
      rw [← Real.rpow_add hpos]; congr 1; ring
    have hbig : (2 : ℝ) ^ N ≤ ((n + 2 : ℕ) : ℝ) ^ (σ - ((k : ℝ) + 1)) := by
      calc (2 : ℝ) ^ N = (2 : ℝ) ^ (N : ℝ) := by rw [Real.rpow_natCast]
        _ ≤ (2 : ℝ) ^ (σ - ((k : ℝ) + 1)) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ ≤ ((n + 2 : ℕ) : ℝ) ^ (σ - ((k : ℝ) + 1)) :=
            Real.rpow_le_rpow (by norm_num) hn2 (by linarith)
    have hA0 : 0 ≤ ‖(ModularFormClass.qExpansion 1 f).coeff (n + 2)‖ ^ 2 := by positivity
    have hk1pos : 0 < ((n + 2 : ℕ) : ℝ) ^ ((k : ℝ) + 1) := by positivity
    have h2N : (0 : ℝ) < 2 ^ N := by positivity
    rw [hsplit, ha]
    simp only []
    rw [div_mul_eq_div_div, show (1 / 2 ^ N) * (‖(ModularFormClass.qExpansion 1 f).coeff (n + 2)‖ ^ 2
        / ((n + 2 : ℕ) : ℝ) ^ ((k : ℝ) + 1))
        = (‖(ModularFormClass.qExpansion 1 f).coeff (n + 2)‖ ^ 2 / ((n + 2 : ℕ) : ℝ) ^ ((k : ℝ) + 1)) / 2 ^ N
        by ring]
    exact div_le_div_of_nonneg_left (by positivity) h2N hbig
  have hs2 : Summable fun n => (1 / 2 ^ N) * a (n + 2) :=
    ((summable_nat_add_iff 2).mpr has).mul_left _
  calc ∑' n : ℕ, ‖(ModularFormClass.qExpansion 1 f).coeff (n + 2)‖ ^ 2 / ((n + 2 : ℕ) : ℝ) ^ σ
      ≤ ∑' n : ℕ, (1 / 2 ^ N) * a (n + 2) :=
        Summable.tsum_le_tsum hterm (Summable.of_nonneg_of_le (fun n => by positivity) hterm hs2) hs2
    _ = (1 / 2 ^ N) * ∑' n : ℕ, a (n + 2) := tsum_mul_left
    _ ≤ (1 / 2 ^ N) * ∑' n : ℕ, a n :=
        mul_le_mul_of_nonneg_left (tsum_shift_two_le ha0 has) (by positivity)
    _ = (1 / 2 ^ N) * rsDbound f ((k : ℝ) + 1) := rfl

include cf in
/-- **The lower bound far to the right**: `∃ σ₀ ≥ 2, ∀ t, 3/8 ≤ ‖G(σ₀ + it)‖`. -/
theorem exists_norm_Gfull_ge (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k) :
    ∃ σ₀ : ℝ, 2 ≤ σ₀ ∧ ∀ t : ℝ, 3 / 8 ≤ ‖Gfull k f ((σ₀ : ℂ) + Complex.I * t)‖ := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (2 * rsDbound f ((k : ℝ) + 1)) (by norm_num : (1 : ℝ) < 2)
  have hd0 := rsDbound_nonneg k f ((k : ℝ) + 1)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  refine ⟨(k : ℝ) + 2 + N, by linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)], fun t => ?_⟩
  set s : ℂ := ((k : ℝ) + 2 + N : ℝ) + Complex.I * t with hs
  have hre : s.re = (k : ℝ) + 2 + N := by simp [hs]
  have hre1 : 1 < s.re := by rw [hre]; linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)]
  rw [Gfull_eq k f hk hre1, norm_mul]
  have h2re : (2 * s).re = 2 * s.re := by rw [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat]; ring
  have hζ : 5 / 6 ≤ ‖riemannZeta (2 * s)‖ :=
    norm_zeta_ge (by rw [h2re, hre]; linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)])
  have hDre : (s + k - 1).re = (k : ℝ) + 2 + N + k - 1 := by rw [shiftk_re, hre]
  have hD : 1 / 2 ≤ ‖rsD f (s + k - 1)‖ := by
    have htail := (norm_rsD_sub_one_le k f hk hf (w := s + k - 1) (by rw [hDre]; linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)])).trans
      (tail_rsD_le k f hk N (σ := (s + k - 1).re) (by rw [hDre]; linarith))
    have hsmall : (1 / 2 ^ N) * rsDbound f ((k : ℝ) + 1) ≤ 1 / 2 := by
      have h2N : (0 : ℝ) < 2 ^ N := by positivity
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ h2N]
      linarith
    have := norm_sub_norm_le (1 : ℂ) (rsD f (s + k - 1))
    rw [norm_one, norm_sub_rev] at this
    linarith
  calc (3 : ℝ) / 8 ≤ (5 / 6) * (1 / 2) := by norm_num
    _ ≤ ‖riemannZeta (2 * s)‖ * ‖rsD f (s + k - 1)‖ :=
        mul_le_mul hζ hD (by norm_num) (norm_nonneg _)

/-! #### The log-derivative bounds -/

/-- `Re (1/(z − u)) ≥ 0` when `Re u ≤ Re z`. -/
lemma re_one_div_sub_nonneg {z u : ℂ} (h : u.re ≤ z.re) : 0 ≤ (1 / (z - u)).re := by
  rw [one_div, Complex.inv_re, Complex.sub_re]
  exact div_nonneg (by linarith) (Complex.normSq_nonneg _)

/-- `Re (1/(z − u)) = 1/(Re z − Re u)` when `Im z = Im u`. -/
lemma re_one_div_sub_of_im_eq {z u : ℂ} (h : z.im = u.im) :
    (1 / (z - u)).re = 1 / (z.re - u.re) := by
  rw [one_div, Complex.inv_re, Complex.sub_re, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    h, sub_self, mul_zero, add_zero]
  rcases eq_or_ne (z.re - u.re) 0 with h0 | h0
  · rw [h0]; simp
  · field_simp

include cf in
/-- The common setup: the disc lemma applied to `G` at `z₀ = σ₀ + iτ`, `R = 4(σ₀ − 1)`. -/
theorem logDeriv_bound_setup (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k) :
    ∃ σ₀ C' t₀ : ℝ, 2 ≤ σ₀ ∧ 0 < C' ∧ 2 ≤ t₀ ∧ ∀ τ : ℝ, t₀ ≤ |τ| →
      ∃ (S : Finset ℂ) (m : ℂ → ℤ),
        (∀ u ∈ S, u ∈ Metric.ball ((σ₀ : ℂ) + Complex.I * τ) (2 * (σ₀ - 1)) ∧ Gfull k f u = 0 ∧ 1 ≤ m u) ∧
        (∀ u ∈ Metric.ball ((σ₀ : ℂ) + Complex.I * τ) (2 * (σ₀ - 1)), Gfull k f u = 0 → u ∈ S) ∧
        ∀ z ∈ Metric.closedBall ((σ₀ : ℂ) + Complex.I * τ) (σ₀ - 1), Gfull k f z ≠ 0 →
          -(logDeriv (Gfull k f) z).re ≤ C' * Real.log |τ| - ∑ u ∈ S, (m u : ℝ) * (1 / (z - u)).re := by
  obtain ⟨σ₀, hσ₀, hlow⟩ := exists_norm_Gfull_ge k f hk hf
  set A : ℕ := ⌈8 * σ₀⌉₊ with hA
  have hA8 : 8 * σ₀ ≤ A := Nat.le_ceil _
  obtain ⟨C, N, hC, hG⟩ := exists_norm_Gfull_le_halfStrip k f hk A
  set R : ℝ := 4 * (σ₀ - 1) with hR
  have hRpos : 0 < R := by rw [hR]; linarith
  set K : ℝ := 2 + 8 * σ₀ with hK
  have hK1 : 1 ≤ K := by rw [hK]; linarith
  set c₀ : ℝ := |Real.log (8 * C / 3)| + N * Real.log K + 1 with hc₀
  have hc₀1 : 1 ≤ c₀ := by
    rw [hc₀]
    have := abs_nonneg (Real.log (8 * C / 3))
    have := mul_nonneg (Nat.cast_nonneg N : (0:ℝ) ≤ N) (Real.log_nonneg hK1)
    linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨σ₀, (48 / R) * (c₀ / Real.log 2 + N), 8 * (σ₀ - 1) + 2, hσ₀, by positivity, by linarith,
    fun τ hτ => ?_⟩
  set z₀ : ℂ := (σ₀ : ℂ) + Complex.I * τ with hz₀
  have hz₀re : z₀.re = σ₀ := by simp [hz₀]
  have hz₀im : z₀.im = τ := by simp [hz₀]
  have hτ2 : 2 ≤ |τ| := by linarith
  have hτ1 : 1 ≤ |τ| := by linarith
  -- the big ball `ball z₀ (2R)`: `|Im w| ≥ 2`, `Re w ≥ −A`, `w ≠ 0, 1`
  have hball : ∀ w ∈ Metric.ball z₀ (2 * R), 2 ≤ |w.im| ∧ -(A : ℝ) ≤ w.re ∧ |w.im| ≤ |τ| + 2 * R := by
    intro w hw
    rw [Metric.mem_ball, Complex.dist_eq] at hw
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
    refine ⟨by linarith, ?_, h3⟩
    linarith
  have hdiff : DifferentiableOn ℂ (Gfull k f) (Metric.ball z₀ (2 * R)) := by
    intro w hw
    obtain ⟨him, -, -⟩ := hball w hw
    refine (differentiableAt_Gfull k f hk ?_ ?_).differentiableWithinAt
    · intro h; rw [h, Complex.zero_im, abs_zero] at him; linarith
    · intro h; rw [h, Complex.one_im, abs_zero] at him; linarith
  -- the growth bound on the big ball, in the form `‖G w‖ ≤ e^M ‖G z₀‖`
  set M : ℝ := c₀ + N * Real.log |τ| with hM
  have hMpos : 0 < M := by
    rw [hM]
    have := mul_nonneg (Nat.cast_nonneg N : (0:ℝ) ≤ N) (Real.log_nonneg hτ1)
    linarith
  have hGz₀ : 3 / 8 ≤ ‖Gfull k f z₀‖ := hlow τ
  have hGz₀ne : Gfull k f z₀ ≠ 0 := by
    intro h; rw [h, norm_zero] at hGz₀; linarith
  have hbound : ∀ w ∈ Metric.ball z₀ (2 * R), ‖Gfull k f w‖ ≤ Real.exp M * ‖Gfull k f z₀‖ := by
    intro w hw
    obtain ⟨him, hreA, himle⟩ := hball w hw
    have hGw := hG w hreA (by linarith)
    -- `1 + |Im w| ≤ K |τ|`
    have h1K : 1 + |w.im| ≤ K * |τ| := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + 8 * σ₀) (by linarith : (0 : ℝ) ≤ |τ| - 1)]
    have hpow : (1 + |w.im|) ^ N ≤ (K * |τ|) ^ N :=
      pow_le_pow_left₀ (by positivity) h1K N
    -- `C (K|τ|)^N ≤ (3/8) e^M`
    have hexp : C * (K * |τ|) ^ N ≤ (3 / 8) * Real.exp M := by
      have hCpos : 0 < 8 * C / 3 := by positivity
      have hKpos : 0 < K := by linarith
      have hτpos : 0 < |τ| := by linarith
      have hlogM : Real.log (8 * C / 3 * (K * |τ|) ^ N) ≤ M := by
        rw [Real.log_mul hCpos.ne' (by positivity), Real.log_pow, Real.log_mul hKpos.ne' hτpos.ne', hM, hc₀]
        have := le_abs_self (Real.log (8 * C / 3))
        nlinarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)]
      have := Real.exp_le_exp.mpr hlogM
      rw [Real.exp_log (by positivity)] at this
      linarith
    calc ‖Gfull k f w‖ ≤ C * (1 + |w.im|) ^ N := hGw
      _ ≤ C * (K * |τ|) ^ N := mul_le_mul_of_nonneg_left hpow hC.le
      _ ≤ (3 / 8) * Real.exp M := hexp
      _ ≤ Real.exp M * ‖Gfull k f z₀‖ := by nlinarith [Real.exp_pos M]
  obtain ⟨S, m, hS1, hS2, hineq⟩ :=
    RankinSelbergDelta.BorelCaratheodory.neg_re_logDeriv_le hRpos hMpos hdiff hGz₀ne hbound
  have hR2 : R / 2 = 2 * (σ₀ - 1) := by rw [hR]; ring
  have hR4 : R / 4 = σ₀ - 1 := by rw [hR]; ring
  rw [hR2] at hS1 hS2
  rw [hR4] at hineq
  refine ⟨S, m, hS1, hS2, fun z hz hz0 => ?_⟩
  have := hineq z hz hz0
  -- `48 M / R ≤ C′ log |τ|`
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

include cf in
/-- **(A)** `−Re (G′/G)(σ + 2iγ) ≤ C′ log|γ|` for `1 < σ ≤ 2`, `|γ| ≥ t₀`. -/
theorem neg_re_logDeriv_Gfull_le (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k) :
    ∃ C' t₀ : ℝ, 0 < C' ∧ 2 ≤ t₀ ∧ ∀ γ : ℝ, t₀ ≤ |γ| → ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      -(logDeriv (Gfull k f) ((σ : ℂ) + 2 * Complex.I * γ)).re ≤ C' * Real.log |γ| := by
  obtain ⟨σ₀, C', t₀, hσ₀, hC', ht₀, hmain⟩ := logDeriv_bound_setup k f hk hf
  refine ⟨2 * C', t₀, by positivity, ht₀, fun γ hγ σ hσ1 hσ2 => ?_⟩
  have hτ : t₀ ≤ |2 * γ| := by rw [abs_mul, abs_two]; linarith [abs_nonneg γ]
  obtain ⟨S, m, hS1, hS2, hineq⟩ := hmain (2 * γ) hτ
  set z : ℂ := (σ : ℂ) + 2 * Complex.I * γ with hz
  have hzre : z.re = σ := by simp [hz]
  have hz' : z = (σ : ℂ) + Complex.I * ((2 * γ : ℝ) : ℂ) := by rw [hz]; push_cast; ring
  have hzmem : z ∈ Metric.closedBall ((σ₀ : ℂ) + Complex.I * ((2 * γ : ℝ) : ℂ)) (σ₀ - 1) := by
    rw [Metric.mem_closedBall, Complex.dist_eq, hz']
    have : (σ : ℂ) + Complex.I * ((2 * γ : ℝ) : ℂ) - ((σ₀ : ℂ) + Complex.I * ((2 * γ : ℝ) : ℂ))
        = ((σ - σ₀ : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hz0 : Gfull k f z ≠ 0 := Gfull_ne_zero_of_one_lt k f hk hf (by rw [hzre]; exact hσ1)
  have h := hineq z hzmem hz0
  -- every zero `u ∈ S` has `Re u ≤ 1 < σ`, so its term is nonnegative
  have hsum : 0 ≤ ∑ u ∈ S, (m u : ℝ) * (1 / (z - u)).re := by
    refine Finset.sum_nonneg fun u hu => ?_
    obtain ⟨-, hu0, hm⟩ := hS1 u hu
    have hure : u.re ≤ 1 := by
      by_contra hcon
      exact Gfull_ne_zero_of_one_lt k f hk hf (by linarith) hu0
    exact mul_nonneg (by exact_mod_cast (by omega : (0 : ℤ) ≤ m u))
      (re_one_div_sub_nonneg (by rw [hzre]; linarith))
  have hlog : 0 ≤ Real.log |2 * γ| := Real.log_nonneg (by linarith)
  have hlog2 : Real.log |2 * γ| ≤ 2 * Real.log |γ| := by
    rw [abs_mul, abs_two, Real.log_mul (by norm_num) (by linarith [abs_nonneg γ] : |γ| ≠ 0)]
    have h2 : Real.log 2 ≤ Real.log |γ| := Real.log_le_log (by norm_num) (by linarith)
    linarith
  calc -(logDeriv (Gfull k f) z).re ≤ C' * Real.log |2 * γ| - ∑ u ∈ S, (m u : ℝ) * (1 / (z - u)).re := h
    _ ≤ C' * Real.log |2 * γ| := by linarith
    _ ≤ 2 * C' * Real.log |γ| := by nlinarith

include cf in
/-- **(B)** for a zero `ρ = β + iγ` of `G` with `3/4 < β < 1`, `|γ| ≥ t₀`:
`−Re (G′/G)(σ + iγ) ≤ −1/(σ − β) + C′ log|γ|` for `1 < σ ≤ 2`. -/
theorem neg_re_logDeriv_Gfull_le_of_zero (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k) :
    ∃ C' t₀ : ℝ, 0 < C' ∧ 2 ≤ t₀ ∧ ∀ β γ : ℝ, 3 / 4 < β → β < 1 → t₀ ≤ |γ| →
      Gfull k f ((β : ℂ) + Complex.I * γ) = 0 → ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      -(logDeriv (Gfull k f) ((σ : ℂ) + Complex.I * γ)).re ≤ -(1 / (σ - β)) + C' * Real.log |γ| := by
  obtain ⟨σ₀, C', t₀, hσ₀, hC', ht₀, hmain⟩ := logDeriv_bound_setup k f hk hf
  refine ⟨C', t₀, hC', ht₀, fun β γ hβ1 hβ2 hγ hρ σ hσ1 hσ2 => ?_⟩
  obtain ⟨S, m, hS1, hS2, hineq⟩ := hmain γ hγ
  set z : ℂ := (σ : ℂ) + Complex.I * γ with hz
  set ρ : ℂ := (β : ℂ) + Complex.I * γ with hρdef
  have hzre : z.re = σ := by simp [hz]
  have hzim : z.im = γ := by simp [hz]
  have hρre : ρ.re = β := by simp [hρdef]
  have hρim : ρ.im = γ := by simp [hρdef]
  have hzmem : z ∈ Metric.closedBall ((σ₀ : ℂ) + Complex.I * γ) (σ₀ - 1) := by
    rw [Metric.mem_closedBall, Complex.dist_eq]
    have : z - ((σ₀ : ℂ) + Complex.I * γ) = ((σ - σ₀ : ℝ) : ℂ) := by rw [hz]; push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hρmem : ρ ∈ Metric.ball ((σ₀ : ℂ) + Complex.I * γ) (2 * (σ₀ - 1)) := by
    rw [Metric.mem_ball, Complex.dist_eq]
    have : ρ - ((σ₀ : ℂ) + Complex.I * γ) = ((β - σ₀ : ℝ) : ℂ) := by rw [hρdef]; push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  have hρS : ρ ∈ S := hS2 ρ hρmem hρ
  have hz0 : Gfull k f z ≠ 0 := Gfull_ne_zero_of_one_lt k f hk hf (by rw [hzre]; exact hσ1)
  have h := hineq z hzmem hz0
  -- every term is nonnegative, and the term of `ρ` is at least `1/(σ − β)`
  have hterm : ∀ u ∈ S, 0 ≤ (m u : ℝ) * (1 / (z - u)).re := by
    intro u hu
    obtain ⟨-, hu0, hm⟩ := hS1 u hu
    have hure : u.re ≤ 1 := by
      by_contra hcon
      exact Gfull_ne_zero_of_one_lt k f hk hf (by linarith) hu0
    exact mul_nonneg (by exact_mod_cast (by omega : (0 : ℤ) ≤ m u))
      (re_one_div_sub_nonneg (by rw [hzre]; linarith))
  have hρterm : 1 / (σ - β) ≤ (m ρ : ℝ) * (1 / (z - ρ)).re := by
    obtain ⟨-, -, hm⟩ := hS1 ρ hρS
    have hre : (1 / (z - ρ)).re = 1 / (σ - β) := by
      rw [re_one_div_sub_of_im_eq (by rw [hzim, hρim]), hzre, hρre]
    rw [hre]
    have hpos : 0 ≤ 1 / (σ - β) := div_nonneg zero_le_one (by linarith)
    have hm1 : (1 : ℝ) ≤ m ρ := by exact_mod_cast hm
    nlinarith
  have hsum : 1 / (σ - β) ≤ ∑ u ∈ S, (m u : ℝ) * (1 / (z - u)).re :=
    hρterm.trans (Finset.single_le_sum hterm hρS)
  linarith

end RankinSelbergDelta.RankinSelberg

/-! ### the simple-pole log-derivative bound:
`−Re(logDeriv G)(σ) ≤ 1/(σ−1) + C` for `1 < σ ≤ 2`, from `(s−1)·G(s) = H(s)` with
`H(s) = rsPre(s)·((s−1) rsJ(s) − ((s−1)/s − 1)∫Φ)` holomorphic off `0` and nonvanishing on `[1, 2]`
(`H(1) = rsPre(1)·∫Φ ≠ 0`, `H(σ) = (σ−1)G(σ) ≠ 0` for `σ > 1`). -/

namespace RankinSelbergDelta.RankinSelberg

open Complex UpperHalfPlane MeasureTheory Set Filter RankinSelbergDelta.Eisenstein
open scoped Real Topology Modular

variable {F : Type*} [FunLike F ℍ ℂ] (k : ℤ)
  [cf : CuspFormClass F (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma 1)) k]

lemma one_mem_strictPeriods_levelOne' :
    (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma 1)).strictPeriods := by
  simp

include cf in
/-- A Hecke eigenform is not the zero function (`a₁ = 1`). -/
lemma ne_zero_of_isHeckeEigenCoeffs (f : F) (hf : IsHeckeEigenCoeffs (rsCoeff f) k) :
    (⇑f : ℍ → ℂ) ≠ 0 := by
  intro h0
  have h1 : (ModularFormClass.qExpansion 1 f).coeff 1 = 0 := by
    have := qExpansion_coeff_unique (f := f) (c := fun _ => (0 : ℂ)) one_pos
      one_mem_strictPeriods_levelOne' (fun τ => by
        rw [show f τ = 0 from congrFun h0 τ]
        simpa using hasSum_zero) 1
    simpa using this.symm
  have := hf.one
  rw [show rsCoeff f 1 = (ModularFormClass.qExpansion 1 f).coeff 1 from rfl, h1] at this
  exact zero_ne_one this

include cf in
/-- **The pole bound**: `−Re (G′/G)(σ) ≤ 1/(σ − 1) + C` for `1 < σ ≤ 2`. -/
theorem neg_re_logDeriv_Gfull_le_pole (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      -(logDeriv (Gfull k f) (σ : ℂ)).re ≤ 1 / (σ - 1) + C := by
  have hf0 : (⇑f : ℍ → ℂ) ≠ 0 := ne_zero_of_isHeckeEigenCoeffs k f hf
  set I₀ : ℂ := ((∫ z in (𝒟 : Set ℍ), phi k f z : ℝ) : ℂ) with hI₀
  have hI₀ne : I₀ ≠ 0 := by
    rw [hI₀]; exact_mod_cast (integral_phi_pos_of_ne_zero k f hf0).ne'
  set H : ℂ → ℂ := fun s => rsPre k s * ((s - 1) * rsJ k f s - ((s - 1) / s - 1) * I₀) with hH
  -- `H = (s − 1) rsG` off `{0, 1}`
  have hHeq : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → H s = (s - 1) * rsG k f s := by
    intro s hs0 hs1
    have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
    rw [rsG_eq_rsPre_mul_rsLambda]
    unfold rsLambda
    show rsPre k s * ((s - 1) * rsJ k f s - ((s - 1) / s - 1) * I₀)
      = (s - 1) * (rsPre k s * (rsJ k f s - (1 / s + 1 / (1 - s)) * I₀))
    field_simp
    ring
  -- `H` is differentiable off `0`
  have hHd : ∀ s : ℂ, s ≠ 0 → DifferentiableAt ℂ H s := fun s hs => by
    have h1 : DifferentiableAt ℂ (fun s : ℂ => (s - 1) * rsJ k f s) s :=
      (differentiableAt_id.sub_const 1).mul (differentiable_rsJ k f hk s)
    have h2 : DifferentiableAt ℂ (fun s : ℂ => ((s - 1) / s - 1) * I₀) s :=
      (((differentiableAt_id.sub_const 1).div differentiableAt_id hs).sub_const 1).mul_const I₀
    exact (differentiable_rsPre k s).mul (h1.sub h2)
  -- `H ≠ 0` on `[1, 2]`
  have hHne : ∀ σ : ℝ, 1 ≤ σ → σ ≤ 2 → H (σ : ℂ) ≠ 0 := by
    intro σ h1 h2
    rcases eq_or_lt_of_le h1 with h1 | h1'
    · subst h1
      have hpre : rsPre k 1 ≠ 0 := rsPre_ne_zero k hk (by simp)
      show rsPre k ((1 : ℝ) : ℂ) * ((((1 : ℝ) : ℂ) - 1) * rsJ k f ((1 : ℝ) : ℂ)
        - ((((1 : ℝ) : ℂ) - 1) / ((1 : ℝ) : ℂ) - 1) * I₀) ≠ 0
      push_cast
      simp only [sub_self, zero_mul, zero_div, zero_sub, neg_mul, one_mul, sub_neg_eq_add, zero_add]
      exact mul_ne_zero hpre hI₀ne
    · have hs0 : (σ : ℂ) ≠ 0 := by exact_mod_cast (by linarith : σ ≠ 0)
      have hs1 : (σ : ℂ) ≠ 1 := by exact_mod_cast (by linarith : σ ≠ 1)
      have hre : (1 : ℝ) < (σ : ℂ).re := by simpa using h1'
      rw [hHeq σ hs0 hs1, rsG_eq_Gfull_of_one_lt k f hk hre]
      exact mul_ne_zero (sub_ne_zero.mpr hs1) (Gfull_ne_zero_of_one_lt k f hk hf hre)
  -- `σ ↦ logDeriv H σ` is continuous on `[1, 2]`, hence bounded
  have hopen : IsOpen ({0}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hHan : AnalyticOnNhd ℂ H ({0}ᶜ : Set ℂ) :=
    DifferentiableOn.analyticOnNhd (fun s hs => (hHd s hs).differentiableWithinAt) hopen
  have hderiv : ContinuousOn (deriv H) ({0}ᶜ : Set ℂ) := (hHan.deriv).continuousOn
  have hcont : ContinuousOn (fun σ : ℝ => logDeriv H (σ : ℂ)) (Set.Icc 1 2) := by
    intro σ hσ
    have hσ0 : (σ : ℂ) ≠ 0 := by exact_mod_cast (by linarith [hσ.1] : σ ≠ 0)
    have hmem : (σ : ℂ) ∈ ({0}ᶜ : Set ℂ) := hσ0
    have hc1 : ContinuousAt (fun σ : ℝ => deriv H (σ : ℂ)) σ :=
      (hderiv.continuousAt (hopen.mem_nhds hmem)).comp Complex.continuous_ofReal.continuousAt
    have hc2 : ContinuousAt (fun σ : ℝ => H (σ : ℂ)) σ :=
      (hHd σ hσ0).continuousAt.comp Complex.continuous_ofReal.continuousAt
    exact (hc1.div hc2 (hHne σ hσ.1 hσ.2)).continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (1 : ℝ) 2)).exists_bound_of_continuousOn hcont
  refine ⟨|C| + 1, by positivity, fun σ h1 h2 => ?_⟩
  have hs0 : (σ : ℂ) ≠ 0 := by exact_mod_cast (by linarith : σ ≠ 0)
  have hs1 : (σ : ℂ) ≠ 1 := by exact_mod_cast (by linarith : σ ≠ 1)
  -- near `σ`, `G = H / (s − 1)`
  have hGeq : Gfull k f =ᶠ[𝓝 (σ : ℂ)] fun s => H s / (s - 1) := by
    have hopen' : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : (σ : ℂ) ∈ {s : ℂ | 1 < s.re} := by show (1 : ℝ) < (σ : ℂ).re; simpa using h1
    filter_upwards [hopen'.mem_nhds hmem] with s hs
    have hs' : (1 : ℝ) < s.re := hs
    have hs0' : s ≠ 0 := by intro h; rw [h, Complex.zero_re] at hs'; linarith
    have hs1' : s ≠ 1 := by intro h; rw [h, Complex.one_re] at hs'; linarith
    rw [← rsG_eq_Gfull_of_one_lt k f hk hs', eq_div_iff (sub_ne_zero.mpr hs1'), hHeq s hs0' hs1']
    ring
  have hlog : logDeriv (Gfull k f) σ = logDeriv H σ - ((1 / (σ - 1) : ℝ) : ℂ) := by
    rw [show logDeriv (Gfull k f) σ = logDeriv (fun s => H s / (s - 1)) σ by
      simp only [logDeriv_apply]
      rw [hGeq.deriv_eq, hGeq.eq_of_nhds]]
    rw [logDeriv_div (f := H) (g := fun s => s - 1) (σ : ℂ) (hHne σ h1.le h2)
      (sub_ne_zero.mpr hs1) (hHd σ hs0) (differentiableAt_id.sub_const 1)]
    congr 1
    rw [logDeriv_apply, deriv_sub_const, deriv_id'']
    push_cast
    ring
  rw [hlog, Complex.sub_re, Complex.ofReal_re]
  have hb := hC σ ⟨h1.le, h2⟩
  have hre := Complex.abs_re_le_norm (logDeriv H σ)
  rw [abs_le] at hre
  linarith [le_abs_self C]

end RankinSelbergDelta.RankinSelberg
