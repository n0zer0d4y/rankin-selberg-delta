import RankinSelbergDelta.RankinSelberg.NegIndexG

/-!
# The explicit formula for smooth compactly supported test functions

`explicitFormula_Gfull_of_smooth`: every analytic hypothesis of `explicitFormula_Gfull` holds when
the test function is smooth with compact support (entire transform, integrability on the two lines,
decay on horizontal segments).
-/

open MeasureTheory Filter
open scoped NNReal MatrixGroups Pointwise

noncomputable section

/-! ## `explicitFormula_Gfull` for smooth compactly supported test functions

Mathlib names relied on: `Continuous.integrable_of_hasCompactSupport`,
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`, `Differentiable.analyticAt`,
`HasCompactSupport.toSchwartzMap`, `SchwartzMap.fourierTransformCLM_apply`, `SchwartzMap.integrable`,
`integral_mul_deriv_eq_deriv_mul_of_integrable`, `ContDiff.iterate_deriv`, `HasCompactSupport.deriv`,
`HasDerivAt.comp_ofReal`, `Complex.abs_im_le_norm`, `Complex.abs_re_le_norm`, `ContDiffBump`. -/

namespace RankinSelbergDelta.RankinSelberg

open UpperHalfPlane MeasureTheory Filter Topology RankinSelbergDelta.ArgPrinciple
open scoped FourierTransform ContDiff

variable {F : Type*} [FunLike F ℍ ℂ] (k : ℤ)
  [cf : CuspFormClass F (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma 1)) k]

lemma continuous_cexp_mul (s : ℂ) : Continuous (fun x : ℝ => Complex.exp (s * x)) :=
  Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)

lemma hasCompactSupport_mul_cexp {g : ℝ → ℂ} (hs : HasCompactSupport g) (s : ℂ) :
    HasCompactSupport (fun x : ℝ => g x * Complex.exp (s * x)) :=
  hs.mul_right

/-- `x ↦ g x · e^{sx}` is integrable for continuous compactly supported `g`. -/
lemma integrable_mul_cexp {g : ℝ → ℂ} (hc : Continuous g) (hs : HasCompactSupport g) (s : ℂ) :
    Integrable (fun x : ℝ => g x * Complex.exp (s * x)) :=
  (hc.mul (continuous_cexp_mul s)).integrable_of_hasCompactSupport (hasCompactSupport_mul_cexp hs s)

lemma norm_cexp_mul_ofReal (s : ℂ) (x : ℝ) :
    ‖Complex.exp (s * x)‖ = Real.exp (s.re * x) := by
  rw [Complex.norm_exp]; congr 1; simp

/-- `ĝ` is differentiable everywhere (differentiation under the integral sign). -/
theorem differentiable_ghat {g : ℝ → ℂ} (hc : Continuous g) (hs : HasCompactSupport g) :
    Differentiable ℂ (ghat g) := by
  intro s₀
  set bound : ℝ → ℝ := fun x => ‖g x‖ * (|x| * Real.exp ((|s₀.re| + 1) * |x|)) with hbound
  have hbc : Continuous bound := by
    simp only [hbound]
    exact hc.norm.mul (continuous_abs.mul (Real.continuous_exp.comp (continuous_const.mul continuous_abs)))
  have hbs : HasCompactSupport bound := hs.norm.mul_right
  have hbi : Integrable bound := hbc.integrable_of_hasCompactSupport hbs
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun (s : ℂ) (x : ℝ) => g x * Complex.exp (s * x))
    (F' := fun (s : ℂ) (x : ℝ) => g x * (Complex.exp (s * x) * x))
    (x₀ := s₀) (s := Metric.ball s₀ 1) (bound := bound) (Metric.ball_mem_nhds s₀ one_pos)
    (Eventually.of_forall fun s => (hc.mul (continuous_cexp_mul s)).aestronglyMeasurable)
    (integrable_mul_cexp hc hs s₀)
    ((hc.mul ((continuous_cexp_mul s₀).mul Complex.continuous_ofReal)).aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_) hbi
    (Eventually.of_forall fun x s _ => ((hasDerivAt_mul_const (x : ℂ)).cexp.const_mul (g x)))
  · exact key.2.differentiableAt
  · intro s hs₁
    have hx : s.re * x ≤ (|s₀.re| + 1) * |x| := by
      have h3 := Complex.abs_re_le_norm (s - s₀)
      rw [Metric.mem_ball, dist_eq_norm] at hs₁
      rw [Complex.sub_re] at h3
      obtain ⟨h4, h5⟩ := abs_lt.mp (lt_of_le_of_lt h3 hs₁)
      have h6 := le_abs_self s₀.re
      have h7 := neg_abs_le s₀.re
      have h1 : |s.re| ≤ |s₀.re| + 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      calc s.re * x ≤ |s.re * x| := le_abs_self _
        _ = |s.re| * |x| := abs_mul _ _
        _ ≤ (|s₀.re| + 1) * |x| := by gcongr
    rw [norm_mul, norm_mul, norm_cexp_mul_ofReal, Complex.norm_real, Real.norm_eq_abs]
    calc ‖g x‖ * (Real.exp (s.re * x) * |x|)
        ≤ ‖g x‖ * (Real.exp ((|s₀.re| + 1) * |x|) * |x|) := by
          gcongr
      _ = bound x := by simp only [hbound]; ring

theorem analyticAt_ghat {g : ℝ → ℂ} (hc : Continuous g) (hs : HasCompactSupport g) (s : ℂ) :
    AnalyticAt ℂ (ghat g) s :=
  (differentiable_ghat hc hs).analyticAt s

theorem continuous_ghat {g : ℝ → ℂ} (hc : Continuous g) (hs : HasCompactSupport g) :
    Continuous (ghat g) :=
  (differentiable_ghat hc hs).continuous

/-- The Fourier transform of a smooth compactly supported function is integrable. -/
theorem integrable_fourierIntegral_of_smooth {h : ℝ → ℂ} (hh : ContDiff ℝ ∞ h)
    (hs : HasCompactSupport h) : Integrable (𝓕 h) := by
  have := (SchwartzMap.fourierTransformCLM ℂ (hs.toSchwartzMap hh)).integrable
    (μ := (volume : MeasureTheory.Measure ℝ))
  rw [SchwartzMap.fourierTransformCLM_apply] at this
  exact this

lemma contDiff_cexp_mul (s : ℂ) : ContDiff ℝ ∞ (fun x : ℝ => Complex.exp (s * x)) :=
  Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)

/-- Integration by parts once: `ĝ'(s) = -s ĝ(s)`. -/
theorem ghat_deriv {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hs : HasCompactSupport g) (s : ℂ) :
    ghat (deriv g) s = -(s * ghat g s) := by
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  have hdc : Continuous (deriv g) := hg.continuous_deriv (by simp)
  have hds : HasCompactSupport (deriv g) := hs.deriv
  have hv : ∀ x : ℝ, HasDerivAt (fun x : ℝ => Complex.exp (s * x)) (Complex.exp (s * x) * s) x := by
    intro x
    have h' : HasDerivAt (fun z : ℂ => Complex.exp (s * z)) (Complex.exp (s * x) * s) (x : ℂ) := by
      simpa using ((hasDerivAt_id ((x : ℂ))).const_mul s).cexp
    exact h'.comp_ofReal
  have huv' : Integrable (fun x : ℝ => g x * (Complex.exp (s * x) * s)) :=
    (hg.continuous.mul ((continuous_cexp_mul s).mul continuous_const)).integrable_of_hasCompactSupport
      hs.mul_right
  have hu'v : Integrable (fun x : ℝ => deriv g x * Complex.exp (s * x)) :=
    (hdc.mul (continuous_cexp_mul s)).integrable_of_hasCompactSupport hds.mul_right
  have hparts : ∫ x : ℝ, g x * (Complex.exp (s * x) * s) = -∫ x : ℝ, deriv g x * Complex.exp (s * x) :=
    integral_mul_deriv_eq_deriv_mul_of_integrable
      (u := g) (v := fun x : ℝ => Complex.exp (s * x)) (u' := deriv g)
      (v' := fun x : ℝ => Complex.exp (s * x) * s)
      (fun x => (hgd x).hasDerivAt) hv huv' hu'v (integrable_mul_cexp hg.continuous hs s)
  have h1 : ∫ x : ℝ, g x * (Complex.exp (s * x) * s) = s * ghat g s := by
    unfold ghat
    rw [← integral_const_mul]
    congr 1; funext x; ring
  have h2 : ∫ x : ℝ, deriv g x * Complex.exp (s * x) = ghat (deriv g) s := rfl
  rw [h1, h2] at hparts
  linear_combination hparts

lemma hasCompactSupport_iterate_deriv {g : ℝ → ℂ} (hs : HasCompactSupport g) :
    ∀ n : ℕ, HasCompactSupport (deriv^[n] g)
  | 0 => hs
  | n + 1 => by
      rw [Function.iterate_succ_apply']
      exact (hasCompactSupport_iterate_deriv hs n).deriv

/-- `N`-fold integration by parts: `ĝ^{(N)}(s) = (-s)^N ĝ(s)`. -/
theorem ghat_iterate_deriv {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hs : HasCompactSupport g)
    (s : ℂ) : ∀ N : ℕ, ghat (deriv^[N] g) s = (-s) ^ N * ghat g s
  | 0 => by simp
  | N + 1 => by
      rw [Function.iterate_succ_apply',
        ghat_deriv (hg.iterate_deriv N) (hasCompactSupport_iterate_deriv hs N) s,
        ghat_iterate_deriv hg hs s N, pow_succ]
      ring

/-- Crude bound: `‖ĝ(s)‖ ≤ ∫ ‖g‖ e^{2|x|}` for `|Re s| ≤ 2`. -/
theorem norm_ghat_le_of_abs_re_le {g : ℝ → ℂ} (hc : Continuous g) (hs : HasCompactSupport g)
    (s : ℂ) (hre : |s.re| ≤ 2) :
    ‖ghat g s‖ ≤ ∫ x : ℝ, ‖g x‖ * Real.exp (2 * |x|) := by
  unfold ghat
  refine (norm_integral_le_integral_norm _).trans ?_
  have hi2 : Integrable (fun x : ℝ => ‖g x‖ * Real.exp (2 * |x|)) :=
    (hc.norm.mul (Real.continuous_exp.comp (continuous_const.mul continuous_abs))).integrable_of_hasCompactSupport
      hs.norm.mul_right
  refine integral_mono (integrable_mul_cexp hc hs s).norm hi2 ?_
  intro x
  have hx : s.re * x ≤ 2 * |x| := by
    calc s.re * x ≤ |s.re * x| := le_abs_self _
      _ = |s.re| * |x| := abs_mul _ _
      _ ≤ 2 * |x| := by gcongr
  show ‖g x * Complex.exp (s * x)‖ ≤ ‖g x‖ * Real.exp (2 * |x|)
  rw [norm_mul, norm_cexp_mul_ofReal]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hx) (norm_nonneg _)

/-- Polynomial decay of every order on the strip `|Re s| ≤ 2`. -/
theorem exists_norm_ghat_mul_pow_le {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hs : HasCompactSupport g)
    (N : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, |s.re| ≤ 2 → ‖ghat g s‖ * ‖s‖ ^ N ≤ B := by
  refine ⟨∫ x : ℝ, ‖deriv^[N] g x‖ * Real.exp (2 * |x|),
    integral_nonneg fun x => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le, ?_⟩
  intro s hre
  have h := norm_ghat_le_of_abs_re_le (hg.iterate_deriv N).continuous
    (hasCompactSupport_iterate_deriv hs N) s hre
  rw [ghat_iterate_deriv hg hs s N, norm_mul, norm_pow, norm_neg] at h
  linarith [h]

/-- The decay in the form needed by `integrable_arch_kernel`: `‖ĝ(s)‖ (1 + |Im s|)^N ≤ B`. -/
theorem exists_norm_ghat_mul_one_add_abs_im_pow_le {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hs : HasCompactSupport g) (N : ℕ) :
    ∃ B : ℝ, ∀ s : ℂ, |s.re| ≤ 2 → ‖ghat g s‖ * (1 + |s.im|) ^ N ≤ B := by
  obtain ⟨B₀, hB₀, h₀⟩ := exists_norm_ghat_mul_pow_le hg hs 0
  obtain ⟨BN, hBN, hN⟩ := exists_norm_ghat_mul_pow_le hg hs N
  refine ⟨2 ^ N * (B₀ + BN), fun s hre => ?_⟩
  have hg0 := h₀ s hre
  have hgN := hN s hre
  simp only [pow_zero, mul_one] at hg0
  have him : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
  have hnn : 0 ≤ ‖ghat g s‖ := norm_nonneg _
  by_cases h1 : |s.im| ≤ 1
  · have : (1 + |s.im|) ^ N ≤ 2 ^ N := by gcongr; linarith
    calc ‖ghat g s‖ * (1 + |s.im|) ^ N ≤ B₀ * 2 ^ N := by gcongr
      _ ≤ 2 ^ N * (B₀ + BN) := by nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) N]
  · push_neg at h1
    have : (1 + |s.im|) ^ N ≤ 2 ^ N * ‖s‖ ^ N := by
      rw [← mul_pow]; gcongr; linarith
    calc ‖ghat g s‖ * (1 + |s.im|) ^ N ≤ ‖ghat g s‖ * (2 ^ N * ‖s‖ ^ N) := by gcongr
      _ = 2 ^ N * (‖ghat g s‖ * ‖s‖ ^ N) := by ring
      _ ≤ 2 ^ N * BN := by gcongr
      _ ≤ 2 ^ N * (B₀ + BN) := by nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) N]

/-- The `hdec` hypothesis of `explicitFormula_Gfull` on the strip `1 - σ ≤ Re s ≤ σ`, `1 < σ < 2`. -/
theorem exists_norm_ghat_mul_im_sq_le {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hs : HasCompactSupport g)
    {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ < 2) :
    ∃ B : ℝ, ∀ s : ℂ, 1 - σ ≤ s.re → s.re ≤ σ → 1 ≤ |s.im| → ‖ghat g s‖ * s.im ^ 2 ≤ B := by
  obtain ⟨B, -, hB⟩ := exists_norm_ghat_mul_pow_le hg hs 2
  refine ⟨B, fun s h1 h2 _ => ?_⟩
  have hre : |s.re| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have := hB s hre
  have him : s.im ^ 2 ≤ ‖s‖ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm s) 2
  calc ‖ghat g s‖ * s.im ^ 2 ≤ ‖ghat g s‖ * ‖s‖ ^ 2 := by gcongr
    _ ≤ B := this

/-- A smooth compactly supported test function exists (a `ContDiffBump`), so the hypotheses
`ContDiff ℝ ∞ g ∧ HasCompactSupport g` are not vacuous. -/
theorem smooth_compactSupport_satisfiable :
    ∃ g : ℝ → ℂ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ g 0 = 1 := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  refine ⟨fun x => (b x : ℂ), Complex.ofRealCLM.contDiff.comp b.contDiff,
    b.hasCompactSupport.comp_left Complex.ofReal_zero, ?_⟩
  simp [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]


/-- **The explicit formula for `g ∈ C_c^∞`.** Every analytic hypothesis of
`explicitFormula_Gfull` holds for a smooth compactly supported test function, so its conclusion
does: there are zero-avoiding heights `T_j ∈ [j, j+1]` along which the zero sums converge to
`ĝ(1) − ∑ Λ_G(n) g(log n) − ∑ Λ_G(n) g(−log n)/n − (1/2π) ∫ (archimedean kernel)`. -/
theorem explicitFormula_Gfull_of_smooth (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k)
    {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ < 2) (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hgs : HasCompactSupport g) :
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
  have hgc : Continuous g := hg.continuous
  -- the reflected function `g(−x) e^{−x}` is again smooth with compact support
  have hneg_s : HasCompactSupport (fun x : ℝ => g (-x)) :=
    hgs.comp_homeomorph (Homeomorph.neg ℝ)
  have hneg_c : ContDiff ℝ ∞ (fun x : ℝ => g (-x)) := hg.comp contDiff_neg
  have hexp_c : ContDiff ℝ ∞ (fun x : ℝ => Complex.exp (-(x : ℂ))) :=
    Complex.contDiff_exp.comp Complex.ofRealCLM.contDiff.neg
  have hrev_c : ContDiff ℝ ∞ (fun x : ℝ => g (-x) * Complex.exp (-(x : ℂ))) := hneg_c.mul hexp_c
  have hrev_s : HasCompactSupport (fun x : ℝ => g (-x) * Complex.exp (-(x : ℂ))) :=
    hneg_s.mul_right
  refine explicitFormula_Gfull k f hk hf hσ1 hσ2 g hgc (analyticAt_ghat hgc hgs)
    (integrable_mul_cexp hgc hgs σ)
    (integrable_fourierIntegral_of_smooth (hg.mul (contDiff_cexp_mul σ)) hgs.mul_right)
    ((hrev_c.continuous.mul (continuous_cexp_mul σ)).integrable_of_hasCompactSupport
      hrev_s.mul_right)
    (integrable_fourierIntegral_of_smooth (hrev_c.mul (contDiff_cexp_mul σ)) hrev_s.mul_right)
    (exists_norm_ghat_mul_im_sq_le hg hgs hσ1 hσ2)
    (integrable_arch_kernel k hk hσ1 hσ2 g (continuous_ghat hgc hgs) fun N => ?_)
  obtain ⟨B, hB⟩ := exists_norm_ghat_mul_one_add_abs_im_pow_le hg hgs N
  refine ⟨B, fun t => ?_⟩
  have hre : (((1 - σ : ℝ) : ℂ) + t * Complex.I).re = 1 - σ := by simp
  have him : (((1 - σ : ℝ) : ℂ) + t * Complex.I).im = t := by simp
  have := hB (((1 - σ : ℝ) : ℂ) + t * Complex.I)
    (by rw [hre]; exact abs_le.mpr ⟨by linarith, by linarith⟩)
  rw [him] at this
  exact this

/-- Non-vacuity witness for the new hypotheses of `explicitFormula_Gfull_of_smooth`: a strip
parameter `σ = 3/2` and a smooth compactly supported `g` with `g 0 = 1` (a `ContDiffBump`). -/
theorem explicitFormula_Gfull_of_smooth_hyps_satisfiable :
    ∃ (σ : ℝ) (g : ℝ → ℂ), 1 < σ ∧ σ < 2 ∧ ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ g 0 = 1 := by
  obtain ⟨g, hg, hgs, hg0⟩ := smooth_compactSupport_satisfiable
  exact ⟨3 / 2, g, by norm_num, by norm_num, hg, hgs, hg0⟩

end RankinSelbergDelta.RankinSelberg
