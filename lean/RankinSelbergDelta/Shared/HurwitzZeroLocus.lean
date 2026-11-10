import Mathlib

/-!
# Hurwitz's theorem, in zero-locus form

If holomorphic functions `f n` have all their zeros in a closed set `S` and converge locally
uniformly on a connected open set `U` to a function `g` that is not identically zero, then every zero
of `g` in `U` lies in `S` (`hurwitz_zero_locus`). With `S = ℝ` (`hurwitz_real_zeros`) this is the
closure of the class of functions with only real zeros. The proof uses isolated zeros and the
maximum modulus principle for `1/f n`; it needs neither Rouché's theorem nor the argument principle.
-/

open Complex Filter Topology Metric Set

namespace RankinSelbergDelta.Shared

/-- **Hurwitz, zero-locus form.** -/
theorem hurwitz_zero_locus {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hf : ∀ n, DifferentiableOn ℂ (f n) U) (hg : DifferentiableOn ℂ g U)
    (hlim : TendstoLocallyUniformlyOn f g atTop U)
    (hne : ∃ z ∈ U, g z ≠ 0)
    {S : Set ℂ} (hS : IsClosed S) (hzero : ∀ n, ∀ z ∈ U, f n z = 0 → z ∈ S) :
    ∀ z ∈ U, g z = 0 → z ∈ S := by
  intro z0 hz0U hgz0
  by_contra hz0S
  -- a ball around `z0` inside `U \ S`
  have hopen : IsOpen (U \ S) := hU.sdiff hS
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen z0 ⟨hz0U, hz0S⟩
  -- the zeros of `g` are isolated
  have hga : AnalyticOnNhd ℂ g U := hg.analyticOnNhd hU
  have hiso : ∀ᶠ z in 𝓝[≠] z0, g z ≠ 0 := by
    by_contra h
    have hfreq : ∃ᶠ z in 𝓝[≠] z0, g z = 0 := h
    have h0 := hga.eqOn_zero_of_preconnected_of_frequently_eq_zero hUc hz0U hfreq
    obtain ⟨w, hwU, hw⟩ := hne
    exact hw (h0 hwU)
  obtain ⟨ε, hε, hεg⟩ := Metric.mem_nhdsWithin_iff.mp hiso
  -- the radius
  set ρ : ℝ := min (r / 2) (ε / 2) with hρ
  have hρpos : 0 < ρ := lt_min (by linarith) (by linarith)
  have hρr : ρ < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hρε : ρ < ε := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hcb_sub : closedBall z0 ρ ⊆ ball z0 r := fun z hz =>
    lt_of_le_of_lt (mem_closedBall.mp hz) hρr
  have hcbU : closedBall z0 ρ ⊆ U := fun z hz => (hball (hcb_sub hz)).1
  have hcbS : ∀ z ∈ closedBall z0 ρ, z ∉ S := fun z hz => (hball (hcb_sub hz)).2
  -- `g` is nonzero on the sphere
  have hsph_ne : ∀ z ∈ sphere z0 ρ, g z ≠ 0 := by
    intro z hz hgz
    have hdz : dist z z0 = ρ := mem_sphere.mp hz
    have hzne : z ≠ z0 := by
      intro h
      rw [h, dist_self] at hdz
      linarith
    have hzε : z ∈ ball z0 ε := by
      rw [mem_ball, hdz]
      exact hρε
    exact hεg ⟨hzε, hzne⟩ hgz
  -- minimum of `|g|` on the sphere
  have hgc : ContinuousOn g (sphere z0 ρ) := hg.continuousOn.mono (fun z hz => hcbU (sphere_subset_closedBall hz))
  obtain ⟨zm, hzm, hmin⟩ := (isCompact_sphere z0 ρ).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr (le_of_lt hρpos)) (hgc.norm)
  set δ : ℝ := ‖g zm‖ with hδ
  have hδpos : 0 < δ := norm_pos_iff.mpr (hsph_ne zm hzm)
  have hδle : ∀ z ∈ sphere z0 ρ, δ ≤ ‖g z‖ := fun z hz => hmin hz
  -- uniform convergence on the closed ball
  have hK : IsCompact (closedBall z0 ρ) := isCompact_closedBall z0 ρ
  have hunif : TendstoUniformlyOn f g atTop (closedBall z0 ρ) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hlim _ hcbU hK
  obtain ⟨n, hn⟩ := ((Metric.tendstoUniformlyOn_iff.mp hunif) (δ / 3) (by linarith)).exists
  -- `f n` has no zero on the closed ball
  have hfne : ∀ z ∈ closedBall z0 ρ, f n z ≠ 0 := fun z hz h0 => hcbS z hz (hzero n z (hcbU hz) h0)
  -- maximum modulus for `1 / f n`
  have hdiff : DifferentiableOn ℂ (fun z => (f n z)⁻¹) (closedBall z0 ρ) :=
    fun z hz => (((hf n) z (hcbU hz)).mono (fun w hw => hcbU hw)).inv (hfne z hz)
  have hdc : DiffContOnCl ℂ (fun z => (f n z)⁻¹) (ball z0 ρ) := by
    refine ⟨hdiff.mono ball_subset_closedBall, ?_⟩
    rw [closure_ball z0 hρpos.ne']
    exact hdiff.continuousOn
  have hfront : ∀ z ∈ frontier (ball z0 ρ), ‖(f n z)⁻¹‖ ≤ 3 / (2 * δ) := by
    intro z hz
    rw [frontier_ball z0 hρpos.ne'] at hz
    have hzcb : z ∈ closedBall z0 ρ := sphere_subset_closedBall hz
    have h1 : dist (g z) (f n z) < δ / 3 := hn z hzcb
    have h2 : ‖g z - f n z‖ < δ / 3 := by rwa [dist_eq_norm] at h1
    have h3 : 2 * δ / 3 < ‖f n z‖ := by
      have := norm_sub_norm_le (g z) (f n z)
      have := hδle z hz
      linarith
    rw [norm_inv, inv_eq_one_div, div_le_div_iff₀ (by linarith) (by linarith)]
    linarith
  have hz0cl : z0 ∈ closure (ball z0 ρ) := by
    rw [closure_ball z0 hρpos.ne']
    exact mem_closedBall_self hρpos.le
  have hbound := Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball) hdc hfront hz0cl
  -- contradiction at `z0`
  have h1 : dist (g z0) (f n z0) < δ / 3 := hn z0 (mem_closedBall_self hρpos.le)
  have h2 : ‖f n z0‖ < δ / 3 := by
    rw [dist_eq_norm, hgz0, zero_sub, norm_neg] at h1
    exact h1
  have hfn0 : 0 < ‖f n z0‖ := norm_pos_iff.mpr (hfne z0 (mem_closedBall_self hρpos.le))
  rw [norm_inv, inv_eq_one_div, div_le_div_iff₀ hfn0 (by linarith)] at hbound
  linarith

/-- **Hurwitz with the real line as zero locus**: a locally uniform limit (on `ℂ`) of entire functions with only real zeros, not identically zero, has only real zeros. -/
theorem hurwitz_real_zeros {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hf : ∀ n, Differentiable ℂ (f n)) (hg : Differentiable ℂ g)
    (hlim : TendstoLocallyUniformlyOn f g atTop univ) (hne : ∃ z, g z ≠ 0)
    (hreal : ∀ n z, f n z = 0 → z.im = 0) :
    ∀ z, g z = 0 → z.im = 0 := by
  have hS : IsClosed {z : ℂ | z.im = 0} := isClosed_eq Complex.continuous_im continuous_const
  have := hurwitz_zero_locus (U := univ) isOpen_univ isPreconnected_univ (fun n => (hf n).differentiableOn)
    hg.differentiableOn hlim (by obtain ⟨z, hz⟩ := hne; exact ⟨z, mem_univ z, hz⟩) hS
    (fun n z _ h => hreal n z h)
  exact fun z hz => this z (mem_univ z) hz

end RankinSelbergDelta.Shared
