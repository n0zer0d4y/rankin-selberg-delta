import RankinSelbergDelta.RankinSelberg.FiniteHeightReach
import RankinSelbergDelta.RankinSelberg.ArchimedeanBound

/-!
# The archimedean term on the critical line

The archimedean factor `rsPre` is real on the real axis (`rsPre_conj`); the archimedean kernel `Ak`;
the contour shift of the archimedean term to the critical line (`archimedean_shift`); and the
resulting identity and lower bound for the archimedean part of the Weil form (`weilForm_arch_eq`,
`weilForm_arch_ge`).
-/

open MeasureTheory Filter
open scoped NNReal MatrixGroups Pointwise

noncomputable section

namespace RankinSelbergDelta.RankinSelberg

open Complex UpperHalfPlane MeasureTheory Set Filter RankinSelbergDelta.Eisenstein RankinSelbergDelta.ArgPrinciple
open scoped Real Topology Modular FourierTransform ComplexConjugate

variable {F : Type*} [FunLike F ℍ ℂ] (k : ℤ)
  [cf : CuspFormClass F (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma 1)) k]

/-! #### A. Schwarz reflection for `rsPre` and the critical-line kernel `A_k` -/

lemma rsPre_conj (s : ℂ) : rsPre k (conj s) = conj (rsPre k s) := by
  unfold rsPre
  have h4 : ((4 * Real.pi : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (by positivity)]; exact Real.pi_ne_zero.symm
  have hπ : (Real.pi : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]; exact Real.pi_ne_zero.symm
  have e1 : conj s + (k : ℂ) - 1 = conj (s + k - 1) := by
    rw [map_sub, map_add, map_intCast, map_one]
  rw [e1, Complex.cpow_conj _ _ h4, Complex.cpow_conj _ _ hπ, Complex.Gamma_conj, Complex.Gamma_conj,
    Complex.conj_ofReal, Complex.conj_ofReal]
  simp only [map_mul, map_div₀, map_inv₀, map_ofNat]

lemma logDeriv_rsPre_conj (s : ℂ) :
    logDeriv (rsPre k) (conj s) = conj (logDeriv (rsPre k) s) :=
  ArchimedeanBound.logDeriv_conj_of_conj (differentiable_rsPre k) (rsPre_conj k) s

/-- The critical-line archimedean kernel `A_k(t) = −2 Re (rsPre′/rsPre)(1/2 + it)`
(the degree-4 referee's `A_k`). -/
noncomputable def Ak (t : ℝ) : ℝ := -(2 * (logDeriv (rsPre k) ((1 / 2 : ℂ) + t * Complex.I)).re)

lemma kernel_line_eq (t : ℝ) :
    logDeriv (rsPre k) ((1 / 2 : ℂ) - t * Complex.I)
      + logDeriv (rsPre k) ((1 / 2 : ℂ) + t * Complex.I) = -((Ak k t : ℝ) : ℂ) := by
  have e : ((1 / 2 : ℂ) - t * Complex.I) = conj ((1 / 2 : ℂ) + t * Complex.I) := by
    apply Complex.ext <;> simp
  rw [e, logDeriv_rsPre_conj, Ak, add_comm, Complex.add_conj]
  push_cast
  ring

/-! #### B. The zero of `rsPre` inside the shift rectangle -/

lemma rsPre_ne_zero_of_im_ne_zero' (hk : 0 < k) {s : ℂ} (hs : s.im ≠ 0) : rsPre k s ≠ 0 := by
  refine rsPre_ne_zero_of_not_int k hk ?_ ?_
  · intro m h; apply hs; rw [h]; simp
  · intro m h; apply hs
    have := congrArg Complex.im h; simpa using this

/-- On `1 − σ ≤ Re u ≤ 1/2` (`1 < σ < 2`), `rsPre u = 0` only at `u = 0`. -/
lemma rsPre_ne_zero_of_mem_strip (hk : 0 < k) {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ < 2) {u : ℂ}
    (h1 : 1 - σ ≤ u.re) (h2 : u.re ≤ 1 / 2) (hu : u ≠ 0) : rsPre k u ≠ 0 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  refine rsPre_ne_zero_of_not_int k hk ?_ ?_
  · intro m h
    have hre := congrArg Complex.re h
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    rcases Nat.eq_zero_or_pos m with hm | hm
    · apply hu; rw [h, hm]; simp
    · have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      linarith
  · intro m h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.sub_re, Complex.intCast_re, Complex.one_re, Complex.neg_re,
      Complex.natCast_re] at hre
    -- u.re = 1 − k − m ≤ 0; it is > −1 only if k = 1 and m = 0, i.e. u = 0
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    rcases le_or_gt k 1 with hk' | hk'
    · have hk1' : k = 1 := le_antisymm hk' hk
      rcases Nat.eq_zero_or_pos m with hm | hm
      · apply hu
        have : u = -(m : ℂ) - k + 1 := by linear_combination h
        rw [this, hm, hk1']; simp
      · have : (1 : ℝ) ≤ m := by exact_mod_cast hm
        linarith
    · have h2k : (2 : ℤ) ≤ k := by omega
      have : (2 : ℝ) ≤ k := by exact_mod_cast h2k
      linarith

/-- The divisor of `rsPre` on the shift rectangle `[1 − σ, 1/2] × [−T, T]` is concentrated at `0`:
`∑ᶠ u, D u · φ u = D 0 · φ 0`. -/
lemma finsum_divisor_rsPre_rect (hk : 0 < k) {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ < 2) {T : ℝ}
    (φ : ℂ → ℂ) :
    (∑ᶠ u, ((MeromorphicOn.divisor (rsPre k) (closedRect ⟨1 - σ, -T⟩ ⟨1 / 2, T⟩)) u : ℂ) * φ u)
      = ((MeromorphicOn.divisor (rsPre k) (closedRect ⟨1 - σ, -T⟩ ⟨1 / 2, T⟩)) 0 : ℂ) * φ 0 := by
  refine finsum_eq_single _ 0 fun u hu => ?_
  set D := MeromorphicOn.divisor (rsPre k) (closedRect ⟨1 - σ, -T⟩ ⟨1 / 2, T⟩) with hD
  have hfa : AnalyticOnNhd ℂ (rsPre k) (closedRect ⟨1 - σ, -T⟩ ⟨1 / 2, T⟩) :=
    fun s _ => (differentiable_rsPre k).analyticAt s
  by_cases huK : u ∈ closedRect ⟨1 - σ, -T⟩ ⟨1 / 2, T⟩
  · have hre : 1 - σ ≤ u.re ∧ u.re ≤ 1 / 2 := by
      have h := huK
      rw [closedRect, Complex.mem_reProdIm, Set.uIcc_of_le (by show 1 - σ ≤ 1 / 2; linarith)] at h
      exact ⟨h.1.1, h.1.2⟩
    have hne : rsPre k u ≠ 0 := rsPre_ne_zero_of_mem_strip k hk hσ1 hσ2 hre.1 hre.2 hu
    have hD0 : D u = 0 := by
      rw [hD, MeromorphicOn.divisor_apply hfa.meromorphicOn huK, (hfa u huK).meromorphicOrderAt_eq,
        analyticOrderAt_eq_zero.mpr (Or.inr hne)]
      rfl
    rw [hD0]; simp
  · have hD0 : D u = 0 := by
      by_contra h
      exact huK (D.supportWithinDomain (Function.mem_support.mpr h))
    rw [hD0]; simp

/-! #### C. The contour shift of the archimedean integral to the critical line -/

/-- A continuous function with polynomial-times-rapid-decay bound on `|t| ≥ 1` is integrable. -/
lemma integrable_of_bound_on_tail {Φ : ℝ → ℂ} (hc : Continuous Φ) {C : ℝ}
    (hb : ∀ t : ℝ, 1 ≤ |t| → ‖Φ t‖ ≤ C * (1 + ‖t‖) ^ (-(2 : ℝ))) : Integrable Φ := by
  have hdom : Integrable (fun t : ℝ => C * (1 + ‖t‖) ^ (-(2 : ℝ))) :=
    (integrable_one_add_norm (by simp : (Module.finrank ℝ ℝ : ℝ) < 2)).const_mul _
  have hK : IntegrableOn Φ (Icc (-1) 1) := hc.continuousOn.integrableOn_compact isCompact_Icc
  have hKc : IntegrableOn Φ (Icc (-1) 1)ᶜ := by
    refine Integrable.mono' hdom.integrableOn hc.aestronglyMeasurable.restrict ?_
    rw [ae_restrict_iff' measurableSet_Icc.compl]
    refine ae_of_all _ fun t ht => hb t ?_
    rw [mem_compl_iff, mem_Icc, not_and_or] at ht
    rw [le_abs]
    rcases ht with h | h
    · right; linarith
    · left; linarith
  have := hK.union hKc
  rwa [union_compl_self, integrableOn_univ] at this

/-- **The archimedean integral on `Re s = 1 − σ` equals the one on the critical line plus the
residue at the zero `s = 0` of `rsPre`.** For `h` with `ĥ` entire and rapidly decaying on the strip
`1 − σ ≤ Re s ≤ σ`:
`∫ (ψ̃(σ − it) + ψ̃(1 − σ + it)) ĥ(1 − σ + it) dt
  = ∫ (ψ̃(1/2 − it) + ψ̃(1/2 + it)) ĥ(1/2 + it) dt − 2π · D₀ · ĥ(0)`,
with `D₀` the order of `rsPre` at `0` (its divisor on any rectangle through `0`). -/
theorem archimedean_shift (hk : 0 < k) {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ < 2) (h : ℝ → ℂ)
    (hga : ∀ s : ℂ, AnalyticAt ℂ (ghat h) s)
    (hdecN : ∀ N : ℕ, ∃ B : ℝ, ∀ s : ℂ, 1 - σ ≤ s.re → s.re ≤ σ → 1 ≤ |s.im| →
      ‖ghat h s‖ * |s.im| ^ N ≤ B)
    (hArch : Integrable (fun t : ℝ =>
      (logDeriv (rsPre k) ((σ : ℂ) - t * Complex.I)
          + logDeriv (rsPre k) (((1 - σ : ℝ) : ℂ) + t * Complex.I))
        * ghat h (((1 - σ : ℝ) : ℂ) + t * Complex.I))) :
    (∫ t : ℝ, (logDeriv (rsPre k) ((σ : ℂ) - t * Complex.I)
          + logDeriv (rsPre k) (((1 - σ : ℝ) : ℂ) + t * Complex.I))
        * ghat h (((1 - σ : ℝ) : ℂ) + t * Complex.I))
      = (∫ t : ℝ, (logDeriv (rsPre k) ((1 / 2 : ℂ) - t * Complex.I)
          + logDeriv (rsPre k) ((1 / 2 : ℂ) + t * Complex.I)) * ghat h ((1 / 2 : ℂ) + t * Complex.I))
        - 2 * Real.pi * ((MeromorphicOn.divisor (rsPre k) (closedRect ⟨1 - σ, -1⟩ ⟨1 / 2, 1⟩)) 0 : ℂ)
          * ghat h 0 := by
  classical
  -- the integrand `Φ(s) = (ψ̃(1 − s) + ψ̃(s)) ĥ(s)`
  set Φ : ℂ → ℂ := fun s => (logDeriv (rsPre k) (1 - s) + logDeriv (rsPre k) s) * ghat h s with hΦ
  have hghc : Continuous (ghat h) := continuous_iff_continuousAt.mpr fun s => (hga s).continuousAt
  obtain ⟨C, hC, N, hψ⟩ := exists_norm_logDeriv_rsPre_le k hk
  obtain ⟨B, hB⟩ := hdecN (N + 2)
  have hB0 : 0 ≤ B := by
    have := hB ⟨1 - σ, 1⟩ le_rfl (by show 1 - σ ≤ σ; linarith) (by show (1 : ℝ) ≤ |1|; simp)
    exact (mul_nonneg (norm_nonneg _) (by positivity)).trans this
  -- continuity of `ψ̃` off the zeros of `rsPre`
  have hcontψ : ∀ s : ℂ, rsPre k s ≠ 0 → ContinuousAt (logDeriv (rsPre k)) s := by
    intro s hs
    have hd : ContinuousAt (deriv (rsPre k)) s :=
      ((differentiable_rsPre k).analyticAt s).deriv.continuousAt
    have hc : ContinuousAt (rsPre k) s := (differentiable_rsPre k s).continuousAt
    have : logDeriv (rsPre k) = fun w => deriv (rsPre k) w / rsPre k w :=
      funext fun w => logDeriv_apply _ _
    rw [this]; exact hd.div hc hs
  have hdiffψ : ∀ s : ℂ, rsPre k s ≠ 0 → DifferentiableAt ℂ (logDeriv (rsPre k)) s := by
    intro s hs
    have : logDeriv (rsPre k) = fun w => deriv (rsPre k) w / rsPre k w :=
      funext fun w => logDeriv_apply _ _
    rw [this]
    exact (((differentiable_rsPre k).analyticAt s).deriv.differentiableAt).div
      (differentiable_rsPre k s) hs
  -- the two rectangle identities on `K_T = [1 − σ, 1/2] × [−T, T]`, `T ≥ 1`
  have hrect : ∀ T : ℝ, 1 ≤ T →
      rectBoundaryIntegral Φ ⟨1 - σ, -T⟩ ⟨1 / 2, T⟩
        = 2 * Real.pi * Complex.I
          * ((MeromorphicOn.divisor (rsPre k) (closedRect ⟨1 - σ, -T⟩ ⟨1 / 2, T⟩)) 0 : ℂ)
          * ghat h 0 := by
    intro T hT
    have hzw : (⟨1 - σ, -T⟩ : ℂ).re < (⟨1 / 2, T⟩ : ℂ).re ∧
        (⟨1 - σ, -T⟩ : ℂ).im < (⟨1 / 2, T⟩ : ℂ).im :=
      ⟨by show 1 - σ < 1 / 2; linarith, by show -T < T; linarith⟩
    have hre_rect : ∀ s ∈ closedRect (⟨1 - σ, -T⟩ : ℂ) ⟨1 / 2, T⟩, 1 - σ ≤ s.re ∧ s.re ≤ 1 / 2 := by
      intro s hs
      rw [closedRect, Complex.mem_reProdIm, Set.uIcc_of_le hzw.1.le] at hs
      exact ⟨hs.1.1, hs.1.2⟩
    -- Φ₁(s) = ψ̃(1 − s) ĥ(s) is analytic on the closed rectangle (Re (1 − s) ≥ 1/2 > 0)
    have hΦ₁ : DifferentiableOn ℂ (fun s => logDeriv (rsPre k) (1 - s) * ghat h s)
        (closedRect (⟨1 - σ, -T⟩ : ℂ) ⟨1 / 2, T⟩) := by
      intro s hs
      have hre := hre_rect s hs
      have hne : rsPre k (1 - s) ≠ 0 := rsPre_ne_zero k hk (by simp; linarith)
      exact ((hdiffψ _ hne).comp s ((differentiableAt_const _).sub differentiableAt_id)).mul
        (hga s).differentiableAt |>.differentiableWithinAt
    have hBI₁ := rectBoundaryIntegral_eq_zero_of_differentiableOn hΦ₁
    -- Φ₂(s) = ψ̃(s) ĥ(s): the argument principle for `rsPre`
    have hfa : AnalyticOnNhd ℂ (rsPre k) (closedRect (⟨1 - σ, -T⟩ : ℂ) ⟨1 / 2, T⟩) :=
      fun s _ => (differentiable_rsPre k).analyticAt s
    have hne : ∀ s ∈ rectBoundary (⟨1 - σ, -T⟩ : ℂ) ⟨1 / 2, T⟩, rsPre k s ≠ 0 := by
      intro s hs
      obtain ⟨hsK, hcase⟩ := hs
      have hre := hre_rect s hsK
      rcases hcase with h | h | h | h
      · change s.re = 1 - σ at h
        exact rsPre_ne_zero_of_mem_strip k hk hσ1 hσ2 hre.1 hre.2 (by
          intro h0; rw [h0, Complex.zero_re] at h; linarith)
      · change s.re = 1 / 2 at h
        exact rsPre_ne_zero k hk (by rw [h]; norm_num)
      · change s.im = -T at h
        exact rsPre_ne_zero_of_im_ne_zero' k hk (by rw [h]; linarith)
      · change s.im = T at h
        exact rsPre_ne_zero_of_im_ne_zero' k hk (by rw [h]; linarith)
    have hBI₂ := rectBoundaryIntegral_logDeriv_mul (rsPre k) (ghat h) ⟨1 - σ, -T⟩ ⟨1 / 2, T⟩ hzw hfa
      (fun s _ => hga s) hne
    rw [finsum_divisor_rsPre_rect k hk hσ1 hσ2] at hBI₂
    -- Φ = Φ₁ + Φ₂ on the boundary
    have hE₁ : EdgeIntegrable (fun s => logDeriv (rsPre k) (1 - s) * ghat h s) ⟨1 - σ, -T⟩ ⟨1 / 2, T⟩ :=
      EdgeIntegrable.of_continuousOn (hΦ₁.continuousOn.mono (rectBoundary_subset _ _))
    have hE₂ : EdgeIntegrable (fun s => logDeriv (rsPre k) s * ghat h s) ⟨1 - σ, -T⟩ ⟨1 / 2, T⟩ := by
      refine EdgeIntegrable.of_continuousOn ?_
      intro s hs
      exact ((hcontψ s (hne s hs)).mul hghc.continuousAt).continuousWithinAt
    have hsplit : ∀ s ∈ rectBoundary (⟨1 - σ, -T⟩ : ℂ) ⟨1 / 2, T⟩, Φ s
        = logDeriv (rsPre k) (1 - s) * ghat h s + logDeriv (rsPre k) s * ghat h s := by
      intro s _; simp only [hΦ]; ring
    rw [rectBoundaryIntegral_congr hsplit, rectBoundaryIntegral_add hE₁ hE₂, hBI₁, hBI₂]
    ring
  -- the divisor value at `0` does not depend on `T`
  have hD₀ : ∀ T : ℝ, 1 ≤ T →
      ((MeromorphicOn.divisor (rsPre k) (closedRect ⟨1 - σ, -T⟩ ⟨1 / 2, T⟩)) 0 : ℂ)
        = ((MeromorphicOn.divisor (rsPre k) (closedRect ⟨1 - σ, -1⟩ ⟨1 / 2, 1⟩)) 0 : ℂ) := by
    intro T hT
    have hfa : ∀ T' : ℝ, AnalyticOnNhd ℂ (rsPre k) (closedRect ⟨1 - σ, -T'⟩ ⟨1 / 2, T'⟩) :=
      fun T' s _ => (differentiable_rsPre k).analyticAt s
    have hmem : ∀ T' : ℝ, 1 ≤ T' → (0 : ℂ) ∈ closedRect (⟨1 - σ, -T'⟩ : ℂ) ⟨1 / 2, T'⟩ := by
      intro T' hT'
      rw [closedRect, Complex.mem_reProdIm, Set.uIcc_of_le (by show 1 - σ ≤ 1 / 2; linarith),
        Set.uIcc_of_le (by show -T' ≤ T'; linarith)]
      exact ⟨⟨by show 1 - σ ≤ (0:ℂ).re; simp; linarith, by show (0:ℂ).re ≤ 1 / 2; simp⟩,
        ⟨by show -T' ≤ (0:ℂ).im; simp; linarith, by show (0:ℂ).im ≤ T'; simp; linarith⟩⟩
    rw [MeromorphicOn.divisor_apply (hfa T).meromorphicOn (hmem T hT),
      MeromorphicOn.divisor_apply (hfa 1).meromorphicOn (hmem 1 le_rfl)]
  -- edges, as functions of `j : ℕ` (T = j ≥ 1)
  have hedge : ∀ (j : ℕ), 1 ≤ j → ∀ (τ : ℝ), τ = (j : ℝ) ∨ τ = -(j : ℝ) →
      ‖∫ x in (1 - σ)..(1 / 2 : ℝ), Φ ((x : ℂ) + τ * Complex.I)‖
        ≤ (2 * C * 2 ^ N * B * (σ - 1 / 2)) / (j : ℝ) ^ 2 := by
    intro j hj τ hτ
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have hτabs : |τ| = j := by rcases hτ with h | h <;> rw [h] <;> simp [abs_of_pos (by linarith : (0:ℝ) < j)]
    have hpt : ∀ x : ℝ, x ∈ Set.uIoc (1 - σ) (1 / 2 : ℝ) →
        ‖Φ ((x : ℂ) + τ * Complex.I)‖ ≤ 2 * C * 2 ^ N * B / (j : ℝ) ^ 2 := by
      intro x hx
      rw [Set.uIoc_of_le (by linarith), Set.mem_Ioc] at hx
      have hψ1 := hψ ((x : ℂ) + τ * Complex.I) (by simp; linarith) (by simp; linarith)
        (by simp [hτabs]; linarith)
      have hψ2 := hψ (1 - ((x : ℂ) + τ * Complex.I)) (by simp; linarith) (by simp; linarith)
        (by simp [hτabs]; linarith)
      have hh := hB ((x : ℂ) + τ * Complex.I) (by simp; linarith) (by simp; linarith)
        (by simp [hτabs]; linarith)
      have e1 : |((x : ℂ) + τ * Complex.I).im| = j := by simp [hτabs]
      have e2 : |(1 - ((x : ℂ) + τ * Complex.I)).im| = j := by simp [hτabs]
      rw [e1] at hψ1 hh; rw [e2] at hψ2
      have hsum : ‖logDeriv (rsPre k) (1 - ((x : ℂ) + τ * Complex.I))
          + logDeriv (rsPre k) ((x : ℂ) + τ * Complex.I)‖ ≤ 2 * C * (1 + (j : ℝ)) ^ N :=
        (norm_add_le _ _).trans (by linarith)
      have hpow : (1 + (j : ℝ)) ^ N ≤ (2 * j) ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
      have hhb : ‖ghat h ((x : ℂ) + τ * Complex.I)‖ ≤ B / (j : ℝ) ^ (N + 2) := by
        rw [le_div_iff₀ (by positivity)]; exact hh
      simp only [hΦ]
      rw [norm_mul]
      calc ‖logDeriv (rsPre k) (1 - ((x : ℂ) + τ * Complex.I))
            + logDeriv (rsPre k) ((x : ℂ) + τ * Complex.I)‖ * ‖ghat h ((x : ℂ) + τ * Complex.I)‖
          ≤ (2 * C * (2 * j) ^ N) * (B / (j : ℝ) ^ (N + 2)) :=
            mul_le_mul (hsum.trans (by nlinarith [hpow, hC.le])) hhb (norm_nonneg _) (by positivity)
        _ = 2 * C * 2 ^ N * B / (j : ℝ) ^ 2 := by
            rw [mul_pow, pow_add]; field_simp; (try ring)
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    rw [abs_of_pos (by linarith : (0 : ℝ) < 1 / 2 - (1 - σ))] at h1
    refine h1.trans (le_of_eq ?_)
    ring
  have hzero : Tendsto (fun j : ℕ => (2 * C * 2 ^ N * B * (σ - 1 / 2)) / (j : ℝ) ^ 2) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := 2 * C * 2 ^ N * B * (σ - 1 / 2))).div_atTop
      ((tendsto_pow_atTop (n := 2) (by norm_num) : Tendsto (fun x : ℝ => x ^ 2) atTop atTop).comp
        tendsto_natCast_atTop_atTop)
    exact this
  have hbot : Tendsto (fun j : ℕ => ∫ x in (1 - σ)..(1 / 2 : ℝ), Φ ((x : ℂ) + ((-(j : ℝ)) : ℝ) * Complex.I))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hzero
    filter_upwards [eventually_ge_atTop 1] with j hj
    exact hedge j hj _ (Or.inr rfl)
  have htop : Tendsto (fun j : ℕ => ∫ x in (1 - σ)..(1 / 2 : ℝ), Φ ((x : ℂ) + ((j : ℝ) : ℝ) * Complex.I))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hzero
    filter_upwards [eventually_ge_atTop 1] with j hj
    exact hedge j hj _ (Or.inl rfl)
  -- the vertical edges: integrability on both lines
  have hint_left : Integrable (fun t : ℝ => Φ (((1 - σ : ℝ) : ℂ) + t * Complex.I)) := by
    refine hArch.congr (Eventually.of_forall fun t => ?_)
    simp only [hΦ]
    congr 2
    push_cast; ring
  have hint_right : Integrable (fun t : ℝ => Φ ((1 / 2 : ℂ) + t * Complex.I)) := by
    refine integrable_of_bound_on_tail ?_ (C := 2 * C * 2 ^ N * B * 4) ?_
    · have hψR : Continuous (fun t : ℝ => logDeriv (rsPre k) (1 - ((1 / 2 : ℂ) + t * Complex.I))) :=
        continuous_iff_continuousAt.mpr fun t =>
          (hcontψ _ (rsPre_ne_zero k hk (by simp <;> norm_num))).comp
            (f := fun t : ℝ => 1 - ((1 / 2 : ℂ) + t * Complex.I)) (by fun_prop)
      have hψL : Continuous (fun t : ℝ => logDeriv (rsPre k) ((1 / 2 : ℂ) + t * Complex.I)) :=
        continuous_iff_continuousAt.mpr fun t =>
          (hcontψ _ (rsPre_ne_zero k hk (by simp <;> norm_num))).comp
            (f := fun t : ℝ => (1 / 2 : ℂ) + t * Complex.I) (by fun_prop)
      exact (hψR.add hψL).mul (hghc.comp (by fun_prop))
    · intro t ht
      have hψ1 := hψ ((1 / 2 : ℂ) + t * Complex.I) (by simp <;> norm_num) (by simp <;> norm_num)
        (by simp; exact ht)
      have hψ2 := hψ (1 - ((1 / 2 : ℂ) + t * Complex.I)) (by simp <;> norm_num) (by simp <;> norm_num)
        (by simp; exact ht)
      have hh := hB ((1 / 2 : ℂ) + t * Complex.I) (by simp; linarith) (by simp; linarith) (by simp; exact ht)
      have e1 : |((1 / 2 : ℂ) + t * Complex.I).im| = |t| := by simp
      have e2 : |(1 - ((1 / 2 : ℂ) + t * Complex.I)).im| = |t| := by simp
      rw [e1] at hψ1 hh; rw [e2] at hψ2
      have ht0 : 0 < |t| := by linarith
      have hsum : ‖logDeriv (rsPre k) (1 - ((1 / 2 : ℂ) + t * Complex.I))
          + logDeriv (rsPre k) ((1 / 2 : ℂ) + t * Complex.I)‖ ≤ 2 * C * (1 + |t|) ^ N :=
        (norm_add_le _ _).trans (by linarith)
      have hpow : (1 + |t|) ^ N ≤ (2 * |t|) ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
      have hhb : ‖ghat h ((1 / 2 : ℂ) + t * Complex.I)‖ ≤ B / |t| ^ (N + 2) := by
        rw [le_div_iff₀ (by positivity)]; exact hh
      simp only [hΦ]
      rw [norm_mul, Real.norm_eq_abs, Real.rpow_neg (by positivity), Real.rpow_two]
      calc ‖logDeriv (rsPre k) (1 - ((1 / 2 : ℂ) + t * Complex.I))
            + logDeriv (rsPre k) ((1 / 2 : ℂ) + t * Complex.I)‖ * ‖ghat h ((1 / 2 : ℂ) + t * Complex.I)‖
          ≤ (2 * C * (2 * |t|) ^ N) * (B / |t| ^ (N + 2)) :=
            mul_le_mul (hsum.trans (by nlinarith [hpow, hC.le])) hhb (norm_nonneg _) (by positivity)
        _ = 2 * C * 2 ^ N * B / |t| ^ 2 := by rw [mul_pow, pow_add]; field_simp; (try ring)
        _ ≤ 2 * C * 2 ^ N * B * 4 * ((1 + |t|) ^ 2)⁻¹ := by
            rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
            have hq : (1 + |t|) ^ 2 ≤ 4 * |t| ^ 2 := by nlinarith
            have hc0 : 0 ≤ 2 * C * 2 ^ N * B := by positivity
            nlinarith [mul_le_mul_of_nonneg_left hq hc0]
  have hTtop : Tendsto (fun j : ℕ => (j : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hTbot : Tendsto (fun j : ℕ => -(j : ℝ)) atTop atBot := tendsto_neg_atTop_atBot.comp hTtop
  have hright : Tendsto (fun j : ℕ => ∫ t in (-(j : ℝ))..(j : ℝ), Φ ((1 / 2 : ℂ) + t * Complex.I)) atTop
      (𝓝 (∫ t : ℝ, Φ ((1 / 2 : ℂ) + t * Complex.I))) :=
    intervalIntegral_tendsto_integral hint_right hTbot hTtop
  have hleft : Tendsto (fun j : ℕ => ∫ t in (-(j : ℝ))..(j : ℝ), Φ (((1 - σ : ℝ) : ℂ) + t * Complex.I)) atTop
      (𝓝 (∫ t : ℝ, Φ (((1 - σ : ℝ) : ℂ) + t * Complex.I))) :=
    intervalIntegral_tendsto_integral hint_left hTbot hTtop
  -- the identity for each `j ≥ 1`, from the rectangle
  have hid : ∀ᶠ j : ℕ in atTop,
      (∫ t in (-(j : ℝ))..(j : ℝ), Φ ((1 / 2 : ℂ) + t * Complex.I))
        - (∫ t in (-(j : ℝ))..(j : ℝ), Φ (((1 - σ : ℝ) : ℂ) + t * Complex.I))
      = 2 * Real.pi * ((MeromorphicOn.divisor (rsPre k) (closedRect ⟨1 - σ, -1⟩ ⟨1 / 2, 1⟩)) 0 : ℂ)
          * ghat h 0
        + Complex.I * ((∫ x in (1 - σ)..(1 / 2 : ℝ), Φ ((x : ℂ) + ((-(j : ℝ)) : ℝ) * Complex.I))
          - ∫ x in (1 - σ)..(1 / 2 : ℝ), Φ ((x : ℂ) + ((j : ℝ) : ℝ) * Complex.I)) := by
    filter_upwards [eventually_ge_atTop 1] with j hj
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have hrc := hrect (j : ℝ) hj1
    rw [hD₀ (j : ℝ) hj1, rectBoundaryIntegral_mk] at hrc
    have e12 : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by push_cast; ring
    simp only [e12] at hrc
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    -- hrc : B − T + I•R − I•L = 2πi D₀ ĥ(0); solve for R − L
    simp only [smul_eq_mul] at hrc
    linear_combination (-Complex.I) * hrc + (((∫ t in (-(j : ℝ))..(j : ℝ), Φ ((1 / 2 : ℂ) + t * Complex.I))
        - ∫ t in (-(j : ℝ))..(j : ℝ), Φ (((1 - σ : ℝ) : ℂ) + t * Complex.I))
        - 2 * Real.pi * ((MeromorphicOn.divisor (rsPre k) (closedRect ⟨1 - σ, -1⟩ ⟨1 / 2, 1⟩)) 0 : ℂ)
          * ghat h 0) * hI
  -- pass to the limit
  have hlim : Tendsto (fun j : ℕ => (∫ t in (-(j : ℝ))..(j : ℝ), Φ ((1 / 2 : ℂ) + t * Complex.I))
      - ∫ t in (-(j : ℝ))..(j : ℝ), Φ (((1 - σ : ℝ) : ℂ) + t * Complex.I)) atTop
      (𝓝 ((∫ t : ℝ, Φ ((1 / 2 : ℂ) + t * Complex.I)) - ∫ t : ℝ, Φ (((1 - σ : ℝ) : ℂ) + t * Complex.I))) :=
    hright.sub hleft
  have hlim2 : Tendsto (fun j : ℕ =>
      2 * Real.pi * ((MeromorphicOn.divisor (rsPre k) (closedRect ⟨1 - σ, -1⟩ ⟨1 / 2, 1⟩)) 0 : ℂ)
          * ghat h 0
        + Complex.I * ((∫ x in (1 - σ)..(1 / 2 : ℝ), Φ ((x : ℂ) + ((-(j : ℝ)) : ℝ) * Complex.I))
          - ∫ x in (1 - σ)..(1 / 2 : ℝ), Φ ((x : ℂ) + ((j : ℝ) : ℝ) * Complex.I))) atTop
      (𝓝 (2 * Real.pi * ((MeromorphicOn.divisor (rsPre k) (closedRect ⟨1 - σ, -1⟩ ⟨1 / 2, 1⟩)) 0 : ℂ)
          * ghat h 0 + Complex.I * (0 - 0))) :=
    tendsto_const_nhds.add ((hbot.sub htop).const_mul _)
  have huniq := tendsto_nhds_unique (hlim.congr' hid) hlim2
  -- unfold `Φ` on the two lines
  have hL : (∫ t : ℝ, Φ (((1 - σ : ℝ) : ℂ) + t * Complex.I))
      = ∫ t : ℝ, (logDeriv (rsPre k) ((σ : ℂ) - t * Complex.I)
          + logDeriv (rsPre k) (((1 - σ : ℝ) : ℂ) + t * Complex.I))
        * ghat h (((1 - σ : ℝ) : ℂ) + t * Complex.I) := by
    congr 1; funext t; simp only [hΦ]; congr 2; push_cast; ring
  have hR : (∫ t : ℝ, Φ ((1 / 2 : ℂ) + t * Complex.I))
      = ∫ t : ℝ, (logDeriv (rsPre k) ((1 / 2 : ℂ) - t * Complex.I)
          + logDeriv (rsPre k) ((1 / 2 : ℂ) + t * Complex.I)) * ghat h ((1 / 2 : ℂ) + t * Complex.I) := by
    congr 1; funext t; simp only [hΦ]; congr 2; ring
  rw [hL, hR] at huniq
  linear_combination -huniq

/-! #### D. The archimedean term of the self-dual Weil form on the critical line, and its lower bound -/

/-- **The archimedean term on the critical line.** For `h = g ⋆ g♯`:
`−(1/2π) ∫ (ψ̃(σ − it) + ψ̃(1 − σ + it)) ĥ(1 − σ + it) dt
  = (1/2π) ∫ A_k(t) ‖ĝ(1/2 + it)‖² dt + D₀ · ĝ(0) conj(ĝ(1))`
(`D₀` the order of `rsPre` at `0`): the kernel `A_k` against the square of `ĝ` on the line, plus the
companion `ĥ(0) = ĝ(0) conj(ĝ(1))` of the pole term `ĥ(1) = ĝ(1) conj(ĝ(0))`. -/
theorem weilForm_arch_eq (hk : 0 < k) {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ < 2) (g : ℝ → ℂ)
    (hc : Continuous g) (hs : HasCompactSupport g)
    (hga : ∀ s : ℂ, AnalyticAt ℂ (ghat (WeilForm.selfDual g)) s)
    (hdecN : ∀ N : ℕ, ∃ B : ℝ, ∀ s : ℂ, 1 - σ ≤ s.re → s.re ≤ σ → 1 ≤ |s.im| →
      ‖ghat (WeilForm.selfDual g) s‖ * |s.im| ^ N ≤ B)
    (hArch : Integrable (fun t : ℝ =>
      (logDeriv (rsPre k) ((σ : ℂ) - t * Complex.I)
          + logDeriv (rsPre k) (((1 - σ : ℝ) : ℂ) + t * Complex.I))
        * ghat (WeilForm.selfDual g) (((1 - σ : ℝ) : ℂ) + t * Complex.I))) :
    -((1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (logDeriv (rsPre k) ((σ : ℂ) - t * Complex.I)
          + logDeriv (rsPre k) (((1 - σ : ℝ) : ℂ) + t * Complex.I))
        * ghat (WeilForm.selfDual g) (((1 - σ : ℝ) : ℂ) + t * Complex.I))
      = ((1 / (2 * Real.pi) * ∫ t : ℝ, Ak k t * ‖ghat g ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2 : ℝ) : ℂ)
        + ((MeromorphicOn.divisor (rsPre k) (closedRect ⟨1 - σ, -1⟩ ⟨1 / 2, 1⟩)) 0 : ℂ)
          * (ghat g 0 * conj (ghat g 1)) := by
  rw [archimedean_shift k hk hσ1 hσ2 (WeilForm.selfDual g) hga hdecN hArch]
  have hpt : ∀ t : ℝ, (logDeriv (rsPre k) ((1 / 2 : ℂ) - t * Complex.I)
        + logDeriv (rsPre k) ((1 / 2 : ℂ) + t * Complex.I))
        * ghat (WeilForm.selfDual g) ((1 / 2 : ℂ) + t * Complex.I)
      = (((-(Ak k t * ‖ghat g ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2)) : ℝ) : ℂ) := by
    intro t
    have hl : ghat (WeilForm.selfDual g) ((1 / 2 : ℂ) + t * Complex.I)
        = ((‖ghat g ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2 : ℝ) : ℂ) :=
      WeilForm.ghat_selfDual_line g hc hs t
    rw [kernel_line_eq, hl]
    push_cast; ring
  have h0 : ghat (WeilForm.selfDual g) 0 = ghat g 0 * conj (ghat g 1) := by
    have := WeilForm.ghat_selfDual_eq g hc hs 0
    simp only [map_zero, sub_zero] at this
    exact this
  rw [h0]
  simp_rw [hpt]
  have hI : (∫ t : ℝ, (((-(Ak k t * ‖ghat g ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2)) : ℝ) : ℂ))
      = (((∫ t : ℝ, -(Ak k t * ‖ghat g ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2)) : ℝ) : ℂ) :=
    integral_ofReal (𝕜 := ℂ) (f := fun t : ℝ => -(Ak k t * ‖ghat g ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2))
  rw [hI, integral_neg]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hcomm : (∫ a : ℝ, Ak k a * ‖ghat g ((1 / 2 : ℂ) + Complex.I * a)‖ ^ 2)
      = ∫ a : ℝ, Ak k a * ‖ghat g ((1 / 2 : ℂ) + a * Complex.I)‖ ^ 2 := by
    congr 1; funext a; rw [mul_comm Complex.I]
  push_cast
  field_simp
  (try ring_nf)
  (try rw [hcomm])
  (try ring)

/-- **The archimedean lower bound**. Under the sign pattern of the kernel,
`A_k ≥ −A₀` on `|t| < t₀` and `A_k ≥ 0` on `|t| ≥ t₀`, and the Paley–Wiener bound
`‖ĝ(s)‖ ≤ e^{|Re s| L} M` on the line `Re s = 1/2`, the archimedean quadratic form is bounded below:
`(1/2π) ∫ A_k ‖ĝ(1/2 + it)‖² dt ≥ −(1/2π) · 2 t₀ A₀ e^{L} M²`. -/
theorem weilForm_arch_ge {σ : ℝ} {L M t₀ A₀ : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M) (ht₀ : 0 ≤ t₀)
    (hA₀ : 0 ≤ A₀) (g : ℝ → ℂ)
    (hint : Integrable (fun t : ℝ => Ak k t * ‖ghat g ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2))
    (hPW : ∀ s : ℂ, ‖ghat g s‖ ≤ Real.exp (|s.re| * L) * M)
    (hpos : ∀ t : ℝ, t₀ ≤ |t| → 0 ≤ Ak k t) (hneg : ∀ t : ℝ, |t| < t₀ → -A₀ ≤ Ak k t) :
    -((1 / (2 * Real.pi)) * (2 * t₀ * A₀ * (Real.exp L * M ^ 2)))
      ≤ (1 / (2 * Real.pi)) * ∫ t : ℝ, Ak k t * ‖ghat g ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2 := by
  have hW : ∀ t : ℝ, ‖ghat g ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2 ≤ Real.exp L * M ^ 2 := by
    intro t
    have h := hPW ((1 / 2 : ℂ) + t * Complex.I)
    have hre : |((1 / 2 : ℂ) + t * Complex.I).re| = 1 / 2 := by simp <;> norm_num
    rw [hre] at h
    have h2 : Real.exp (1 / 2 * L) ^ 2 = Real.exp L := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    calc ‖ghat g ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2 ≤ (Real.exp (1 / 2 * L) * M) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = Real.exp L * M ^ 2 := by rw [mul_pow, h2]
  have := ArchimedeanBound.integral_kernel_ge ht₀ hA₀ (by positivity) hint
    (fun t => by positivity) hW hpos hneg
  have hπ : 0 < 1 / (2 * Real.pi) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left this hπ.le]

end RankinSelbergDelta.RankinSelberg
