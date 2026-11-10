import RankinSelbergDelta.RankinSelberg.ExplicitFormula

/-!
# Polynomial growth of the archimedean kernel

`‖rsPre′(s) / rsPre(s)‖ ≤ C (1 + |Im s|)^N` for `−1 ≤ Re s ≤ 2` and `|Im s| ≥ 1`
(`exists_norm_logDeriv_rsPre_le`). This gives the integrability
hypothesis of the explicit formula for every test function whose transform decays.
-/

open MeasureTheory Filter
open scoped NNReal MatrixGroups Pointwise

noncomputable section


/-! ### the ARCHIMEDEAN kernel is polynomially bounded, so the integrability hypothesis
`hArch` of `explicitFormula_Gfull` follows from rapid decay of `ĝ` on the line `Re s = 1 − σ`. `‖rsPre′/rsPre(s)‖ ≤ C (1 + |Im s|)^N` on `−1 ≤ Re s ≤ 2`,
`|Im s| ≥ 1`: the Cauchy estimate for `rsPre′` from `exists_norm_rsPre_le`, and a lower bound on
`‖rsPre‖` from the upper bound `exists_norm_Gamma_le` on `‖Γ‖` moved to `Re u ≥ −1` by
`Γ(u) = Γ(u + 2)/(u (u + 1))`. -/

namespace RankinSelbergDelta.RankinSelberg

open Complex UpperHalfPlane MeasureTheory Set Filter Metric RankinSelbergDelta.Eisenstein
open scoped Real Topology Modular

variable {F : Type*} [FunLike F ℍ ℂ] (k : ℤ)
  [cf : CuspFormClass F (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma 1)) k]

/-- `‖Γ(u)‖ ≤ ‖Γ(u + n)‖` for `|Im u| ≥ 1` (each shift multiplies by `‖u + j‖ ≥ 1`). -/
lemma norm_Gamma_le_norm_Gamma_add_nat {u : ℂ} (hu : 1 ≤ |u.im|) (n : ℕ) :
    ‖Complex.Gamma u‖ ≤ ‖Complex.Gamma (u + n)‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hne : u + n ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp at this
      rw [this] at hu
      norm_num at hu
    have h1 : Complex.Gamma (u + ((n + 1 : ℕ) : ℂ)) = (u + n) * Complex.Gamma (u + n) := by
      rw [show (u + ((n + 1 : ℕ) : ℂ)) = (u + n) + 1 by push_cast; ring]
      exact Complex.Gamma_add_one _ hne
    rw [h1, norm_mul]
    have hn1 : 1 ≤ ‖u + n‖ := by
      calc (1:ℝ) ≤ |u.im| := hu
        _ = |(u + n).im| := by simp
        _ ≤ ‖u + n‖ := Complex.abs_im_le_norm _
    calc ‖Complex.Gamma u‖ ≤ ‖Complex.Gamma (u + n)‖ := ih
      _ = 1 * ‖Complex.Gamma (u + n)‖ := (one_mul _).symm
      _ ≤ ‖u + n‖ * ‖Complex.Gamma (u + n)‖ :=
          mul_le_mul_of_nonneg_right hn1 (norm_nonneg _)

/-- The Stirling-type upper bound on `‖Γ‖`, moved to `−1 ≤ Re u ≤ m`, `|Im u| ≥ 1`. -/
lemma exists_norm_Gamma_le_of_re_ge_neg_one (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℂ, -1 ≤ u.re → u.re ≤ m → 1 ≤ |u.im| →
      ‖Complex.Gamma u‖ ≤ C * (1 + |u.im|) ^ (m + 2) * Real.exp (-(Real.pi * |u.im| / 2)) := by
  obtain ⟨C, hC, hΓ⟩ := exists_norm_Gamma_le (m + 1)
  refine ⟨C, hC, fun u h1 h2 h3 => ?_⟩
  have h := hΓ (u + 2) (by simp; linarith) (by simp; push_cast; linarith)
  have him : (u + 2).im = u.im := by simp
  rw [him] at h
  have h2' := norm_Gamma_le_norm_Gamma_add_nat h3 2
  push_cast at h2'
  exact h2'.trans h

/-- A lower bound on `‖rsPre‖`: `c e^{π|Im s|} / (1 + |Im s|)^N ≤ ‖rsPre(s)‖` on `−1 ≤ Re s ≤ 2`,
`|Im s| ≥ 1`. -/
lemma exists_norm_rsPre_ge (hk : 0 < k) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
      c * Real.exp (Real.pi * |s.im|) / (1 + |s.im|) ^ N ≤ ‖rsPre k s‖ := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set m : ℕ := k.toNat + 2 with hm
  have hmk : (k : ℝ) + 1 ≤ m := by
    have : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk.le
    rw [hm]; push_cast; linarith
  have hm2 : (2 : ℝ) ≤ m := by rw [hm]; push_cast; linarith [(Nat.cast_nonneg k.toNat : (0:ℝ) ≤ k.toNat)]
  obtain ⟨C, hC, hΓ⟩ := exists_norm_Gamma_le_of_re_ge_neg_one m
  refine ⟨1 / (8 * Real.pi ^ 2 * C ^ 2), by positivity, 2 * (m + 2), fun s h1 h2 h3 => ?_⟩
  have hπ1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have h4π : (1 : ℝ) ≤ 4 * Real.pi := by linarith
  have hΓs := hΓ s h1 (by linarith) h3
  have hskre : (s + k - 1).re = s.re + k - 1 := by simp
  have hskim : (s + k - 1).im = s.im := by simp
  have hΓk := hΓ (s + k - 1) (by rw [hskre]; linarith) (by rw [hskre]; linarith) (by rw [hskim]; exact h3)
  rw [hskim] at hΓk
  have hΓs0 : 0 < ‖Complex.Gamma s‖ := by
    rw [norm_pos_iff]
    exact Complex.Gamma_ne_zero fun n h => by
      have := congrArg Complex.im h; simp at this; rw [this] at h3; norm_num at h3
  have hΓk0 : 0 < ‖Complex.Gamma (s + k - 1)‖ := by
    rw [norm_pos_iff]
    exact Complex.Gamma_ne_zero fun n h => by
      have := congrArg Complex.im h; rw [hskim] at this; simp at this; rw [this] at h3
      norm_num at h3
  set t : ℝ := |s.im| with ht
  have ht0 : 0 ≤ t := abs_nonneg _
  set E : ℝ := Real.exp (-(Real.pi * t / 2)) with hE
  have hEpos : 0 < E := Real.exp_pos _
  set Q : ℝ := C * (1 + t) ^ (m + 2) * E with hQ
  have hQpos : 0 < Q := by positivity
  have hΓs' : ‖Complex.Gamma s‖ ≤ Q := hΓs
  have hΓk' : ‖Complex.Gamma (s + k - 1)‖ ≤ Q := hΓk
  unfold rsPre
  rw [norm_div, norm_mul, norm_mul, norm_mul, norm_inv, norm_inv,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
    hskre]
  have hn2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [hn2]
  -- the four lower bounds
  have hA : (4 * Real.pi) ^ (-1 : ℝ) ≤ (4 * Real.pi) ^ (s.re + k - 1) :=
    Real.rpow_le_rpow_of_exponent_le h4π (by linarith)
  have hB : Real.pi ^ (-1 : ℝ) ≤ Real.pi ^ s.re :=
    Real.rpow_le_rpow_of_exponent_le hπ1 (by linarith)
  have hC' : Q⁻¹ ≤ ‖Complex.Gamma (s + k - 1)‖⁻¹ := inv_anti₀ hΓk0 hΓk'
  have hD : Q⁻¹ ≤ ‖Complex.Gamma s‖⁻¹ := inv_anti₀ hΓs0 hΓs'
  rw [Real.rpow_neg_one] at hA
  rw [Real.rpow_neg_one] at hB
  have hprod : (4 * Real.pi)⁻¹ * Real.pi⁻¹ * (Q⁻¹ * Q⁻¹) / 2
      ≤ (4 * Real.pi) ^ (s.re + k - 1) * Real.pi ^ s.re
        * (‖Complex.Gamma (s + k - 1)‖⁻¹ * ‖Complex.Gamma s‖⁻¹) / 2 := by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply mul_le_mul (mul_le_mul hA hB (by positivity) (by positivity))
      (mul_le_mul hC' hD (by positivity) (by positivity)) (by positivity) (by positivity)
  refine le_trans (le_of_eq ?_) hprod
  rw [hQ, hE, Real.exp_neg]
  have hexp : Real.exp (Real.pi * t) = Real.exp (Real.pi * t / 2) * Real.exp (Real.pi * t / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp, two_mul, pow_add]
  have hx : 0 < Real.exp (Real.pi * t / 2) := Real.exp_pos _
  have h1t : 0 < 1 + t := by linarith
  have hpt : 0 < (1 + t) ^ (m + 2) := by positivity
  field_simp
  ring

/-- The Cauchy estimate for `rsPre′` on `−1 ≤ Re s ≤ 2`. -/
lemma exists_norm_deriv_rsPre_le (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 →
      ‖deriv (rsPre k) s‖ ≤ C * (1 + |s.im|) ^ N * Real.exp (Real.pi * |s.im|) := by
  obtain ⟨C, hC, hpre⟩ := exists_norm_rsPre_le k hk 3
  refine ⟨2 * C * 2 ^ (2 * 3 + 2) * Real.exp (Real.pi / 2), by positivity, 2 * 3 + 2,
    fun s h1 h2 => ?_⟩
  have hd : DiffContOnCl ℂ (rsPre k) (ball s (1 / 2)) :=
    (differentiable_rsPre k).differentiableOn.diffContOnCl
  have hsph : ∀ z ∈ sphere s (1 / 2), ‖rsPre k z‖
      ≤ C * (2 * (1 + |s.im|)) ^ (2 * 3 + 2) * (Real.exp (Real.pi * |s.im|) * Real.exp (Real.pi / 2)) := by
    intro z hz
    rw [mem_sphere, Complex.dist_eq] at hz
    have hre := Complex.abs_re_le_norm (z - s)
    have him := Complex.abs_im_le_norm (z - s)
    rw [Complex.sub_re, hz] at hre
    rw [Complex.sub_im, hz] at him
    rw [abs_le] at hre him
    have hzre2 : z.re ≤ (3 : ℕ) := by push_cast; linarith
    have hzim : |z.im| ≤ |s.im| + 1 / 2 := by
      have := abs_sub_abs_le_abs_sub z.im s.im
      have h2 : |z.im - s.im| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
      linarith
    have hp := hpre z (by push_cast; linarith) hzre2
    have hpow : (1 + |z.im|) ^ (2 * 3 + 2) ≤ (2 * (1 + |s.im|)) ^ (2 * 3 + 2) :=
      pow_le_pow_left₀ (by positivity) (by linarith [abs_nonneg s.im]) _
    have hexp : Real.exp (Real.pi * |z.im|) ≤ Real.exp (Real.pi * |s.im|) * Real.exp (Real.pi / 2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_pos]
    calc ‖rsPre k z‖ ≤ C * (1 + |z.im|) ^ (2 * 3 + 2) * Real.exp (Real.pi * |z.im|) := hp
      _ ≤ C * (2 * (1 + |s.im|)) ^ (2 * 3 + 2) * (Real.exp (Real.pi * |s.im|) * Real.exp (Real.pi / 2)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hpow hC.le) hexp (by positivity) (by positivity)
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0:ℝ) < 1 / 2) hd hsph
  refine this.trans (le_of_eq ?_)
  rw [mul_pow]
  field_simp

/-- **The archimedean kernel is polynomially bounded**: `‖rsPre′/rsPre(s)‖ ≤ C (1 + |Im s|)^N` on
`−1 ≤ Re s ≤ 2`, `|Im s| ≥ 1`. -/
theorem exists_norm_logDeriv_rsPre_le (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
      ‖logDeriv (rsPre k) s‖ ≤ C * (1 + |s.im|) ^ N := by
  obtain ⟨C₁, hC₁, N₁, hup⟩ := exists_norm_deriv_rsPre_le k hk
  obtain ⟨c, hc, N₂, hlow⟩ := exists_norm_rsPre_ge k hk
  refine ⟨C₁ / c, by positivity, N₁ + N₂, fun s h1 h2 h3 => ?_⟩
  rw [logDeriv_apply, norm_div]
  have hpos : 0 < c * Real.exp (Real.pi * |s.im|) / (1 + |s.im|) ^ N₂ := by positivity
  have hlow' := hlow s h1 h2 h3
  have hup' := hup s h1 h2
  have hx : 0 < Real.exp (Real.pi * |s.im|) := Real.exp_pos _
  have h1t : 0 < 1 + |s.im| := by linarith [abs_nonneg s.im]
  calc ‖deriv (rsPre k) s‖ / ‖rsPre k s‖
      ≤ (C₁ * (1 + |s.im|) ^ N₁ * Real.exp (Real.pi * |s.im|))
          / (c * Real.exp (Real.pi * |s.im|) / (1 + |s.im|) ^ N₂) :=
        div_le_div₀ (by positivity) hup' hpos hlow'
    _ = C₁ / c * (1 + |s.im|) ^ (N₁ + N₂) := by
        rw [pow_add]; field_simp

lemma continuous_logDeriv_rsPre_line (hk : 0 < k) {a : ℝ} (ha : ∀ y : ℝ, rsPre k ((a : ℂ) + y * Complex.I) ≠ 0) :
    Continuous (fun y : ℝ => logDeriv (rsPre k) ((a : ℂ) + y * Complex.I)) := by
  have hcontψ : ∀ s : ℂ, rsPre k s ≠ 0 → ContinuousAt (logDeriv (rsPre k)) s := by
    intro s hs
    have hd : ContinuousAt (deriv (rsPre k)) s :=
      ((differentiable_rsPre k).analyticAt s).deriv.continuousAt
    have hc : ContinuousAt (rsPre k) s := (differentiable_rsPre k s).continuousAt
    have : logDeriv (rsPre k) = fun w => deriv (rsPre k) w / rsPre k w :=
      funext fun w => logDeriv_apply _ _
    rw [this]; exact hd.div hc hs
  exact continuous_iff_continuousAt.mpr fun y =>
    (hcontψ _ (ha y)).comp (f := fun y : ℝ => (a : ℂ) + y * Complex.I) (by fun_prop)

/-- **The archimedean integrability hypothesis of `explicitFormula_Gfull` follows from rapid decay
of `ĝ` on the line `Re s = 1 − σ`** (true for `g ∈ C_c^∞`, by repeated integration by parts). -/
theorem integrable_arch_kernel (hk : 0 < k) {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ < 2) (g : ℝ → ℂ)
    (hghc : Continuous (ghat g))
    (hdecay : ∀ N : ℕ, ∃ B : ℝ, ∀ t : ℝ,
      ‖ghat g (((1 - σ : ℝ) : ℂ) + t * Complex.I)‖ * (1 + |t|) ^ N ≤ B) :
    Integrable (fun t : ℝ =>
      (logDeriv (rsPre k) ((σ : ℂ) - t * Complex.I)
          + logDeriv (rsPre k) (((1 - σ : ℝ) : ℂ) + t * Complex.I))
        * ghat g (((1 - σ : ℝ) : ℂ) + t * Complex.I)) := by
  obtain ⟨C, hC, N, hψ⟩ := exists_norm_logDeriv_rsPre_le k hk
  obtain ⟨B, hB⟩ := hdecay (N + 2)
  have hB0 : 0 ≤ B := (mul_nonneg (norm_nonneg _) (by positivity)).trans (hB 0)
  -- continuity of the integrand
  have hψR : Continuous (fun y : ℝ => logDeriv (rsPre k) ((σ : ℂ) - y * Complex.I)) := by
    have h := continuous_logDeriv_rsPre_line k hk (a := σ)
      (fun y => rsPre_ne_zero k hk (by simp; linarith))
    have : (fun y : ℝ => logDeriv (rsPre k) ((σ : ℂ) - y * Complex.I))
        = (fun y : ℝ => logDeriv (rsPre k) ((σ : ℂ) + y * Complex.I)) ∘ (fun y : ℝ => -y) := by
      funext y; simp only [Function.comp]; congr 1; push_cast; ring
    rw [this]; exact h.comp continuous_neg
  have hψL : Continuous (fun y : ℝ => logDeriv (rsPre k) (((1 - σ : ℝ) : ℂ) + y * Complex.I)) :=
    continuous_logDeriv_rsPre_line k hk (a := 1 - σ) (rsPre_ne_zero_left k hk hσ1 hσ2)
  have hĝL : Continuous (fun y : ℝ => ghat g (((1 - σ : ℝ) : ℂ) + y * Complex.I)) :=
    hghc.comp (by fun_prop)
  have hcont : Continuous (fun t : ℝ =>
      (logDeriv (rsPre k) ((σ : ℂ) - t * Complex.I)
          + logDeriv (rsPre k) (((1 - σ : ℝ) : ℂ) + t * Complex.I))
        * ghat g (((1 - σ : ℝ) : ℂ) + t * Complex.I)) := (hψR.add hψL).mul hĝL
  -- the dominating function on `|t| ≥ 1`
  have hdom : Integrable (fun t : ℝ => 2 * C * B * (1 + ‖t‖) ^ (-(2 : ℝ))) :=
    (integrable_one_add_norm (by simp : (Module.finrank ℝ ℝ : ℝ) < 2)).const_mul _
  have hbound : ∀ t : ℝ, 1 ≤ |t| →
      ‖(logDeriv (rsPre k) ((σ : ℂ) - t * Complex.I)
          + logDeriv (rsPre k) (((1 - σ : ℝ) : ℂ) + t * Complex.I))
        * ghat g (((1 - σ : ℝ) : ℂ) + t * Complex.I)‖ ≤ 2 * C * B * (1 + ‖t‖) ^ (-(2 : ℝ)) := by
    intro t ht
    have h1t : 0 < 1 + |t| := by linarith [abs_nonneg t]
    have hψ1 := hψ ((σ : ℂ) - t * Complex.I) (by simp; linarith) (by simp; linarith) (by simp; exact ht)
    have hψ2 := hψ (((1 - σ : ℝ) : ℂ) + t * Complex.I) (by simp; linarith) (by simp; linarith)
      (by simp; exact ht)
    have hψ12 : ‖logDeriv (rsPre k) ((σ : ℂ) - t * Complex.I)
        + logDeriv (rsPre k) (((1 - σ : ℝ) : ℂ) + t * Complex.I)‖ ≤ 2 * C * (1 + |t|) ^ N := by
      refine (norm_add_le _ _).trans ?_
      have e1 : |((σ : ℂ) - t * Complex.I).im| = |t| := by simp
      have e2 : |(((1 - σ : ℝ) : ℂ) + t * Complex.I).im| = |t| := by simp
      rw [e1] at hψ1; rw [e2] at hψ2
      linarith
    have hĝ : ‖ghat g (((1 - σ : ℝ) : ℂ) + t * Complex.I)‖ ≤ B / (1 + |t|) ^ (N + 2) := by
      rw [le_div_iff₀ (by positivity)]; exact hB t
    rw [norm_mul, Real.norm_eq_abs, Real.rpow_neg h1t.le, Real.rpow_two]
    calc ‖_‖ * ‖_‖ ≤ (2 * C * (1 + |t|) ^ N) * (B / (1 + |t|) ^ (N + 2)) :=
          mul_le_mul hψ12 hĝ (norm_nonneg _) (by positivity)
      _ = 2 * C * B * ((1 + |t|) ^ 2)⁻¹ := by
          rw [pow_add]; field_simp
  -- split `ℝ = [−1, 1] ∪ [−1, 1]ᶜ`
  have hK : IntegrableOn (fun t : ℝ =>
      (logDeriv (rsPre k) ((σ : ℂ) - t * Complex.I)
          + logDeriv (rsPre k) (((1 - σ : ℝ) : ℂ) + t * Complex.I))
        * ghat g (((1 - σ : ℝ) : ℂ) + t * Complex.I)) (Icc (-1) 1) :=
    hcont.continuousOn.integrableOn_compact isCompact_Icc
  have hKc : IntegrableOn (fun t : ℝ =>
      (logDeriv (rsPre k) ((σ : ℂ) - t * Complex.I)
          + logDeriv (rsPre k) (((1 - σ : ℝ) : ℂ) + t * Complex.I))
        * ghat g (((1 - σ : ℝ) : ℂ) + t * Complex.I)) (Icc (-1) 1)ᶜ := by
    refine Integrable.mono' hdom.integrableOn hcont.aestronglyMeasurable.restrict ?_
    rw [ae_restrict_iff' measurableSet_Icc.compl]
    refine ae_of_all _ fun t ht => hbound t ?_
    rw [mem_compl_iff, mem_Icc, not_and_or] at ht
    rw [le_abs]
    rcases ht with h | h
    · right; linarith
    · left; linarith
  have := hK.union hKc
  rwa [union_compl_self, integrableOn_univ] at this

end RankinSelbergDelta.RankinSelberg
