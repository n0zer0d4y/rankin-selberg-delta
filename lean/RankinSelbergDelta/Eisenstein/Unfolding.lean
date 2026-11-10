import RankinSelbergDelta.Eisenstein.EisensteinCosets

/-!
# The Rankin–Selberg unfolding

With `phi k f z = ‖f z‖² (Im z)^k`, the `PSL₂(ℤ)`-invariant Petersson integrand, and the coset
expansion of `E`:
`∫_𝒟 phi · E(z, σ) dμ = ∫_{strip} phi · (Im w)^σ dμ` for real `σ > 1`
(`unfolding_integral_eisensteinE`), together with the unconditional `ℝ≥0∞` form
(`unfolding_lintegral`) and the Bochner form (`unfolding_integral`).
-/

namespace RankinSelbergDelta.Eisenstein

open Complex UpperHalfPlane ModularGroup MeasureTheory Set CongruenceSubgroup
open scoped MatrixGroups Modular Pointwise ENNReal

noncomputable section

variable {F : Type*} [FunLike F ℍ ℂ] (k : ℤ)
  [cf : CuspFormClass F (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ(1)) k]

/-! ### The Petersson density `Φ(z) = |f(z)|² (Im z)^k` and its invariance -/

/-- `Φ(z) = |f(z)|² (Im z)^k`. -/
def phi (f : F) (z : ℍ) : ℝ := Complex.normSq (f z) * z.im ^ k

lemma phi_nonneg (f : F) (z : ℍ) : 0 ≤ phi k f z :=
  mul_nonneg (Complex.normSq_nonneg _) (zpow_nonneg z.im_pos.le _)

include cf in
lemma continuous_phi (f : F) : Continuous (phi k f) :=
  (Complex.continuous_normSq.comp (ModularFormClass.continuous f)).mul
    (UpperHalfPlane.continuous_im.zpow₀ k fun z => Or.inl z.im_ne_zero)

include cf in
/-- `Φ` is `SL(2, ℤ)`-invariant: the slash equation and `Im (g • z) = Im z / |cz + d|²`. -/
lemma phi_smul (f : F) (g : SL(2, ℤ)) (z : ℍ) : phi k f (g • z) = phi k f z := by
  have hslash := SlashInvariantForm.slash_action_eqn_SL'' f (mem_Gamma_one g) z
  have hden : Complex.normSq (denom g z) ≠ 0 := (Complex.normSq_pos.mpr (denom_ne_zero g z)).ne'
  rw [phi, phi, hslash, map_mul, map_zpow₀, ModularGroup.im_smul_eq_div_normSq, div_zpow]
  field_simp

include cf in
lemma phi_psl_smul (f : F) (c : PSL2Z) (z : ℍ) : phi k f (c • z) = phi k f z := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
  rw [mk_smul]
  exact phi_smul k f g z

include cf in
lemma phi_vadd (f : F) (n : ℤ) (z : ℍ) : phi k f (n +ᵥ z) = phi k f z := by
  rw [int_vadd_eq_T_zpow_smul]
  exact phi_smul k f _ z

/-! ### The real Eisenstein summand `Im (γ • z)^σ` -/

/-- `(Im (γ • z))^σ` on a right coset, for real `σ`. -/
def eisTermR (z : ℍ) (σ : ℝ) : CosetPSL → ℝ :=
  Quotient.lift (fun c : PSL2Z => (c • z).im ^ σ)
    (fun a b hab => by
      have hab' : b * a⁻¹ ∈ cuspStab := QuotientGroup.rightRel_apply.mp hab
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hab'
      have hb : b = (QuotientGroup.mk ModularGroup.T : PSL2Z) ^ n * a := by
        rw [hn, inv_mul_cancel_right]
      beta_reduce
      rw [hb, mul_smul, ← QuotientGroup.mk_zpow, mk_smul, modular_T_zpow_smul, vadd_im])

lemma eisTermR_mk (z : ℍ) (σ : ℝ) (c : PSL2Z) :
    eisTermR z σ (Quotient.mk (QuotientGroup.rightRel cuspStab) c) = (c • z).im ^ σ := rfl

lemma eisTermR_nonneg (z : ℍ) (σ : ℝ) (d : CosetPSL) : 0 ≤ eisTermR z σ d := by
  induction d using Quotient.inductionOn with
  | h c => exact Real.rpow_nonneg (c • z).im_pos.le _

lemma eisTerm_eq_ofReal (z : ℍ) (σ : ℝ) (d : CosetPSL) :
    eisTerm z (σ : ℂ) d = ((eisTermR z σ d : ℝ) : ℂ) := by
  induction d using Quotient.inductionOn with
  | h c => rw [eisTerm_mk, eisTermR_mk, Complex.ofReal_cpow (c • z).im_pos.le]

/-! ### `[T]` has infinite order, and the fibres of `PSL2Z → CosetPSL` are copies of `ℤ` -/

lemma mkT_zpow_eq_one_iff (n : ℤ) :
    ((QuotientGroup.mk ModularGroup.T : PSL2Z) ^ n = 1) ↔ n = 0 := by
  constructor
  · intro h
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq_one_iff] at h
    rcases eq_one_or_neg_one_of_mem_slKer h with h1 | h1
    · have := congrArg (fun g : SL(2, ℤ) => g 0 1) h1
      simpa [ModularGroup.coe_T_zpow] using this
    · have := congrArg (fun g : SL(2, ℤ) => g 0 0) h1
      simp [ModularGroup.coe_T_zpow] at this
  · rintro rfl
    simp

lemma mkT_zpow_injective :
    Function.Injective fun n : ℤ => (QuotientGroup.mk ModularGroup.T : PSL2Z) ^ n := by
  intro n m h
  have h' : (QuotientGroup.mk ModularGroup.T : PSL2Z) ^ (n - m) = 1 := by
    simp only at h
    rw [zpow_sub, h, mul_inv_cancel]
  exact sub_eq_zero.mp ((mkT_zpow_eq_one_iff _).mp h')

lemma mkT_zpow_smul (n : ℤ) (w : ℍ) :
    ((QuotientGroup.mk ModularGroup.T : PSL2Z) ^ n) • w = n +ᵥ w := by
  rw [← QuotientGroup.mk_zpow, mk_smul, int_vadd_eq_T_zpow_smul]

lemma smul_set_eq_vadd (n : ℤ) (A : Set ℍ) :
    ((QuotientGroup.mk ModularGroup.T : PSL2Z) ^ n) • A = n +ᵥ A :=
  Set.image_congr fun a _ => mkT_zpow_smul n a

instance : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
instance : Countable SL(2, ℤ) :=
  inferInstanceAs (Countable {A : Matrix (Fin 2) (Fin 2) ℤ // A.det = 1})
instance : Countable PSL2Z := (QuotientGroup.mk_surjective (s := slKer)).countable
instance : Countable CosetPSL := inferInstance

/-- The projection to right cosets. -/
abbrev projPSL : PSL2Z → CosetPSL := fun c => Quotient.mk (QuotientGroup.rightRel cuspStab) c

/-- Each fibre of `projPSL` is a copy of `ℤ`: `n ↦ [T]^n * d.out`. -/
def fiberEquiv (d : CosetPSL) : ℤ ≃ (projPSL ⁻¹' {d}) :=
  Equiv.ofBijective
    (fun n => ⟨(QuotientGroup.mk ModularGroup.T : PSL2Z) ^ n * d.out, by
      show projPSL _ = d
      conv_rhs => rw [← Quotient.out_eq d]
      apply Quotient.sound
      refine QuotientGroup.rightRel_apply.mpr ?_
      rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul, ← zpow_neg]
      exact Subgroup.mem_zpowers_iff.mpr ⟨-n, rfl⟩⟩)
    ⟨fun n m h => by
        have h' := congrArg Subtype.val h
        simp only at h'
        exact mkT_zpow_injective (mul_right_cancel h'),
     fun ⟨c, hc⟩ => by
        have hc0 : projPSL c = d := hc
        have hc' : projPSL c = projPSL d.out := by
          rw [hc0]
          exact (Quotient.out_eq d).symm
        have h3 : d.out * c⁻¹ ∈ cuspStab := QuotientGroup.rightRel_apply.mp (Quotient.exact hc')
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h3
        have hd : d.out = (QuotientGroup.mk ModularGroup.T : PSL2Z) ^ n * c := by
          rw [hn, inv_mul_cancel_right]
        refine ⟨-n, Subtype.ext ?_⟩
        simp only
        rw [hd, zpow_neg, ← mul_assoc, inv_mul_cancel, one_mul]⟩

/-! ### The unfolding, in `ℝ≥0∞` (no summability or integrability hypotheses) -/

lemma continuous_im_smul (c : PSL2Z) : Continuous fun z : ℍ => (c • z).im := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
  have h : Continuous fun z : ℍ => (g : GL (Fin 2) ℝ) • z := continuous_const_smul _
  exact UpperHalfPlane.continuous_im.comp h

/-- The integrand on the strip side: `Φ(w) · (Im w)^σ`, as an extended nonnegative real. -/
def dens (f : F) (σ : ℝ) (w : ℍ) : ℝ≥0∞ := ENNReal.ofReal (phi k f w) * ENNReal.ofReal (w.im ^ σ)

include cf in
lemma measurable_dens (f : F) (σ : ℝ) : Measurable (dens k f σ) :=
  (ENNReal.measurable_ofReal.comp (continuous_phi k f).measurable).mul
    (ENNReal.measurable_ofReal.comp
      (UpperHalfPlane.continuous_im.rpow_const fun z => Or.inl z.im_ne_zero).measurable)

include cf in
lemma measurable_phi_mul_eisTermR (f : F) (σ : ℝ) (d : CosetPSL) :
    Measurable fun z : ℍ => ENNReal.ofReal (phi k f z) * ENNReal.ofReal (eisTermR z σ d) := by
  induction d using Quotient.inductionOn with
  | h c =>
    simp only [eisTermR_mk]
    exact (ENNReal.measurable_ofReal.comp (continuous_phi k f).measurable).mul
      (ENNReal.measurable_ofReal.comp
        ((continuous_im_smul c).rpow_const
          fun z => Or.inl (c • z).im_ne_zero).measurable)

include cf in
/-- **The Rankin–Selberg unfolding** (Lebesgue form):
`∫_𝒟 Φ(z) · Σ_{Γ∞\PSL} Im(γ z)^σ dμ = ∫_strip Φ(w) (Im w)^σ dμ`, in `ℝ≥0∞`, for every real `σ`. -/
theorem unfolding_lintegral (f : F) (σ : ℝ) :
    ∫⁻ z in (𝒟 : Set ℍ),
        ENNReal.ofReal (phi k f z) * ∑' d : CosetPSL, ENNReal.ofReal (eisTermR z σ d)
      = ∫⁻ w in strip, dens k f σ w := by
  -- the `𝒟` side: swap, then move each term to `γ_d • 𝒟`
  have hL : ∀ d : CosetPSL,
      (∫⁻ z in (𝒟 : Set ℍ), ENNReal.ofReal (phi k f z) * ENNReal.ofReal (eisTermR z σ d))
        = ∫⁻ w in d.out • (𝒟 : Set ℍ), dens k f σ w := by
    intro d
    conv_lhs => rw [← Quotient.out_eq d]
    simp only [eisTermR_mk]
    rw [← Set.image_smul, ← (measurePreserving_smul d.out volume).setLIntegral_comp_emb
      (measurableEmbedding_const_smul _) (dens k f σ) 𝒟]
    refine lintegral_congr fun z => ?_
    rw [dens, phi_psl_smul k f]
  simp_rw [← ENNReal.tsum_mul_left]
  rw [lintegral_tsum fun d => (measurable_phi_mul_eisTermR k f σ d).aemeasurable]
  simp_rw [hL]
  -- the strip side: tile by `PSL2Z`, group the tiles by cosets, collapse each coset by `ℤ`
  rw [isFundamentalDomain_fd.setLIntegral_eq_tsum (dens k f σ) strip,
    ← ENNReal.tsum_fiberwise _ projPSL]
  refine tsum_congr fun d => ?_
  rw [← (fiberEquiv d).tsum_eq]
  simp only [fiberEquiv, Equiv.ofBijective_apply]
  have hset : ∀ n : ℤ,
      (strip ∩ ((QuotientGroup.mk ModularGroup.T : PSL2Z) ^ n * d.out) • (𝒟 : Set ℍ))
        = (n +ᵥ (d.out • (𝒟 : Set ℍ))) ∩ strip := by
    intro n
    rw [mul_smul, smul_set_eq_vadd, Set.inter_comm]
  simp_rw [hset]
  rw [isAddFundamentalDomain_strip.setLIntegral_eq_tsum' (dens k f σ) (d.out • (𝒟 : Set ℍ))]
  refine tsum_congr fun n => ?_
  refine lintegral_congr fun w => ?_
  rw [dens, dens, phi_vadd k f, int_vadd_def, vadd_im]

/-! ### Summability of the real Eisenstein summand and the Bochner forms, `σ > 1` -/

lemma summable_eisTermR (z : ℍ) {σ : ℝ} (hσ : 1 < σ) : Summable (eisTermR z σ) := by
  have hs : 1 < (σ : ℂ).re := by simpa using hσ
  have hfib := (summable_eisTermSL z hs).hasSum.tsum_fiberwise projCoset
  have hd : ∀ d : CosetPSL,
      (∑' c : projCoset ⁻¹' {d}, eisTermSL z (σ : ℂ) c) = 2 * eisTerm z (σ : ℂ) d := by
    intro d
    induction d using Quotient.inductionOn with
    | h c =>
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
      rw [← projCoset_mk, tsum_fiber_projCoset, eisTerm_projCoset]
  simp_rw [hd] at hfib
  have h2 : Summable fun d => eisTerm z (σ : ℂ) d := by
    have := hfib.summable.mul_left (1 / 2)
    refine this.congr fun d => ?_
    ring
  rw [← Complex.summable_ofReal]
  refine h2.congr fun d => ?_
  exact eisTerm_eq_ofReal z σ d

lemma eisensteinE_eq_ofReal_tsum (z : ℍ) {σ : ℝ} (hσ : 1 < σ) :
    eisensteinE z (σ : ℂ) = ((∑' d : CosetPSL, eisTermR z σ d : ℝ) : ℂ) := by
  rw [eisensteinE_eq_tsum_coset z (by simpa using hσ), Complex.ofReal_tsum]
  exact tsum_congr fun d => eisTerm_eq_ofReal z σ d

include cf in
/-- **The Rankin–Selberg unfolding** (real Bochner form, `σ > 1`). -/
theorem unfolding_integral (f : F) {σ : ℝ} (hσ : 1 < σ) :
    ∫ z in (𝒟 : Set ℍ), phi k f z * ∑' d : CosetPSL, eisTermR z σ d
      = ∫ w in strip, phi k f w * w.im ^ σ := by
  have hpos1 : ∀ z : ℍ, 0 ≤ phi k f z * ∑' d : CosetPSL, eisTermR z σ d :=
    fun z => mul_nonneg (phi_nonneg k f z) (tsum_nonneg (eisTermR_nonneg z σ))
  have hpos2 : ∀ w : ℍ, 0 ≤ phi k f w * w.im ^ σ :=
    fun w => mul_nonneg (phi_nonneg k f w) (Real.rpow_nonneg w.im_pos.le σ)
  have hfun : (fun z : ℍ => phi k f z * ∑' d : CosetPSL, eisTermR z σ d)
      = fun z => phi k f z * (∑' d : CosetPSL, ENNReal.ofReal (eisTermR z σ d)).toReal := by
    funext z
    rw [← ENNReal.ofReal_tsum_of_nonneg (eisTermR_nonneg z σ) (summable_eisTermR z hσ),
      ENNReal.toReal_ofReal (tsum_nonneg (eisTermR_nonneg z σ))]
  have hm1 : AEStronglyMeasurable (fun z : ℍ => phi k f z * ∑' d : CosetPSL, eisTermR z σ d)
      (volume.restrict (𝒟 : Set ℍ)) := by
    rw [hfun]
    refine ((continuous_phi k f).measurable.mul ?_).aestronglyMeasurable
    refine Measurable.ennreal_toReal (Measurable.ennreal_tsum fun d => ?_)
    induction d using Quotient.inductionOn with
    | h c =>
      simp only [eisTermR_mk]
      exact ENNReal.measurable_ofReal.comp
        ((continuous_im_smul c).rpow_const
          fun z => Or.inl (c • z).im_ne_zero).measurable
  have hm2 : AEStronglyMeasurable (fun w : ℍ => phi k f w * w.im ^ σ)
      (volume.restrict strip) :=
    ((continuous_phi k f).mul (UpperHalfPlane.continuous_im.rpow_const fun z => Or.inl z.im_ne_zero)).aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hpos1) hm1,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hpos2) hm2]
  congr 1
  have h1 : ∀ z : ℍ, ENNReal.ofReal (phi k f z * ∑' d : CosetPSL, eisTermR z σ d)
      = ENNReal.ofReal (phi k f z) * ∑' d : CosetPSL, ENNReal.ofReal (eisTermR z σ d) := by
    intro z
    rw [ENNReal.ofReal_mul (phi_nonneg k f z),
      ENNReal.ofReal_tsum_of_nonneg (eisTermR_nonneg z σ) (summable_eisTermR z hσ)]
  simp_rw [h1]
  rw [unfolding_lintegral k f σ]
  refine lintegral_congr fun w => ?_
  rw [dens, ENNReal.ofReal_mul (phi_nonneg k f w)]

include cf in
/-- **The Rankin–Selberg unfolding** against `eisensteinE`, for real `σ > 1`:
`∫_𝒟 Φ(z) E(z, σ) dμ = ∫_strip Φ(w) (Im w)^σ dμ`. -/
theorem unfolding_integral_eisensteinE (f : F) {σ : ℝ} (hσ : 1 < σ) :
    ∫ z in (𝒟 : Set ℍ), (phi k f z : ℂ) * eisensteinE z (σ : ℂ)
      = ∫ w in strip, (phi k f w : ℂ) * ((w.im : ℝ) : ℂ) ^ (σ : ℂ) := by
  have h1 : (fun z : ℍ => (phi k f z : ℂ) * eisensteinE z (σ : ℂ))
      = fun z => ((phi k f z * ∑' d : CosetPSL, eisTermR z σ d : ℝ) : ℂ) := by
    funext z
    rw [eisensteinE_eq_ofReal_tsum z hσ, Complex.ofReal_mul]
  have h2 : (fun w : ℍ => (phi k f w : ℂ) * ((w.im : ℝ) : ℂ) ^ (σ : ℂ))
      = fun w => ((phi k f w * w.im ^ σ : ℝ) : ℂ) := by
    funext w
    rw [Complex.ofReal_mul, Complex.ofReal_cpow w.im_pos.le]
  rw [h1, h2]
  calc ∫ z in (𝒟 : Set ℍ), ((phi k f z * ∑' d : CosetPSL, eisTermR z σ d : ℝ) : ℂ)
      = ((∫ z in (𝒟 : Set ℍ), phi k f z * ∑' d : CosetPSL, eisTermR z σ d : ℝ) : ℂ) :=
        integral_ofReal
    _ = ((∫ w in strip, phi k f w * w.im ^ σ : ℝ) : ℂ) := by rw [unfolding_integral k f hσ]
    _ = ∫ w in strip, ((phi k f w * w.im ^ σ : ℝ) : ℂ) := integral_ofReal.symm

end

end RankinSelbergDelta.Eisenstein
