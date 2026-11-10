import RankinSelbergDelta.Eisenstein.Unfolding
import RankinSelbergDelta.RankinSelberg.MellinPole
import RankinSelbergDelta.RankinSelberg.MeanSquare

/-!
# The simple pole of the Rankin–Selberg Dirichlet series

For a level-one cusp form `f ≠ 0` of weight `k > 0`, with `rsDcont` the continuation
`(4π)^σ Γ(σ)^{−1} ∫_𝒟 Φ · E(·, σ − k + 1)` of `D(σ) = Σ |a(n)|² n^{−σ}` (`rsD_simplePole`):
`rsDcont σ = D(σ)` for real `σ > k + 1`; `(σ − k) rsDcont σ → (4π)^k Γ(k)^{−1} (3/π) ⟨f, f⟩` as
`σ → k⁺`; and this residue is positive. The proof bounds the theta function uniformly on `𝒟` and
passes the pole of the Eisenstein series through the integral by dominated convergence.
-/

namespace RankinSelbergDelta.RankinSelberg

open Complex UpperHalfPlane MeasureTheory Set RankinSelbergDelta.Eisenstein
open scoped ENNReal Modular NNReal Pointwise

noncomputable section

/-- `ofComplex` is measurable: the inverse of the open embedding on `{0 < im}`, constant off it. -/
lemma measurable_ofComplex : Measurable (ofComplex : ℂ → ℍ) := by
  have hset : MeasurableSet {w : ℂ | 0 < w.im} :=
    measurableSet_lt measurable_const Complex.measurable_im
  refine measurable_of_restrict_of_restrict_compl hset ?_ ?_
  · have h : UpperHalfPlane.coe ∘ ({w : ℂ | 0 < w.im}.restrict ofComplex) = Subtype.val := by
      funext w
      simp [Set.restrict_apply, ofComplex_apply_of_im_pos w.2]
    exact measurableEmbedding_coe.measurable_comp_iff.mp (h ▸ measurable_subtype_coe)
  · have h : ({w : ℂ | 0 < w.im}ᶜ.restrict ofComplex) = fun _ => ofComplex 0 := by
      funext w
      have hw : (w : ℂ).im ≤ 0 := not_lt.mp w.2
      simp only [Set.restrict_apply]
      rw [ofComplex_apply_of_im_nonpos hw, ofComplex_apply_of_im_nonpos (by simp)]
    rw [h]
    exact measurable_const

/-- The image of the strip in `ℂ`. -/
lemma coe_image_strip :
    (UpperHalfPlane.coe '' strip) = {w : ℂ | w.re ∈ Ico (0 : ℝ) 1 ∧ 0 < w.im} := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨hz, z.im_pos⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨w, h2⟩, h1, rfl⟩

lemma measurable_density : Measurable fun z : ℍ => (((1 / ‖z.im‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) :=
  (ENNReal.continuous_coe.comp ((continuous_const.div₀
    (continuous_nnnorm.comp UpperHalfPlane.continuous_im)
    fun z => nnnorm_ne_zero_iff.mpr z.im_ne_zero).pow 2)).measurable

lemma measurable_density_complex : Measurable fun w : ℂ => (((1 / ‖w.im‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) := by
  have : (fun w : ℂ => (((1 / ‖w.im‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞))
      = fun w => (((‖w.im‖₊⁻¹) ^ 2 : ℝ≥0) : ℝ≥0∞) := by
    funext w; simp [one_div]
  rw [this]
  exact ((Complex.measurable_im.nnnorm.inv).pow_const 2).coe_nnreal_ennreal

/-- **Fubini on the strip**: `∫_strip g dμ = ∫_0^∞ ∫_0^1 g(x + iy) y⁻² dx dy`, in `ℝ≥0∞`. -/
theorem lintegral_strip_eq (g : ℍ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ z in strip, g z
      = ∫⁻ y in Ioi (0 : ℝ), ∫⁻ x in Ico (0 : ℝ) 1,
          (((1 / ‖y‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) * g (ofComplex ⟨x, y⟩) := by
  set H : ℂ → ℝ≥0∞ := fun w => (((1 / ‖w.im‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) * g (ofComplex w) with hH
  have hHm : Measurable H := measurable_density_complex.mul (hg.comp measurable_ofComplex)
  rw [show (volume : Measure ℍ) = (volume.comap UpperHalfPlane.coe).withDensity
      (fun z => (((1 / ‖z.im‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞)) from volume_def,
    restrict_withDensity measurableSet_strip,
    lintegral_withDensity_eq_lintegral_mul _ measurable_density hg]
  have hmp : MeasurePreserving UpperHalfPlane.coe (volume.comap UpperHalfPlane.coe)
      (volume.restrict (Set.range UpperHalfPlane.coe)) :=
    ⟨measurable_coe, by rw [measurableEmbedding_coe.map_comap]⟩
  have h1 : ∫⁻ z in strip, ((fun z : ℍ => (((1 / ‖z.im‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞)) * g) z
        ∂(volume.comap UpperHalfPlane.coe)
      = ∫⁻ z in strip, H (z : ℂ) ∂(volume.comap UpperHalfPlane.coe) := by
    refine lintegral_congr fun z => ?_
    simp [hH, ofComplex_apply]
  rw [h1, hmp.setLIntegral_comp_emb measurableEmbedding_coe H strip,
    Measure.restrict_restrict (measurableEmbedding_coe.measurableSet_image.mpr measurableSet_strip),
    inter_eq_self_of_subset_left (image_subset_range _ _), coe_image_strip]
  have hS : {w : ℂ | w.re ∈ Ico (0 : ℝ) 1 ∧ 0 < w.im}
      = Complex.measurableEquivRealProd ⁻¹' (Ico (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ)) := by
    ext w
    simp [Complex.measurableEquivRealProd]
  have hHe : ∀ w : ℂ,
      H w = (H ∘ Complex.measurableEquivRealProd.symm) (Complex.measurableEquivRealProd w) := by
    intro w
    simp
  rw [hS, lintegral_congr hHe,
    Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_emb
      Complex.measurableEquivRealProd.measurableEmbedding,
    Set.image_preimage_eq _ Complex.measurableEquivRealProd.surjective,
    Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod _ (hHm.comp Complex.measurableEquivRealProd.symm.measurable).aemeasurable,
    lintegral_lintegral_swap (f := fun x y => (H ∘ Complex.measurableEquivRealProd.symm) (x, y))
      (by exact (hHm.comp Complex.measurableEquivRealProd.symm.measurable).aemeasurable)]
  refine lintegral_congr fun y => lintegral_congr fun x => ?_
  clear hHe hS h1 hmp hHm
  have hpt : (Complex.measurableEquivRealProd.symm (x, y) : ℂ) = ⟨x, y⟩ := by
    first
    | rfl
    | simp [Complex.measurableEquivRealProd, Complex.equivRealProdCLM, Complex.mk_eq_add_mul_I]
  simp only [hH, Function.comp_apply, hpt]

/-! ### the unfolded strip integral is the Mellin transform of the mean square -/

variable {F : Type*} [FunLike F ℍ ℂ] (k : ℤ)
  [cf : CuspFormClass F (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma 1)) k]

/-- The `x`-average `G(y) = ∫₀¹ |f(x+iy)|² dx`, as a Lebesgue integral (so that measurability in
`y` is automatic); for `y ≤ 0` it is some irrelevant value. -/
def meanSq (f : F) (y : ℝ) : ℝ :=
  (∫⁻ x in Ico (0 : ℝ) 1, ENNReal.ofReal (Complex.normSq (f (ofComplex ⟨x, y⟩)))).toReal

include cf in
lemma measurable_normSq_ofComplex (f : F) :
    Measurable fun p : ℝ × ℝ => ENNReal.ofReal (Complex.normSq (f (ofComplex ⟨p.1, p.2⟩))) := by
  refine ENNReal.measurable_ofReal.comp (Complex.continuous_normSq.measurable.comp
    ((ModularFormClass.continuous f).measurable.comp (measurable_ofComplex.comp ?_)))
  exact Complex.measurableEquivRealProd.symm.measurable

include cf in
lemma meanSq_nonneg (f : F) (y : ℝ) : 0 ≤ meanSq f y := ENNReal.toReal_nonneg

include cf in
/-- For `y > 0`, `meanSq` is the interval integral of `|f(x+iy)|²`. -/
lemma meanSq_eq (f : F) {y : ℝ} (hy : 0 < y) :
    meanSq f y = ∫ x : ℝ in (0 : ℝ)..1, ‖f ((⟨⟨x, y⟩, hy⟩ : ℍ))‖ ^ 2 := by
  have hpt : Continuous fun x : ℝ => ((⟨⟨x, y⟩, hy⟩ : ℍ)) := by
    rw [continuous_induced_rng]
    have : ((fun z : ℍ => (z : ℂ)) ∘ fun x : ℝ => ((⟨⟨x, y⟩, hy⟩ : ℍ)))
        = fun x : ℝ => (x : ℂ) + (y : ℂ) * Complex.I := by
      funext x
      exact Complex.mk_eq_add_mul_I x y
    rw [this]
    fun_prop
  have hcont : Continuous fun x : ℝ => ‖f ((⟨⟨x, y⟩, hy⟩ : ℍ))‖ ^ 2 :=
    ((ModularFormClass.continuous f).comp hpt).norm.pow 2
  have hint : IntegrableOn (fun x : ℝ => ‖f ((⟨⟨x, y⟩, hy⟩ : ℍ))‖ ^ 2) (Ico (0 : ℝ) 1) :=
    (hcont.integrableOn_Icc).mono_set Ico_subset_Icc_self
  have hfun : ∀ x : ℝ, Complex.normSq (f (ofComplex ⟨x, y⟩)) = ‖f ((⟨⟨x, y⟩, hy⟩ : ℍ))‖ ^ 2 := by
    intro x
    rw [ofComplex_apply_of_im_pos (by simpa using hy : (0 : ℝ) < (⟨x, y⟩ : ℂ).im),
      Complex.normSq_eq_norm_sq]
  rw [meanSq]
  simp_rw [hfun]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => by positivity),
    ENNReal.toReal_ofReal (integral_nonneg fun x => by positivity),
    MeasureTheory.integral_Ico_eq_integral_Ioo, ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one]

include cf in
lemma summable_sq_exp (f : F) {y : ℝ} (hy : 0 < y) :
    Summable fun n : ℕ => ‖(ModularFormClass.qExpansion 1 f).coeff n‖ ^ 2 * Real.exp (-(4 * Real.pi * n) * y) := by
  have h := summable_norm_shift_term f hy
  have hnn : ∀ n : ℕ, 0 ≤ ‖(ModularFormClass.qExpansion 1 f).coeff n‖ * Real.exp (-(2 * Real.pi * n) * y) :=
    fun n => mul_nonneg (norm_nonneg _) (Real.exp_nonneg _)
  set M := ∑' n : ℕ, ‖(ModularFormClass.qExpansion 1 f).coeff n‖ * Real.exp (-(2 * Real.pi * n) * y) with hM
  have hle : ∀ n : ℕ, ‖(ModularFormClass.qExpansion 1 f).coeff n‖ * Real.exp (-(2 * Real.pi * n) * y) ≤ M :=
    fun n => h.le_tsum n fun m _ => hnn m
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (h.mul_left M)
  have hsq : ‖(ModularFormClass.qExpansion 1 f).coeff n‖ ^ 2 * Real.exp (-(4 * Real.pi * n) * y)
      = (‖(ModularFormClass.qExpansion 1 f).coeff n‖ * Real.exp (-(2 * Real.pi * n) * y)) ^ 2 := by
    rw [mul_pow, sq (Real.exp _), ← Real.exp_add]
    congr 2
    ring
  rw [hsq, sq]
  exact mul_le_mul_of_nonneg_right (hle n) (hnn n)

include cf in
/-- The mean square in the `HasSum` form that `rsMellin_eq` consumes. -/
lemma hasSum_meanSq (f : F) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => (‖(ModularFormClass.qExpansion 1 f).coeff n‖ ^ 2 : ℂ)
        * (Real.exp (-(4 * Real.pi * (n : ℝ)) * t) : ℂ)) ((meanSq f t : ℝ) : ℂ) := by
  rw [meanSq_eq k f ht, integral_sq_eq_tsum f ht]
  have h := Complex.hasSum_ofReal.mpr (summable_sq_exp k f ht).hasSum
  convert h using 1
  funext n
  push_cast
  ring

/-! ### the strip integral is the Mellin transform of the mean square -/

include cf in
lemma measurable_meanSq (f : F) : Measurable fun y : ℝ => meanSq f y := by
  unfold meanSq
  exact ENNReal.measurable_toReal.comp
    (Measurable.lintegral_prod_left' (μ := volume.restrict (Ico (0 : ℝ) 1))
      (measurable_normSq_ofComplex k f))

/-- For `y > 0`: `y⁻² · y^k · y^σ = y^(σ + k - 2)`, in `ℝ≥0∞`. -/
lemma density_rpow_eq {y : ℝ} (hy : 0 < y) (σ : ℝ) :
    (((1 / ‖y‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (y ^ k * y ^ σ)
      = ENNReal.ofReal (y ^ (σ + k - 2)) := by
  have h1 : (((1 / ‖y‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (y ^ (-2 : ℝ)) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
    rw [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one, coe_nnnorm, Real.norm_of_nonneg hy.le,
      Real.rpow_neg hy.le, Real.rpow_two, one_div, inv_pow]
  rw [h1, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [← Real.rpow_intCast, ← Real.rpow_add hy, ← Real.rpow_add hy]
  congr 1
  push_cast
  ring

include cf in
/-- **The strip integral is the Mellin transform of the mean square**, for every real `σ`
(both sides may be infinite / zero in the Bochner convention): with `Φ = |f|² (Im)^k`,
`∫_strip Φ (Im)^σ dμ = mellin (y ↦ ∫₀¹ |f(x+iy)|² dx) (σ + k - 1)`. -/
theorem unfolding_strip_eq_mellin (f : F) (σ : ℝ) :
    ((∫ w in strip, phi k f w * w.im ^ σ : ℝ) : ℂ)
      = mellin (fun y : ℝ => (meanSq f y : ℂ)) ((σ + k - 1 : ℝ) : ℂ) := by
  have hnn : ∀ w : ℍ, 0 ≤ phi k f w * w.im ^ σ :=
    fun w => mul_nonneg (phi_nonneg k f w) (Real.rpow_nonneg w.im_pos.le σ)
  have hmeas : Measurable fun w : ℍ => phi k f w * w.im ^ σ :=
    (continuous_phi k f).measurable.mul
      (UpperHalfPlane.continuous_im.rpow_const fun z => Or.inl z.im_ne_zero).measurable
  -- the strip side
  have hstrip : (∫ w in strip, phi k f w * w.im ^ σ : ℝ)
      = (∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (y ^ (σ + k - 2) * meanSq f y)).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnn)
      hmeas.aestronglyMeasurable,
      lintegral_strip_eq (fun z => ENNReal.ofReal (phi k f z * z.im ^ σ))
        (ENNReal.measurable_ofReal.comp hmeas)]
    congr 1
    refine setLIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    have hy : 0 < y := hy
    have him : ∀ x : ℝ, (ofComplex ⟨x, y⟩).im = y := fun x => by
      simp [ofComplex_apply_of_im_pos (by simpa using hy : (0 : ℝ) < (⟨x, y⟩ : ℂ).im)]
    have hphi : ∀ x : ℝ, ENNReal.ofReal (phi k f (ofComplex ⟨x, y⟩) * (ofComplex ⟨x, y⟩).im ^ σ)
        = ENNReal.ofReal (Complex.normSq (f (ofComplex ⟨x, y⟩))) * ENNReal.ofReal (y ^ k * y ^ σ) := by
      intro x
      rw [phi, him, ← ENNReal.ofReal_mul (Complex.normSq_nonneg _)]
      congr 1
      ring
    simp_rw [hphi]
    have hfin : (∫⁻ x in Ico (0 : ℝ) 1, ENNReal.ofReal (Complex.normSq (f (ofComplex ⟨x, y⟩)))) ≠ ⊤ := by
      have hpt : Continuous fun x : ℝ => ((⟨⟨x, y⟩, hy⟩ : ℍ)) := by
        rw [continuous_induced_rng]
        have : ((fun z : ℍ => (z : ℂ)) ∘ fun x : ℝ => ((⟨⟨x, y⟩, hy⟩ : ℍ)))
            = fun x : ℝ => (x : ℂ) + (y : ℂ) * Complex.I := by
          funext x
          exact Complex.mk_eq_add_mul_I x y
        rw [this]
        fun_prop
      have hfun : ∀ x : ℝ, Complex.normSq (f (ofComplex ⟨x, y⟩)) = ‖f ((⟨⟨x, y⟩, hy⟩ : ℍ))‖ ^ 2 := by
        intro x
        rw [ofComplex_apply_of_im_pos (by simpa using hy : (0 : ℝ) < (⟨x, y⟩ : ℂ).im),
          Complex.normSq_eq_norm_sq]
      simp_rw [hfun]
      have hint : IntegrableOn (fun x : ℝ => ‖f ((⟨⟨x, y⟩, hy⟩ : ℍ))‖ ^ 2) (Ico (0 : ℝ) 1) :=
        (((ModularFormClass.continuous f).comp hpt).norm.pow 2).integrableOn_Icc.mono_set
          Ico_subset_Icc_self
      rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => by positivity)]
      exact ENNReal.ofReal_ne_top
    have hmx : Measurable fun x : ℝ => ENNReal.ofReal (Complex.normSq (f (ofComplex ⟨x, y⟩))) := by
      exact (measurable_normSq_ofComplex k f).comp (measurable_id.prodMk measurable_const)
    rw [lintegral_const_mul _ (hmx.mul_const _), lintegral_mul_const _ hmx,
      ENNReal.ofReal_mul (Real.rpow_nonneg hy.le _), meanSq, ENNReal.ofReal_toReal hfin,
      ← density_rpow_eq k hy σ]
    ring
  -- the Mellin side
  have hmel : mellin (fun y : ℝ => (meanSq f y : ℂ)) ((σ + k - 1 : ℝ) : ℂ)
      = ((∫ y in Ioi (0 : ℝ), y ^ (σ + k - 2) * meanSq f y : ℝ) : ℂ) := by
    rw [mellin]
    have hcongr : (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (((σ + k - 1 : ℝ) : ℂ) - 1) • ((meanSq f t : ℝ) : ℂ))
        = ∫ t in Ioi (0 : ℝ), ((t ^ (σ + k - 2) * meanSq f t : ℝ) : ℂ) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
      have hy : 0 < y := hy
      rw [show ((σ + k - 1 : ℝ) : ℂ) - 1 = ((σ + k - 2 : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cpow hy.le, smul_eq_mul, ← Complex.ofReal_mul]
    rw [hcongr]
    exact integral_ofReal
  have hnn' : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun y : ℝ => y ^ (σ + k - 2) * meanSq f y :=
    ae_restrict_of_forall_mem measurableSet_Ioi fun y hy =>
      mul_nonneg (Real.rpow_nonneg (le_of_lt hy) _) (meanSq_nonneg k f y)
  have hm' : AEStronglyMeasurable (fun y : ℝ => y ^ (σ + k - 2) * meanSq f y)
      (volume.restrict (Ioi (0 : ℝ))) :=
    ((measurable_id.pow_const _).mul (measurable_meanSq k f)).aestronglyMeasurable
  rw [hmel, hstrip, integral_eq_lintegral_of_nonneg_ae hnn' hm']

/-! ### the unfolded Eisenstein integral is the archimedean factor times `D` -/

include cf in
/-- **Identification with the Rankin–Selberg Dirichlet series**: for real `σ > 2`,
`∫_𝒟 Φ(z) E(z, σ) dμ = (4π)^{-(σ+k-1)} Γ(σ+k-1) D(σ+k-1)`. -/
theorem rs_integral_eq (f : F) (hk : 0 < k) {σ : ℝ} (hσ : 2 < σ) :
    ((∫ z in (𝒟 : Set ℍ), phi k f z * ∑' d : CosetPSL, eisTermR z σ d : ℝ) : ℂ)
      = ((4 * Real.pi : ℝ) : ℂ) ^ (-((σ + k - 1 : ℝ) : ℂ)) * Complex.Gamma ((σ + k - 1 : ℝ) : ℂ)
          * rsD f ((σ + k - 1 : ℝ) : ℂ) := by
  have hσ1 : 1 < σ := by linarith
  rw [unfolding_integral k f hσ1, unfolding_strip_eq_mellin k f σ]
  have hw : (k : ℝ) + 1 < (((σ + k - 1 : ℝ) : ℂ)).re := by
    rw [Complex.ofReal_re]
    linarith
  exact rsMellin_eq f hk hw (fun y => (meanSq f y : ℂ)) (fun t ht => hasSum_meanSq k f ht)

/-! ### positivity of the Petersson norm -/

/-- Nonempty open subsets of `ℍ` have positive volume. -/
instance : (volume : Measure ℍ).IsOpenPosMeasure := by
  refine ⟨fun U hU hne => ?_⟩
  rw [volume_eq_lintegral]
  have hUo : IsOpen (UpperHalfPlane.coe '' U) := isOpenEmbedding_coe.isOpenMap U hU
  have hUne : (UpperHalfPlane.coe '' U).Nonempty := hne.image _
  have hpos : 0 < (volume : Measure ℂ) (UpperHalfPlane.coe '' U) := hUo.measure_pos volume hUne
  rw [← pos_iff_ne_zero, lintegral_pos_iff_support measurable_density_complex,
    Measure.restrict_apply' (hUo.measurableSet)]
  refine lt_of_lt_of_le hpos (measure_mono fun w hw => ⟨?_, hw⟩)
  obtain ⟨z, -, rfl⟩ := hw
  simp [Function.mem_support, z.im_ne_zero]

include cf in
/-- **Positivity of the Petersson norm**: if `Φ` is integrable on `𝒟` and `f` does not vanish at
some interior point of `𝒟`, then `∫_𝒟 Φ > 0`. -/
theorem integral_phi_pos (f : F) (hint : IntegrableOn (phi k f) (𝒟 : Set ℍ))
    (hz : ∃ z ∈ (𝒟ᵒ : Set ℍ), f z ≠ 0) : 0 < ∫ z in (𝒟 : Set ℍ), phi k f z := by
  obtain ⟨z₀, hz₀, hfz₀⟩ := hz
  have hphi0 : 0 < phi k f z₀ :=
    mul_pos (Complex.normSq_pos.mpr hfz₀) (zpow_pos z₀.im_pos _)
  have hopen : IsOpen (𝒟ᵒ : Set ℍ) := by
    have h1 : IsOpen {z : ℍ | 1 < Complex.normSq (z : ℂ)} :=
      isOpen_lt continuous_const (Complex.continuous_normSq.comp continuous_coe)
    have h2 : IsOpen {z : ℍ | |z.re| < (1 : ℝ) / 2} :=
      isOpen_lt (continuous_abs.comp UpperHalfPlane.continuous_re) continuous_const
    exact h1.inter h2
  -- a neighbourhood of `z₀` inside `𝒟ᵒ` on which `Φ > Φ(z₀)/2`
  have hev : ∀ᶠ z in nhds z₀, phi k f z₀ / 2 < phi k f z ∧ z ∈ (𝒟ᵒ : Set ℍ) :=
    (continuousAt_const.eventually_lt (continuous_phi k f).continuousAt
      (by linarith : phi k f z₀ / 2 < phi k f z₀)).and (hopen.mem_nhds hz₀)
  obtain ⟨U, hUsub, hUo, hz₀U⟩ := mem_nhds_iff.mp hev
  have hUpos : 0 < volume U := hUo.measure_pos volume ⟨z₀, hz₀U⟩
  rw [setIntegral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall (phi_nonneg k f)) hint]
  refine lt_of_lt_of_le hUpos (measure_mono fun z hzU => ⟨?_, ?_⟩)
  · have := (hUsub hzU).1
    rw [Function.mem_support]
    exact ne_of_gt (lt_of_le_of_lt (by positivity) this)
  · exact ((hUsub hzU).2).1 |> fun h => ⟨le_of_lt h, le_of_lt (hUsub hzU).2.2⟩

/-! ### `Φ` is bounded, `𝒟` has finite volume, so `Φ` is integrable on `𝒟` -/

include cf in
/-- `Φ = ‖petersson k f f‖`, hence bounded on all of `ℍ` (Mathlib's `petersson_bounded_left`). -/
lemma phi_bounded (f : F) : ∃ C : ℝ, ∀ z : ℍ, phi k f z ≤ C := by
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left k
    (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma 1)) f f
  refine ⟨C, fun z => le_trans (le_of_eq ?_) (hC z)⟩
  rw [petersson, phi, norm_mul, norm_mul, Complex.norm_conj, ← sq, ← Complex.normSq_eq_norm_sq,
    Complex.norm_zpow, Complex.norm_real, Real.norm_of_nonneg z.im_pos.le]

/-- The hyperbolic density `(1/‖y‖₊)²` is `y^(-2)` in `ℝ≥0∞`, for `y > 0`. -/
lemma density_eq_rpow_neg_two {y : ℝ} (hy : 0 < y) :
    (((1 / ‖y‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (y ^ (-2 : ℝ)) := by
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1
  rw [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one, coe_nnnorm, Real.norm_of_nonneg hy.le,
    Real.rpow_neg hy.le, Real.rpow_two, one_div, inv_pow]

/-- The part of the strip above height `c > 0` has finite hyperbolic volume (it is `1 / c`). -/
lemma volume_strip_inter_lt_top {c : ℝ} (hc : 0 < c) :
    volume (strip ∩ {z : ℍ | c ≤ z.im}) < ⊤ := by
  have hmeas : MeasurableSet {z : ℍ | c ≤ z.im} :=
    measurableSet_le measurable_const UpperHalfPlane.continuous_im.measurable
  rw [Set.inter_comm, ← Measure.restrict_apply' measurableSet_strip,
    ← lintegral_indicator_one hmeas,
    lintegral_strip_eq (fun z => {z : ℍ | c ≤ z.im}.indicator 1 z) (measurable_one.indicator hmeas)]
  have hin : ∀ y ∈ Ioi (0 : ℝ),
      (∫⁻ x in Ico (0 : ℝ) 1, (((1 / ‖y‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞)
          * {z : ℍ | c ≤ z.im}.indicator 1 (ofComplex ⟨x, y⟩))
        = (Ici c).indicator (fun y : ℝ => ENNReal.ofReal (y ^ (-2 : ℝ))) y := by
    intro y hy
    have hy : 0 < y := hy
    have him : ∀ x : ℝ, (ofComplex ⟨x, y⟩).im = y := fun x => by
      simp [ofComplex_apply_of_im_pos (by simpa using hy : (0 : ℝ) < (⟨x, y⟩ : ℂ).im)]
    have hpt : ∀ x : ℝ, {z : ℍ | c ≤ z.im}.indicator (1 : ℍ → ℝ≥0∞) (ofComplex ⟨x, y⟩)
        = (Ici c).indicator (1 : ℝ → ℝ≥0∞) y := by
      intro x
      simp only [Set.indicator_apply, Set.mem_setOf_eq, Set.mem_Ici, him, Pi.one_apply]
    simp_rw [hpt]
    rw [setLIntegral_const, Real.volume_Ico, sub_zero, ENNReal.ofReal_one, mul_one,
      density_eq_rpow_neg_two hy]
    by_cases hcy : y ∈ Ici c
    · simp [Set.indicator_of_mem hcy]
    · simp [Set.indicator_of_notMem hcy]
  refine (setLIntegral_congr_fun measurableSet_Ioi hin).trans_lt ?_
  rw [lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
    Set.inter_eq_left.mpr (Set.Ici_subset_Ioi.mpr hc)]
  have hint : IntegrableOn (fun t : ℝ => t ^ (-2 : ℝ)) (Ici c) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (f := fun t : ℝ => t ^ (-2 : ℝ)) (b := c)
      (μ := volume) (by finiteness)).mpr
      (integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) hc)
  exact hint.lintegral_lt_top

/-- `𝒟` lies in the union of the strip above height `1/2` and its translate by `-1`. -/
lemma fd_subset_union : (𝒟 : Set ℍ) ⊆
    (strip ∩ {z : ℍ | (1 : ℝ) / 2 ≤ z.im})
      ∪ ((-1 : ℤ) +ᵥ (strip ∩ {z : ℍ | (1 : ℝ) / 2 ≤ z.im})) := by
  intro z hz
  have him : (1 : ℝ) / 2 ≤ z.im := by
    nlinarith [ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz, z.im_pos]
  have hre : |z.re| ≤ (1 : ℝ) / 2 := hz.2
  rw [abs_le] at hre
  by_cases h0 : 0 ≤ z.re
  · left
    simp only [strip, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Ico]
    exact ⟨⟨h0, by linarith [hre.2]⟩, him⟩
  · right
    push_neg at h0
    rw [Set.mem_vadd_set]
    refine ⟨(1 : ℤ) +ᵥ z, ?_, ?_⟩
    · simp only [strip, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Ico, int_vadd_def, vadd_re,
        vadd_im, Int.cast_one]
      exact ⟨⟨by linarith [hre.1], by linarith⟩, him⟩
    · rw [vadd_vadd, show (-1 : ℤ) + 1 = 0 by norm_num, zero_vadd]

/-- The fundamental domain has finite hyperbolic volume. -/
lemma volume_fd_lt_top : volume (𝒟 : Set ℍ) < ⊤ := by
  set A : Set ℍ := strip ∩ {z : ℍ | (1 : ℝ) / 2 ≤ z.im} with hAdef
  have hA : MeasurableSet A :=
    measurableSet_strip.inter
      (measurableSet_le measurable_const UpperHalfPlane.continuous_im.measurable)
  have hfin : volume A < ⊤ := volume_strip_inter_lt_top (c := (1 : ℝ) / 2) (by norm_num)
  have htr : volume ((-1 : ℤ) +ᵥ A) = volume A := by
    rw [← smul_set_eq_vadd, ← Set.preimage_smul_inv]
    exact SMulInvariantMeasure.measure_preimage_smul (μ := volume) _ hA
  calc volume (𝒟 : Set ℍ) ≤ volume (A ∪ ((-1 : ℤ) +ᵥ A)) := measure_mono fd_subset_union
    _ ≤ volume A + volume ((-1 : ℤ) +ᵥ A) := measure_union_le _ _
    _ < ⊤ := by rw [htr]; exact ENNReal.add_lt_top.mpr ⟨hfin, hfin⟩

include cf in
/-- **`Φ` is integrable on `𝒟`**: it is bounded on `ℍ` and `𝒟` has finite volume. -/
theorem integrableOn_phi_fd (f : F) : IntegrableOn (phi k f) (𝒟 : Set ℍ) := by
  obtain ⟨C, hC⟩ := phi_bounded k f
  refine Measure.integrableOn_of_bounded volume_fd_lt_top.ne
    (continuous_phi k f).aestronglyMeasurable (M := C) (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_of_nonneg (phi_nonneg k f z)]
  exact hC z

/-! ### a nonzero cusp form does not vanish identically on `𝒟ᵒ`, so `⟨f,f⟩ > 0` -/

/-- The open fundamental domain is open in `ℍ`. -/
lemma isOpen_fdo : IsOpen (𝒟ᵒ : Set ℍ) := by
  have h1 : IsOpen {z : ℍ | 1 < Complex.normSq (z : ℂ)} :=
    isOpen_lt continuous_const (Complex.continuous_normSq.comp continuous_coe)
  have h2 : IsOpen {z : ℍ | |z.re| < (1 : ℝ) / 2} :=
    isOpen_lt (continuous_abs.comp UpperHalfPlane.continuous_re) continuous_const
  exact h1.inter h2

include cf in
/-- **Identity theorem**: a cusp form vanishing on the open set `𝒟ᵒ` vanishes identically, so a
nonzero one has a point of `𝒟ᵒ` where it is nonzero. -/
theorem exists_fdo_ne_zero (f : F) (hf : (⇑f : ℍ → ℂ) ≠ 0) :
    ∃ z ∈ (𝒟ᵒ : Set ℍ), f z ≠ 0 := by
  by_contra h
  push_neg at h
  refine hf (UpperHalfPlane.eq_zero_of_frequently (ModularFormClass.holo f) (τ := twoI) ?_)
  have hev : ∀ᶠ z in nhds twoI, f z = 0 :=
    Filter.eventually_of_mem (isOpen_fdo.mem_nhds twoI_mem_fdo) h
  exact (hev.filter_mono nhdsWithin_le_nhds).frequently

include cf in
/-- **Positivity of the Petersson norm**: `⟨f, f⟩ = ∫_𝒟 |f|² (Im)^k > 0` for every nonzero cusp
form `f` of level 1 and weight `k`. -/
theorem integral_phi_pos_of_ne_zero (f : F) (hf : (⇑f : ℍ → ℂ) ≠ 0) :
    0 < ∫ z in (𝒟 : Set ℍ), phi k f z :=
  integral_phi_pos k f (integrableOn_phi_fd k f) (exists_fdo_ne_zero k f hf)

/-! ### the lattice theta tail, bounded through Mathlib's Jacobi theta -/

/-- The lattice theta function as a real series. -/
def thetaR (z : ℍ) (t : ℝ) : ℝ := ∑' p : ℤ × ℤ, Real.exp (-Real.pi * t * Qform z p.1 p.2)

lemma thetaQ_eq_ofReal (z : ℍ) (t : ℝ) : thetaQ z t = (thetaR z t : ℂ) := by
  rw [thetaQ, thetaR, Complex.ofReal_tsum]

lemma summable_thetaR (z : ℍ) {t : ℝ} (ht : 0 < t) :
    Summable fun p : ℤ × ℤ => Real.exp (-Real.pi * t * Qform z p.1 p.2) := by
  have h := summable_thetaQ z ht
  rwa [Complex.summable_ofReal] at h

lemma thetaR_sub_one_nonneg (z : ℍ) {t : ℝ} (ht : 0 < t) : 0 ≤ thetaR z t - 1 := by
  have h := (summable_thetaR z ht).le_tsum (0, 0) (fun _ _ => Real.exp_nonneg _)
  simp only [Qform_zero, mul_zero, Real.exp_zero] at h
  rw [thetaR]
  linarith

lemma summable_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    Summable fun m : ℤ => Real.exp (-b * (m : ℝ) ^ 2) := by
  refine (summable_exp_neg_sq (a := b / Real.pi) (by positivity)).congr fun m => ?_
  congr 1
  field_simp

lemma gauss_sum_eq_jacobiTheta {b : ℝ} (hb : 0 < b) :
    ((∑' m : ℤ, Real.exp (-b * (m : ℝ) ^ 2) : ℝ) : ℂ)
      = jacobiTheta (Complex.I * ((b / Real.pi : ℝ) : ℂ)) := by
  rw [Complex.ofReal_tsum, jacobiTheta]
  refine tsum_congr fun m => ?_
  rw [Complex.ofReal_exp]
  congr 1
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  linear_combination (-(b : ℂ) * (m : ℂ) ^ 2 * (Real.pi : ℂ) * (Real.pi : ℂ)⁻¹) * Complex.I_mul_I
    + ((b : ℂ) * (m : ℂ) ^ 2) * (mul_inv_cancel₀ hπ)

/-- `Σ_{m ∈ ℤ} e^{-b m²} ≤ 1 + 2/b` for `b > 0` (from Mathlib's bound on `jacobiTheta - 1`). -/
lemma gauss_sum_le {b : ℝ} (hb : 0 < b) :
    ∑' m : ℤ, Real.exp (-b * (m : ℝ) ^ 2) ≤ 1 + 2 / b := by
  have hτ : 0 < (Complex.I * ((b / Real.pi : ℝ) : ℂ)).im := by
    simp only [Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero, Complex.I_im,
      Complex.ofReal_re, one_mul, zero_add]
    positivity
  have h := norm_jacobiTheta_sub_one_le hτ
  rw [← gauss_sum_eq_jacobiTheta hb] at h
  have him : (Complex.I * ((b / Real.pi : ℝ) : ℂ)).im = b / Real.pi := by
    simp only [Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero, Complex.I_im,
      Complex.ofReal_re, one_mul, zero_add]
  rw [him, show -Real.pi * (b / Real.pi) = -b by field_simp] at h
  have hre : (∑' m : ℤ, Real.exp (-b * (m : ℝ) ^ 2)) - 1
      ≤ ‖((∑' m : ℤ, Real.exp (-b * (m : ℝ) ^ 2) : ℝ) : ℂ) - 1‖ := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real]
    exact le_abs_self _
  have hlt : Real.exp (-b) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have h1 : 0 < 1 - Real.exp (-b) := by linarith
  have hgeom : 2 / (1 - Real.exp (-b)) * Real.exp (-b) ≤ 2 / b := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ h1 hb]
    have h2 : b + 1 ≤ Real.exp b := Real.add_one_le_exp b
    have h3 : Real.exp (-b) * Real.exp b = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-b), h2, h3]
  linarith

/-- `1 ≤ m² + n²` for `(m, n) ≠ (0, 0)`. -/
lemma one_le_sq_add_sq {p : ℤ × ℤ} (hp : p ≠ (0, 0)) :
    (1 : ℝ) ≤ (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 := by
  rw [ne_eq, Prod.ext_iff, not_and_or] at hp
  rcases hp with h | h
  · have hz : (1 : ℤ) ≤ p.1 ^ 2 := by nlinarith [Int.one_le_abs h, sq_abs p.1]
    have : (1 : ℝ) ≤ (p.1 : ℝ) ^ 2 := by exact_mod_cast hz
    nlinarith [sq_nonneg (p.2 : ℝ)]
  · have hz : (1 : ℤ) ≤ p.2 ^ 2 := by nlinarith [Int.one_le_abs h, sq_abs p.2]
    have : (1 : ℝ) ≤ (p.2 : ℝ) ^ 2 := by exact_mod_cast hz
    nlinarith [sq_nonneg (p.1 : ℝ)]

/-- **The theta tail bound.** If `c (m² + n²) ≤ Q_z(m, n)` with `c > 0`, then for `t > 0` and
`a = π t c`: `θ_z(t) − 1 ≤ e^{-a/2} (1 + 4/a)²`. -/
lemma thetaR_sub_one_le (z : ℍ) {t c : ℝ} (ht : 0 < t) (hc : 0 < c)
    (hcle : ∀ m n : ℤ, c * ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) ≤ Qform z m n) :
    thetaR z t - 1
      ≤ Real.exp (-(Real.pi * t * c) / 2) * (1 + 4 / (Real.pi * t * c)) ^ 2 := by
  set a := Real.pi * t * c with ha
  have ha0 : 0 < a := by positivity
  have hsum := summable_thetaR z ht
  have hsplit : thetaR z t - 1
      = ∑' p : ℤ × ℤ, (if p = (0, 0) then 0 else Real.exp (-Real.pi * t * Qform z p.1 p.2)) := by
    rw [thetaR, hsum.tsum_eq_add_tsum_ite (0, 0)]
    simp [Qform_zero]
  set g : ℤ × ℤ → ℝ := fun p => Real.exp (-(a / 2))
      * (Real.exp (-(a / 2) * (p.1 : ℝ) ^ 2) * Real.exp (-(a / 2) * (p.2 : ℝ) ^ 2)) with hg
  have ha2 : (0 : ℝ) < a / 2 := by positivity
  have hg_summ : Summable g :=
    ((summable_exp_neg_mul_sq ha2).mul_of_nonneg (summable_exp_neg_mul_sq ha2)
      (fun _ => Real.exp_nonneg _) (fun _ => Real.exp_nonneg _)).mul_left _
  have hle : ∀ p : ℤ × ℤ,
      (if p = (0, 0) then 0 else Real.exp (-Real.pi * t * Qform z p.1 p.2)) ≤ g p := by
    intro p
    simp only [hg]
    split_ifs with h
    · positivity
    · rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h1 := one_le_sq_add_sq h
      have h3 : a * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) ≤ Real.pi * t * Qform z p.1 p.2 := by
        calc a * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)
            = (Real.pi * t) * (c * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by rw [ha]; ring
          _ ≤ (Real.pi * t) * Qform z p.1 p.2 :=
            mul_le_mul_of_nonneg_left (hcle p.1 p.2) (by positivity)
      nlinarith [h1, h3, ha0]
  have hite_summ : Summable fun p : ℤ × ℤ =>
      (if p = (0, 0) then 0 else Real.exp (-Real.pi * t * Qform z p.1 p.2)) := by
    refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) hsum
    · split_ifs <;> positivity
    · split_ifs
      · exact Real.exp_nonneg _
      · exact le_rfl
  have hf_norm : Summable fun m : ℤ => ‖Real.exp (-(a / 2) * (m : ℝ) ^ 2)‖ :=
    (summable_exp_neg_mul_sq ha2).congr fun m => (Real.norm_of_nonneg (Real.exp_nonneg _)).symm
  rw [hsplit]
  calc ∑' p : ℤ × ℤ, (if p = (0, 0) then 0 else Real.exp (-Real.pi * t * Qform z p.1 p.2))
      ≤ ∑' p, g p := Summable.tsum_le_tsum hle hite_summ hg_summ
    _ = Real.exp (-(a / 2)) * ((∑' m : ℤ, Real.exp (-(a / 2) * (m : ℝ) ^ 2))
          * ∑' n : ℤ, Real.exp (-(a / 2) * (n : ℝ) ^ 2)) := by
        rw [tsum_mul_tsum_of_summable_norm hf_norm hf_norm]
        simp only [hg]
        rw [tsum_mul_left]
    _ ≤ Real.exp (-(a / 2)) * ((1 + 2 / (a / 2)) * (1 + 2 / (a / 2))) := by
        have hS := gauss_sum_le ha2
        have hS0 : 0 ≤ ∑' m : ℤ, Real.exp (-(a / 2) * (m : ℝ) ^ 2) :=
          tsum_nonneg fun m => Real.exp_nonneg _
        exact mul_le_mul_of_nonneg_left (mul_le_mul hS hS hS0 (by positivity)) (Real.exp_nonneg _)
    _ = Real.exp (-a / 2) * (1 + 4 / a) ^ 2 := by
        rw [show (2 : ℝ) / (a / 2) = 4 / a by rw [div_div_eq_mul_div]; norm_num, neg_div]
        ring

/-- On the fundamental domain, `Q_z(m, n) ≥ (m² + n²) / (3 y)`. -/
lemma Qform_lower_bound_fd {z : ℍ} (hz : z ∈ (𝒟 : Set ℍ)) (m n : ℤ) :
    1 / (3 * z.im) * ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) ≤ Qform z m n := by
  have hy : 0 < z.im := z.im_pos
  have hre : |z.re| ≤ 1 / 2 := hz.2
  have hX : z.re ^ 2 ≤ 1 / 4 := by
    have := abs_le.mp hre
    nlinarith [this.1, this.2]
  have hY : 3 / 4 ≤ z.im ^ 2 := by
    have := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
    linarith
  rw [Qform_eq, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) hy]
  have key : (m : ℝ) ^ 2 + (n : ℝ) ^ 2
      ≤ 3 * (((n : ℝ) + m * z.re) ^ 2 + (m : ℝ) ^ 2 * z.im ^ 2) := by
    nlinarith [sq_nonneg ((n : ℝ) + 3 / 2 * m * z.re), sq_nonneg (m : ℝ),
      mul_nonneg (sq_nonneg (m : ℝ)) (by linarith : (0 : ℝ) ≤ 1 / 4 - z.re ^ 2),
      mul_nonneg (sq_nonneg (m : ℝ)) (by linarith : (0 : ℝ) ≤ z.im ^ 2 - 3 / 4)]
  nlinarith [key, hy]

/-! ### the entire part `Λ₀` of the Epstein FE-pair as a self-dual integral over `(1, ∞)` -/

/-- `Λ₀_z = mellin f_modif`: entire, and `Λ_z(s) = Λ₀_z(s) − 1/s − 1/(1 − s)`. -/
def epsteinΛ₀ (z : ℍ) : ℂ → ℂ := (epsteinFEPair z).Λ₀

lemma differentiable_epsteinΛ₀ (z : ℍ) : Differentiable ℂ (epsteinΛ₀ z) :=
  (epsteinFEPair z).differentiable_Λ₀

lemma epsteinΛ_eq_Λ₀ (z : ℍ) (s : ℂ) :
    epsteinΛ z s = epsteinΛ₀ z s - 1 / s - 1 / (1 - s) := by
  simp [epsteinΛ, epsteinΛ₀, WeakFEPair.Λ, epsteinFEPair]

/-- The one-sided integral `M_z(s) = ∫_1^∞ t^{s−1} (θ_z(t) − 1) dt`. -/
def thetaM (z : ℍ) (s : ℂ) : ℂ := ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) * (thetaQ z t - 1)

/-- The tail piece `F₁ = 𝟙_{(1,∞)} (θ_z − 1)`. -/
def thetaTail (z : ℍ) : ℝ → ℂ := (Ioi (1 : ℝ)).indicator fun t => thetaQ z t - 1

/-- `θ_z(t) = t⁻¹ θ_z(1/t)` (the functional equation at `1/t`). -/
lemma thetaQ_eq_inv_mul (z : ℍ) {t : ℝ} (ht : 0 < t) :
    thetaQ z t = (t : ℂ)⁻¹ * thetaQ z t⁻¹ := by
  have h := thetaQ_functional_equation z (inv_pos.mpr ht)
  rw [one_div, inv_inv, Complex.ofReal_inv] at h
  exact h

/-- `f_modif` of the Epstein FE-pair, for `t > 0`: `F₁(t) + t⁻¹ F₁(t⁻¹)`. -/
lemma f_modif_eq (z : ℍ) {t : ℝ} (ht : 0 < t) :
    (epsteinFEPair z).f_modif t = thetaTail z t + (t : ℂ)⁻¹ * thetaTail z t⁻¹ := by
  simp only [WeakFEPair.f_modif, epsteinFEPair, thetaTail, Pi.add_apply]
  rcases lt_trichotomy t 1 with h | rfl | h
  · have h3 : 1 < t⁻¹ := one_lt_inv_iff₀.mpr ⟨ht, h⟩
    simp only [Set.indicator_apply, Set.mem_Ioi, Set.mem_Ioo, h, h3, ht, not_lt.mpr h.le,
      and_self, if_true, if_false, one_mul, smul_eq_mul, mul_one, Real.rpow_neg_one,
      Complex.ofReal_inv, zero_add]
    rw [thetaQ_eq_inv_mul z ht]
    ring
  · simp
  · have h4 : t⁻¹ < 1 := inv_lt_one_of_one_lt₀ h
    simp only [Set.indicator_apply, Set.mem_Ioi, Set.mem_Ioo, h, not_lt.mpr h4.le,
      not_lt.mpr h.le, and_false, if_true, if_false, add_zero, mul_zero]

lemma mellinConvergent_f_modif (z : ℍ) (s : ℂ) :
    MellinConvergent (epsteinFEPair z).f_modif s :=
  ((epsteinFEPair z).toStrongFEPair.hasMellin s).1

lemma integrable_tail_piece (z : ℍ) (s : ℂ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • thetaTail z t) (Ioi 0) := by
  have h := (mellinConvergent_f_modif z s).indicator (measurableSet_Ioi (a := (1 : ℝ)))
  refine h.congr (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
  have ht : (0 : ℝ) < t := ht
  beta_reduce
  by_cases h1 : 1 < t
  · have h4 : t⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
    have h0 : thetaTail z t⁻¹ = 0 :=
      Set.indicator_of_notMem (by simp only [Set.mem_Ioi, not_lt]; exact h4.le) _
    rw [Set.indicator_of_mem (Set.mem_Ioi.mpr h1), f_modif_eq z ht, h0, mul_zero, add_zero]
  · have h0 : thetaTail z t = 0 :=
      Set.indicator_of_notMem (by simp only [Set.mem_Ioi]; exact h1) _
    rw [Set.indicator_of_notMem (by simp only [Set.mem_Ioi]; exact h1), h0, smul_zero]

lemma integrable_inv_piece (z : ℍ) (s : ℂ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • ((t : ℂ)⁻¹ * thetaTail z t⁻¹)) (Ioi 0) := by
  have h := (mellinConvergent_f_modif z s).indicator (measurableSet_Ioo (a := (0 : ℝ)) (b := 1))
  refine h.congr (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
  have ht : (0 : ℝ) < t := ht
  beta_reduce
  by_cases h1 : t < 1
  · have h0 : thetaTail z t = 0 :=
      Set.indicator_of_notMem (by simp only [Set.mem_Ioi, not_lt]; exact h1.le) _
    rw [Set.indicator_of_mem (Set.mem_Ioo.mpr ⟨ht, h1⟩), f_modif_eq z ht, h0, zero_add]
  · have h4 : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (not_lt.mp h1)
    have h0 : thetaTail z t⁻¹ = 0 :=
      Set.indicator_of_notMem (by simp only [Set.mem_Ioi, not_lt]; exact h4) _
    rw [Set.indicator_of_notMem (fun h' => h1 h'.2), h0, mul_zero, smul_zero]

/-- **`Λ₀` is the self-dual tail integral**: `Λ₀_z(s) = M_z(s) + M_z(1 − s)` for every `s`. -/
theorem epsteinΛ₀_eq (z : ℍ) (s : ℂ) : epsteinΛ₀ z s = thetaM z s + thetaM z (1 - s) := by
  have hsplit : epsteinΛ₀ z s
      = (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • thetaTail z t)
        + ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • ((t : ℂ)⁻¹ * thetaTail z t⁻¹) := by
    rw [epsteinΛ₀, WeakFEPair.Λ₀, mellin,
      ← integral_add (integrable_tail_piece z s) (integrable_inv_piece z s)]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [f_modif_eq z ht, smul_add]
  have hind : ∀ (w : ℂ) (t : ℝ), (t : ℂ) ^ (w - 1) • thetaTail z t
      = (Ioi 1).indicator (fun t : ℝ => (t : ℂ) ^ (w - 1) * (thetaQ z t - 1)) t := by
    intro w t
    simp only [thetaTail, Set.indicator_apply, smul_eq_mul]
    split_ifs <;> simp
  have h1 : (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • thetaTail z t) = thetaM z s := by
    rw [thetaM]
    simp_rw [hind s]
    rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      Set.inter_eq_left.mpr (Set.Ioi_subset_Ioi zero_le_one)]
  have h2 : (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • ((t : ℂ)⁻¹ * thetaTail z t⁻¹))
      = thetaM z (1 - s) := by
    have hm : (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • ((t : ℂ)⁻¹ * thetaTail z t⁻¹))
        = mellin (fun t : ℝ => thetaTail z (t ^ (-1 : ℝ))) (s - 1) := by
      rw [mellin]
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
      rw [Real.rpow_neg_one, smul_eq_mul, smul_eq_mul, Complex.cpow_sub (s - 1) 1 ht0, Complex.cpow_one]
      ring
    rw [hm, mellin_comp_rpow, thetaM]
    simp only [abs_neg, abs_one, inv_one, one_smul]
    rw [show (s - 1) / ((-1 : ℝ) : ℂ) = 1 - s by push_cast; ring, mellin]
    simp_rw [hind (1 - s)]
    rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      Set.inter_eq_left.mpr (Set.Ioi_subset_Ioi zero_le_one)]
  rw [hsplit, h1, h2]

/-! ### the polynomial bound `‖M_z(s)‖ ≤ 2048 (1 + y)⁵` on `𝒟`, uniformly for `Re s ≤ 3` -/

/-- `x² ≤ 2 e^x` for `x ≥ 0`. -/
lemma sq_le_two_mul_exp {x : ℝ} (hx : 0 ≤ x) : x ^ 2 ≤ 2 * Real.exp x := by
  have h := Real.pow_div_factorial_le_exp x hx 2
  rw [Nat.factorial_two, Nat.cast_ofNat, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)] at h
  linarith

/-- The one-sided integral is bounded by `128 (1 + 4/b)² / b³`, `b = π c`, whenever
`c (m² + n²) ≤ Q_z(m, n)` and `Re s ≤ 3`. -/
lemma norm_thetaM_le_of_lower_bound (z : ℍ) {c : ℝ} (hc : 0 < c)
    (hcle : ∀ m n : ℤ, c * ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) ≤ Qform z m n) {s : ℂ} (hs : s.re ≤ 3) :
    ‖thetaM z s‖ ≤ 128 * (1 + 4 / (Real.pi * c)) ^ 2 / (Real.pi * c) ^ 3 := by
  set b := Real.pi * c with hb
  have hb0 : 0 < b := by positivity
  set K := (1 + 4 / b) ^ 2 * (32 / b ^ 2) with hK
  have hint : IntegrableOn (fun t : ℝ => K * Real.exp (-(b / 4) * t)) (Ioi 1) :=
    (exp_neg_integrableOn_Ioi 1 (by positivity : 0 < b / 4)).const_mul K
  have hbound : ∀ t ∈ Ioi (1 : ℝ),
      ‖(t : ℂ) ^ (s - 1) * (thetaQ z t - 1)‖ ≤ K * Real.exp (-(b / 4) * t) := by
    intro t ht
    have ht1 : 1 < t := ht
    have ht0 : 0 < t := by linarith
    have hθ0 : 0 ≤ thetaR z t - 1 := thetaR_sub_one_nonneg z ht0
    have hnorm : ‖thetaQ z t - 1‖ = thetaR z t - 1 := by
      rw [thetaQ_eq_ofReal, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_of_nonneg hθ0]
    rw [norm_mul, hnorm, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re, Complex.one_re]
    have hθ := thetaR_sub_one_le z ht0 hc hcle
    have hpow : t ^ (s.re - 1) ≤ t ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le ht1.le (by linarith)
    rw [Real.rpow_two] at hpow
    have ha : Real.pi * t * c = b * t := by rw [hb]; ring
    rw [ha] at hθ
    have h1 : (1 + 4 / (b * t)) ^ 2 ≤ (1 + 4 / b) ^ 2 := by
      have hdiv : 4 / (b * t) ≤ 4 / b :=
        div_le_div_of_nonneg_left (by norm_num) hb0 (by nlinarith)
      have h0 : 0 ≤ 1 + 4 / (b * t) := by positivity
      gcongr
    have h2 : t ^ 2 * Real.exp (-(b * t) / 2) ≤ 32 / b ^ 2 * Real.exp (-(b / 4) * t) := by
      have hx := sq_le_two_mul_exp (by positivity : 0 ≤ b * t / 4)
      have hexp : Real.exp (-(b * t) / 2) = Real.exp (-(b / 4) * t) * Real.exp (-(b * t / 4)) := by
        rw [← Real.exp_add]; congr 1; ring
      have hE : Real.exp (b * t / 4) * Real.exp (-(b * t / 4)) = 1 := by
        rw [← Real.exp_add]; simp
      have ht2 : t ^ 2 ≤ 32 / b ^ 2 * Real.exp (b * t / 4) := by
        have hsq : (b * t / 4) ^ 2 = b ^ 2 * t ^ 2 / 16 := by ring
        rw [hsq] at hx
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        nlinarith [hx]
      rw [hexp]
      calc t ^ 2 * (Real.exp (-(b / 4) * t) * Real.exp (-(b * t / 4)))
          ≤ 32 / b ^ 2 * Real.exp (b * t / 4)
              * (Real.exp (-(b / 4) * t) * Real.exp (-(b * t / 4))) :=
            mul_le_mul_of_nonneg_right ht2 (by positivity)
        _ = 32 / b ^ 2 * Real.exp (-(b / 4) * t)
              * (Real.exp (b * t / 4) * Real.exp (-(b * t / 4))) := by ring
        _ = 32 / b ^ 2 * Real.exp (-(b / 4) * t) := by rw [hE, mul_one]
    calc t ^ (s.re - 1) * (thetaR z t - 1)
        ≤ t ^ 2 * (Real.exp (-(b * t) / 2) * (1 + 4 / (b * t)) ^ 2) :=
          mul_le_mul hpow hθ hθ0 (by positivity)
      _ = (t ^ 2 * Real.exp (-(b * t) / 2)) * (1 + 4 / (b * t)) ^ 2 := by ring
      _ ≤ (32 / b ^ 2 * Real.exp (-(b / 4) * t)) * (1 + 4 / b) ^ 2 :=
          mul_le_mul h2 h1 (by positivity) (by positivity)
      _ = K * Real.exp (-(b / 4) * t) := by rw [hK]; ring
  have hM : ‖thetaM z s‖ ≤ ∫ t in Ioi (1 : ℝ), K * Real.exp (-(b / 4) * t) := by
    rw [thetaM]
    exact norm_integral_le_of_norm_le hint (ae_restrict_of_forall_mem measurableSet_Ioi hbound)
  refine hM.trans ?_
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -(b / 4) < 0)]
  have he : Real.exp (-(b / 4) * 1) ≤ 1 :=
    calc Real.exp (-(b / 4) * 1) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  have hval : -Real.exp (-(b / 4) * 1) / -(b / 4) = Real.exp (-(b / 4) * 1) * (4 / b) := by
    field_simp
  rw [hval, hK]
  calc (1 + 4 / b) ^ 2 * (32 / b ^ 2) * (Real.exp (-(b / 4) * 1) * (4 / b))
      ≤ (1 + 4 / b) ^ 2 * (32 / b ^ 2) * (1 * (4 / b)) := by gcongr
    _ = 128 * (1 + 4 / b) ^ 2 / b ^ 3 := by field_simp; ring

/-- **The uniform bound on `𝒟`**: `‖M_z(s)‖ ≤ 2048 (1 + Im z)⁵` for `z ∈ 𝒟` and `Re s ≤ 3`. -/
theorem norm_thetaM_le_fd {z : ℍ} (hz : z ∈ (𝒟 : Set ℍ)) {s : ℂ} (hs : s.re ≤ 3) :
    ‖thetaM z s‖ ≤ 2048 * (1 + z.im) ^ 5 := by
  have hy : 0 < z.im := z.im_pos
  have hc : 0 < 1 / (3 * z.im) := by positivity
  refine (norm_thetaM_le_of_lower_bound z hc (Qform_lower_bound_fd hz) hs).trans ?_
  set y := z.im with hy_def
  set b := Real.pi * (1 / (3 * y)) with hb
  have hb0 : 0 < b := by positivity
  have hπ3 : 3 < Real.pi := Real.pi_gt_three
  have hu : b⁻¹ ≤ y := by
    rw [hb, show Real.pi * (1 / (3 * y)) = Real.pi / (3 * y) by ring, inv_div,
      div_le_iff₀ Real.pi_pos]
    nlinarith
  have hu0 : 0 ≤ b⁻¹ := inv_nonneg.mpr hb0.le
  have hrw : 128 * (1 + 4 / b) ^ 2 / b ^ 3 = 128 * (1 + 4 * b⁻¹) ^ 2 * (b⁻¹) ^ 3 := by
    field_simp
  rw [hrw]
  have hA : (1 + 4 * b⁻¹) ^ 2 ≤ (4 * (1 + y)) ^ 2 := by gcongr; linarith
  have hB : (b⁻¹) ^ 3 ≤ (1 + y) ^ 3 := by gcongr; linarith
  calc 128 * (1 + 4 * b⁻¹) ^ 2 * (b⁻¹) ^ 3
      ≤ 128 * (4 * (1 + y)) ^ 2 * (1 + y) ^ 3 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hA (by norm_num)) hB (by positivity) (by positivity)
    _ = 2048 * (1 + y) ^ 5 := by ring

open Filter Topology

/-! ### dominated convergence, `(σ − 1) ∫_𝒟 Φ E(·, σ) → (3/π) ∫_𝒟 Φ` as `σ → 1⁺` -/

include cf in
/-- `Φ (1 + Im)^n` is bounded on `𝒟`, by the exponential decay of a cusp form at `i∞`. -/
lemma phi_mul_pow_bounded (f : F) (hk : 0 < k) (n : ℕ) :
    ∃ M : ℝ, ∀ z ∈ (𝒟 : Set ℍ), phi k f z * (1 + z.im) ^ n ≤ M := by
  obtain ⟨c, hc, hdecay⟩ := CuspFormClass.exp_decay_atImInfty' f
  rw [Asymptotics.isBigO_iff] at hdecay
  obtain ⟨C, hC⟩ := hdecay
  rw [Filter.eventually_iff, UpperHalfPlane.atImInfty_mem] at hC
  obtain ⟨A, hA⟩ := hC
  obtain ⟨Cφ, hCφ⟩ := phi_bounded k f
  set A' := max A 0 with hA'
  set N := k.toNat + n with hN
  set K₁ := (N.factorial : ℝ) * Real.exp (2 * c) / (2 * c) ^ N with hK₁
  refine ⟨max (C ^ 2 * K₁) (max Cφ 0 * (1 + A') ^ n), fun z hz => ?_⟩
  have hy : 0 < z.im := z.im_pos
  by_cases hyA : A' ≤ z.im
  · have hb := hA z (le_trans (le_max_left A 0) hyA)
    simp only [Set.mem_setOf_eq, Real.norm_eq_abs, Real.abs_exp] at hb
    have hC0 : 0 ≤ C := by
      by_contra hneg
      push_neg at hneg
      have : C * Real.exp (-c * z.im) < 0 := mul_neg_of_neg_of_pos hneg (Real.exp_pos _)
      linarith [norm_nonneg (f z)]
    have hsq : ‖f z‖ ^ 2 ≤ (C * Real.exp (-c * z.im)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hb 2
    have hzpow : z.im ^ k = z.im ^ k.toNat := by
      rw [← zpow_natCast, Int.toNat_of_nonneg hk.le]
    have hyk : z.im ^ k.toNat * (1 + z.im) ^ n ≤ (1 + z.im) ^ N := by
      rw [hN, pow_add]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hy.le (by linarith) _) (by positivity)
    have hfac := Real.pow_div_factorial_le_exp (2 * c * (1 + z.im)) (by positivity) N
    have hexp2 : Real.exp (2 * c * (1 + z.im)) = Real.exp (2 * c) * Real.exp (2 * c * z.im) := by
      rw [← Real.exp_add]; congr 1; ring
    have hpowN : (1 + z.im) ^ N ≤ K₁ * Real.exp (2 * c * z.im) := by
      rw [mul_pow, div_le_iff₀ (by positivity), hexp2] at hfac
      have h2c : 0 < (2 * c) ^ N := by positivity
      rw [hK₁, div_mul_eq_mul_div, le_div_iff₀ h2c]
      linarith [hfac]
    have hEE : Real.exp (-c * z.im) ^ 2 * Real.exp (2 * c * z.im) = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add,
        show ((2 : ℕ) : ℝ) * (-c * z.im) + 2 * c * z.im = 0 by push_cast; ring, Real.exp_zero]
    calc phi k f z * (1 + z.im) ^ n
        = ‖f z‖ ^ 2 * (z.im ^ k.toNat * (1 + z.im) ^ n) := by
          rw [phi, Complex.normSq_eq_norm_sq, hzpow]; ring
      _ ≤ (C * Real.exp (-c * z.im)) ^ 2 * (1 + z.im) ^ N :=
          mul_le_mul hsq hyk (by positivity) (by positivity)
      _ ≤ (C * Real.exp (-c * z.im)) ^ 2 * (K₁ * Real.exp (2 * c * z.im)) :=
          mul_le_mul_of_nonneg_left hpowN (by positivity)
      _ = C ^ 2 * K₁ * (Real.exp (-c * z.im) ^ 2 * Real.exp (2 * c * z.im)) := by ring
      _ = C ^ 2 * K₁ := by rw [hEE, mul_one]
      _ ≤ _ := le_max_left _ _
  · push_neg at hyA
    have hA0 : 0 ≤ A' := le_max_right A 0
    have h1 : phi k f z * (1 + z.im) ^ n ≤ max Cφ 0 * (1 + A') ^ n := by
      have hp : (1 + z.im) ^ n ≤ (1 + A') ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      exact mul_le_mul (le_trans (hCφ z) (le_max_left _ _)) hp (by positivity) (by positivity)
    exact h1.trans (le_max_right _ _)

/-- The prefactor `π^s / Γ(s) / (2 ζ(2s))` of `E(z, s) = eisPre s · Λ_z(s)`. -/
def eisPre (s : ℂ) : ℂ := (Real.pi : ℂ) ^ s / Complex.Gamma s / (2 * riemannZeta (2 * s))

lemma eisensteinE_eq_pre (z : ℍ) (s : ℂ) : eisensteinE z s = eisPre s * epsteinΛ z s := by
  rw [eisensteinE, epsteinZeta, eisPre]
  ring

lemma continuousAt_eisPre_one : ContinuousAt eisPre 1 := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hζ : ContinuousAt (fun s : ℂ => riemannZeta (2 * s)) 1 := by
    have : ContinuousAt riemannZeta (2 * 1) :=
      (differentiableAt_riemannZeta (by norm_num)).continuousAt
    exact this.comp (by fun_prop)
  have hne : (2 : ℂ) * riemannZeta (2 * 1) ≠ 0 := by
    rw [mul_one, riemannZeta_two]
    exact mul_ne_zero two_ne_zero (div_ne_zero (pow_ne_zero 2 hπ) (by norm_num))
  have hΓ : Complex.Gamma 1 ≠ 0 := by rw [Complex.Gamma_one]; exact one_ne_zero
  exact ((continuousAt_const_cpow hπ).div Complex.differentiableAt_Gamma_one.continuousAt hΓ).div
    (continuousAt_const.mul hζ) hne

/-- **The uniform bound on `𝒟`** for the residue factor: for `σ ∈ (1, 2]`,
`‖(σ − 1) Λ_z(σ)‖ ≤ 4096 (1 + Im z)⁵ + 2`. -/
lemma norm_sub_one_mul_epsteinΛ_le {z : ℍ} (hz : z ∈ (𝒟 : Set ℍ)) {σ : ℝ} (hσ1 : 1 < σ)
    (hσ2 : σ ≤ 2) :
    ‖((σ : ℂ) - 1) * epsteinΛ z σ‖ ≤ 4096 * (1 + z.im) ^ 5 + 2 := by
  have hσ0 : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hσ1' : (1 : ℂ) - σ ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have heq : ((σ : ℂ) - 1) * epsteinΛ z σ
      = ((σ : ℂ) - 1) * epsteinΛ₀ z σ - ((σ : ℂ) - 1) / σ + 1 := by
    rw [epsteinΛ_eq_Λ₀]
    field_simp
    ring
  rw [heq]
  have hΛ₀ : ‖epsteinΛ₀ z σ‖ ≤ 4096 * (1 + z.im) ^ 5 := by
    rw [epsteinΛ₀_eq]
    refine (norm_add_le _ _).trans ?_
    have h1 := norm_thetaM_le_fd hz (s := σ) (by simp only [Complex.ofReal_re]; linarith)
    have h2 := norm_thetaM_le_fd hz (s := 1 - σ)
      (by simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]; linarith)
    linarith
  have hs1 : ‖((σ : ℂ) - 1)‖ = σ - 1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  have hfrac : ‖((σ : ℂ) - 1) / σ‖ ≤ 1 := by
    rw [norm_div, hs1, Complex.norm_real, Real.norm_of_nonneg (by linarith),
      div_le_one (by linarith)]
    linarith
  have hprod : ‖((σ : ℂ) - 1) * epsteinΛ₀ z σ‖ ≤ 1 * (4096 * (1 + z.im) ^ 5) := by
    rw [norm_mul, hs1]
    exact mul_le_mul (by linarith) hΛ₀ (norm_nonneg _) zero_le_one
  calc ‖((σ : ℂ) - 1) * epsteinΛ₀ z σ - ((σ : ℂ) - 1) / σ + 1‖
      ≤ ‖((σ : ℂ) - 1) * epsteinΛ₀ z σ‖ + ‖((σ : ℂ) - 1) / σ‖ + ‖(1 : ℂ)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ 1 * (4096 * (1 + z.im) ^ 5) + 1 + 1 := by
        rw [norm_one]
        linarith [hprod, hfrac]
    _ = 4096 * (1 + z.im) ^ 5 + 2 := by ring

/-- Measurability of `z ↦ Σ_d Im(γ_d z)^σ` on `ℍ`, for `σ > 1`. -/
lemma measurable_eisSum {σ : ℝ} (hσ : 1 < σ) :
    Measurable fun z : ℍ => ∑' d : CosetPSL, eisTermR z σ d := by
  have hfun : (fun z : ℍ => ∑' d : CosetPSL, eisTermR z σ d)
      = fun z => (∑' d : CosetPSL, ENNReal.ofReal (eisTermR z σ d)).toReal := by
    funext z
    rw [← ENNReal.ofReal_tsum_of_nonneg (eisTermR_nonneg z σ) (summable_eisTermR z hσ),
      ENNReal.toReal_ofReal (tsum_nonneg (eisTermR_nonneg z σ))]
  rw [hfun]
  refine Measurable.ennreal_toReal (Measurable.ennreal_tsum fun d => ?_)
  induction d using Quotient.inductionOn with
  | h c =>
    simp only [eisTermR_mk]
    exact ENNReal.measurable_ofReal.comp
      ((continuous_im_smul c).rpow_const fun z => Or.inl (c • z).im_ne_zero).measurable

/-- `σ ↦ (σ : ℂ)` maps `𝓝[>] 1` into `𝓝[≠] 1`. -/
lemma tendsto_ofReal_nhdsGT_one :
    Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
  have h0 : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
    have := (Complex.continuous_ofReal.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Ioi 1))
    simpa using this
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h0 ?_
  refine eventually_mem_nhdsWithin.mono fun σ hσ => ?_
  have hσ : 1 < σ := hσ
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_one]
  exact ne_of_gt hσ

include cf in
/-- **The pole of the unfolded integral**: `(σ − 1) ∫_𝒟 Φ(z) E(z, σ) dμ → (3/π) ∫_𝒟 Φ`
as `σ → 1⁺`, by dominated convergence with the dominant `Φ · (G (4096 (1 + y)⁵ + 2))`. -/
theorem tendsto_rs_integral (f : F) (hk : 0 < k) :
    Tendsto (fun σ : ℝ => (σ - 1) * ∫ z in (𝒟 : Set ℍ), phi k f z * ∑' d : CosetPSL, eisTermR z σ d)
      (𝓝[>] (1 : ℝ)) (𝓝 (3 / Real.pi * ∫ z in (𝒟 : Set ℍ), phi k f z)) := by
  set G : ℝ := ‖eisPre 1‖ + 1 with hG
  have hG0 : 0 ≤ G := by rw [hG]; positivity
  have hGev : ∀ᶠ s in 𝓝 (1 : ℂ), ‖eisPre s‖ ≤ G :=
    continuousAt_eisPre_one.norm.tendsto.eventually (eventually_le_nhds (lt_add_one _))
  have hofReal' := tendsto_ofReal_nhdsGT_one
  have hofReal : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) :=
    hofReal'.mono_right nhdsWithin_le_nhds
  have hlt2 : ∀ᶠ σ in 𝓝[>] (1 : ℝ), σ < 2 :=
    (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2)).filter_mono nhdsWithin_le_nhds
  set F : ℝ → ℍ → ℝ := fun σ z => phi k f z * ((σ - 1) * ∑' d : CosetPSL, eisTermR z σ d) with hF
  set bound : ℍ → ℝ := fun z => phi k f z * (G * (4096 * (1 + z.im) ^ 5 + 2)) with hbound
  have hbound_nonneg : ∀ z, 0 ≤ bound z := fun z => by
    simp only [hbound]
    exact mul_nonneg (phi_nonneg k f z) (mul_nonneg hG0 (by positivity))
  have hbound_meas : Measurable bound :=
    (continuous_phi k f).measurable.mul
      (continuous_const.mul ((continuous_const.mul
        ((continuous_const.add UpperHalfPlane.continuous_im).pow 5)).add continuous_const)).measurable
  have hF_meas : ∀ᶠ σ in 𝓝[>] (1 : ℝ), AEStronglyMeasurable (F σ) (volume.restrict (𝒟 : Set ℍ)) := by
    filter_upwards [eventually_mem_nhdsWithin] with σ hσ
    have hσ : 1 < σ := hσ
    simp only [hF]
    exact ((continuous_phi k f).measurable.mul
      (measurable_const.mul (measurable_eisSum hσ))).aestronglyMeasurable
  have h_bound : ∀ᶠ σ in 𝓝[>] (1 : ℝ), ∀ᵐ z ∂(volume.restrict (𝒟 : Set ℍ)),
      ‖F σ z‖ ≤ bound z := by
    filter_upwards [eventually_mem_nhdsWithin, hlt2, hofReal.eventually hGev] with σ hσ1 hσ2 hGσ
    refine ae_restrict_of_forall_mem measurableSet_fd fun z hz => ?_
    have hσ1 : 1 < σ := hσ1
    have hre : (σ - 1) * ∑' d : CosetPSL, eisTermR z σ d
        = (((σ : ℂ) - 1) * eisensteinE z σ).re := by
      rw [eisensteinE_eq_ofReal_tsum z hσ1, ← Complex.ofReal_one, ← Complex.ofReal_sub,
        ← Complex.ofReal_mul, Complex.ofReal_re]
    have hE : ‖((σ : ℂ) - 1) * eisensteinE z σ‖ ≤ G * (4096 * (1 + z.im) ^ 5 + 2) := by
      rw [eisensteinE_eq_pre, show ((σ : ℂ) - 1) * (eisPre σ * epsteinΛ z σ)
          = eisPre σ * (((σ : ℂ) - 1) * epsteinΛ z σ) by ring, norm_mul]
      exact mul_le_mul hGσ (norm_sub_one_mul_epsteinΛ_le hz hσ1 hσ2.le) (norm_nonneg _) hG0
    simp only [hF, hbound]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (phi_nonneg k f z), hre]
    exact mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans hE) (phi_nonneg k f z)
  have hbound_int : Integrable bound (volume.restrict (𝒟 : Set ℍ)) := by
    obtain ⟨M₅, hM₅⟩ := phi_mul_pow_bounded k f hk 5
    obtain ⟨Cφ, hCφ⟩ := phi_bounded k f
    refine Measure.integrableOn_of_bounded volume_fd_lt_top.ne hbound_meas.aestronglyMeasurable
      (M := G * (4096 * M₅ + 2 * max Cφ 0))
      (ae_restrict_of_forall_mem measurableSet_fd fun z hz => ?_)
    rw [Real.norm_of_nonneg (hbound_nonneg z)]
    have h5 := hM₅ z hz
    have hφ : phi k f z ≤ max Cφ 0 := (hCφ z).trans (le_max_left _ _)
    calc bound z = G * (4096 * (phi k f z * (1 + z.im) ^ 5) + 2 * phi k f z) := by
          simp only [hbound]; ring
      _ ≤ G * (4096 * M₅ + 2 * max Cφ 0) :=
          mul_le_mul_of_nonneg_left (by linarith [h5, hφ]) hG0
  have h_lim : ∀ᵐ z ∂(volume.restrict (𝒟 : Set ℍ)),
      Tendsto (fun σ => F σ z) (𝓝[>] (1 : ℝ)) (𝓝 (phi k f z * (3 / Real.pi))) := by
    refine Filter.Eventually.of_forall fun z => ?_
    simp only [hF]
    refine Tendsto.const_mul _ ?_
    have hres : Tendsto (fun σ : ℝ => (((σ : ℂ) - 1) * eisensteinE z σ).re) (𝓝[>] (1 : ℝ))
        (𝓝 (3 / Real.pi)) := by
      have h3 : (3 / (Real.pi : ℂ)).re = 3 / Real.pi := by
        rw [show (3 / (Real.pi : ℂ)) = ((3 / Real.pi : ℝ) : ℂ) by norm_cast, Complex.ofReal_re]
      have := (Complex.continuous_re.tendsto _).comp ((eisensteinE_residue_one z).comp hofReal')
      rw [h3] at this
      exact this
    refine hres.congr' ?_
    filter_upwards [eventually_mem_nhdsWithin] with σ hσ
    have hσ : 1 < σ := hσ
    rw [eisensteinE_eq_ofReal_tsum z hσ, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  have key := tendsto_integral_filter_of_dominated_convergence bound hF_meas h_bound hbound_int h_lim
  have hlimval : (∫ z in (𝒟 : Set ℍ), phi k f z * (3 / Real.pi))
      = 3 / Real.pi * ∫ z in (𝒟 : Set ℍ), phi k f z := by
    rw [integral_mul_const, mul_comm]
  rw [hlimval] at key
  refine key.congr fun σ => ?_
  simp only [hF]
  rw [← integral_const_mul]
  congr 1
  funext z
  ring

/-! ### the pole of `D(w)` at `w = k` -/

/-- The Rankin–Selberg function continued along the real axis:
`rsDcont σ = (4π)^σ Γ(σ)^{-1} ∫_𝒟 Φ(z) E(z, σ − k + 1) dμ`. For `σ > k + 1` it equals `D(σ)`. -/
def rsDcont (f : F) (σ : ℝ) : ℝ :=
  (4 * Real.pi) ^ σ / Real.Gamma σ
    * ∫ z in (𝒟 : Set ℍ), phi k f z * ∑' d : CosetPSL, eisTermR z (σ - k + 1) d

include cf in
/-- For real `σ > k + 1`, the continued function is `D(σ)` (from `rs_integral_eq`). -/
theorem rsDcont_eq_rsD (f : F) (hk : 0 < k) {σ : ℝ} (hσ : (k : ℝ) + 1 < σ) :
    (rsDcont k f σ : ℂ) = rsD f (σ : ℂ) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h := rs_integral_eq k f hk (σ := σ - k + 1) (by linarith)
  have hw : ((σ - k + 1 + k - 1 : ℝ) : ℂ) = (σ : ℂ) := by push_cast; ring
  rw [hw] at h
  have hΓ : Complex.Gamma (σ : ℂ) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp only [Complex.ofReal_re]; linarith)
  have h4π : ((4 * Real.pi : ℝ) : ℂ) ^ (σ : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    left
    exact Complex.ofReal_ne_zero.mpr (by positivity)
  rw [rsDcont, Complex.ofReal_mul, h, Complex.ofReal_div, Complex.ofReal_cpow (by positivity),
    ← Complex.Gamma_ofReal, Complex.cpow_neg]
  field_simp

include cf in
/-- **The simple pole of `D` at `w = k`** (real approach): `(σ − k) · rsDcont σ` tends to
`(4π)^k Γ(k)^{-1} (3/π) ∫_𝒟 Φ` as `σ → k⁺`. -/
theorem tendsto_rsDcont_pole (f : F) (hk : 0 < k) :
    Tendsto (fun σ : ℝ => (σ - k) * rsDcont k f σ) (𝓝[>] (k : ℝ))
      (𝓝 ((4 * Real.pi) ^ k / Real.Gamma k * (3 / Real.pi * ∫ z in (𝒟 : Set ℍ), phi k f z))) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hpre : Tendsto (fun σ : ℝ => (4 * Real.pi) ^ σ / Real.Gamma σ) (𝓝[>] (k : ℝ))
      (𝓝 ((4 * Real.pi) ^ (k : ℝ) / Real.Gamma k)) := by
    have hΓ : ContinuousAt Real.Gamma k := by
      refine (Real.differentiableAt_Gamma fun m => ?_).continuousAt
      intro h
      have := Nat.cast_nonneg (α := ℝ) m
      linarith
    have hc : ContinuousAt (fun σ : ℝ => (4 * Real.pi) ^ σ / Real.Gamma σ) k :=
      (Real.continuousAt_const_rpow (by positivity)).div hΓ (Real.Gamma_pos_of_pos hk').ne'
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have hshift : Tendsto (fun σ : ℝ => σ - k + 1) (𝓝[>] (k : ℝ)) (𝓝[>] (1 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun σ : ℝ => σ - k + 1) (𝓝 (k : ℝ)) (𝓝 ((k : ℝ) - k + 1)) :=
        ((continuous_id.sub continuous_const).add continuous_const).tendsto _
      simpa using this.mono_left nhdsWithin_le_nhds
    · exact eventually_mem_nhdsWithin.mono fun σ hσ => by
        simp only [Set.mem_Ioi] at hσ ⊢; linarith
  have hmain := (tendsto_rs_integral k f hk).comp hshift
  have heq : (fun σ : ℝ => (σ - k) * rsDcont k f σ)
      = fun σ => ((4 * Real.pi) ^ σ / Real.Gamma σ)
          * ((σ - k + 1 - 1) * ∫ z in (𝒟 : Set ℍ), phi k f z
              * ∑' d : CosetPSL, eisTermR z (σ - k + 1) d) := by
    funext σ; rw [rsDcont]; ring
  rw [heq, show (4 * Real.pi) ^ k = (4 * Real.pi) ^ (k : ℝ) from (Real.rpow_intCast _ _).symm]
  exact hpre.mul hmain

include cf in
/-- The residue is positive for a nonzero cusp form. -/
theorem rs_residue_pos (f : F) (hk : 0 < k) (hf : (⇑f : ℍ → ℂ) ≠ 0) :
    0 < (4 * Real.pi) ^ k / Real.Gamma k * (3 / Real.pi * ∫ z in (𝒟 : Set ℍ), phi k f z) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 : 0 < (4 * Real.pi) ^ k / Real.Gamma k :=
    div_pos (zpow_pos (by positivity) k) (Real.Gamma_pos_of_pos hk')
  have h2 : 0 < 3 / Real.pi * ∫ z in (𝒟 : Set ℍ), phi k f z :=
    mul_pos (by positivity) (integral_phi_pos_of_ne_zero k f hf)
  exact mul_pos h1 h2

include cf in
/-- **the simple pole of `D(w) = Σ |a_n|² n^{-w}` at `w = k`** (along the real axis):
`rsDcont` agrees with `D` for `σ > k + 1`, `(σ − k) rsDcont σ → (4π)^k Γ(k)^{-1} (3/π) ⟨f, f⟩`
as `σ → k⁺`, and that residue is positive for `f ≠ 0`. -/
theorem rsD_simplePole (f : F) (hk : 0 < k) (hf : (⇑f : ℍ → ℂ) ≠ 0) :
    (∀ σ : ℝ, (k : ℝ) + 1 < σ → (rsDcont k f σ : ℂ) = rsD f (σ : ℂ)) ∧
    Tendsto (fun σ : ℝ => (σ - k) * rsDcont k f σ) (𝓝[>] (k : ℝ))
      (𝓝 ((4 * Real.pi) ^ k / Real.Gamma k * (3 / Real.pi * ∫ z in (𝒟 : Set ℍ), phi k f z))) ∧
    0 < (4 * Real.pi) ^ k / Real.Gamma k * (3 / Real.pi * ∫ z in (𝒟 : Set ℍ), phi k f z) :=
  ⟨fun _ hσ => rsDcont_eq_rsD k f hk hσ, tendsto_rsDcont_pole k f hk, rs_residue_pos k f hk hf⟩

end

/-- Witness that the hypotheses of `rs_integral_eq` are satisfiable (non-vacuous): a concrete
level-one cusp-form type carries the `CuspFormClass` instance, and `rs_integral_eq` has no
`f ≠ 0` hypothesis, so the zero cusp form at weight `12` with `σ = 3` satisfies all of them. -/
theorem rs_integral_eq_hyps_satisfiable :
    ∃ (_f : CuspForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ)
          (CongruenceSubgroup.Gamma 1)) 12) (σ : ℝ), (0 : ℤ) < 12 ∧ 2 < σ :=
  ⟨0, 3, by norm_num, by norm_num⟩

end RankinSelbergDelta.RankinSelberg
