import Mathlib

/-!
# The invariant measure on the upper half-plane

The measure `dx dy / y²` on `ℍ` and its invariance under `SL(2, ℝ)` acting by Möbius
transformations, with the derivative lemmas needed for the change of variables. Only the
orientation-preserving case `0 < det g` is treated, which is all the unfolding needs.
-/

open MeasureTheory Filter
open scoped NNReal MatrixGroups Pointwise

noncomputable section

namespace UpperHalfPlane

instance : MeasurableSpace ℍ := .comap UpperHalfPlane.coe inferInstance

instance : BorelSpace ℍ := ⟨borel_comap.symm⟩

lemma measurableEmbedding_coe : MeasurableEmbedding UpperHalfPlane.coe :=
  isOpenEmbedding_coe.measurableEmbedding

@[fun_prop]
lemma measurable_coe : Measurable UpperHalfPlane.coe :=
  measurableEmbedding_coe.measurable

/-- The invariant measure on the upper half-plane, defined by `dx dy / y ^ 2`. -/
instance : MeasureSpace ℍ :=
  ⟨(volume.comap UpperHalfPlane.coe).withDensity
    fun z ↦ ↑((1 / ‖z.im‖₊) ^ 2 : ℝ≥0)⟩

theorem volume_def :
    (volume : Measure ℍ) = (volume.comap UpperHalfPlane.coe).withDensity fun z ↦
      ↑((1 / ‖z.im‖₊) ^ 2 : ℝ≥0) :=
  rfl

instance : IsFiniteMeasureOnCompacts (volume.comap UpperHalfPlane.coe) :=
  .comap' _ continuous_coe measurableEmbedding_coe

instance : IsLocallyFiniteMeasure (volume.comap UpperHalfPlane.coe) := inferInstance

instance : SigmaFinite (volume.comap UpperHalfPlane.coe) := inferInstance

instance : SFinite (volume.comap UpperHalfPlane.coe) := inferInstance

instance : IsLocallyFiniteMeasure (volume : Measure ℍ) := by
  show IsLocallyFiniteMeasure
    ((volume.comap UpperHalfPlane.coe).withDensity fun z ↦ ↑((1 / ‖z.im‖₊) ^ 2 : ℝ≥0))
  refine IsLocallyFiniteMeasure.withDensity_coe (μ := volume.comap UpperHalfPlane.coe)
    (f := fun z : ℍ ↦ (1 / ‖z.im‖₊) ^ 2) ?_
  refine (continuous_const.div₀ (continuous_nnnorm.comp continuous_im) fun x ↦ ?_).pow _
  exact nnnorm_ne_zero_iff.mpr x.im_ne_zero

instance : IsFiniteMeasureOnCompacts (volume : Measure ℍ) := inferInstance

instance : SigmaFinite (volume : Measure ℍ) := inferInstance

instance : SFinite (volume : Measure ℍ) := inferInstance

/-- Express the volume of a measurable set as a Lebesgue integral
over the corresponding subset of `ℂ`. -/
lemma volume_eq_lintegral (s : Set ℍ) :
    volume s = ∫⁻ z : ℂ in (↑) '' s, ↑((1 / ‖z.im‖₊) ^ 2 : NNReal) := by
  have : MeasurePreserving UpperHalfPlane.coe (volume.comap UpperHalfPlane.coe)
      (volume.restrict (.range UpperHalfPlane.coe)) :=
    ⟨measurable_coe, by rw [measurableEmbedding_coe.map_comap]⟩
  rw [volume_def, withDensity_apply',
    ← Set.inter_eq_self_of_subset_left (Set.image_subset_range _ _),
    ← Measure.restrict_restrict', ← this.setLIntegral_comp_emb measurableEmbedding_coe]
  · simp
  · exact measurableEmbedding_coe.measurableSet_range

/-! ### The derivative of `z ↦ g • z` (orientation-preserving case), from upstream `Manifold.lean` -/

lemma hasStrictDerivAt_smul {g : GL (Fin 2) ℝ} (hg : 0 < g.val.det) (τ : ℍ) :
    HasStrictDerivAt (fun z ↦ ↑(g • ofComplex z) : ℂ → ℂ) (g.val.det / denom g τ ^ 2) τ := by
  suffices HasStrictDerivAt (num g / denom g) (g.val.det / denom g τ ^ 2) τ by
    refine this.congr_of_eventuallyEq ?_
    rw [← isOpenEmbedding_coe.map_nhds_eq, eventuallyEq_map]
    simp [Function.comp_def, coe_smul_of_det_pos hg]
  convert
    ((hasStrictDerivAt_id (τ : ℂ)).const_mul _ |>.add_const _).div
      ((hasStrictDerivAt_id (τ : ℂ)).const_mul _ |>.add_const _) _ using 2
  · simp [Matrix.det_fin_two]; ring
  · apply denom_ne_zero

/-- The real derivative of `z ↦ g • z` for `0 < det g`: multiplication by `det g / (c z + d)²`. -/
def smulFDerivPos (g : GL (Fin 2) ℝ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.toSpanSingleton ℂ (g.val.det / denom g z ^ 2)).restrictScalars ℝ

lemma det_smulFDerivPos (g : GL (Fin 2) ℝ) (z : ℂ) :
    (smulFDerivPos g z).det = g.val.det ^ 2 / ‖denom g z‖ ^ 4 := by
  simp [smulFDerivPos, ContinuousLinearMap.det, LinearMap.det_restrictScalars,
    Algebra.norm_complex_eq, Complex.normSq_eq_norm_sq, ← pow_mul]

lemma hasStrictFDerivAt_smul_of_det_pos {g : GL (Fin 2) ℝ} (hg : 0 < g.val.det) (τ : ℍ) :
    HasStrictFDerivAt (fun z ↦ ↑(g • ofComplex z) : ℂ → ℂ) (smulFDerivPos g τ) τ :=
  (hasStrictDerivAt_smul hg τ).hasStrictFDerivAt.restrictScalars ℝ

/-! ### Invariance -/

/-- The pointwise Jacobian identity: the density transforms by the inverse of `|det|`. -/
lemma jacobian_density {g : GL (Fin 2) ℝ} (hg : 0 < g.val.det) (τ : ℍ) :
    ENNReal.ofReal |(smulFDerivPos g τ).det|
        * ↑((1 / ‖(↑(g • ofComplex (τ : ℂ)) : ℂ).im‖₊) ^ 2 : ℝ≥0)
      = ↑((1 / ‖(τ : ℂ).im‖₊) ^ 2 : ℝ≥0) := by
  have hden : ‖denom g τ‖ ≠ 0 := norm_ne_zero_iff.mpr (denom_ne_zero g τ)
  have hy : τ.im ≠ 0 := τ.im_ne_zero
  have hg2 : (0 : ℝ) < g.det.val := hg
  have hpos : (0 : ℝ) < g.det.val * τ.im / ‖denom g τ‖ ^ 2 :=
    div_pos (mul_pos hg2 τ.im_pos) (pow_pos (norm_pos_iff.mpr (denom_ne_zero g τ)) 2)
  rw [ofComplex_apply, det_smulFDerivPos,
    abs_of_nonneg (show (0 : ℝ) ≤ g.val.det ^ 2 / ‖denom g τ‖ ^ 4 by positivity),
    coe_im, coe_im, im_smul_eq_div_normSq, abs_of_pos hg2,
    Complex.normSq_eq_norm_sq, ENNReal.ofReal_eq_coe_nnreal (by positivity)]
  norm_cast
  ext
  simp only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one, NNReal.coe_mk,
    coe_nnnorm, Real.norm_eq_abs, abs_of_pos hpos, abs_of_pos τ.im_pos]
  have hdd : (g.det.val : ℝ) = g.val.det := Matrix.GeneralLinearGroup.val_det_apply g
  simp only [hdd] at hpos ⊢
  field_simp

/-- The measure of `g • s` equals the measure of `s` for `0 < det g` and measurable `s`. -/
lemma volume_smul_of_det_pos {g : GL (Fin 2) ℝ} (hg : 0 < g.val.det) {s : Set ℍ}
    (hs : MeasurableSet s) : volume (g • s) = volume s := by
  rw [volume_eq_lintegral, volume_eq_lintegral, ← Set.image_smul, Set.image_image]
  have hinj : Set.InjOn (fun z ↦ ↑(g • ofComplex z) : ℂ → ℂ) (UpperHalfPlane.coe '' s) :=
    .image_of_comp <| by simp
  have main := MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
      volume (measurableEmbedding_coe.measurableSet_image.mpr hs)
      (Set.forall_mem_image.mpr fun z hz ↦
        (hasStrictFDerivAt_smul_of_det_pos hg _).hasFDerivAt.hasFDerivWithinAt)
      hinj
      (fun z ↦ ↑((1 / ‖z.im‖₊) ^ 2 : NNReal))
  have himg : (fun z ↦ ↑(g • ofComplex z) : ℂ → ℂ) '' (UpperHalfPlane.coe '' s)
      = (fun x : ℍ ↦ (↑(g • x) : ℂ)) '' s := by
    rw [Set.image_image]; simp
  have hpt : ∫⁻ x in UpperHalfPlane.coe '' s,
        ENNReal.ofReal |(smulFDerivPos g x).det| * ↑((1 / ‖(↑(g • ofComplex x) : ℂ).im‖₊) ^ 2 : ℝ≥0)
      = ∫⁻ x in UpperHalfPlane.coe '' s, ↑((1 / ‖x.im‖₊) ^ 2 : ℝ≥0) := by
    apply setLIntegral_congr_fun (measurableEmbedding_coe.measurableSet_image.mpr hs)
    rintro _ ⟨τ, -, rfl⟩
    exact jacobian_density hg τ
  rw [himg, hpt] at main
  exact main

instance : MeasurableConstSMul SL(2, ℤ) ℍ :=
  ⟨fun g ↦ by
    show Measurable fun z : ℍ ↦ (g : GL (Fin 2) ℝ) • z
    exact (continuous_const_smul _).measurable⟩

/-- The measure on the upper half-plane is invariant under `SL(2, ℤ)`. -/
instance : SMulInvariantMeasure SL(2, ℤ) ℍ volume := by
  refine ((smulInvariantMeasure_tfae _ _).out 2 0).mp fun g s hs ↦ ?_
  have hdet : 0 < ((g : GL (Fin 2) ℝ)).val.det := by
    have h1 : ((g : GL (Fin 2) ℝ)).val.det
        = ((Int.castRingHom ℝ).mapMatrix (g : Matrix (Fin 2) (Fin 2) ℤ)).det := rfl
    rw [h1, ← RingHom.map_det, Matrix.SpecialLinearGroup.det_coe]; simp
  exact volume_smul_of_det_pos hdet hs

end UpperHalfPlane

end
