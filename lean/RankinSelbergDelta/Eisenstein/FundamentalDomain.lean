import RankinSelbergDelta.Eisenstein.HyperbolicMeasure

/-!
# Fundamental domains for the unfolding

Since `−1` acts trivially, `ModularGroup.fd` is a fundamental domain for `PSL(2, ℤ)`, not for
`SL(2, ℤ)`. This file proves `isFundamentalDomain_fd : IsFundamentalDomain PSL2Z 𝒟 volume` for the
invariant measure, and `isAddFundamentalDomain_strip` for the strip `0 ≤ Re z < 1` under integer
translations, together with the measurability of `𝒟` and the nullity of its boundary.
-/

namespace RankinSelbergDelta.Eisenstein

open UpperHalfPlane MeasureTheory ModularGroup Set
open scoped MatrixGroups Pointwise Modular

noncomputable section

/-- The kernel of the action of `SL(2, ℤ)` on `ℍ`; it is `{1, -1}`. -/
abbrev slKer : Subgroup SL(2, ℤ) := (MulAction.toPermHom SL(2, ℤ) ℍ).ker

lemma mem_slKer_iff {g : SL(2, ℤ)} : g ∈ slKer ↔ ∀ z : ℍ, g • z = z := by
  rw [slKer, MonoidHom.mem_ker, Equiv.ext_iff]
  exact Iff.rfl

lemma neg_one_mem_slKer : (-1 : SL(2, ℤ)) ∈ slKer := by
  rw [mem_slKer_iff]
  intro z
  simp

/-- `PSL(2, ℤ)`, as the quotient of `SL(2, ℤ)` by the kernel of its action on `ℍ`. -/
abbrev PSL2Z : Type := SL(2, ℤ) ⧸ slKer

/-- The (faithful) action of `PSL2Z` on `ℍ`. -/
instance : MulAction PSL2Z ℍ :=
  MulAction.compHom ℍ (QuotientGroup.kerLift (MulAction.toPermHom SL(2, ℤ) ℍ))

@[simp] lemma mk_smul (g : SL(2, ℤ)) (z : ℍ) : (QuotientGroup.mk g : PSL2Z) • z = g • z := rfl

lemma mk_eq_one_iff {g : SL(2, ℤ)} : (QuotientGroup.mk g : PSL2Z) = 1 ↔ ∀ z : ℍ, g • z = z := by
  rw [QuotientGroup.eq_one_iff, mem_slKer_iff]

instance : MeasurableConstSMul PSL2Z ℍ :=
  ⟨fun c ↦ by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    show Measurable fun z : ℍ ↦ g • z
    exact measurable_const_smul g⟩

instance : SMulInvariantMeasure PSL2Z ℍ volume :=
  ⟨fun c s hs ↦ by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    show volume ((fun z : ℍ ↦ g • z) ⁻¹' s) = volume s
    exact SMulInvariantMeasure.measure_preimage_smul (μ := (volume : Measure ℍ)) g hs⟩

/-! ### The closed fundamental domain `𝒟` -/

lemma isClosed_fd : IsClosed (𝒟 : Set ℍ) := by
  have h1 : IsClosed {z : ℍ | 1 ≤ Complex.normSq (z : ℂ)} :=
    isClosed_le continuous_const (Complex.continuous_normSq.comp continuous_coe)
  have h2 : IsClosed {z : ℍ | |z.re| ≤ (1 : ℝ) / 2} :=
    isClosed_le (continuous_abs.comp continuous_re) continuous_const
  exact h1.inter h2

lemma measurableSet_fd : MeasurableSet (𝒟 : Set ℍ) := isClosed_fd.measurableSet

/-- The unit circle in `ℍ` is null. -/
lemma volume_normSq_eq_one : volume {z : ℍ | Complex.normSq (z : ℂ) = 1} = 0 := by
  refine withDensity_absolutelyContinuous _ _ ?_
  rw [measurableEmbedding_coe.comap_apply]
  refine measure_mono_null ?_ (Measure.addHaar_sphere volume (0 : ℂ) 1)
  rintro _ ⟨z, hz, rfl⟩
  have h2 : ‖(z : ℂ)‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq]; exact hz
  have h0 : 0 ≤ ‖(z : ℂ)‖ := norm_nonneg _
  rw [Metric.mem_sphere, dist_zero_right]
  nlinarith [h2, h0]

/-- A vertical line in `ℍ` is null. -/
lemma volume_re_eq (c : ℝ) : volume {z : ℍ | z.re = c} = 0 := by
  refine withDensity_absolutelyContinuous _ _ ?_
  rw [measurableEmbedding_coe.comap_apply]
  refine measure_mono_null (t := {w : ℂ | w.re = c}) ?_ ?_
  · rintro _ ⟨z, hz, rfl⟩
    exact hz
  · have hset : {w : ℂ | w.re = c} = Complex.measurableEquivRealProd ⁻¹' ({c} ×ˢ Set.univ) := by
      ext w
      simp [Complex.measurableEquivRealProd]
    rw [hset, Complex.volume_preserving_equiv_real_prod.measure_preimage
      ((measurableSet_singleton c).prod MeasurableSet.univ).nullMeasurableSet,
      Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]

lemma fd_diff_fdo_subset :
    (𝒟 \ 𝒟ᵒ : Set ℍ) ⊆ {z | Complex.normSq (z : ℂ) = 1}
      ∪ ({z | z.re = 1 / 2} ∪ {z | z.re = -(1 / 2)}) := by
  rintro z ⟨⟨h1, h2⟩, h3⟩
  simp only [fdo, Set.mem_setOf_eq, not_and_or, not_lt] at h3
  rcases h3 with h3 | h3
  · left
    exact le_antisymm h3 h1
  · right
    rcases abs_le.mp h2 with ⟨hl, hr⟩
    rcases le_or_gt 0 z.re with h0 | h0
    · left
      rw [abs_of_nonneg h0] at h3
      show z.re = 1 / 2
      linarith
    · right
      rw [abs_of_neg h0] at h3
      show z.re = -(1 / 2)
      linarith

/-- The boundary of the fundamental domain is null. -/
lemma volume_fd_diff_fdo : volume (𝒟 \ 𝒟ᵒ : Set ℍ) = 0 :=
  measure_mono_null fd_diff_fdo_subset
    (measure_union_null volume_normSq_eq_one
      (measure_union_null (volume_re_eq _) (volume_re_eq _)))

/-- For `g` not in the kernel, `g • 𝒟` meets `𝒟` only along the boundary. -/
lemma smul_fd_inter_fd_subset {g : SL(2, ℤ)} (hg : g ∉ slKer) :
    (g • 𝒟 ∩ 𝒟 : Set ℍ) ⊆ g • (𝒟 \ 𝒟ᵒ) ∪ (𝒟 \ 𝒟ᵒ) := by
  rintro z ⟨⟨w, hw, rfl⟩, hz⟩
  by_cases hw' : w ∈ 𝒟ᵒ
  · by_cases hz' : g • w ∈ 𝒟ᵒ
    · exfalso
      apply hg
      rw [mem_slKer_iff]
      obtain ⟨n, hn⟩ := exists_eq_T_zpow_of_c_eq_zero (c_eq_zero hw' hz')
      have hn0 : n = 0 :=
        eq_zero_of_mem_fdo_of_T_zpow_mem_fdo hw' (by rw [← hn w]; exact hz')
      intro y
      rw [hn y, hn0, zpow_zero, one_smul]
    · right
      exact ⟨hz, hz'⟩
  · left
    exact ⟨w, ⟨hw, hw'⟩, rfl⟩

lemma aedisjoint_smul_fd {c : PSL2Z} (hc : c ≠ 1) : AEDisjoint volume (c • 𝒟 : Set ℍ) 𝒟 := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
  have hg : g ∉ slKer := fun h ↦ hc ((QuotientGroup.eq_one_iff g).mpr h)
  have hsub : ((QuotientGroup.mk g : PSL2Z) • 𝒟 ∩ 𝒟 : Set ℍ) ⊆ g • (𝒟 \ 𝒟ᵒ) ∪ (𝒟 \ 𝒟ᵒ) := by
    rw [show ((QuotientGroup.mk g : PSL2Z) • 𝒟 : Set ℍ) = g • 𝒟 from rfl]
    exact smul_fd_inter_fd_subset hg
  exact measure_mono_null hsub
    (measure_union_null (by rw [measure_smul]; exact volume_fd_diff_fdo) volume_fd_diff_fdo)

/-- **`𝒟` is a fundamental domain for `PSL(2, ℤ)`.** -/
theorem isFundamentalDomain_fd : IsFundamentalDomain PSL2Z (𝒟 : Set ℍ) volume := by
  refine IsFundamentalDomain.mk'' measurableSet_fd.nullMeasurableSet ?_
    (fun c hc ↦ aedisjoint_smul_fd hc)
    (fun c ↦ (measurePreserving_smul c volume).quasiMeasurePreserving)
  refine Filter.Eventually.of_forall fun z ↦ ?_
  obtain ⟨g, hg⟩ := exists_smul_mem_fd z
  exact ⟨QuotientGroup.mk g, hg⟩

/-! ### The strip, a fundamental domain for the translations -/

/-- `ℤ` acts on `ℍ` by translation, `n +ᵥ z = z + n`. -/
instance : AddAction ℤ ℍ := AddAction.compHom ℍ (Int.castAddHom ℝ)

lemma int_vadd_def (n : ℤ) (z : ℍ) : n +ᵥ z = (n : ℝ) +ᵥ z := rfl

lemma int_vadd_eq_T_zpow_smul (n : ℤ) (z : ℍ) : n +ᵥ z = ModularGroup.T ^ n • z := by
  rw [int_vadd_def, modular_T_zpow_smul]

/-- The strip `{0 ≤ re z < 1}`. -/
def strip : Set ℍ := {z | z.re ∈ Set.Ico (0 : ℝ) 1}

lemma measurableSet_strip : MeasurableSet strip :=
  measurableSet_Ico.preimage continuous_re.measurable

instance : MeasurableConstVAdd ℤ ℍ :=
  ⟨fun n ↦ by
    have : (fun z : ℍ ↦ n +ᵥ z) = fun z ↦ ModularGroup.T ^ n • z := by
      funext z; exact int_vadd_eq_T_zpow_smul n z
    rw [this]
    exact measurable_const_smul _⟩

instance : VAddInvariantMeasure ℤ ℍ volume :=
  ⟨fun n s hs ↦ by
    have : (fun z : ℍ ↦ n +ᵥ z) = fun z ↦ ModularGroup.T ^ n • z := by
      funext z; exact int_vadd_eq_T_zpow_smul n z
    rw [this]
    exact SMulInvariantMeasure.measure_preimage_smul (μ := (volume : Measure ℍ))
      (ModularGroup.T ^ n) hs⟩

/-- **The strip is a fundamental domain for the translation action of `ℤ`.** -/
theorem isAddFundamentalDomain_strip : IsAddFundamentalDomain ℤ strip volume := by
  refine IsAddFundamentalDomain.mk' measurableSet_strip.nullMeasurableSet fun z ↦ ?_
  refine ⟨-⌊z.re⌋, ?_, ?_⟩
  · show (-⌊z.re⌋ : ℤ) +ᵥ z ∈ strip
    rw [int_vadd_def]
    simp only [strip, Set.mem_setOf_eq, vadd_re, Int.cast_neg, Set.mem_Ico]
    constructor <;> linarith [Int.floor_le z.re, Int.lt_floor_add_one z.re]
  · intro m hm
    rw [int_vadd_def] at hm
    simp only [strip, Set.mem_setOf_eq, vadd_re, Set.mem_Ico] at hm
    have hfl : ⌊z.re⌋ = -m := by
      rw [Int.floor_eq_iff]
      push_cast
      constructor <;> linarith [hm.1, hm.2]
    rw [hfl, neg_neg]

end

end RankinSelbergDelta.Eisenstein
