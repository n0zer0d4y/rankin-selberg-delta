import Mathlib

/-!
# The negative index of a symmetric bilinear form

`negIndex B`, the largest dimension of a subspace on which `B` is negative definite, for a bilinear
form on a finite-dimensional real space; one half of Sylvester's law of inertia
(`exists_isNonnegOn_finrank_add_negIndex`); subadditivity (`negIndex_add_le`); and the bounds
`negIndex ≤ 1` for a real pair form and `negIndex ≤ 2` for a Hermitian pair form.
-/

open Module

namespace RankinSelbergDelta.RankinSelberg.NegIndex

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- `B` is negative definite on the subspace `K`. -/
def IsNegDefOn (B : LinearMap.BilinForm ℝ V) (K : Submodule ℝ V) : Prop :=
  ∀ x ∈ K, x ≠ 0 → B x x < 0

/-- `B` is nonnegative on the subspace `P`. -/
def IsNonnegOn (B : LinearMap.BilinForm ℝ V) (P : Submodule ℝ V) : Prop :=
  ∀ x ∈ P, 0 ≤ B x x

/-- The dimensions of the subspaces on which `B` is negative definite. -/
def negDims (B : LinearMap.BilinForm ℝ V) : Set ℕ :=
  (fun K : Submodule ℝ V => finrank ℝ K) '' {K | IsNegDefOn B K}

/-- **The negative index**: the largest dimension of a subspace on which `B` is negative
definite. -/
noncomputable def negIndex (B : LinearMap.BilinForm ℝ V) : ℕ := sSup (negDims B)

lemma isNegDefOn_bot (B : LinearMap.BilinForm ℝ V) : IsNegDefOn B ⊥ := by
  intro x hx hx0
  exact absurd ((Submodule.mem_bot ℝ).1 hx) hx0

lemma negDims_nonempty (B : LinearMap.BilinForm ℝ V) : (negDims B).Nonempty :=
  ⟨finrank ℝ (⊥ : Submodule ℝ V), ⊥, isNegDefOn_bot B, rfl⟩

lemma negDims_bddAbove (B : LinearMap.BilinForm ℝ V) : BddAbove (negDims B) :=
  ⟨finrank ℝ V, by rintro _ ⟨K, -, rfl⟩; exact Submodule.finrank_le K⟩

/-- The negative index is at most the dimension. -/
theorem negIndex_le_finrank (B : LinearMap.BilinForm ℝ V) : negIndex B ≤ finrank ℝ V :=
  csSup_le (negDims_nonempty B) (by rintro _ ⟨K, -, rfl⟩; exact Submodule.finrank_le K)

/-- Every negative-definite subspace has dimension at most the negative index. -/
theorem finrank_le_negIndex {B : LinearMap.BilinForm ℝ V} {K : Submodule ℝ V}
    (hK : IsNegDefOn B K) : finrank ℝ K ≤ negIndex B :=
  le_csSup (negDims_bddAbove B) ⟨K, hK, rfl⟩

/-- The negative index is attained. -/
theorem exists_isNegDefOn_finrank_eq (B : LinearMap.BilinForm ℝ V) :
    ∃ K : Submodule ℝ V, IsNegDefOn B K ∧ finrank ℝ K = negIndex B := by
  obtain ⟨K, hK, h⟩ := Nat.sSup_mem (negDims_nonempty B) (negDims_bddAbove B)
  exact ⟨K, hK, h⟩

/-- A form that is nonnegative everywhere has negative index zero. -/
theorem negIndex_eq_zero_of_isNonnegOn_top {B : LinearMap.BilinForm ℝ V}
    (hB : IsNonnegOn B ⊤) : negIndex B = 0 := by
  apply Nat.le_zero.1
  apply csSup_le (negDims_nonempty B)
  rintro _ ⟨K, hK, rfl⟩
  have hbot : K = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    by_contra h0
    exact absurd (hB x Submodule.mem_top) (not_le.2 (hK x hx h0))
  subst hbot
  simp

/-- A subspace on which `A + B` is negative definite meets trivially the intersection of a
subspace on which `A` is nonnegative with one on which `B` is nonnegative. -/
lemma inf_eq_bot_of_isNegDefOn_add {A B : LinearMap.BilinForm ℝ V} {W PA PB : Submodule ℝ V}
    (hW : IsNegDefOn (A + B) W) (hA : IsNonnegOn A PA) (hB : IsNonnegOn B PB) :
    W ⊓ PA ⊓ PB = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  rw [Submodule.mem_inf, Submodule.mem_inf] at hx
  obtain ⟨⟨hxW, hxA⟩, hxB⟩ := hx
  by_contra h0
  have h1 := hW x hxW h0
  have h2 := hA x hxA
  have h3 := hB x hxB
  simp only [LinearMap.add_apply] at h1
  linarith

lemma finrank_add_le_finrank_inf_add (s t : Submodule ℝ V) :
    finrank ℝ s + finrank ℝ t ≤ finrank ℝ ↥(s ⊓ t) + finrank ℝ V := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq s t
  have h2 := Submodule.finrank_le (s ⊔ t)
  omega

/-- The value of `B` on a combination of pairwise `B`-orthogonal vectors. -/
lemma apply_sum_smul_of_isOrthoᵢ {ι : Type*} [Fintype ι] {B : LinearMap.BilinForm ℝ V}
    {w : ι → V} (hw : B.IsOrthoᵢ w) (c : ι → ℝ) :
    B (∑ i, c i • w i) (∑ i, c i • w i) = ∑ i, c i * c i * B (w i) (w i) := by
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · ring
  · intro j _ hji
    have h0 : B (w i) (w j) = 0 := hw hji.symm
    have h0' : B (w j) (w i) = 0 := hw hji
    simp [h0, h0']
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- **Sylvester, the half we need**: a symmetric form is nonnegative on a subspace of
dimension at least `finrank V − negIndex B`. -/
theorem exists_isNonnegOn_finrank_add_negIndex {B : LinearMap.BilinForm ℝ V} (hB : B.IsSymm) :
    ∃ P : Submodule ℝ V, IsNonnegOn B P ∧ finrank ℝ V ≤ finrank ℝ P + negIndex B := by
  classical
  haveI : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis (K := ℝ) (V := V) (B := B)
    (LinearMap.BilinForm.isSymm_iff.1 hB)
  let p : Fin (finrank ℝ V) → Prop := fun i => 0 ≤ B (v i) (v i)
  let vp : {i // p i} → V := v ∘ Subtype.val
  let vn : {i // ¬ p i} → V := v ∘ Subtype.val
  have hvp : B.IsOrthoᵢ vp := fun i j hij => hv (fun h => hij (Subtype.ext h))
  have hvn : B.IsOrthoᵢ vn := fun i j hij => hv (fun h => hij (Subtype.ext h))
  have hlp : LinearIndependent ℝ vp := v.linearIndependent.comp _ Subtype.val_injective
  have hln : LinearIndependent ℝ vn := v.linearIndependent.comp _ Subtype.val_injective
  refine ⟨Submodule.span ℝ (Set.range vp), ?_, ?_⟩
  · intro x hx
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hx
    rw [apply_sum_smul_of_isOrthoᵢ hvp]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (mul_self_nonneg _) i.2
  · have hK : IsNegDefOn B (Submodule.span ℝ (Set.range vn)) := by
      intro x hx hx0
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hx
      rw [apply_sum_smul_of_isOrthoᵢ hvn]
      have hne : ∃ i, c i ≠ 0 := by
        by_contra h
        push_neg at h
        apply hx0
        simp [h]
      obtain ⟨i₀, hi₀⟩ := hne
      have hneg : ∀ i : {i // ¬ p i}, B (vn i) (vn i) < 0 := fun i => not_le.1 i.2
      calc ∑ i, c i * c i * B (vn i) (vn i) < ∑ _i : {i // ¬ p i}, (0 : ℝ) := by
            apply Finset.sum_lt_sum
            · intro i _
              exact mul_nonpos_of_nonneg_of_nonpos (mul_self_nonneg _) (hneg i).le
            · exact ⟨i₀, Finset.mem_univ _,
                mul_neg_of_pos_of_neg (mul_self_pos.2 hi₀) (hneg i₀)⟩
        _ = 0 := by simp
    have h1 := finrank_le_negIndex hK
    rw [finrank_span_eq_card hln] at h1
    rw [finrank_span_eq_card hlp]
    have hcard := Fintype.card_subtype_compl p
    have hle := Fintype.card_subtype_le p
    simp only [Fintype.card_fin] at hcard hle
    omega

/-- **Subadditivity of the negative index.** -/
theorem negIndex_add_le {A B : LinearMap.BilinForm ℝ V} (hA : A.IsSymm) (hB : B.IsSymm) :
    negIndex (A + B) ≤ negIndex A + negIndex B := by
  obtain ⟨W, hW, hWdim⟩ := exists_isNegDefOn_finrank_eq (A + B)
  obtain ⟨PA, hPA, hPAdim⟩ := exists_isNonnegOn_finrank_add_negIndex hA
  obtain ⟨PB, hPB, hPBdim⟩ := exists_isNonnegOn_finrank_add_negIndex hB
  have hbot := inf_eq_bot_of_isNegDefOn_add hW hPA hPB
  have h0 : finrank ℝ ↥(W ⊓ PA ⊓ PB) = 0 := by
    rw [hbot]
    simp
  have h1 := finrank_add_le_finrank_inf_add W PA
  have h2 := finrank_add_le_finrank_inf_add (W ⊓ PA) PB
  omega

lemma isSymm_sum {ι : Type*} (s : Finset ι) (Bf : ι → LinearMap.BilinForm ℝ V)
    (hs : ∀ i ∈ s, (Bf i).IsSymm) : (∑ i ∈ s, Bf i).IsSymm := by
  rw [LinearMap.BilinForm.isSymm_def]
  intro x y
  simp only [LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun i hi => (hs i hi).eq x y

/-- Subadditivity over a finite sum of symmetric forms. -/
theorem negIndex_sum_le {ι : Type*} (s : Finset ι) (Bf : ι → LinearMap.BilinForm ℝ V)
    (hs : ∀ i ∈ s, (Bf i).IsSymm) :
    negIndex (∑ i ∈ s, Bf i) ≤ ∑ i ∈ s, negIndex (Bf i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact (negIndex_eq_zero_of_isNonnegOn_top fun x _ => by simp).le
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hsum : (∑ i ∈ s, Bf i).IsSymm :=
      isSymm_sum s Bf fun i hi => hs i (Finset.mem_insert_of_mem hi)
    have ih' := ih fun i hi => hs i (Finset.mem_insert_of_mem hi)
    exact (negIndex_add_le (hs a (Finset.mem_insert_self a s)) hsum).trans
      (Nat.add_le_add_left ih' _)

/-- If a linear map `f` is nonzero on every vector where `B` is negative, the negative index is
bounded by the dimension of the target. -/
theorem negIndex_le_finrank_of_ne_zero {W : Type*} [AddCommGroup W] [Module ℝ W]
    [FiniteDimensional ℝ W] (B : LinearMap.BilinForm ℝ V) (f : V →ₗ[ℝ] W)
    (hf : ∀ x, B x x < 0 → f x ≠ 0) : negIndex B ≤ finrank ℝ W := by
  obtain ⟨K, hK, hdim⟩ := exists_isNegDefOn_finrank_eq B
  rw [← hdim]
  have hinj : Function.Injective (f.domRestrict K) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra h0
    have hx0 : (x : V) ≠ 0 := fun h => h0 (Subtype.ext h)
    exact hf x (hK x x.2 hx0) hx
  exact LinearMap.finrank_le_finrank_of_injective hinj

/-- The real pair form `(x, y) ↦ a x · b y + b x · a y`. -/
noncomputable def pairForm (a b : V →ₗ[ℝ] ℝ) : LinearMap.BilinForm ℝ V :=
  a.smulRight b + b.smulRight a

@[simp] lemma pairForm_apply (a b : V →ₗ[ℝ] ℝ) (x y : V) :
    pairForm a b x y = a x * b y + b x * a y := by
  simp [pairForm]

lemma pairForm_isSymm (a b : V →ₗ[ℝ] ℝ) : (pairForm a b).IsSymm := by
  rw [LinearMap.BilinForm.isSymm_def]
  intro x y
  simp only [pairForm_apply]
  ring

lemma smul_pairForm_isSymm (a b : V →ₗ[ℝ] ℝ) (w : ℝ) : (w • pairForm a b).IsSymm := by
  rw [LinearMap.BilinForm.isSymm_def]
  intro x y
  simp only [LinearMap.smul_apply, pairForm_apply, smul_eq_mul]
  ring

/-- **The pair lemma, real version**: a weighted pair form `w • (a x b y + b x a y)`, `w ≥ 0`,
has negative index at most one (its negative part is the single square `w (a − b)²`). -/
theorem negIndex_smul_pairForm_le_one (a b : V →ₗ[ℝ] ℝ) {w : ℝ} (hw : 0 ≤ w) :
    negIndex (w • pairForm a b) ≤ 1 := by
  have h := negIndex_le_finrank_of_ne_zero (w • pairForm a b) (a - b) ?_
  · simpa using h
  · intro x hx hzero
    rw [LinearMap.sub_apply, sub_eq_zero] at hzero
    rw [LinearMap.smul_apply, LinearMap.smul_apply, pairForm_apply, hzero, smul_eq_mul] at hx
    have : 0 ≤ w * (b x * b x + b x * b x) :=
      mul_nonneg hw (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))
    linarith

theorem negIndex_pairForm_le_one (a b : V →ₗ[ℝ] ℝ) : negIndex (pairForm a b) ≤ 1 := by
  simpa using negIndex_smul_pairForm_le_one a b zero_le_one

/-- `(x, y) ↦ Re (ℓ₁ x · conj (ℓ₂ y))` as a real bilinear form. -/
noncomputable def hermTerm (ℓ₁ ℓ₂ : V →ₗ[ℝ] ℂ) : LinearMap.BilinForm ℝ V :=
  (Complex.reLm ∘ₗ ℓ₁).smulRight (Complex.reLm ∘ₗ ℓ₂)
    + (Complex.imLm ∘ₗ ℓ₁).smulRight (Complex.imLm ∘ₗ ℓ₂)

@[simp] lemma hermTerm_apply (ℓ₁ ℓ₂ : V →ₗ[ℝ] ℂ) (x y : V) :
    hermTerm ℓ₁ ℓ₂ x y = (ℓ₁ x * (starRingEnd ℂ) (ℓ₂ y)).re := by
  simp only [hermTerm, LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, Complex.reLm_coe, Complex.imLm_coe, smul_eq_mul, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  ring

/-- The diagonal term `Re (ℓ x · conj (ℓ y)) = Re (ℓ x) Re (ℓ y) + Im (ℓ x) Im (ℓ y)` is
symmetric and nonnegative: this is the contribution of a zero ON the line. -/
lemma hermTerm_self_isSymm (ℓ : V →ₗ[ℝ] ℂ) : (hermTerm ℓ ℓ).IsSymm := by
  rw [LinearMap.BilinForm.isSymm_def]
  intro x y
  simp only [hermTerm_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

lemma hermTerm_self_nonneg (ℓ : V →ₗ[ℝ] ℂ) (x : V) : 0 ≤ hermTerm ℓ ℓ x x := by
  simp only [hermTerm_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im, mul_neg,
    sub_neg_eq_add]
  nlinarith [mul_self_nonneg (ℓ x).re, mul_self_nonneg (ℓ x).im]

/-- The symmetrized pair `Re (ℓ₁ x conj (ℓ₂ y)) + Re (ℓ₂ x conj (ℓ₁ y))` is the sum of two real
pair forms, one for the real parts and one for the imaginary parts. -/
lemma hermTerm_add_hermTerm (ℓ₁ ℓ₂ : V →ₗ[ℝ] ℂ) :
    hermTerm ℓ₁ ℓ₂ + hermTerm ℓ₂ ℓ₁
      = pairForm (Complex.reLm ∘ₗ ℓ₁) (Complex.reLm ∘ₗ ℓ₂)
        + pairForm (Complex.imLm ∘ₗ ℓ₁) (Complex.imLm ∘ₗ ℓ₂) := by
  ext x y
  simp only [LinearMap.add_apply, hermTerm_apply, pairForm_apply, LinearMap.comp_apply,
    Complex.reLm_coe, Complex.imLm_coe, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

lemma hermPair_isSymm (ℓ₁ ℓ₂ : V →ₗ[ℝ] ℂ) : (hermTerm ℓ₁ ℓ₂ + hermTerm ℓ₂ ℓ₁).IsSymm := by
  rw [hermTerm_add_hermTerm, LinearMap.BilinForm.isSymm_def]
  intro x y
  simp only [LinearMap.add_apply, pairForm_apply]
  ring

/-- **The pair lemma, complex version**: an off-line pair `{ρ, 1 − conj ρ}` contributes the real
form `w • (Re (ℓ₁ x conj (ℓ₂ y)) + Re (ℓ₂ x conj (ℓ₁ y)))`, `w ≥ 0`, whose REAL negative index is
at most two (= one complex dimension). -/
theorem negIndex_smul_hermPair_le_two (ℓ₁ ℓ₂ : V →ₗ[ℝ] ℂ) {w : ℝ} (hw : 0 ≤ w) :
    negIndex (w • (hermTerm ℓ₁ ℓ₂ + hermTerm ℓ₂ ℓ₁)) ≤ 2 := by
  rw [hermTerm_add_hermTerm, smul_add]
  have h := negIndex_add_le
    (smul_pairForm_isSymm (Complex.reLm ∘ₗ ℓ₁) (Complex.reLm ∘ₗ ℓ₂) w)
    (smul_pairForm_isSymm (Complex.imLm ∘ₗ ℓ₁) (Complex.imLm ∘ₗ ℓ₂) w)
  have h1 := negIndex_smul_pairForm_le_one (Complex.reLm ∘ₗ ℓ₁) (Complex.reLm ∘ₗ ℓ₂) hw
  have h2 := negIndex_smul_pairForm_le_one (Complex.imLm ∘ₗ ℓ₁) (Complex.imLm ∘ₗ ℓ₂) hw
  omega

theorem negIndex_hermPair_le_two (ℓ₁ ℓ₂ : V →ₗ[ℝ] ℂ) :
    negIndex (hermTerm ℓ₁ ℓ₂ + hermTerm ℓ₂ ℓ₁) ≤ 2 := by
  simpa using negIndex_smul_hermPair_le_two ℓ₁ ℓ₂ zero_le_one

/-- The involution `ρ ↦ 1 − conj ρ` of the functional equation; its fixed points are the
critical line `Re ρ = 1/2`. -/
def refl (ρ : ℂ) : ℂ := 1 - (starRingEnd ℂ) ρ

lemma refl_refl (ρ : ℂ) : refl (refl ρ) = ρ := by
  unfold refl
  simp

lemma refl_injective : Function.Injective refl := by
  intro a b h
  have := congrArg refl h
  rwa [refl_refl, refl_refl] at this

lemma refl_eq_self_iff (ρ : ℂ) : refl ρ = ρ ↔ ρ.re = 1 / 2 := by
  unfold refl
  constructor
  · intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  · intro h
    apply Complex.ext
    · simp
      linarith
    · simp

/-- **The self-dual zero-sum form** over a finite set `Z` of zeros with multiplicities `w`:
`(x, y) ↦ Σ_{ρ ∈ Z} w ρ · Re (φ ρ x · conj (φ (1 − conj ρ) y))`, the real part of
`Σ_ρ D ρ · ĥ(ρ)` with `ĥ(ρ) = ĝ(ρ) · conj ĝ(1 − conj ρ)` (`WeilForm.ghat_selfDual_eq`),
where `φ s` is the real-linear map `g ↦ ĝ(s)` on the finite-dimensional test space. -/
noncomputable def zeroSumForm (φ : ℂ → V →ₗ[ℝ] ℂ) (w : ℂ → ℝ) (Z : Finset ℂ) :
    LinearMap.BilinForm ℝ V :=
  ∑ ρ ∈ Z, w ρ • hermTerm (φ ρ) (φ (refl ρ))

/-- Splitting the zero sum into the zeros on the line, a set `R` of representatives of the
off-line pairs, and their reflections. -/
theorem zeroSumForm_split (φ : ℂ → V →ₗ[ℝ] ℂ) (w : ℂ → ℝ) (Zon R : Finset ℂ)
    (hon : ∀ ρ ∈ Zon, refl ρ = ρ) (hRw : ∀ ρ ∈ R, w (refl ρ) = w ρ)
    (h₁ : Disjoint R (R.image refl)) (h₂ : Disjoint Zon (R ∪ R.image refl)) :
    zeroSumForm φ w (Zon ∪ (R ∪ R.image refl))
      = (∑ ρ ∈ Zon, w ρ • hermTerm (φ ρ) (φ ρ))
        + ∑ ρ ∈ R, w ρ • (hermTerm (φ ρ) (φ (refl ρ)) + hermTerm (φ (refl ρ)) (φ ρ)) := by
  unfold zeroSumForm
  rw [Finset.sum_union h₂, Finset.sum_union h₁,
    Finset.sum_image (fun x _ y _ h => refl_injective h), ← Finset.sum_add_distrib]
  congr 1
  · exact Finset.sum_congr rfl fun ρ hρ => by rw [hon ρ hρ]
  · exact Finset.sum_congr rfl fun ρ hρ => by rw [refl_refl, hRw ρ hρ, smul_add]

/-- **Rank control of the negative eigenspace ().** With nonnegative multiplicities `w`
symmetric under the functional equation, the self-dual zero-sum form over the zeros on the
line together with the off-line pairs represented by `R` has real negative index at most
`2 · #R`: one complex dimension per off-line pair, none per zero on the line, uniformly in the
test space. -/
theorem negIndex_zeroSumForm_le (φ : ℂ → V →ₗ[ℝ] ℂ) (w : ℂ → ℝ) (hw : ∀ ρ, 0 ≤ w ρ)
    (Zon R : Finset ℂ) (hon : ∀ ρ ∈ Zon, refl ρ = ρ) (hRw : ∀ ρ ∈ R, w (refl ρ) = w ρ)
    (h₁ : Disjoint R (R.image refl)) (h₂ : Disjoint Zon (R ∪ R.image refl)) :
    negIndex (zeroSumForm φ w (Zon ∪ (R ∪ R.image refl))) ≤ 2 * R.card := by
  rw [zeroSumForm_split φ w Zon R hon hRw h₁ h₂]
  have hon_symm : ∀ ρ ∈ Zon, (w ρ • hermTerm (φ ρ) (φ ρ)).IsSymm := fun ρ _ => by
    rw [LinearMap.BilinForm.isSymm_def]
    intro x y
    simp only [LinearMap.smul_apply, smul_eq_mul, (hermTerm_self_isSymm (φ ρ)).eq x y]
  have hpair_symm : ∀ ρ ∈ R,
      (w ρ • (hermTerm (φ ρ) (φ (refl ρ)) + hermTerm (φ (refl ρ)) (φ ρ))).IsSymm :=
    fun ρ _ => by
      rw [LinearMap.BilinForm.isSymm_def]
      intro x y
      simp only [LinearMap.smul_apply, smul_eq_mul,
        (hermPair_isSymm (φ ρ) (φ (refl ρ))).eq x y]
  have hA : negIndex (∑ ρ ∈ Zon, w ρ • hermTerm (φ ρ) (φ ρ)) = 0 := by
    apply negIndex_eq_zero_of_isNonnegOn_top
    intro x _
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    exact Finset.sum_nonneg fun ρ _ => mul_nonneg (hw ρ) (hermTerm_self_nonneg (φ ρ) x)
  have hB : negIndex (∑ ρ ∈ R,
      w ρ • (hermTerm (φ ρ) (φ (refl ρ)) + hermTerm (φ (refl ρ)) (φ ρ))) ≤ 2 * R.card := by
    refine (negIndex_sum_le R _ hpair_symm).trans ?_
    calc ∑ ρ ∈ R, negIndex (w ρ • (hermTerm (φ ρ) (φ (refl ρ)) + hermTerm (φ (refl ρ)) (φ ρ)))
        ≤ ∑ _ρ ∈ R, 2 :=
          Finset.sum_le_sum fun ρ _ => negIndex_smul_hermPair_le_two _ _ (hw ρ)
      _ = 2 * R.card := by simp [mul_comm]
  have hsymA := isSymm_sum Zon _ hon_symm
  have hsymB := isSymm_sum R _ hpair_symm
  have := negIndex_add_le hsymA hsymB
  omega

/-- Satisfiability witness: the statements are not vacuous. On `V = ℝ`, with the zero family
`φ`, `w = 1`, `Zon = {1/2}` and `R = {1}` (the off-line pair `{1, 0}`), every hypothesis of
`negIndex_zeroSumForm_le` holds and `R` is nonempty. -/
example : ∃ (φ : ℂ → ℝ →ₗ[ℝ] ℂ) (w : ℂ → ℝ) (Zon R : Finset ℂ),
    (∀ ρ, 0 ≤ w ρ) ∧ (∀ ρ ∈ Zon, refl ρ = ρ) ∧ (∀ ρ ∈ R, w (refl ρ) = w ρ) ∧
    Disjoint R (R.image refl) ∧ Disjoint Zon (R ∪ R.image refl) ∧ R.card = 1 := by
  refine ⟨fun _ => 0, fun _ => 1, {1 / 2}, {1}, fun _ => zero_le_one, ?_, fun _ _ => rfl,
    ?_, ?_, Finset.card_singleton _⟩
  · intro ρ hρ
    rw [Finset.mem_singleton] at hρ
    subst hρ
    rw [refl_eq_self_iff]
    norm_num
  · rw [Finset.image_singleton, Finset.disjoint_singleton]
    norm_num [refl]
  · rw [Finset.image_singleton, Finset.disjoint_singleton_left]
    norm_num [refl]

end RankinSelbergDelta.RankinSelberg.NegIndex
