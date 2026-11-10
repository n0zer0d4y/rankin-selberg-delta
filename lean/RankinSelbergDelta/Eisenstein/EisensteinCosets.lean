import RankinSelbergDelta.Eisenstein.FundamentalDomain
import RankinSelbergDelta.Eisenstein.EpsteinZeta

/-!
# The coset expansion of the real-analytic Eisenstein series

For `Re s > 1`, `Z_z(s) = 2 ζ(2s) Σ_{Γ_∞ \ PSL₂(ℤ)} Im(γz)^s`, from the Epstein-zeta lattice sum by
the gcd factorisation of lattice points and the bijection between cosets and coprime bottom rows
(`epsteinZeta_eq_zeta_mul_tsum_coprime`, `epsteinZeta_eq_two_zeta_mul_tsum_coset`,
`eisensteinE_eq_tsum_coset`). Also the kernel `{1, −1}` of the action of `SL(2, ℤ)`.
-/

namespace RankinSelbergDelta.Eisenstein

open Complex UpperHalfPlane ModularGroup MeasureTheory Set
open scoped MatrixGroups Modular Pointwise

noncomputable section

/-! ### `slKer = {1, -1}` -/

/-- The point `2i`, an interior point of the fundamental domain. -/
def twoI : ℍ := ⟨2 * Complex.I, by simp⟩

lemma twoI_mem_fdo : twoI ∈ 𝒟ᵒ := by
  refine ⟨?_, ?_⟩
  · show (1 : ℝ) < Complex.normSq (2 * Complex.I)
    rw [Complex.normSq_apply]
    norm_num
  · show |(2 * Complex.I).re| < (1 : ℝ) / 2
    norm_num

lemma det_entries (h : SL(2, ℤ)) : h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1 := by
  have := h.det_coe
  rwa [Matrix.det_fin_two] at this

lemma c_eq_zero_of_mem_slKer {h : SL(2, ℤ)} (hh : h ∈ slKer) : h 1 0 = 0 :=
  c_eq_zero twoI_mem_fdo (by rw [(mem_slKer_iff.mp hh) twoI]; exact twoI_mem_fdo)

/-- The kernel of the action is `{1, -1}`. -/
lemma eq_one_or_neg_one_of_mem_slKer {h : SL(2, ℤ)} (hh : h ∈ slKer) : h = 1 ∨ h = -1 := by
  have hc : h 1 0 = 0 := c_eq_zero_of_mem_slKer hh
  have hdet := det_entries h
  rw [hc, mul_zero, sub_zero] at hdet
  -- `b = 0` from `h • i = i`
  have hI : h • UpperHalfPlane.I = UpperHalfPlane.I := (mem_slKer_iff.mp hh) _
  have hcoe : (((h 0 0 : ℤ) : ℂ) * Complex.I + (h 0 1 : ℤ)) / (((h 1 0 : ℤ) : ℂ) * Complex.I + (h 1 1 : ℤ))
      = Complex.I := by
    have := congrArg (fun w : ℍ => (w : ℂ)) hI
    simpa [UpperHalfPlane.specialLinearGroup_apply, UpperHalfPlane.coe_I] using this
  rw [hc] at hcoe
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨ha, hd⟩ | ⟨ha, hd⟩
  · rw [ha, hd] at hcoe
    have hb : (h 0 1 : ℂ) = 0 := by
      have := hcoe
      push_cast at this
      field_simp at this
      linear_combination this
    have hb' : h 0 1 = 0 := by exact_mod_cast hb
    left
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hb', hc, hd]
  · rw [ha, hd] at hcoe
    have hb : (h 0 1 : ℂ) = 0 := by
      have := hcoe
      push_cast at this
      field_simp at this
      linear_combination this
    have hb' : h 0 1 = 0 := by exact_mod_cast hb
    right
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hb', hc, hd]

lemma neg_one_mem_slKer' : (-1 : SL(2, ℤ)) ∈ slKer := neg_one_mem_slKer

/-! ### Bottom rows and the stabiliser of the cusp in `SL(2, ℤ)` -/

/-- The stabiliser of `∞` in `SL(2, ℤ)`: the powers of `T`. -/
abbrev stabT : Subgroup SL(2, ℤ) := Subgroup.zpowers ModularGroup.T

/-- The bottom row of `g`, as a vector. -/
def bottomRow (g : SL(2, ℤ)) : Fin 2 → ℤ := ![g 1 0, g 1 1]

@[simp] lemma bottomRow_zero (g : SL(2, ℤ)) : bottomRow g 0 = g 1 0 := rfl
@[simp] lemma bottomRow_one (g : SL(2, ℤ)) : bottomRow g 1 = g 1 1 := rfl

lemma isCoprime_bottomRow (g : SL(2, ℤ)) : IsCoprime (g 1 0) (g 1 1) :=
  ⟨-g 0 1, g 0 0, by linear_combination det_entries g⟩

lemma bottomRow_mem_gammaSet (g : SL(2, ℤ)) : bottomRow g ∈ EisensteinSeries.gammaSet 1 1 0 := by
  rw [EisensteinSeries.mem_gammaSet_one, bottomRow_zero, bottomRow_one]
  exact isCoprime_bottomRow g

lemma exists_bottomRow_eq {v : Fin 2 → ℤ} (hv : v ∈ EisensteinSeries.gammaSet 1 1 0) :
    ∃ g : SL(2, ℤ), bottomRow g = v := by
  rw [EisensteinSeries.mem_gammaSet_one] at hv
  obtain ⟨u, w, huw⟩ := hv
  refine ⟨⟨!![w, -u; v 0, v 1], ?_⟩, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination huw
  · ext i
    fin_cases i <;> simp [bottomRow]

lemma bottomRow_T_zpow_mul (n : ℤ) (g : SL(2, ℤ)) :
    bottomRow (ModularGroup.T ^ n * g) = bottomRow g := by
  ext i
  fin_cases i <;> simp [bottomRow]

lemma eq_T_zpow_of_row {h : SL(2, ℤ)} (hc : h 1 0 = 0) (hd : h 1 1 = 1) :
    h = ModularGroup.T ^ (h 0 1) := by
  have hdet := det_entries h
  rw [hc, hd] at hdet
  have ha : h 0 0 = 1 := by linarith
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ModularGroup.coe_T_zpow, ha, hc, hd]

lemma mul_inv_mem_stabT_of_bottomRow_eq {g g' : SL(2, ℤ)} (h : bottomRow g = bottomRow g') :
    g' * g⁻¹ ∈ stabT := by
  have h0 : g' 1 0 = g 1 0 := by
    have := congrFun h 0; simp only [bottomRow_zero] at this; exact this.symm
  have h1 : g' 1 1 = g 1 1 := by
    have := congrFun h 1; simp only [bottomRow_one] at this; exact this.symm
  have hdet := det_entries g
  have hc : (g' * g⁻¹) 1 0 = 0 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.SL2_inv_expl,
      Matrix.mul_apply, Fin.sum_univ_two, h0, h1]
    ring
  have hd : (g' * g⁻¹) 1 1 = 1 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.SL2_inv_expl,
      Matrix.mul_apply, Fin.sum_univ_two, h0, h1]
    linear_combination hdet
  rw [eq_T_zpow_of_row hc hd]
  exact Subgroup.mem_zpowers_iff.mpr ⟨_, rfl⟩

lemma bottomRow_eq_of_mem_stabT {g g' : SL(2, ℤ)} (h : g' * g⁻¹ ∈ stabT) :
    bottomRow g' = bottomRow g := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h
  have : g' = ModularGroup.T ^ n * g := by rw [hn, inv_mul_cancel_right]
  rw [this, bottomRow_T_zpow_mul]

/-- Right cosets `⟨T⟩ \ SL(2, ℤ)`. -/
abbrev CosetSL : Type := Quotient (QuotientGroup.rightRel stabT)

/-- The bottom row of a right coset. -/
def rowOfCoset : CosetSL → EisensteinSeries.gammaSet 1 1 0 :=
  Quotient.lift (fun g : SL(2, ℤ) => ⟨bottomRow g, bottomRow_mem_gammaSet g⟩)
    (fun a b hab => by
      have hab' : b * a⁻¹ ∈ stabT := QuotientGroup.rightRel_apply.mp hab
      exact Subtype.ext (bottomRow_eq_of_mem_stabT hab').symm)

lemma rowOfCoset_mk (g : SL(2, ℤ)) :
    rowOfCoset (Quotient.mk (QuotientGroup.rightRel stabT) g) = ⟨bottomRow g, bottomRow_mem_gammaSet g⟩ :=
  rfl

lemma rowOfCoset_bijective : Function.Bijective rowOfCoset := by
  constructor
  · intro a b hab
    induction a using Quotient.inductionOn with
    | h g =>
      induction b using Quotient.inductionOn with
      | h g' =>
        apply Quotient.sound
        refine QuotientGroup.rightRel_apply.mpr (mul_inv_mem_stabT_of_bottomRow_eq ?_)
        have := congrArg Subtype.val hab
        simpa [rowOfCoset_mk] using this
  · intro v
    obtain ⟨g, hg⟩ := exists_bottomRow_eq v.2
    exact ⟨Quotient.mk _ g, Subtype.ext (by rw [rowOfCoset_mk]; exact hg)⟩

/-- `⟨T⟩ \ SL(2, ℤ) ≃` coprime pairs, by the bottom row. -/
def cosetRowEquiv : CosetSL ≃ EisensteinSeries.gammaSet 1 1 0 :=
  Equiv.ofBijective rowOfCoset rowOfCoset_bijective

/-! ### `Im (g • z)` depends only on the bottom row, and equals `Q_z(c, d)⁻¹` -/

lemma Qform_bottomRow (z : ℍ) (g : SL(2, ℤ)) :
    Qform z (g 1 0) (g 1 1) = ((g • z).im)⁻¹ := by
  rw [ModularGroup.im_smul_eq_div_normSq, inv_div, Qform, Complex.normSq_eq_norm_sq,
    ModularGroup.denom_apply]

lemma cpow_Qform_bottomRow (z : ℍ) (g : SL(2, ℤ)) (s : ℂ) :
    ((Qform z (g 1 0) (g 1 1) : ℝ) : ℂ) ^ (-s) = (((g • z).im : ℝ) : ℂ) ^ s := by
  rw [Qform_bottomRow, Complex.ofReal_inv, Complex.inv_cpow _ _ ?_, Complex.cpow_neg, inv_inv]
  rw [Complex.arg_ofReal_of_nonneg (g • z).im_pos.le]
  exact Real.pi_ne_zero.symm

lemma im_T_zpow_mul_smul (n : ℤ) (g : SL(2, ℤ)) (z : ℍ) :
    ((ModularGroup.T ^ n * g) • z).im = (g • z).im := by
  rw [mul_smul, modular_T_zpow_smul, vadd_im]

/-- The Eisenstein summand on a right coset: `(Im (g • z))^s`. -/
def eisTermSL (z : ℍ) (s : ℂ) : CosetSL → ℂ :=
  Quotient.lift (fun g : SL(2, ℤ) => (((g • z).im : ℝ) : ℂ) ^ s)
    (fun a b hab => by
      have hab' : b * a⁻¹ ∈ stabT := QuotientGroup.rightRel_apply.mp hab
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hab'
      have : b = ModularGroup.T ^ n * a := by rw [hn, inv_mul_cancel_right]
      simp only [this, im_T_zpow_mul_smul])

lemma eisTermSL_mk (z : ℍ) (s : ℂ) (g : SL(2, ℤ)) :
    eisTermSL z s (Quotient.mk (QuotientGroup.rightRel stabT) g) = (((g • z).im : ℝ) : ℂ) ^ s :=
  rfl

/-! ### The lattice sum over `Fin 2 → ℤ` and its gcd factorisation -/

/-- The summand `Q_z(v)^{-s}` on all of `Fin 2 → ℤ` (it vanishes at `v = 0` for `s ≠ 0`). -/
def latTerm (z : ℍ) (s : ℂ) (v : Fin 2 → ℤ) : ℂ := ((Qform z (v 0) (v 1) : ℝ) : ℂ) ^ (-s)

lemma latTerm_zero (z : ℍ) {s : ℂ} (hs : s ≠ 0) : latTerm z s 0 = 0 := by
  simp [latTerm, Qform_zero, Complex.zero_cpow (neg_ne_zero.mpr hs)]

lemma Qform_smul (z : ℍ) (r : ℤ) (m n : ℤ) :
    Qform z (r * m) (r * n) = (r : ℝ) ^ 2 * Qform z m n := by
  rw [Qform_eq, Qform_eq]
  push_cast
  ring

lemma latTerm_smul (z : ℍ) (s : ℂ) (r : ℕ) (v : Fin 2 → ℤ) :
    latTerm z s ((r : ℤ) • v) = ((r : ℂ) ^ (-s)) ^ 2 * latTerm z s v := by
  simp only [latTerm, Pi.smul_apply, smul_eq_mul, Qform_smul]
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) (Qform_nonneg z _ _),
    show ((r : ℤ) : ℝ) ^ 2 = ((r : ℤ) : ℝ) * ((r : ℤ) : ℝ) by ring, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
  push_cast
  ring

/-- Summability of the lattice sum, from the `summable_Qform_neg_rpow`. -/
lemma summable_latTerm (z : ℍ) {s : ℂ} (hs : 1 < s.re) : Summable (latTerm z s) := by
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have hsub : Summable fun p : {p : ℤ × ℤ // p ≠ 0} =>
      ((Qform z (p : ℤ × ℤ).1 (p : ℤ × ℤ).2 : ℝ) : ℂ) ^ (-s) := by
    refine Summable.of_norm ((summable_Qform_neg_rpow z hs).congr fun p => ?_)
    have hpos : 0 < Qform z (p : ℤ × ℤ).1 (p : ℤ × ℤ).2 := by
      obtain ⟨c, hc, hcle⟩ := Qform_lower_bound z
      have hmn : (0 : ℝ) < ((p : ℤ × ℤ).1 : ℝ) ^ 2 + ((p : ℤ × ℤ).2 : ℝ) ^ 2 := by
        by_contra h
        push_neg at h
        have h1 : ((p : ℤ × ℤ).1 : ℝ) = 0 ∧ ((p : ℤ × ℤ).2 : ℝ) = 0 := by
          constructor <;> nlinarith [sq_nonneg ((p : ℤ × ℤ).1 : ℝ), sq_nonneg ((p : ℤ × ℤ).2 : ℝ)]
        exact p.2 (Prod.ext (by exact_mod_cast h1.1) (by exact_mod_cast h1.2))
      calc (0 : ℝ) < c * (((p : ℤ × ℤ).1 : ℝ) ^ 2 + ((p : ℤ × ℤ).2 : ℝ) ^ 2) := by positivity
        _ ≤ _ := hcle _ _
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos, Complex.neg_re]
  -- extend by zero to all of `ℤ × ℤ`, then transport to `Fin 2 → ℤ`
  have hfull : Summable fun p : ℤ × ℤ => ((Qform z p.1 p.2 : ℝ) : ℂ) ^ (-s) := by
    have h := (summable_subtype_iff_indicator (s := {p : ℤ × ℤ | p ≠ 0})
      (f := fun p : ℤ × ℤ => ((Qform z p.1 p.2 : ℝ) : ℂ) ^ (-s))).mp hsub
    refine h.congr fun p => ?_
    by_cases hp : p = 0
    · subst hp
      simp [Qform_zero, Complex.zero_cpow (neg_ne_zero.mpr hs0)]
    · simp [Set.indicator, hp]
  have := (finTwoArrowEquiv ℤ).summable_iff.mpr hfull
  exact this

/-- The lattice sum, rewritten over `Fin 2 → ℤ`. -/
lemma epsteinZeta_eq_tsum_latTerm (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    epsteinZeta z s = ∑' v : Fin 2 → ℤ, latTerm z s v := by
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  rw [epsteinZeta_eq_tsum z hs]
  have hsupp : Function.support (fun p : ℤ × ℤ => ((Qform z p.1 p.2 : ℝ) : ℂ) ^ (-s))
      ⊆ {p : ℤ × ℤ | p ≠ 0} := by
    intro p hp
    by_contra h0
    simp only [Set.mem_setOf_eq, not_not] at h0
    subst h0
    simp [Function.mem_support, Qform_zero, Complex.zero_cpow (neg_ne_zero.mpr hs0)] at hp
  have h1 := tsum_subtype_eq_of_support_subset hsupp
  change ∑' x : ({p : ℤ × ℤ | p ≠ 0} : Set (ℤ × ℤ)),
      (fun p : ℤ × ℤ => ((Qform z p.1 p.2 : ℝ) : ℂ) ^ (-s)) (x : ℤ × ℤ) = _
  rw [h1, ← (finTwoArrowEquiv ℤ).tsum_eq]
  rfl

/-- The gcd factorisation: `Z_z(s) = ζ(2s) · Σ_{coprime} Q^{-s}`. -/
theorem epsteinZeta_eq_zeta_mul_tsum_coprime (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    epsteinZeta z s
      = riemannZeta (2 * s) * ∑' v : EisensteinSeries.gammaSet 1 1 0, latTerm z s v := by
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have hsum := summable_latTerm z hs
  rw [epsteinZeta_eq_tsum_latTerm z hs]
  -- transport along the sigma equivalence
  set e := EisensteinSeries.gammaSetDivGcdSigmaEquiv with he
  have hsumσ : Summable fun x : Σ r : ℕ, EisensteinSeries.gammaSet 1 r 0 =>
      latTerm z s (x.2 : Fin 2 → ℤ) := by
    have := (e.symm.summable_iff (f := latTerm z s)).mpr hsum
    refine this.congr fun x => ?_
    simp [he]
  rw [← e.symm.tsum_eq (latTerm z s)]
  simp only [he, EisensteinSeries.gammaSetDivGcdSigmaEquiv_symm_eq]
  rw [Summable.tsum_sigma' (fun r => hsumσ.sigma_factor r) hsumσ]
  -- each `r`-slice is `r^{-2s}` times the coprime sum
  have hslice : ∀ r : ℕ,
      (∑' w : EisensteinSeries.gammaSet 1 r 0, latTerm z s (w : Fin 2 → ℤ))
        = ((r : ℂ) ^ (-s)) ^ 2 * ∑' v : EisensteinSeries.gammaSet 1 1 0, latTerm z s v := by
    intro r
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr
      have hzero : ∀ w : EisensteinSeries.gammaSet 1 0 0, latTerm z s (w : Fin 2 → ℤ) = 0 := by
        intro w
        have hw := (EisensteinSeries.gammaSet_one_mem_iff 0 (w : Fin 2 → ℤ)).mp w.2
        rw [Int.gcd_eq_zero_iff] at hw
        have : (w : Fin 2 → ℤ) = 0 := by
          ext i; fin_cases i
          · exact hw.1
          · exact hw.2
        rw [this, latTerm_zero z hs0]
      rw [tsum_congr hzero, tsum_zero]
      simp [Complex.zero_cpow (neg_ne_zero.mpr hs0)]
    · haveI : NeZero r := ⟨hr.ne'⟩
      rw [← (EisensteinSeries.gammaSetDivGcdEquiv r).symm.tsum_eq
        (fun w : EisensteinSeries.gammaSet 1 r 0 => latTerm z s (w : Fin 2 → ℤ)), ← tsum_mul_left]
      refine tsum_congr fun v => ?_
      have hv : (((EisensteinSeries.gammaSetDivGcdEquiv r).symm v : EisensteinSeries.gammaSet 1 r 0)
          : Fin 2 → ℤ) = (r : ℤ) • (v : Fin 2 → ℤ) := by
        have h := (EisensteinSeries.gammaSetDivGcdEquiv r).apply_symm_apply v
        have h' := congrArg Subtype.val h
        rw [EisensteinSeries.gammaSetDivGcdEquiv_eq] at h'
        -- `divIntMap r w = v`, i.e. `w / r = v`, so `w = r • v`
        ext i
        have hi := congrFun h' i
        simp only [EisensteinSeries.divIntMap, Pi.div_apply, Pi.intCast_apply] at hi
        have hdvd : (r : ℤ) ∣ ((EisensteinSeries.gammaSetDivGcdEquiv r).symm v : Fin 2 → ℤ) i :=
          EisensteinSeries.gammaSet_div_gcd ((EisensteinSeries.gammaSetDivGcdEquiv r).symm v).2 i
        have hi2 : ((EisensteinSeries.gammaSetDivGcdEquiv r).symm v : Fin 2 → ℤ) i / (r : ℤ)
            = (v : Fin 2 → ℤ) i := by simpa using hi
        rw [Pi.smul_apply, smul_eq_mul, ← hi2, Int.mul_ediv_cancel' hdvd]
      rw [hv, latTerm_smul]
  rw [tsum_congr hslice, tsum_mul_right, zeta_eq_tsum_one_div_nat_cpow (by rw [Complex.mul_re]; norm_num; linarith)]
  congr 1
  refine tsum_congr fun r => ?_
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have h2s : (2 : ℂ) * s ≠ 0 := mul_ne_zero two_ne_zero hs0
    simp [Complex.zero_cpow (neg_ne_zero.mpr hs0), Complex.zero_cpow h2s]
  · have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    rw [sq, ← Complex.cpow_add _ _ hr', one_div, ← Complex.cpow_neg]
    congr 1
    ring

/-- **The coset decomposition over `SL(2, ℤ)`**: `Z_z(s) = ζ(2s) · Σ_{⟨T⟩ \ SL(2,ℤ)} Im(g z)^s`. -/
theorem epsteinZeta_eq_zeta_mul_tsum_cosetSL (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    epsteinZeta z s = riemannZeta (2 * s) * ∑' c : CosetSL, eisTermSL z s c := by
  rw [epsteinZeta_eq_zeta_mul_tsum_coprime z hs,
    ← cosetRowEquiv.tsum_eq (fun v : EisensteinSeries.gammaSet 1 1 0 => latTerm z s v)]
  congr 1
  refine tsum_congr fun c => ?_
  induction c using Quotient.inductionOn with
  | h g =>
    rw [eisTermSL_mk]
    show latTerm z s (bottomRow g) = _
    simp only [latTerm, bottomRow_zero, bottomRow_one]
    exact cpow_Qform_bottomRow z g s

lemma summable_eisTermSL (z : ℍ) {s : ℂ} (hs : 1 < s.re) : Summable (eisTermSL z s) := by
  have h := (summable_latTerm z hs).subtype (EisensteinSeries.gammaSet 1 1 0)
  have h2 := (cosetRowEquiv.summable_iff
    (f := fun v : EisensteinSeries.gammaSet 1 1 0 => latTerm z s v)).mpr h
  refine h2.congr fun c => ?_
  induction c using Quotient.inductionOn with
  | h g =>
    rw [eisTermSL_mk]
    show latTerm z s (bottomRow g) = _
    simp only [latTerm, bottomRow_zero, bottomRow_one]
    exact cpow_Qform_bottomRow z g s

/-! ### Passing to `PSL(2, ℤ)`: the factor `2` -/

/-- The stabiliser of the cusp in `PSL2Z`: the powers of the image of `T`. -/
abbrev cuspStab : Subgroup PSL2Z := Subgroup.zpowers (QuotientGroup.mk ModularGroup.T : PSL2Z)

/-- Right cosets `Γ∞ \ PSL(2, ℤ)`. -/
abbrev CosetPSL : Type := Quotient (QuotientGroup.rightRel cuspStab)

/-- The projection `⟨T⟩ \ SL(2, ℤ) → Γ∞ \ PSL(2, ℤ)`. -/
def projCoset : CosetSL → CosetPSL :=
  Quotient.lift
    (fun g : SL(2, ℤ) => Quotient.mk (QuotientGroup.rightRel cuspStab) (QuotientGroup.mk g))
    (fun a b hab => by
      apply Quotient.sound
      have hab' : b * a⁻¹ ∈ stabT := QuotientGroup.rightRel_apply.mp hab
      refine QuotientGroup.rightRel_apply.mpr ?_
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hab'
      refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
      rw [← QuotientGroup.mk_zpow, hn, QuotientGroup.mk_mul, QuotientGroup.mk_inv])

lemma projCoset_mk (g : SL(2, ℤ)) :
    projCoset (Quotient.mk (QuotientGroup.rightRel stabT) g)
      = Quotient.mk (QuotientGroup.rightRel cuspStab) (QuotientGroup.mk g) := rfl

/-- The Eisenstein summand on a right coset of `PSL2Z`: `(Im (γ • z))^s`. -/
def eisTerm (z : ℍ) (s : ℂ) : CosetPSL → ℂ :=
  Quotient.lift (fun c : PSL2Z => (((c • z).im : ℝ) : ℂ) ^ s)
    (fun a b hab => by
      have hab' : b * a⁻¹ ∈ cuspStab := QuotientGroup.rightRel_apply.mp hab
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hab'
      have hb : b = (QuotientGroup.mk ModularGroup.T : PSL2Z) ^ n * a := by
        rw [hn, inv_mul_cancel_right]
      beta_reduce
      rw [hb, mul_smul, ← QuotientGroup.mk_zpow, mk_smul, modular_T_zpow_smul, vadd_im])

lemma eisTerm_mk (z : ℍ) (s : ℂ) (c : PSL2Z) :
    eisTerm z s (Quotient.mk (QuotientGroup.rightRel cuspStab) c) = (((c • z).im : ℝ) : ℂ) ^ s :=
  rfl

lemma eisTerm_projCoset (z : ℍ) (s : ℂ) (c : CosetSL) :
    eisTerm z s (projCoset c) = eisTermSL z s c := by
  induction c using Quotient.inductionOn with
  | h g => rfl

lemma mk_neg_eq_mk (g : SL(2, ℤ)) : (QuotientGroup.mk (-g) : PSL2Z) = QuotientGroup.mk g := by
  rw [QuotientGroup.eq, inv_neg, neg_mul, inv_mul_cancel]
  exact neg_one_mem_slKer

/-- The fibres of `projCoset` are the pairs `{[g], [-g]}`. -/
lemma projCoset_eq_iff (g g' : SL(2, ℤ)) :
    projCoset (Quotient.mk (QuotientGroup.rightRel stabT) g')
        = projCoset (Quotient.mk (QuotientGroup.rightRel stabT) g)
      ↔ Quotient.mk (QuotientGroup.rightRel stabT) g' = Quotient.mk (QuotientGroup.rightRel stabT) g
        ∨ Quotient.mk (QuotientGroup.rightRel stabT) g'
          = Quotient.mk (QuotientGroup.rightRel stabT) (-g) := by
  constructor
  · intro h
    rw [projCoset_mk, projCoset_mk] at h
    have h' := Quotient.exact h
    have h'' : (QuotientGroup.mk g : PSL2Z) * (QuotientGroup.mk g' : PSL2Z)⁻¹ ∈ cuspStab :=
      QuotientGroup.rightRel_apply.mp h'
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h''
    rw [← QuotientGroup.mk_zpow, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      QuotientGroup.eq] at hn
    rcases eq_one_or_neg_one_of_mem_slKer hn with h1 | h1
    · left
      apply Quotient.sound
      refine QuotientGroup.rightRel_apply.mpr ?_
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, inv_mul_eq_one.mp h1⟩
    · right
      apply Quotient.sound
      refine QuotientGroup.rightRel_apply.mpr ?_
      refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
      have h2 : g * g'⁻¹ = ModularGroup.T ^ n * (-1) := inv_mul_eq_iff_eq_mul.mp h1
      rw [neg_mul, h2, mul_neg, mul_one, neg_neg]
  · rintro (h | h)
    · rw [h]
    · rw [h, projCoset_mk, projCoset_mk, mk_neg_eq_mk]

lemma mk_ne_mk_neg (g : SL(2, ℤ)) :
    Quotient.mk (QuotientGroup.rightRel stabT) g
      ≠ Quotient.mk (QuotientGroup.rightRel stabT) (-g) := by
  intro h
  have h' := Quotient.exact h
  have h'' : -g * g⁻¹ ∈ stabT := QuotientGroup.rightRel_apply.mp h'
  rw [neg_mul, mul_inv_cancel] at h''
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h''
  have := congrArg (fun h : SL(2, ℤ) => h 0 0) hn
  simp [ModularGroup.coe_T_zpow] at this

lemma tsum_fiber_projCoset (z : ℍ) (s : ℂ) (g : SL(2, ℤ)) :
    (∑' c : projCoset ⁻¹' {projCoset (Quotient.mk (QuotientGroup.rightRel stabT) g)},
        eisTermSL z s c)
      = 2 * eisTermSL z s (Quotient.mk (QuotientGroup.rightRel stabT) g) := by
  classical
  have hset : projCoset ⁻¹' {projCoset (Quotient.mk (QuotientGroup.rightRel stabT) g)}
      = ↑({Quotient.mk (QuotientGroup.rightRel stabT) g,
            Quotient.mk (QuotientGroup.rightRel stabT) (-g)} : Finset CosetSL) := by
    ext c
    induction c using Quotient.inductionOn with
    | h g' =>
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.coe_insert, Finset.coe_singleton,
        Set.mem_insert_iff]
      exact projCoset_eq_iff g g'
  rw [tsum_congr_set_coe _ hset, Finset.tsum_subtype', Finset.sum_pair (mk_ne_mk_neg g),
    eisTermSL_mk, eisTermSL_mk, SL_neg_smul]
  ring

/-- **The coset decomposition over `PSL(2, ℤ)`**:
`Z_z(s) = 2 ζ(2s) · Σ_{Γ∞ \ PSL(2,ℤ)} Im(γ z)^s` for `Re s > 1`. -/
theorem epsteinZeta_eq_two_zeta_mul_tsum_coset (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    epsteinZeta z s = 2 * riemannZeta (2 * s) * ∑' d : CosetPSL, eisTerm z s d := by
  rw [epsteinZeta_eq_zeta_mul_tsum_cosetSL z hs]
  have hfib := (summable_eisTermSL z hs).hasSum.tsum_fiberwise projCoset
  rw [← hfib.tsum_eq]
  have hd : ∀ d : CosetPSL,
      (∑' c : projCoset ⁻¹' {d}, eisTermSL z s c) = 2 * eisTerm z s d := by
    intro d
    induction d using Quotient.inductionOn with
    | h c =>
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
      rw [← projCoset_mk, tsum_fiber_projCoset, eisTerm_projCoset]
  simp_rw [hd]
  rw [tsum_mul_left]
  ring

/-- **The Eisenstein series as a coset sum**: `E(z, s) = Σ_{Γ∞ \ PSL(2,ℤ)} Im(γ z)^s`
for `Re s > 1`. -/
theorem eisensteinE_eq_tsum_coset (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    eisensteinE z s = ∑' d : CosetPSL, eisTerm z s d := by
  have hζ : riemannZeta (2 * s) ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_le_re
    rw [Complex.mul_re]
    norm_num
    linarith
  rw [eisensteinE, epsteinZeta_eq_two_zeta_mul_tsum_coset z hs]
  field_simp

end

end RankinSelbergDelta.Eisenstein
