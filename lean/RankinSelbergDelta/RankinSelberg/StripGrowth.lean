import RankinSelbergDelta.RankinSelberg.GammaGrowth

/-!
# Growth on vertical strips

Completed L-functions of strong functional-equation pairs are bounded on vertical strips;
polynomial growth of `L(f, w)`, of the archimedean factor `rsPre`, of `rsJ`, `rsLambda`, `rsG` and of
the Rankin–Selberg square `G` on strips; and `G ≠ 0` for `Re s > 1`.
-/

open MeasureTheory Filter
open scoped NNReal MatrixGroups Pointwise

noncomputable section


/-! ### the completed L-function of a strong FE-pair is bounded on vertical strips
(from the Mellin integral: `‖∫ x^{s−1} f‖ ≤ ∫ ‖f‖ (x^{a−1} + x^{b−1})`). -/

namespace RankinSelbergDelta.RankinSelberg

open Complex MeasureTheory Set Filter
open scoped Real Topology

/-- `x^{σ−1} ≤ x^{a−1} + x^{b−1}` for `x > 0` and `a ≤ σ ≤ b`. -/
lemma rpow_sub_one_le_add {x a b σ : ℝ} (hx : 0 < x) (ha : a ≤ σ) (hb : σ ≤ b) :
    x ^ (σ - 1) ≤ x ^ (a - 1) + x ^ (b - 1) := by
  rcases le_or_gt x 1 with hx1 | hx1
  · have h : x ^ (σ - 1) ≤ x ^ (a - 1) :=
      Real.rpow_le_rpow_of_exponent_ge hx hx1 (by linarith)
    have h0 : 0 ≤ x ^ (b - 1) := by positivity
    linarith
  · have h : x ^ (σ - 1) ≤ x ^ (b - 1) :=
      Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
    have h0 : 0 ≤ x ^ (a - 1) := by positivity
    linarith

/-- **The completed L-function of a strong FE-pair is bounded on every vertical strip.** -/
theorem StrongFEPair.exists_norm_Λ_le (P : StrongFEPair ℂ) (a b : ℝ) :
    ∃ C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖P.Λ s‖ ≤ C := by
  have hmeas : AEStronglyMeasurable P.f (volume.restrict (Ioi 0)) :=
    P.hf_int.aestronglyMeasurable
  have ha : IntegrableOn (fun t : ℝ => t ^ (a - 1) * ‖P.f t‖) (Ioi 0) := by
    have h := (P.hasMellin (a : ℂ)).1
    rw [MellinConvergent, mellin_convergent_iff_norm Subset.rfl measurableSet_Ioi hmeas] at h
    simpa using h
  have hb : IntegrableOn (fun t : ℝ => t ^ (b - 1) * ‖P.f t‖) (Ioi 0) := by
    have h := (P.hasMellin (b : ℂ)).1
    rw [MellinConvergent, mellin_convergent_iff_norm Subset.rfl measurableSet_Ioi hmeas] at h
    simpa using h
  refine ⟨∫ t in Ioi (0 : ℝ), (t ^ (a - 1) * ‖P.f t‖ + t ^ (b - 1) * ‖P.f t‖),
    fun s hs1 hs2 => ?_⟩
  show ‖∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • P.f t‖ ≤ _
  refine norm_integral_le_of_norm_le (ha.add hb)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
  have ht0 : 0 < t := ht
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re, Complex.one_re]
  have hF : 0 ≤ ‖P.f t‖ := norm_nonneg _
  calc t ^ (s.re - 1) * ‖P.f t‖ ≤ (t ^ (a - 1) + t ^ (b - 1)) * ‖P.f t‖ :=
        mul_le_mul_of_nonneg_right (rpow_sub_one_le_add ht0 hs1 hs2) hF
    _ = t ^ (a - 1) * ‖P.f t‖ + t ^ (b - 1) * ‖P.f t‖ := by ring

end RankinSelbergDelta.RankinSelberg

/-! ### the completed L-function of a level-1 cusp form is bounded on
vertical strips, from `StrongFEPair.exists_norm_Λ_le` applied to `fePair f hk`. -/

namespace RankinSelbergDelta.CuspForm

open Complex UpperHalfPlane ModularForm SlashInvariantForm CongruenceSubgroup ModularFormClass

variable {F : Type*} [FunLike F ℍ ℂ] {k : ℤ}
  [cf : CuspFormClass F (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma 1)) k]

include cf in
theorem exists_norm_completedLSeries_le (f : F) (hk : 0 < k) (a b : ℝ) :
    ∃ C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖completedLSeries f hk s‖ ≤ C :=
  RankinSelbergDelta.RankinSelberg.StrongFEPair.exists_norm_Λ_le (fePair f hk) a b

end RankinSelbergDelta.CuspForm

/-! ### polynomial growth of `L(f, w)` on the strip `−1/8 ≤ Re w ≤ 9/8`
(Phragmén–Lindelöf for `Λ` with the weight `cos(π(2w−1)/4)`, boundary values from the Dirichlet
series on `Re w = 9/8` and the functional equation on `Re w = −1/8`). -/

namespace RankinSelbergDelta.RankinSelberg

open Complex UpperHalfPlane MeasureTheory Set Filter
open scoped Real Topology

/-! #### The weight `lPhi w = cos(π(2w − 1)/4)` -/

lemma cos_ge_half_of_abs_le_pi_div_three {x : ℝ} (hx : |x| ≤ π / 3) : 1 / 2 ≤ Real.cos x := by
  have h := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg x)
    (by linarith [Real.pi_pos] : π / 3 ≤ π) hx
  rw [Real.cos_pi_div_three, Real.cos_abs] at h
  exact h

noncomputable def lPhi (w : ℂ) : ℂ := Complex.cos ((π : ℂ) * (2 * w - 1) / 4)

lemma lPhi_arg (w : ℂ) :
    (π : ℂ) * (2 * w - 1) / 4
      = ((π * (2 * w.re - 1) / 4 : ℝ) : ℂ) + ((π * (2 * w.im) / 4 : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;> simp <;> ring

lemma norm_lPhi_le (w : ℂ) : ‖lPhi w‖ ≤ Real.exp (π * |w.im| / 2) := by
  have := norm_cos_le_exp ((π : ℂ) * (2 * w - 1) / 4)
  have him : ((π : ℂ) * (2 * w - 1) / 4).im = π * |w.im| / 2 ∨
      ((π : ℂ) * (2 * w - 1) / 4).im = -(π * |w.im| / 2) := by
    have h : ((π : ℂ) * (2 * w - 1) / 4).im = π * w.im / 2 := by simp; ring
    rcases le_or_gt 0 w.im with ht | ht
    · left; rw [h, abs_of_nonneg ht]
    · right; rw [h, abs_of_neg ht]; ring
  rcases him with h | h
  · rw [h, abs_of_nonneg (by positivity)] at this
    simpa [lPhi] using this
  · rw [h, abs_neg, abs_of_nonneg (by positivity)] at this
    simpa [lPhi] using this

lemma norm_lPhi_ge {w : ℂ} (h1 : -1 / 8 ≤ w.re) (h2 : w.re ≤ 9 / 8) :
    Real.exp (π * |w.im| / 2) / 4 ≤ ‖lPhi w‖ := by
  set x : ℝ := π * (2 * w.re - 1) / 4 with hx
  set y : ℝ := π * (2 * w.im) / 4 with hy
  have hre : (lPhi w).re = Real.cos x * Real.cosh y := by
    rw [lPhi, lPhi_arg, ← hx, ← hy, Complex.cos_add_mul_I]
    simp [← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sin, ← Complex.ofReal_sinh]
  have hxabs : |x| ≤ π / 3 := by
    rw [hx, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    have : |2 * w.re - 1| ≤ 5 / 4 := by rw [abs_le]; constructor <;> linarith
    calc π * |2 * w.re - 1| / 4 ≤ π * (5 / 4) / 4 := by gcongr
      _ ≤ π / 3 := by linarith [Real.pi_pos]
  have hcos : 1 / 2 ≤ Real.cos x := cos_ge_half_of_abs_le_pi_div_three hxabs
  have hcosh : Real.exp |y| / 2 ≤ Real.cosh y := by
    rw [Real.cosh_eq]
    rcases le_or_gt 0 y with hy0 | hy0
    · rw [abs_of_nonneg hy0]; linarith [Real.exp_pos (-y)]
    · rw [abs_of_neg hy0]; linarith [Real.exp_pos y]
  have hyabs : |y| = π * |w.im| / 2 := by
    have : y = (π / 2) * w.im := by rw [hy]; ring
    rw [this, abs_mul, abs_of_pos (by positivity)]; ring
  calc Real.exp (π * |w.im| / 2) / 4 = (1 / 2) * (Real.exp |y| / 2) := by rw [hyabs]; ring
    _ ≤ Real.cos x * Real.cosh y :=
        mul_le_mul hcos hcosh (by positivity) (by linarith)
    _ = (lPhi w).re := hre.symm
    _ ≤ |(lPhi w).re| := le_abs_self _
    _ ≤ ‖lPhi w‖ := Complex.abs_re_le_norm _

lemma lPhi_ne_zero {w : ℂ} (h1 : -1 / 8 ≤ w.re) (h2 : w.re ≤ 9 / 8) : lPhi w ≠ 0 := by
  intro h
  have := norm_lPhi_ge h1 h2
  rw [h, norm_zero] at this
  linarith [Real.exp_pos (π * |w.im| / 2)]

lemma differentiable_lPhi : Differentiable ℂ lPhi := by
  show Differentiable ℂ (Complex.cos ∘ fun z : ℂ => (π : ℂ) * (2 * z - 1) / 4)
  exact Complex.differentiable_cos.comp
    ((((differentiable_id.const_mul _).sub_const _).const_mul _).div_const _)

/-! #### `w + 2` on the strip `−1/8 ≤ Re w ≤ 9/8` -/

lemma norm_add_two_ge' {w : ℂ} (h1 : -1 / 8 ≤ w.re) : (1 + |w.im|) / 2 ≤ ‖w + 2‖ := by
  have hre := Complex.abs_re_le_norm (w + 2)
  have him := Complex.abs_im_le_norm (w + 2)
  rw [Complex.add_re, Complex.re_ofNat] at hre
  rw [Complex.add_im, Complex.im_ofNat, add_zero] at him
  have h : |w.re + 2| = w.re + 2 := abs_of_pos (by linarith)
  linarith

lemma norm_add_two_le' {w : ℂ} (h1 : -1 / 8 ≤ w.re) (h2 : w.re ≤ 9 / 8) :
    ‖w + 2‖ ≤ 4 * (1 + |w.im|) := by
  have h := Complex.norm_le_abs_re_add_abs_im (w + 2)
  rw [Complex.add_re, Complex.add_im, Complex.re_ofNat, Complex.im_ofNat, add_zero] at h
  have hre : |w.re + 2| ≤ 25 / 8 := by rw [abs_le]; constructor <;> linarith
  linarith [abs_nonneg w.im]

lemma one_le_norm_add_two' {w : ℂ} (h1 : -1 / 8 ≤ w.re) : 1 ≤ ‖w + 2‖ := by
  have hre := Complex.abs_re_le_norm (w + 2)
  rw [Complex.add_re, Complex.re_ofNat] at hre
  have h : |w.re + 2| = w.re + 2 := abs_of_pos (by linarith)
  linarith

lemma add_two_ne_zero' {w : ℂ} (h1 : -1 / 8 ≤ w.re) : w + 2 ≠ 0 := by
  intro h
  have := one_le_norm_add_two' h1
  rw [h, norm_zero] at this
  linarith

/-- The strip `a ≤ Re ≤ b` is the closure of the open strip (one inclusion). -/
lemma closure_strip_subset' (a b : ℝ) :
    closure (Complex.re ⁻¹' Ioo a b) ⊆ {w : ℂ | a ≤ w.re ∧ w.re ≤ b} := by
  refine closure_minimal (fun w hw => ⟨hw.1.le, hw.2.le⟩) ?_
  exact (isClosed_le continuous_const Complex.continuous_re).inter
    (isClosed_le Complex.continuous_re continuous_const)

/-! #### `Λ` in the analytic normalisation -/

variable {F : Type*} [FunLike F ℍ ℂ] (k : ℤ)
  [cf : CuspFormClass F (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma 1)) k]

/-- `Λ_w(w) = Λ(w + (k−1)/2)`, so that `L(f, w) = Λ_w(w) (2π)^{w'} / Γ(w')`. -/
noncomputable def lamW (f : F) (hk : 0 < k) (w : ℂ) : ℂ :=
  RankinSelbergDelta.CuspForm.completedLSeries f hk (w + ((k : ℂ) - 1) / 2)

lemma shift_re (w : ℂ) : (w + ((k : ℂ) - 1) / 2).re = w.re + ((k : ℝ) - 1) / 2 := by
  have : ((((k : ℂ) - 1) / 2)).re = ((k : ℝ) - 1) / 2 := by simp [Complex.div_re]
  rw [Complex.add_re, this]

lemma shift_im (w : ℂ) : (w + ((k : ℂ) - 1) / 2).im = w.im := by
  have : ((((k : ℂ) - 1) / 2)).im = 0 := by simp [Complex.div_im]
  rw [Complex.add_im, this, add_zero]

include cf in
lemma Lfun_eq_lamW_mul (f : F) (hk : 0 < k) (w : ℂ) :
    Lfun k f hk w = lamW k f hk w * ((2 * Real.pi : ℝ) : ℂ) ^ (w + ((k : ℂ) - 1) / 2)
      * (Complex.Gamma (w + ((k : ℂ) - 1) / 2))⁻¹ := rfl

include cf in
lemma differentiable_lamW (f : F) (hk : 0 < k) : Differentiable ℂ (lamW k f hk) :=
  (RankinSelbergDelta.CuspForm.differentiable_completedLSeries f hk).comp (differentiable_id.add_const _)

include cf in
lemma lamW_eq_Lfun_mul (f : F) (hk : 0 < k) {w : ℂ} (hre : 0 < (w + ((k : ℂ) - 1) / 2).re) :
    lamW k f hk w = Lfun k f hk w * ((2 * Real.pi : ℝ) : ℂ) ^ (-(w + ((k : ℂ) - 1) / 2))
      * Complex.Gamma (w + ((k : ℂ) - 1) / 2) := by
  have hΓ : Complex.Gamma (w + ((k : ℂ) - 1) / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hre
  have h2π : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hpow : ((2 * Real.pi : ℝ) : ℂ) ^ (w + ((k : ℂ) - 1) / 2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    push_neg
    intro h
    exact absurd h h2π
  rw [Lfun_eq_lamW_mul, Complex.cpow_neg]
  set P : ℂ := ((2 * Real.pi : ℝ) : ℂ) ^ (w + ((k : ℂ) - 1) / 2) with hP
  set G : ℂ := Complex.Gamma (w + ((k : ℂ) - 1) / 2) with hG
  rw [show lamW k f hk w * P * G⁻¹ * P⁻¹ * G = lamW k f hk w * (P * P⁻¹) * (G⁻¹ * G) by ring,
    mul_inv_cancel₀ hpow, inv_mul_cancel₀ hΓ, mul_one, mul_one]

include cf in
/-- The functional equation in the analytic normalisation: `Λ_w(w) = I^k Λ_w(1 − w)`. -/
lemma lamW_eq_lamW_one_sub (f : F) (hk : 0 < k) (w : ℂ) :
    lamW k f hk w = Complex.I ^ k * lamW k f hk (1 - w) := by
  unfold lamW
  have := RankinSelbergDelta.CuspForm.completedLSeries_functional_equation f hk ((1 - w) + ((k : ℂ) - 1) / 2)
  rw [smul_eq_mul,
    show (((k : ℤ) : ℝ) : ℂ) - ((1 - w) + ((k : ℂ) - 1) / 2) = w + ((k : ℂ) - 1) / 2 by
      push_cast; ring] at this
  exact this

include cf in
lemma norm_lamW_eq_norm_one_sub (f : F) (hk : 0 < k) (w : ℂ) :
    ‖lamW k f hk w‖ = ‖lamW k f hk (1 - w)‖ := by
  rw [lamW_eq_lamW_one_sub k f hk w, norm_mul, norm_zpow, Complex.norm_I, one_zpow, one_mul]

/-! #### The right edge `Re w = 9/8`: the Dirichlet series -/

/-- The absolute Dirichlet series at `w = 9/8`. -/
noncomputable def rsLedge (f : F) : ℝ :=
  ∑' n : ℕ, ‖rsCoeff f n * (n : ℂ) ^ (-(((9 / 8 : ℝ) : ℂ) + ((k : ℂ) - 1) / 2))‖

include cf in
lemma norm_rsL_le_rsLedge (f : F) (hk : 0 < k) {w : ℂ} (hw : w.re = 9 / 8) :
    ‖rsL k f w‖ ≤ rsLedge k f := by
  have hw' : 1 < w.re := by rw [hw]; norm_num
  have hsum := summable_norm_rsLterm k f hk hw'
  unfold rsL rsLedge
  refine (norm_tsum_le_tsum_norm hsum).trans (le_of_eq (tsum_congr fun n => ?_))
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [rsCoeff, RankinSelbergDelta.CuspForm.qExpansion_coeff_zero_cusp f]
  · rw [norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos hn, Complex.norm_natCast_cpow_of_pos hn,
      Complex.neg_re, Complex.neg_re, Complex.add_re, Complex.add_re, hw, Complex.ofReal_re]

include cf in
lemma rsLedge_nonneg (f : F) : 0 ≤ rsLedge k f := tsum_nonneg fun n => norm_nonneg _

include cf in
/-- `‖Λ_w‖` on both edges of the strip: `C (1 + |t|)^{m+1} e^{−π|t|/2}` with `m = k`. -/
theorem exists_norm_lamW_le_edges (f : F) (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, (w.re = 9 / 8 ∨ w.re = -1 / 8) →
      ‖lamW k f hk w‖ ≤ C * (1 + |w.im|) ^ (k.toNat + 1) * Real.exp (-(π * |w.im| / 2)) := by
  obtain ⟨CΓ, hCΓ, hΓ⟩ := exists_norm_Gamma_le k.toNat
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hm : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk.le
  have hL0 : 0 ≤ rsLedge k f := rsLedge_nonneg k f
  -- the right edge
  have hright : ∀ w : ℂ, w.re = 9 / 8 →
      ‖lamW k f hk w‖ ≤ (rsLedge k f + 1) * CΓ * (1 + |w.im|) ^ (k.toNat + 1)
        * Real.exp (-(π * |w.im| / 2)) := by
    intro w hw
    have hre' : (w + ((k : ℂ) - 1) / 2).re = 9 / 8 + ((k : ℝ) - 1) / 2 := by rw [shift_re, hw]
    have hpos : 0 < (w + ((k : ℂ) - 1) / 2).re := by rw [hre']; linarith
    rw [lamW_eq_Lfun_mul k f hk hpos, norm_mul, norm_mul]
    have hL : ‖Lfun k f hk w‖ ≤ rsLedge k f := by
      rw [Lfun_eq_rsL k f hk (by rw [hw]; norm_num)]
      exact norm_rsL_le_rsLedge k f hk hw
    have hP : ‖((2 * Real.pi : ℝ) : ℂ) ^ (-(w + ((k : ℂ) - 1) / 2))‖ ≤ 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re, hre']
      exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by linarith)
    have hG : ‖Complex.Gamma (w + ((k : ℂ) - 1) / 2)‖
        ≤ CΓ * (1 + |w.im|) ^ (k.toNat + 1) * Real.exp (-(π * |w.im| / 2)) := by
      have := hΓ (w + ((k : ℂ) - 1) / 2) (by rw [hre']; linarith) (by rw [hre', hm]; linarith)
      rwa [shift_im] at this
    have hX : 0 ≤ (1 + |w.im|) ^ (k.toNat + 1) * Real.exp (-(π * |w.im| / 2)) := by positivity
    calc ‖Lfun k f hk w‖ * ‖((2 * Real.pi : ℝ) : ℂ) ^ (-(w + ((k : ℂ) - 1) / 2))‖
          * ‖Complex.Gamma (w + ((k : ℂ) - 1) / 2)‖
        ≤ rsLedge k f * 1 * (CΓ * ((1 + |w.im|) ^ (k.toNat + 1) * Real.exp (-(π * |w.im| / 2)))) := by
          refine mul_le_mul (mul_le_mul hL hP (norm_nonneg _) hL0) ?_ (norm_nonneg _) (by linarith)
          calc ‖Complex.Gamma (w + ((k : ℂ) - 1) / 2)‖
              ≤ CΓ * (1 + |w.im|) ^ (k.toNat + 1) * Real.exp (-(π * |w.im| / 2)) := hG
            _ = CΓ * ((1 + |w.im|) ^ (k.toNat + 1) * Real.exp (-(π * |w.im| / 2))) := by ring
      _ = rsLedge k f * CΓ * ((1 + |w.im|) ^ (k.toNat + 1) * Real.exp (-(π * |w.im| / 2))) := by
          ring
      _ ≤ (rsLedge k f + 1) * CΓ * ((1 + |w.im|) ^ (k.toNat + 1) * Real.exp (-(π * |w.im| / 2))) := by
          apply mul_le_mul_of_nonneg_right _ hX
          apply mul_le_mul_of_nonneg_right _ hCΓ.le
          linarith
      _ = (rsLedge k f + 1) * CΓ * (1 + |w.im|) ^ (k.toNat + 1) * Real.exp (-(π * |w.im| / 2)) := by
          ring
  refine ⟨(rsLedge k f + 1) * CΓ, mul_pos (by linarith) hCΓ, fun w hw => ?_⟩
  rcases hw with hw | hw
  · exact hright w hw
  · -- the left edge, by the functional equation
    rw [norm_lamW_eq_norm_one_sub k f hk w]
    have h1 : (1 - w).re = 9 / 8 := by rw [Complex.sub_re, Complex.one_re, hw]; norm_num
    have h2 : |(1 - w).im| = |w.im| := by rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
    have := hright (1 - w) h1
    rwa [h2] at this

/-! #### Phragmén–Lindelöf on the strip -/

/-- The weighted function `H(w) = Λ_w(w) φ(w) / (w + 2)^{m+1}`. -/
noncomputable def lamH (f : F) (hk : 0 < k) (w : ℂ) : ℂ :=
  lamW k f hk w * lPhi w / (w + 2) ^ (k.toNat + 1)

include cf in
lemma differentiableOn_lamH (f : F) (hk : 0 < k) :
    DifferentiableOn ℂ (lamH k f hk) {w : ℂ | -1 / 8 ≤ w.re ∧ w.re ≤ 9 / 8} := by
  unfold lamH
  refine DifferentiableOn.div ((differentiable_lamW k f hk).mul differentiable_lPhi).differentiableOn
    ((differentiable_id.add_const _).pow _).differentiableOn fun z hz => ?_
  exact pow_ne_zero _ (add_two_ne_zero' hz.1)

include cf in
lemma norm_lamH_le_edges (f : F) (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, (w.re = 9 / 8 ∨ w.re = -1 / 8) → ‖lamH k f hk w‖ ≤ C := by
  obtain ⟨C, hC, hedge⟩ := exists_norm_lamW_le_edges k f hk
  refine ⟨C * 2 ^ (k.toNat + 1), by positivity, fun w hw => ?_⟩
  have h1 : -1 / 8 ≤ w.re := by rcases hw with hw | hw <;> rw [hw] <;> norm_num
  have hden := norm_add_two_ge' h1
  have hdenpos : 0 < ‖w + 2‖ := by linarith [abs_nonneg w.im]
  have hE : Real.exp (-(π * |w.im| / 2)) * Real.exp (π * |w.im| / 2) = 1 := by
    rw [← Real.exp_add]; simp
  unfold lamH
  rw [norm_div, norm_mul, norm_pow, div_le_iff₀ (pow_pos hdenpos _)]
  calc ‖lamW k f hk w‖ * ‖lPhi w‖
      ≤ (C * (1 + |w.im|) ^ (k.toNat + 1) * Real.exp (-(π * |w.im| / 2)))
          * Real.exp (π * |w.im| / 2) :=
        mul_le_mul (hedge w hw) (norm_lPhi_le w) (norm_nonneg _) (by positivity)
    _ = C * (1 + |w.im|) ^ (k.toNat + 1)
          * (Real.exp (-(π * |w.im| / 2)) * Real.exp (π * |w.im| / 2)) := by ring
    _ = C * (1 + |w.im|) ^ (k.toNat + 1) := by rw [hE, mul_one]
    _ = C * 2 ^ (k.toNat + 1) * ((1 + |w.im|) / 2) ^ (k.toNat + 1) := by
        rw [div_pow]; field_simp
    _ ≤ C * 2 ^ (k.toNat + 1) * ‖w + 2‖ ^ (k.toNat + 1) := by
        have := pow_le_pow_left₀ (by positivity) hden (k.toNat + 1)
        exact mul_le_mul_of_nonneg_left this (by positivity)

include cf in
lemma lamH_isBigO (f : F) (hk : 0 < k) :
    lamH k f hk =O[Filter.comap (fun z : ℂ => |z.im|) Filter.atTop ⊓
        Filter.principal (Complex.re ⁻¹' Ioo (-1 / 8 : ℝ) (9 / 8))]
      fun z => Real.exp (π * Real.exp (1 * |z.im|)) := by
  obtain ⟨CΛ, hΛ⟩ := RankinSelbergDelta.CuspForm.exists_norm_completedLSeries_le f hk
    (-1 / 8 + ((k : ℝ) - 1) / 2) (9 / 8 + ((k : ℝ) - 1) / 2)
  refine Asymptotics.IsBigO.of_bound (max CΛ 0) ?_
  rw [Filter.eventually_inf_principal]
  refine Filter.Eventually.of_forall fun z hz => ?_
  have hz1 : -1 / 8 ≤ z.re := hz.1.le
  have hz2 : z.re ≤ 9 / 8 := hz.2.le
  have hΛz : ‖lamW k f hk z‖ ≤ max CΛ 0 := by
    refine (hΛ (z + ((k : ℂ) - 1) / 2) ?_ ?_).trans (le_max_left _ _)
    · rw [shift_re]; linarith
    · rw [shift_re]; linarith
  have hphi := norm_lPhi_le z
  have hden := one_le_norm_add_two' hz1
  have hgrow : Real.exp (π * |z.im| / 2) ≤ Real.exp (π * Real.exp (1 * |z.im|)) := by
    refine Real.exp_le_exp.mpr ?_
    have h1 := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (1 * |z.im|)) Real.pi_pos.le
    have h2 := mul_nonneg Real.pi_pos.le (abs_nonneg z.im)
    linarith [Real.pi_pos]
  have hM : 0 ≤ max CΛ 0 := le_max_right _ _
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  unfold lamH
  rw [norm_div, norm_mul, norm_pow, div_le_iff₀ (pow_pos (by linarith) _)]
  calc ‖lamW k f hk z‖ * ‖lPhi z‖ ≤ max CΛ 0 * Real.exp (π * |z.im| / 2) :=
        mul_le_mul hΛz hphi (norm_nonneg _) hM
    _ ≤ max CΛ 0 * Real.exp (π * Real.exp (1 * |z.im|)) :=
        mul_le_mul_of_nonneg_left hgrow hM
    _ = max CΛ 0 * Real.exp (π * Real.exp (1 * |z.im|)) * 1 := by ring
    _ ≤ max CΛ 0 * Real.exp (π * Real.exp (1 * |z.im|)) * ‖z + 2‖ ^ (k.toNat + 1) := by
        have := one_le_pow₀ (M₀ := ℝ) hden (n := k.toNat + 1)
        exact mul_le_mul_of_nonneg_left this (by positivity)

include cf in
theorem exists_norm_lamH_le_strip (f : F) (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, -1 / 8 ≤ w.re → w.re ≤ 9 / 8 → ‖lamH k f hk w‖ ≤ C := by
  obtain ⟨C, hC, hedge⟩ := norm_lamH_le_edges k f hk
  refine ⟨C, hC, fun w h1 h2 => ?_⟩
  refine PhragmenLindelof.vertical_strip (a := -1 / 8) (b := 9 / 8) ?_ ?_ ?_ ?_ h1 h2
  · exact DifferentiableOn.diffContOnCl
      ((differentiableOn_lamH k f hk).mono (closure_strip_subset' _ _))
  · refine ⟨1, ?_, π, lamH_isBigO k f hk⟩
    rw [show (9 / 8 : ℝ) - -1 / 8 = 5 / 4 by norm_num, lt_div_iff₀ (by norm_num)]
    linarith [Real.pi_gt_three]
  · intro z hz
    exact hedge z (Or.inr hz)
  · intro z hz
    exact hedge z (Or.inl hz)

include cf in
/-- **`Λ_w` on the strip**: the sharp exponential decay with a polynomial factor. -/
theorem exists_norm_lamW_le_strip (f : F) (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, -1 / 8 ≤ w.re → w.re ≤ 9 / 8 →
      ‖lamW k f hk w‖ ≤ C * (1 + |w.im|) ^ (k.toNat + 1) * Real.exp (-(π * |w.im| / 2)) := by
  obtain ⟨C, hC, hH⟩ := exists_norm_lamH_le_strip k f hk
  refine ⟨C * 4 ^ (k.toNat + 1) * 4, by positivity, fun w h1 h2 => ?_⟩
  have hphi_ne : lPhi w ≠ 0 := lPhi_ne_zero h1 h2
  have hphipos : 0 < ‖lPhi w‖ := norm_pos_iff.mpr hphi_ne
  have hden_ne : w + 2 ≠ 0 := add_two_ne_zero' h1
  have hw' : lamW k f hk w = lamH k f hk w * (w + 2) ^ (k.toNat + 1) / lPhi w := by
    unfold lamH; field_simp
  have hphi := norm_lPhi_ge h1 h2
  have hden := norm_add_two_le' h1 h2
  have hE : 0 < Real.exp (π * |w.im| / 2) := Real.exp_pos _
  rw [hw', norm_div, norm_mul, norm_pow, div_le_iff₀ hphipos]
  calc ‖lamH k f hk w‖ * ‖w + 2‖ ^ (k.toNat + 1)
      ≤ C * (4 * (1 + |w.im|)) ^ (k.toNat + 1) := by
        have := pow_le_pow_left₀ (norm_nonneg _) hden (k.toNat + 1)
        exact mul_le_mul (hH w h1 h2) this (by positivity) hC.le
    _ = C * 4 ^ (k.toNat + 1) * 4 * (1 + |w.im|) ^ (k.toNat + 1) * Real.exp (-(π * |w.im| / 2))
          * (Real.exp (π * |w.im| / 2) / 4) := by
        rw [Real.exp_neg, mul_pow]; field_simp
    _ ≤ C * 4 ^ (k.toNat + 1) * 4 * (1 + |w.im|) ^ (k.toNat + 1) * Real.exp (-(π * |w.im| / 2))
          * ‖lPhi w‖ := by
        exact mul_le_mul_of_nonneg_left hphi (by positivity)

include cf in
/-- **Polynomial growth of `L(f, w)` on the strip `−1/8 ≤ Re w ≤ 9/8`** (which contains the
edge `Re w = 1` of the critical strip). -/
theorem exists_norm_Lfun_le_strip (f : F) (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, -1 / 8 ≤ w.re → w.re ≤ 9 / 8 →
      ‖Lfun k f hk w‖ ≤ C * (1 + |w.im|) ^ (k.toNat + 3) := by
  obtain ⟨CΛ, hCΛ, hΛ⟩ := exists_norm_lamW_le_strip k f hk
  obtain ⟨CΓ, hCΓ, hΓ⟩ := exists_norm_inv_Gamma_le 1 (k.toNat + 1)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hm : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk.le
  set b : ℝ := 9 / 8 + ((k : ℝ) - 1) / 2 with hb
  refine ⟨CΛ * (2 * Real.pi) ^ b * CΓ, by positivity, fun w h1 h2 => ?_⟩
  have hre := shift_re k w
  have him := shift_im k w
  have hP : ‖((2 * Real.pi : ℝ) : ℂ) ^ (w + ((k : ℂ) - 1) / 2)‖ ≤ (2 * Real.pi) ^ b := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), hre]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by rw [hb]; linarith)
  have hG : ‖(Complex.Gamma (w + ((k : ℂ) - 1) / 2))⁻¹‖
      ≤ CΓ * (1 + |w.im|) ^ (1 + 1) * Real.exp (π * |w.im| / 2) := by
    have := hΓ (w + ((k : ℂ) - 1) / 2) (by rw [hre]; push_cast; linarith)
      (by rw [hre]; push_cast; rw [hm]; linarith)
    rwa [him] at this
  have hE : Real.exp (-(π * |w.im| / 2)) * Real.exp (π * |w.im| / 2) = 1 := by
    rw [← Real.exp_add]; simp
  have hP0 : 0 ≤ (2 * Real.pi) ^ b := by positivity
  rw [Lfun_eq_lamW_mul, norm_mul, norm_mul]
  calc ‖lamW k f hk w‖ * ‖((2 * Real.pi : ℝ) : ℂ) ^ (w + ((k : ℂ) - 1) / 2)‖
        * ‖(Complex.Gamma (w + ((k : ℂ) - 1) / 2))⁻¹‖
      ≤ (CΛ * (1 + |w.im|) ^ (k.toNat + 1) * Real.exp (-(π * |w.im| / 2))) * (2 * Real.pi) ^ b
          * (CΓ * (1 + |w.im|) ^ (1 + 1) * Real.exp (π * |w.im| / 2)) := by
        refine mul_le_mul (mul_le_mul (hΛ w h1 h2) hP (norm_nonneg _) (by positivity)) hG
          (norm_nonneg _) (by positivity)
    _ = CΛ * (2 * Real.pi) ^ b * CΓ * (1 + |w.im|) ^ (k.toNat + 3)
          * (Real.exp (-(π * |w.im| / 2)) * Real.exp (π * |w.im| / 2)) := by ring
    _ = CΛ * (2 * Real.pi) ^ b * CΓ * (1 + |w.im|) ^ (k.toNat + 3) := by rw [hE, mul_one]

end RankinSelbergDelta.RankinSelberg

/-! ### the growth bounds (a) `rsPre`, (b) `rsJ` / `rsLambda`, (c) `rsG` on vertical
strips, from the Γ bounds of `GammaGrowth.lean` and the theta bound on `𝒟`. -/

namespace RankinSelbergDelta.RankinSelberg

open Complex UpperHalfPlane MeasureTheory Set Filter RankinSelbergDelta.Eisenstein
open scoped Real Topology Modular

variable {F : Type*} [FunLike F ℍ ℂ] (k : ℤ)
  [cf : CuspFormClass F (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma 1)) k]

lemma shiftk_re (s : ℂ) : (s + k - 1).re = s.re + k - 1 := by simp

lemma shiftk_im (s : ℂ) : (s + k - 1).im = s.im := by simp

/-- **(a) `rsPre` on a vertical strip `−A ≤ Re s ≤ A`**: polynomial times `e^{π|t|}`. -/
theorem exists_norm_rsPre_le (hk : 0 < k) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, -(A : ℝ) ≤ s.re → s.re ≤ A →
      ‖rsPre k s‖ ≤ C * (1 + |s.im|) ^ (2 * A + 2) * Real.exp (π * |s.im|) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_inv_Gamma_le A (A + k.toNat)
  obtain ⟨C₂, hC₂, h₂⟩ := exists_norm_inv_Gamma_le A A
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hm : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk.le
  have h4π : (1 : ℝ) ≤ 4 * π := by linarith [Real.pi_gt_three]
  have hπ : (1 : ℝ) ≤ π := by linarith [Real.pi_gt_three]
  refine ⟨(4 * π) ^ ((A : ℝ) + k) * π ^ (A : ℝ) * C₁ * C₂ / 2, by positivity, fun s hA hB => ?_⟩
  have hre := shiftk_re k s
  have him := shiftk_im k s
  have hP1 : ‖((4 * Real.pi : ℝ) : ℂ) ^ (s + k - 1)‖ ≤ (4 * π) ^ ((A : ℝ) + k) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), hre]
    exact Real.rpow_le_rpow_of_exponent_le h4π (by linarith)
  have hP2 : ‖(Real.pi : ℂ) ^ s‖ ≤ π ^ (A : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    exact Real.rpow_le_rpow_of_exponent_le hπ hB
  have hG1 : ‖(Complex.Gamma (s + k - 1))⁻¹‖
      ≤ C₁ * (1 + |s.im|) ^ (A + 1) * Real.exp (π * |s.im| / 2) := by
    have := h₁ (s + k - 1) (by rw [hre]; linarith) (by rw [hre]; push_cast; rw [hm]; linarith)
    rwa [him] at this
  have hG2 : ‖(Complex.Gamma s)⁻¹‖ ≤ C₂ * (1 + |s.im|) ^ (A + 1) * Real.exp (π * |s.im| / 2) :=
    h₂ s hA hB
  have hE : Real.exp (π * |s.im| / 2) * Real.exp (π * |s.im| / 2) = Real.exp (π * |s.im|) := by
    rw [← Real.exp_add]; congr 1; ring
  unfold rsPre
  rw [norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_ofNat]
  have hX1 : 0 ≤ (4 * π) ^ ((A : ℝ) + k) := by positivity
  have hX2 : 0 ≤ π ^ (A : ℝ) := by positivity
  calc ‖((4 * Real.pi : ℝ) : ℂ) ^ (s + k - 1)‖ * ‖(Real.pi : ℂ) ^ s‖
        * (‖(Complex.Gamma (s + k - 1))⁻¹‖ * ‖(Complex.Gamma s)⁻¹‖) / 2
      ≤ (4 * π) ^ ((A : ℝ) + k) * π ^ (A : ℝ)
          * ((C₁ * (1 + |s.im|) ^ (A + 1) * Real.exp (π * |s.im| / 2))
            * (C₂ * (1 + |s.im|) ^ (A + 1) * Real.exp (π * |s.im| / 2))) / 2 := by
        gcongr
    _ = (4 * π) ^ ((A : ℝ) + k) * π ^ (A : ℝ) * C₁ * C₂ / 2 * (1 + |s.im|) ^ (2 * A + 2)
          * (Real.exp (π * |s.im| / 2) * Real.exp (π * |s.im| / 2)) := by ring
    _ = (4 * π) ^ ((A : ℝ) + k) * π ^ (A : ℝ) * C₁ * C₂ / 2 * (1 + |s.im|) ^ (2 * A + 2)
          * Real.exp (π * |s.im|) := by rw [hE]

include cf in
/-- **(b) `rsJ` is bounded on every vertical strip `−n ≤ Re s ≤ n + 1`.** -/
theorem exists_norm_rsJ_le (f : F) (hk : 0 < k) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, -(n : ℝ) ≤ s.re → s.re ≤ n + 1 → ‖rsJ k f s‖ ≤ C := by
  obtain ⟨M, hM⟩ := phi_mul_pow_bounded k f hk (n + 3)
  have hC := thetaC_pos n
  refine ⟨2 * thetaC n * |M| * volume.real (𝒟 : Set ℍ),
    mul_nonneg (by positivity) measureReal_nonneg, fun s hs1 hs2 => ?_⟩
  unfold rsJ
  refine norm_setIntegral_le_of_norm_le_const volume_fd_lt_top fun z hz => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (phi_nonneg k f z)]
  calc phi k f z * ‖epsteinΛ₀ z s‖ ≤ phi k f z * (2 * thetaC n * (1 + z.im) ^ (n + 3)) :=
        mul_le_mul_of_nonneg_left (norm_epsteinΛ₀_le_fd' n hz hs1 hs2) (phi_nonneg k f z)
    _ = 2 * thetaC n * (phi k f z * (1 + z.im) ^ (n + 3)) := by ring
    _ ≤ 2 * thetaC n * M := by nlinarith [hM z hz]
    _ ≤ 2 * thetaC n * |M| := by
        have := le_abs_self M
        nlinarith

include cf in
/-- **(b′) `rsLambda` is bounded on vertical strips away from the discs of radius `1/2` at `0`
and `1`.** -/
theorem exists_norm_rsLambda_le (f : F) (hk : 0 < k) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, -(n : ℝ) ≤ s.re → s.re ≤ n + 1 → 1 / 2 ≤ ‖s‖ → 1 / 2 ≤ ‖1 - s‖ →
      ‖rsLambda k f s‖ ≤ C := by
  obtain ⟨C, hC0, hJ⟩ := exists_norm_rsJ_le k f hk n
  refine ⟨C + 4 * ‖((∫ z in (𝒟 : Set ℍ), phi k f z : ℝ) : ℂ)‖, by positivity,
    fun s hs1 hs2 h0 h1 => ?_⟩
  have hs0 : 0 < ‖s‖ := by linarith
  have hs1' : 0 < ‖1 - s‖ := by linarith
  have hinv0 : ‖1 / s‖ ≤ 2 := by
    rw [norm_div, norm_one, div_le_iff₀ hs0]; linarith
  have hinv1 : ‖1 / (1 - s)‖ ≤ 2 := by
    rw [norm_div, norm_one, div_le_iff₀ hs1']; linarith
  have hsum : ‖1 / s + 1 / (1 - s)‖ ≤ 4 := by
    linarith [norm_add_le (1 / s) (1 / (1 - s))]
  unfold rsLambda
  calc ‖rsJ k f s - (1 / s + 1 / (1 - s)) * ((∫ z in (𝒟 : Set ℍ), phi k f z : ℝ) : ℂ)‖
      ≤ ‖rsJ k f s‖ + ‖(1 / s + 1 / (1 - s)) * ((∫ z in (𝒟 : Set ℍ), phi k f z : ℝ) : ℂ)‖ :=
        norm_sub_le _ _
    _ = ‖rsJ k f s‖ + ‖1 / s + 1 / (1 - s)‖ * ‖((∫ z in (𝒟 : Set ℍ), phi k f z : ℝ) : ℂ)‖ := by
        rw [norm_mul]
    _ ≤ C + 4 * ‖((∫ z in (𝒟 : Set ℍ), phi k f z : ℝ) : ℂ)‖ := by
        gcongr
        exact hJ s hs1 hs2

include cf in
/-- **(c) `rsG` on a vertical strip `−A ≤ Re s ≤ A`, off the discs at `0` and `1`**:
`‖G(s)‖ ≤ C (1 + |t|)^{2A+2} e^{π|t|}`. -/
theorem exists_norm_rsG_le (f : F) (hk : 0 < k) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, -(A : ℝ) ≤ s.re → s.re ≤ A → 1 / 2 ≤ ‖s‖ → 1 / 2 ≤ ‖1 - s‖ →
      ‖rsG k f s‖ ≤ C * (1 + |s.im|) ^ (2 * A + 2) * Real.exp (π * |s.im|) := by
  obtain ⟨Cp, hCp, hpre⟩ := exists_norm_rsPre_le k hk A
  obtain ⟨CΛ, hCΛ0, hΛ⟩ := exists_norm_rsLambda_le k f hk A
  refine ⟨Cp * (CΛ + 1), by positivity, fun s hs1 hs2 h0 h1 => ?_⟩
  have hΛs := hΛ s hs1 (by linarith) h0 h1
  rw [rsG_eq_rsPre_mul_rsLambda, norm_mul]
  calc ‖rsPre k s‖ * ‖rsLambda k f s‖
      ≤ (Cp * (1 + |s.im|) ^ (2 * A + 2) * Real.exp (π * |s.im|)) * (CΛ + 1) :=
        mul_le_mul (hpre s hs1 hs2) (by linarith) (norm_nonneg _) (by positivity)
    _ = Cp * (CΛ + 1) * (1 + |s.im|) ^ (2 * A + 2) * Real.exp (π * |s.im|) := by ring

end RankinSelbergDelta.RankinSelberg

/-! ### POLYNOMIAL growth of the Rankin–Selberg square `G = Gfull` on the strip
`−1/8 ≤ Re s ≤ 2`: Phragmén–Lindelöf for the entire function
`E(s) = s(1−s) rsJ(s) − ∫Φ = s(1−s) rsLambda(s)` with the weight `lPhi²`, boundary values from the
absolutely convergent Dirichlet series `ζ(2s) D(s+k−1)` on `Re s = 9/8` and the sharp Γ upper bounds
(`exists_norm_Gamma_le`), transported to `Re s = −1/8` by `rsJ_symm`. -/

namespace RankinSelbergDelta.RankinSelberg

open Complex UpperHalfPlane MeasureTheory Set Filter RankinSelbergDelta.Eisenstein
open scoped Real Topology Modular

/-! #### Dirichlet-series bounds on the right -/

/-- `Σ 1/n^σ` (the real zeta series). -/
noncomputable def zetaBound (σ : ℝ) : ℝ := ∑' n : ℕ, 1 / (n : ℝ) ^ σ

lemma norm_one_div_natCast_cpow {s : ℂ} (hs : 1 < s.re) (n : ℕ) :
    ‖1 / (n : ℂ) ^ s‖ = 1 / (n : ℝ) ^ s.re := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [zero_cpow (Complex.ne_zero_of_one_lt_re hs), Real.zero_rpow (by linarith : s.re ≠ 0)]
  · rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos hn]

lemma norm_zeta_le {s : ℂ} (hs : 1 < s.re) : ‖riemannZeta s‖ ≤ zetaBound s.re := by
  rw [zeta_eq_tsum_one_div_nat_cpow hs]
  have hsum : Summable fun n : ℕ => ‖1 / (n : ℂ) ^ s‖ :=
    (Real.summable_one_div_nat_rpow.mpr hs).congr fun n => (norm_one_div_natCast_cpow hs n).symm
  refine (norm_tsum_le_tsum_norm hsum).trans (le_of_eq ?_)
  unfold zetaBound
  exact tsum_congr fun n => norm_one_div_natCast_cpow hs n

lemma zetaBound_nonneg (σ : ℝ) : 0 ≤ zetaBound σ := tsum_nonneg fun n => by positivity

lemma zetaBound_anti {σ τ : ℝ} (hσ : 1 < σ) (h : σ ≤ τ) : zetaBound τ ≤ zetaBound σ := by
  unfold zetaBound
  refine Summable.tsum_le_tsum (fun n => ?_) (Real.summable_one_div_nat_rpow.mpr (by linarith))
    (Real.summable_one_div_nat_rpow.mpr hσ)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Real.zero_rpow (by linarith : σ ≠ 0), Real.zero_rpow (by linarith : τ ≠ 0)]
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact one_div_le_one_div_of_le (by positivity) (Real.rpow_le_rpow_of_exponent_le hn1 h)

variable {F : Type*} [FunLike F ℍ ℂ] (k : ℤ)
  [cf : CuspFormClass F (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma 1)) k]

/-- `Σ ‖a_n‖² / n^σ` (the real Rankin–Selberg series). -/
noncomputable def rsDbound (f : F) (σ : ℝ) : ℝ :=
  ∑' n : ℕ, ‖(ModularFormClass.qExpansion 1 f).coeff n‖ ^ 2 / (n : ℝ) ^ σ

include cf in
lemma norm_rsD_term (f : F) (w : ℂ) (n : ℕ) :
    ‖((‖(ModularFormClass.qExpansion 1 f).coeff n‖ : ℂ)) ^ 2 / (n : ℂ) ^ w‖
      = ‖(ModularFormClass.qExpansion 1 f).coeff n‖ ^ 2 / (n : ℝ) ^ w.re := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [RankinSelbergDelta.CuspForm.qExpansion_coeff_zero_cusp f]
  · rw [norm_div, norm_pow, Complex.norm_real, norm_norm, Complex.norm_natCast_cpow_of_pos hn]

include cf in
lemma norm_rsD_le (f : F) (hk : 0 < k) {w : ℂ} (hw : (k : ℝ) < w.re) :
    ‖rsD f w‖ ≤ rsDbound f w.re := by
  have hsum : Summable fun n : ℕ =>
      ‖((‖(ModularFormClass.qExpansion 1 f).coeff n‖ : ℂ)) ^ 2 / (n : ℂ) ^ w‖ :=
    (summable_rsDirichlet' k f hk hw).congr fun n => (norm_rsD_term k f w n).symm
  unfold rsD rsDbound
  refine (norm_tsum_le_tsum_norm hsum).trans (le_of_eq ?_)
  exact tsum_congr fun n => norm_rsD_term k f w n

include cf in
lemma rsDbound_nonneg (f : F) (σ : ℝ) : 0 ≤ rsDbound f σ := tsum_nonneg fun n => by positivity

include cf in
lemma rsDbound_anti (f : F) (hk : 0 < k) {σ τ : ℝ} (hσ : (k : ℝ) < σ) (h : σ ≤ τ) :
    rsDbound f τ ≤ rsDbound f σ := by
  unfold rsDbound
  refine Summable.tsum_le_tsum (fun n => ?_) (summable_rsDirichlet' k f hk (by linarith))
    (summable_rsDirichlet' k f hk hσ)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [RankinSelbergDelta.CuspForm.qExpansion_coeff_zero_cusp f]
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (Real.rpow_le_rpow_of_exponent_le hn1 h)

/-! #### `rsPre⁻¹` and `rsLambda` on the right edge -/

lemma rsPre_ne_zero (hk : 0 < k) {s : ℂ} (hs : 0 < s.re) : rsPre k s ≠ 0 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h4π : ((4 * Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hP1 : ((4 * Real.pi : ℝ) : ℂ) ^ (s + k - 1) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; push_neg; intro h; exact absurd h h4π
  have hP2 : (Real.pi : ℂ) ^ s ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; push_neg; intro h; exact absurd h hπ
  have hΓ1 : Complex.Gamma (s + k - 1) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by rw [shiftk_re]; linarith)
  have hΓ2 : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs
  unfold rsPre
  exact div_ne_zero (mul_ne_zero (mul_ne_zero hP1 hP2) (mul_ne_zero (inv_ne_zero hΓ1) (inv_ne_zero hΓ2)))
    two_ne_zero

lemma inv_rsPre_eq (s : ℂ) :
    (rsPre k s)⁻¹ = 2 * Complex.Gamma (s + k - 1) * Complex.Gamma s
      * (((4 * Real.pi : ℝ) : ℂ) ^ (s + k - 1))⁻¹ * ((Real.pi : ℂ) ^ s)⁻¹ := by
  unfold rsPre
  rw [inv_div, div_eq_mul_inv, mul_inv, mul_inv, mul_inv, inv_inv, inv_inv]
  ring

/-- `‖(rsPre s)⁻¹‖ ≤ 2 ‖Γ(s+k−1)‖ ‖Γ(s)‖` for `Re s ≥ 0` (the powers of `4π`, `π` have norm `≥ 1`). -/
lemma norm_inv_rsPre_le (hk : 0 < k) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖(rsPre k s)⁻¹‖ ≤ 2 * ‖Complex.Gamma (s + k - 1)‖ * ‖Complex.Gamma s‖ := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hP1 : 1 ≤ ‖((4 * Real.pi : ℝ) : ℂ) ^ (s + k - 1)‖ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), shiftk_re]
    exact Real.one_le_rpow (by linarith [Real.pi_gt_three]) (by linarith)
  have hP2 : 1 ≤ ‖(Real.pi : ℂ) ^ s‖ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    exact Real.one_le_rpow (by linarith [Real.pi_gt_three]) hs
  rw [inv_rsPre_eq, norm_mul, norm_mul, norm_mul, norm_mul, norm_inv, norm_inv, Complex.norm_ofNat]
  have h1 : ‖((4 * Real.pi : ℝ) : ℂ) ^ (s + k - 1)‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hP1
  have h2 : ‖(Real.pi : ℂ) ^ s‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hP2
  calc 2 * ‖Complex.Gamma (s + k - 1)‖ * ‖Complex.Gamma s‖
        * ‖((4 * Real.pi : ℝ) : ℂ) ^ (s + k - 1)‖⁻¹ * ‖(Real.pi : ℂ) ^ s‖⁻¹
      ≤ 2 * ‖Complex.Gamma (s + k - 1)‖ * ‖Complex.Gamma s‖ * 1 * 1 := by
        gcongr
    _ = 2 * ‖Complex.Gamma (s + k - 1)‖ * ‖Complex.Gamma s‖ := by ring

include cf in
lemma rsLambda_eq_rsG_mul_inv (f : F) (hk : 0 < k) {s : ℂ} (hs : 0 < s.re) :
    rsLambda k f s = rsG k f s * (rsPre k s)⁻¹ := by
  rw [rsG_eq_rsPre_mul_rsLambda, mul_comm (rsPre k s) (rsLambda k f s), mul_assoc,
    mul_inv_cancel₀ (rsPre_ne_zero k hk hs), mul_one]

include cf in
/-- `‖G(9/8 + it)‖ ≤ ζ(9/4) · D(k + 1/8)` by the absolutely convergent Dirichlet series. -/
lemma norm_rsG_right (f : F) (hk : 0 < k) {s : ℂ} (hs : s.re = 9 / 8) :
    ‖rsG k f s‖ ≤ zetaBound (9 / 4) * rsDbound f (9 / 8 + k - 1) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hG : rsG k f s = Gfull k f s := by
    unfold Gfull; rw [if_pos (by rw [hs]; norm_num)]
  rw [hG, Gfull_eq k f hk (by rw [hs]; norm_num), norm_mul]
  have h2 : (2 * s).re = 9 / 4 := by
    rw [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, hs]; norm_num
  have hz : ‖riemannZeta (2 * s)‖ ≤ zetaBound (9 / 4) := by
    have := norm_zeta_le (s := 2 * s) (by rw [h2]; norm_num)
    rwa [h2] at this
  have hre : (s + k - 1).re = 9 / 8 + k - 1 := by rw [shiftk_re, hs]
  have hd : ‖rsD f (s + k - 1)‖ ≤ rsDbound f (9 / 8 + k - 1) := by
    have := norm_rsD_le k f hk (w := s + k - 1) (by rw [hre]; linarith)
    rwa [hre] at this
  exact mul_le_mul hz hd (norm_nonneg _) (zetaBound_nonneg _)

include cf in
/-- **`rsLambda` on the right edge** `Re s = 9/8`: `C (1 + |t|)^{2m+2} e^{−π|t|}`, `m = k`. -/
lemma exists_norm_rsLambda_right (f : F) (hk : 0 < k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, s.re = 9 / 8 →
      ‖rsLambda k f s‖ ≤ C * (1 + |s.im|) ^ (2 * k.toNat + 2) * Real.exp (-(π * |s.im|)) := by
  obtain ⟨CΓ, hCΓ, hΓ⟩ := exists_norm_Gamma_le k.toNat
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hm : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk.le
  have hz0 := zetaBound_nonneg (9 / 4)
  have hd0 := rsDbound_nonneg k f (9 / 8 + k - 1)
  refine ⟨zetaBound (9 / 4) * rsDbound f (9 / 8 + k - 1) * (2 * CΓ * CΓ), by positivity,
    fun s hs => ?_⟩
  have hspos : 0 < s.re := by rw [hs]; norm_num
  have hre := shiftk_re k s
  have him := shiftk_im k s
  have hG1 : ‖Complex.Gamma (s + k - 1)‖
      ≤ CΓ * (1 + |s.im|) ^ (k.toNat + 1) * Real.exp (-(π * |s.im| / 2)) := by
    have := hΓ (s + k - 1) (by rw [hre, hs]; linarith) (by rw [hre, hs, hm]; linarith)
    rwa [him] at this
  have hG2 : ‖Complex.Gamma s‖
      ≤ CΓ * (1 + |s.im|) ^ (k.toNat + 1) * Real.exp (-(π * |s.im| / 2)) :=
    hΓ s (by rw [hs]; norm_num) (by rw [hs]; linarith [(Nat.cast_nonneg k.toNat : (0 : ℝ) ≤ k.toNat)])
  have hE : Real.exp (-(π * |s.im| / 2)) * Real.exp (-(π * |s.im| / 2)) = Real.exp (-(π * |s.im|)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [rsLambda_eq_rsG_mul_inv k f hk hspos, norm_mul]
  calc ‖rsG k f s‖ * ‖(rsPre k s)⁻¹‖
      ≤ (zetaBound (9 / 4) * rsDbound f (9 / 8 + k - 1))
          * (2 * ‖Complex.Gamma (s + k - 1)‖ * ‖Complex.Gamma s‖) :=
        mul_le_mul (norm_rsG_right k f hk hs) (norm_inv_rsPre_le k hk hspos.le) (norm_nonneg _)
          (by positivity)
    _ ≤ (zetaBound (9 / 4) * rsDbound f (9 / 8 + k - 1))
          * (2 * (CΓ * (1 + |s.im|) ^ (k.toNat + 1) * Real.exp (-(π * |s.im| / 2)))
              * (CΓ * (1 + |s.im|) ^ (k.toNat + 1) * Real.exp (-(π * |s.im| / 2)))) := by
        gcongr
    _ = zetaBound (9 / 4) * rsDbound f (9 / 8 + k - 1) * (2 * CΓ * CΓ)
          * (1 + |s.im|) ^ (2 * k.toNat + 2)
          * (Real.exp (-(π * |s.im| / 2)) * Real.exp (-(π * |s.im| / 2))) := by ring
    _ = zetaBound (9 / 4) * rsDbound f (9 / 8 + k - 1) * (2 * CΓ * CΓ)
          * (1 + |s.im|) ^ (2 * k.toNat + 2) * Real.exp (-(π * |s.im|)) := by rw [hE]

/-! #### The entire function `E(s) = s(1−s) rsJ(s) − ∫Φ` -/

/-- `E(s) = s(1−s)·rsJ(s) − ∫Φ`, entire, equal to `s(1−s)·rsLambda(s)` off `{0, 1}`. -/
noncomputable def rsE (f : F) (s : ℂ) : ℂ :=
  s * (1 - s) * rsJ k f s - ((∫ z in (𝒟 : Set ℍ), phi k f z : ℝ) : ℂ)

include cf in
lemma rsE_eq (f : F) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    rsE k f s = s * (1 - s) * rsLambda k f s := by
  have h1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  unfold rsE rsLambda
  field_simp
  ring

include cf in
lemma rsE_symm (f : F) (s : ℂ) : rsE k f (1 - s) = rsE k f s := by
  unfold rsE
  rw [← rsJ_symm k f s]
  ring

include cf in
lemma differentiable_rsE (f : F) (hk : 0 < k) : Differentiable ℂ (rsE k f) := by
  have h : Differentiable ℂ fun s : ℂ => s * (1 - s) * rsJ k f s :=
    (differentiable_id.mul ((differentiable_const _).sub differentiable_id)).mul
      (differentiable_rsJ k f hk)
  exact h.sub_const _

lemma norm_le_two_mul_of_re_le {s : ℂ} (h : |s.re| ≤ 2) : ‖s‖ ≤ 2 * (1 + |s.im|) := by
  have := Complex.norm_le_abs_re_add_abs_im s
  linarith [abs_nonneg s.im]

include cf in
/-- `‖E‖` on both edges `Re s = 9/8`, `Re s = −1/8`: `C (1+|t|)^{2m+4} e^{−π|t|}`. -/
lemma exists_norm_rsE_edges (f : F) (hk : 0 < k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, (s.re = 9 / 8 ∨ s.re = -1 / 8) →
      ‖rsE k f s‖ ≤ C * (1 + |s.im|) ^ (2 * k.toNat + 4) * Real.exp (-(π * |s.im|)) := by
  obtain ⟨C, hC, hΛ⟩ := exists_norm_rsLambda_right k f hk
  have hright : ∀ s : ℂ, s.re = 9 / 8 →
      ‖rsE k f s‖ ≤ 4 * C * (1 + |s.im|) ^ (2 * k.toNat + 4) * Real.exp (-(π * |s.im|)) := by
    intro s hs
    have hs0 : s ≠ 0 := by intro h; rw [h, Complex.zero_re] at hs; norm_num at hs
    have hs1 : s ≠ 1 := by intro h; rw [h, Complex.one_re] at hs; norm_num at hs
    have hn1 : ‖s‖ ≤ 2 * (1 + |s.im|) := norm_le_two_mul_of_re_le (by rw [hs, abs_le]; constructor <;> norm_num)
    have hn2 : ‖1 - s‖ ≤ 2 * (1 + |s.im|) := by
      have : |(1 - s).re| ≤ 2 := by rw [Complex.sub_re, Complex.one_re, hs, abs_le]; constructor <;> norm_num
      have h := norm_le_two_mul_of_re_le this
      rwa [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at h
    rw [rsE_eq k f hs0 hs1, norm_mul, norm_mul]
    calc ‖s‖ * ‖1 - s‖ * ‖rsLambda k f s‖
        ≤ (2 * (1 + |s.im|)) * (2 * (1 + |s.im|))
            * (C * (1 + |s.im|) ^ (2 * k.toNat + 2) * Real.exp (-(π * |s.im|))) :=
          mul_le_mul (mul_le_mul hn1 hn2 (norm_nonneg _) (by positivity)) (hΛ s hs) (norm_nonneg _)
            (by positivity)
      _ = 4 * C * (1 + |s.im|) ^ (2 * k.toNat + 4) * Real.exp (-(π * |s.im|)) := by ring
  refine ⟨4 * C, by positivity, fun s hs => ?_⟩
  rcases hs with hs | hs
  · exact hright s hs
  · rw [← rsE_symm k f s]
    have h1 : (1 - s).re = 9 / 8 := by rw [Complex.sub_re, Complex.one_re, hs]; norm_num
    have h2 : |(1 - s).im| = |s.im| := by rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
    have := hright (1 - s) h1
    rwa [h2] at this

/-- The weighted function `H(s) = E(s) φ(s)² / (s + 2)^{2m+4}`. -/
noncomputable def rsH (f : F) (s : ℂ) : ℂ :=
  rsE k f s * lPhi s ^ 2 / (s + 2) ^ (2 * k.toNat + 4)

include cf in
lemma differentiableOn_rsH (f : F) (hk : 0 < k) :
    DifferentiableOn ℂ (rsH k f) {w : ℂ | -1 / 8 ≤ w.re ∧ w.re ≤ 9 / 8} := by
  unfold rsH
  refine DifferentiableOn.div
    ((differentiable_rsE k f hk).mul (differentiable_lPhi.pow 2)).differentiableOn
    ((differentiable_id.add_const _).pow _).differentiableOn fun z hz => ?_
  exact pow_ne_zero _ (add_two_ne_zero' hz.1)

include cf in
lemma norm_rsH_le_edges (f : F) (hk : 0 < k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, (w.re = 9 / 8 ∨ w.re = -1 / 8) → ‖rsH k f w‖ ≤ C := by
  obtain ⟨C, hC, hedge⟩ := exists_norm_rsE_edges k f hk
  refine ⟨C * 2 ^ (2 * k.toNat + 4), by positivity, fun w hw => ?_⟩
  have h1 : -1 / 8 ≤ w.re := by rcases hw with hw | hw <;> rw [hw] <;> norm_num
  have hden := norm_add_two_ge' h1
  have hdenpos : 0 < ‖w + 2‖ := by linarith [abs_nonneg w.im]
  have hphi : ‖lPhi w ^ 2‖ ≤ Real.exp (π * |w.im|) := by
    rw [norm_pow]
    calc ‖lPhi w‖ ^ 2 ≤ (Real.exp (π * |w.im| / 2)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_lPhi_le w) 2
      _ = Real.exp (π * |w.im|) := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hE : Real.exp (-(π * |w.im|)) * Real.exp (π * |w.im|) = 1 := by
    rw [← Real.exp_add]; simp
  unfold rsH
  rw [norm_div, norm_mul, norm_pow (w + 2) (2 * k.toNat + 4), div_le_iff₀ (pow_pos hdenpos _)]
  calc ‖rsE k f w‖ * ‖lPhi w ^ 2‖
      ≤ (C * (1 + |w.im|) ^ (2 * k.toNat + 4) * Real.exp (-(π * |w.im|))) * Real.exp (π * |w.im|) :=
        mul_le_mul (hedge w hw) hphi (norm_nonneg _) (by positivity)
    _ = C * (1 + |w.im|) ^ (2 * k.toNat + 4) * (Real.exp (-(π * |w.im|)) * Real.exp (π * |w.im|)) := by
        ring
    _ = C * (1 + |w.im|) ^ (2 * k.toNat + 4) := by rw [hE, mul_one]
    _ = C * 2 ^ (2 * k.toNat + 4) * ((1 + |w.im|) / 2) ^ (2 * k.toNat + 4) := by
        rw [div_pow]; field_simp
    _ ≤ C * 2 ^ (2 * k.toNat + 4) * ‖w + 2‖ ^ (2 * k.toNat + 4) := by
        have := pow_le_pow_left₀ (by positivity) hden (2 * k.toNat + 4)
        exact mul_le_mul_of_nonneg_left this (by positivity)

include cf in
lemma rsH_isBigO (f : F) (hk : 0 < k) :
    rsH k f =O[Filter.comap (fun z : ℂ => |z.im|) Filter.atTop ⊓
        Filter.principal (Complex.re ⁻¹' Ioo (-1 / 8 : ℝ) (9 / 8))]
      fun z => Real.exp (π * Real.exp (2 * |z.im|)) := by
  obtain ⟨CJ, hCJ, hJ⟩ := exists_norm_rsJ_le k f hk 1
  set I₀ : ℝ := ‖((∫ z in (𝒟 : Set ℍ), phi k f z : ℝ) : ℂ)‖ with hI₀
  have hI₀0 : 0 ≤ I₀ := norm_nonneg _
  refine Asymptotics.IsBigO.of_bound (4 * CJ + I₀) ?_
  rw [Filter.eventually_inf_principal]
  refine Filter.Eventually.of_forall fun z hz => ?_
  have hz1 : -1 / 8 ≤ z.re := hz.1.le
  have hz2 : z.re ≤ 9 / 8 := hz.2.le
  have ht0 : 0 ≤ |z.im| := abs_nonneg _
  have hn1 : ‖z‖ ≤ 2 * (1 + |z.im|) := norm_le_two_mul_of_re_le (by rw [abs_le]; constructor <;> linarith)
  have hn2 : ‖1 - z‖ ≤ 2 * (1 + |z.im|) := by
    have : |(1 - z).re| ≤ 2 := by rw [Complex.sub_re, Complex.one_re, abs_le]; constructor <;> linarith
    have h := norm_le_two_mul_of_re_le this
    rwa [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at h
  have hJz : ‖rsJ k f z‖ ≤ CJ := hJ z (by push_cast; linarith) (by push_cast; linarith)
  -- `‖E z‖ ≤ 4 CJ (1+|t|)² + I₀ ≤ (4 CJ + I₀)(1+|t|)²`
  have hEz : ‖rsE k f z‖ ≤ (4 * CJ + I₀) * (1 + |z.im|) ^ 2 := by
    unfold rsE
    have hpow1 : (1 : ℝ) ≤ (1 + |z.im|) ^ 2 := one_le_pow₀ (by linarith)
    calc ‖z * (1 - z) * rsJ k f z - ((∫ w in (𝒟 : Set ℍ), phi k f w : ℝ) : ℂ)‖
        ≤ ‖z * (1 - z) * rsJ k f z‖ + I₀ := norm_sub_le _ _
      _ = ‖z‖ * ‖1 - z‖ * ‖rsJ k f z‖ + I₀ := by rw [norm_mul, norm_mul]
      _ ≤ (2 * (1 + |z.im|)) * (2 * (1 + |z.im|)) * CJ + I₀ := by
          have := mul_le_mul (mul_le_mul hn1 hn2 (norm_nonneg _) (by positivity)) hJz
            (norm_nonneg _) (by positivity)
          linarith
      _ = 4 * CJ * (1 + |z.im|) ^ 2 + I₀ * 1 := by ring
      _ ≤ 4 * CJ * (1 + |z.im|) ^ 2 + I₀ * (1 + |z.im|) ^ 2 := by gcongr
      _ = (4 * CJ + I₀) * (1 + |z.im|) ^ 2 := by ring
  have hphi : ‖lPhi z ^ 2‖ ≤ Real.exp (π * |z.im|) := by
    rw [norm_pow]
    calc ‖lPhi z‖ ^ 2 ≤ (Real.exp (π * |z.im| / 2)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_lPhi_le z) 2
      _ = Real.exp (π * |z.im|) := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hden := one_le_norm_add_two' hz1
  -- `(1+|t|)² e^{π|t|} ≤ e^{2|t|} e^{π|t|} = e^{(π+2)|t|} ≤ e^{π e^{2|t|}}`
  have hgrow : (1 + |z.im|) ^ 2 * Real.exp (π * |z.im|) ≤ Real.exp (π * Real.exp (2 * |z.im|)) := by
    have ha : 1 + |z.im| ≤ Real.exp |z.im| := by
      have := Real.add_one_le_exp |z.im|; linarith
    have hb : (1 + |z.im|) ^ 2 ≤ Real.exp (2 * |z.im|) := by
      have h2 : Real.exp (2 * |z.im|) = Real.exp |z.im| ^ 2 := by
        rw [← Real.exp_nat_mul]; norm_cast
      rw [h2]
      exact pow_le_pow_left₀ (by linarith) ha 2
    have hc : (π + 2) * |z.im| ≤ π * Real.exp (2 * |z.im|) := by
      have := Real.add_one_le_exp (2 * |z.im|)
      nlinarith [Real.pi_gt_three]
    calc (1 + |z.im|) ^ 2 * Real.exp (π * |z.im|)
        ≤ Real.exp (2 * |z.im|) * Real.exp (π * |z.im|) :=
          mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
      _ = Real.exp ((π + 2) * |z.im|) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (π * Real.exp (2 * |z.im|)) := Real.exp_le_exp.mpr hc
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  unfold rsH
  rw [norm_div, norm_mul, norm_pow (z + 2) (2 * k.toNat + 4), div_le_iff₀ (pow_pos (by linarith) _)]
  have hM : 0 ≤ 4 * CJ + I₀ := by positivity
  calc ‖rsE k f z‖ * ‖lPhi z ^ 2‖
      ≤ ((4 * CJ + I₀) * (1 + |z.im|) ^ 2) * Real.exp (π * |z.im|) :=
        mul_le_mul hEz hphi (norm_nonneg _) (by positivity)
    _ = (4 * CJ + I₀) * ((1 + |z.im|) ^ 2 * Real.exp (π * |z.im|)) := by ring
    _ ≤ (4 * CJ + I₀) * Real.exp (π * Real.exp (2 * |z.im|)) :=
        mul_le_mul_of_nonneg_left hgrow hM
    _ = (4 * CJ + I₀) * Real.exp (π * Real.exp (2 * |z.im|)) * 1 := by ring
    _ ≤ (4 * CJ + I₀) * Real.exp (π * Real.exp (2 * |z.im|)) * ‖z + 2‖ ^ (2 * k.toNat + 4) := by
        have := one_le_pow₀ (M₀ := ℝ) hden (n := 2 * k.toNat + 4)
        exact mul_le_mul_of_nonneg_left this (by positivity)

include cf in
theorem exists_norm_rsH_le_strip (f : F) (hk : 0 < k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, -1 / 8 ≤ w.re → w.re ≤ 9 / 8 → ‖rsH k f w‖ ≤ C := by
  obtain ⟨C, hC, hedge⟩ := norm_rsH_le_edges k f hk
  refine ⟨C, hC, fun w h1 h2 => ?_⟩
  refine PhragmenLindelof.vertical_strip (a := -1 / 8) (b := 9 / 8) ?_ ?_ ?_ ?_ h1 h2
  · exact DifferentiableOn.diffContOnCl
      ((differentiableOn_rsH k f hk).mono (closure_strip_subset' _ _))
  · refine ⟨2, ?_, π, rsH_isBigO k f hk⟩
    rw [show (9 / 8 : ℝ) - -1 / 8 = 5 / 4 by norm_num, lt_div_iff₀ (by norm_num)]
    linarith [Real.pi_gt_three]
  · intro z hz
    exact hedge z (Or.inr hz)
  · intro z hz
    exact hedge z (Or.inl hz)

include cf in
/-- **`E` on the strip**: `‖E(s)‖ ≤ C (1+|t|)^{2m+4} e^{−π|t|}` for `−1/8 ≤ Re s ≤ 9/8`. -/
theorem exists_norm_rsE_le_strip (f : F) (hk : 0 < k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, -1 / 8 ≤ s.re → s.re ≤ 9 / 8 →
      ‖rsE k f s‖ ≤ C * (1 + |s.im|) ^ (2 * k.toNat + 4) * Real.exp (-(π * |s.im|)) := by
  obtain ⟨C, hC, hH⟩ := exists_norm_rsH_le_strip k f hk
  refine ⟨C * 4 ^ (2 * k.toNat + 4) * 16, by positivity, fun w h1 h2 => ?_⟩
  have hphi_ne : lPhi w ≠ 0 := lPhi_ne_zero h1 h2
  have hphipos : 0 < ‖lPhi w ^ 2‖ := by rw [norm_pow]; positivity
  have hden_ne : w + 2 ≠ 0 := add_two_ne_zero' h1
  have hw' : rsE k f w = rsH k f w * (w + 2) ^ (2 * k.toNat + 4) / lPhi w ^ 2 := by
    unfold rsH; field_simp
  have hphi : Real.exp (π * |w.im|) / 16 ≤ ‖lPhi w ^ 2‖ := by
    rw [norm_pow]
    calc Real.exp (π * |w.im|) / 16 = (Real.exp (π * |w.im| / 2) / 4) ^ 2 := by
          rw [div_pow, ← Real.exp_nat_mul]; push_cast
          rw [show (2 : ℝ) * (π * |w.im| / 2) = π * |w.im| by ring]; norm_num
      _ ≤ ‖lPhi w‖ ^ 2 := pow_le_pow_left₀ (by positivity) (norm_lPhi_ge h1 h2) 2
  have hden := norm_add_two_le' h1 h2
  have hE : 0 < Real.exp (π * |w.im|) := Real.exp_pos _
  rw [hw', norm_div, norm_mul, norm_pow, div_le_iff₀ hphipos]
  calc ‖rsH k f w‖ * ‖w + 2‖ ^ (2 * k.toNat + 4)
      ≤ C * (4 * (1 + |w.im|)) ^ (2 * k.toNat + 4) := by
        have := pow_le_pow_left₀ (norm_nonneg _) hden (2 * k.toNat + 4)
        exact mul_le_mul (hH w h1 h2) this (by positivity) hC
    _ = C * 4 ^ (2 * k.toNat + 4) * 16 * (1 + |w.im|) ^ (2 * k.toNat + 4) * Real.exp (-(π * |w.im|))
          * (Real.exp (π * |w.im|) / 16) := by
        rw [Real.exp_neg, mul_pow]; field_simp
    _ ≤ C * 4 ^ (2 * k.toNat + 4) * 16 * (1 + |w.im|) ^ (2 * k.toNat + 4) * Real.exp (-(π * |w.im|))
          * ‖lPhi w ^ 2‖ := by
        exact mul_le_mul_of_nonneg_left hphi (by positivity)

include cf in
/-- **`rsLambda` on the strip, away from the real axis**: for `|t| ≥ 1`,
`‖rsLambda(s)‖ ≤ ‖E(s)‖` since `‖s‖, ‖1 − s‖ ≥ |t| ≥ 1`. -/
theorem exists_norm_rsLambda_le_strip' (f : F) (hk : 0 < k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, -1 / 8 ≤ s.re → s.re ≤ 9 / 8 → 1 ≤ |s.im| →
      ‖rsLambda k f s‖ ≤ C * (1 + |s.im|) ^ (2 * k.toNat + 4) * Real.exp (-(π * |s.im|)) := by
  obtain ⟨C, hC, hE⟩ := exists_norm_rsE_le_strip k f hk
  refine ⟨C, hC, fun s h1 h2 ht => ?_⟩
  have hs0 : s ≠ 0 := by intro h; rw [h, Complex.zero_im, abs_zero] at ht; linarith
  have hs1 : s ≠ 1 := by intro h; rw [h, Complex.one_im, abs_zero] at ht; linarith
  have hn1 : 1 ≤ ‖s‖ := le_trans ht (Complex.abs_im_le_norm s)
  have hn2 : 1 ≤ ‖1 - s‖ := by
    have := Complex.abs_im_le_norm (1 - s)
    rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at this
    exact le_trans ht this
  have hEs := hE s h1 h2
  rw [rsE_eq k f hs0 hs1, norm_mul, norm_mul] at hEs
  calc ‖rsLambda k f s‖ = 1 * 1 * ‖rsLambda k f s‖ := by ring
    _ ≤ ‖s‖ * ‖1 - s‖ * ‖rsLambda k f s‖ := by gcongr
    _ ≤ C * (1 + |s.im|) ^ (2 * k.toNat + 4) * Real.exp (-(π * |s.im|)) := hEs

include cf in
/-- **Polynomial growth of `rsG` on the strip `−1/8 ≤ Re s ≤ 9/8`** for `|t| ≥ 1`. -/
theorem exists_norm_rsG_le_strip (f : F) (hk : 0 < k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, -1 / 8 ≤ s.re → s.re ≤ 9 / 8 → 1 ≤ |s.im| →
      ‖rsG k f s‖ ≤ C * (1 + |s.im|) ^ (2 * k.toNat + 10) := by
  obtain ⟨Cp, hCp, hpre⟩ := exists_norm_rsPre_le k hk 2
  obtain ⟨CΛ, hCΛ, hΛ⟩ := exists_norm_rsLambda_le_strip' k f hk
  refine ⟨Cp * CΛ, by positivity, fun s h1 h2 ht => ?_⟩
  have hE : Real.exp (π * |s.im|) * Real.exp (-(π * |s.im|)) = 1 := by
    rw [← Real.exp_add]; simp
  rw [rsG_eq_rsPre_mul_rsLambda, norm_mul]
  calc ‖rsPre k s‖ * ‖rsLambda k f s‖
      ≤ (Cp * (1 + |s.im|) ^ (2 * 2 + 2) * Real.exp (π * |s.im|))
          * (CΛ * (1 + |s.im|) ^ (2 * k.toNat + 4) * Real.exp (-(π * |s.im|))) :=
        mul_le_mul (hpre s (by push_cast; linarith) (by push_cast; linarith)) (hΛ s h1 h2 ht)
          (norm_nonneg _) (by positivity)
    _ = Cp * CΛ * (1 + |s.im|) ^ (2 * k.toNat + 10)
          * (Real.exp (π * |s.im|) * Real.exp (-(π * |s.im|))) := by ring
    _ = Cp * CΛ * (1 + |s.im|) ^ (2 * k.toNat + 10) := by rw [hE, mul_one]

include cf in
/-- **POLYNOMIAL VERTICAL GROWTH OF THE RANKIN–SELBERG SQUARE** `G = Gfull` on
`−1/8 ≤ Re s ≤ 2`, `|Im s| ≥ 1`: `‖G(s)‖ ≤ C (1 + |Im s|)^{2k+10}`. -/
theorem exists_norm_Gfull_le_strip (f : F) (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, -1 / 8 ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
      ‖Gfull k f s‖ ≤ C * (1 + |s.im|) ^ (2 * k.toNat + 10) := by
  obtain ⟨C₁, hC₁, hG⟩ := exists_norm_rsG_le_strip k f hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hz0 := zetaBound_nonneg (9 / 4)
  have hd0 := rsDbound_nonneg k f (9 / 8 + k - 1)
  refine ⟨C₁ + zetaBound (9 / 4) * rsDbound f (9 / 8 + k - 1) + 1, by positivity,
    fun s h1 h2 ht => ?_⟩
  have hpow : (1 : ℝ) ≤ (1 + |s.im|) ^ (2 * k.toNat + 10) := one_le_pow₀ (by linarith [abs_nonneg s.im])
  rcases le_or_gt s.re (9 / 8) with h98 | h98
  · -- the strip of the PL argument: `Gfull = rsG`
    have hG' : Gfull k f s = rsG k f s := by unfold Gfull; rw [if_pos (by linarith)]
    rw [hG']
    calc ‖rsG k f s‖ ≤ C₁ * (1 + |s.im|) ^ (2 * k.toNat + 10) := hG s h1 h98 ht
      _ ≤ (C₁ + zetaBound (9 / 4) * rsDbound f (9 / 8 + k - 1) + 1) * (1 + |s.im|) ^ (2 * k.toNat + 10) := by
          gcongr; linarith [mul_nonneg hz0 hd0]
  · -- `9/8 < Re s ≤ 2`: the Dirichlet series, with the monotone bounds
    rw [Gfull_eq k f hk (by linarith), norm_mul]
    have h2re : (2 * s).re = 2 * s.re := by rw [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat]; ring
    have hz : ‖riemannZeta (2 * s)‖ ≤ zetaBound (9 / 4) := by
      have := norm_zeta_le (s := 2 * s) (by rw [h2re]; linarith)
      rw [h2re] at this
      exact this.trans (zetaBound_anti (by norm_num) (by linarith))
    have hre := shiftk_re k s
    have hd : ‖rsD f (s + k - 1)‖ ≤ rsDbound f (9 / 8 + k - 1) := by
      have := norm_rsD_le k f hk (w := s + k - 1) (by rw [hre]; linarith)
      rw [hre] at this
      exact this.trans (rsDbound_anti k f hk (by linarith) (by linarith))
    calc ‖riemannZeta (2 * s)‖ * ‖rsD f (s + k - 1)‖
        ≤ zetaBound (9 / 4) * rsDbound f (9 / 8 + k - 1) :=
          mul_le_mul hz hd (norm_nonneg _) hz0
      _ = zetaBound (9 / 4) * rsDbound f (9 / 8 + k - 1) * 1 := by ring
      _ ≤ (C₁ + zetaBound (9 / 4) * rsDbound f (9 / 8 + k - 1) + 1) * (1 + |s.im|) ^ (2 * k.toNat + 10) := by
          gcongr
          linarith

end RankinSelbergDelta.RankinSelberg

/-! ### `rsG = ζ(2s) D(s+k−1)` on all of `Re s > 1`, nonvanishing there, and the growth
of `G = Gfull` on every strip `−A ≤ Re s` (functional equation + the Γ bounds). Inputs for the
de la Vallée Poussin log-derivative bounds. -/

namespace RankinSelbergDelta.RankinSelberg

open Complex UpperHalfPlane MeasureTheory Set Filter RankinSelbergDelta.Eisenstein
open scoped Real Topology Modular

variable {F : Type*} [FunLike F ℍ ℂ] (k : ℤ)
  [cf : CuspFormClass F (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma 1)) k]

include cf in
/-- `D` is holomorphic on `Re w > k`. -/
lemma differentiableOn_rsD (f : F) (hk : 0 < k) :
    DifferentiableOn ℂ (rsD f) {w : ℂ | (k : ℝ) < w.re} := by
  have heq : rsD f = LSeries (fun n => (‖(ModularFormClass.qExpansion 1 f).coeff n‖ ^ 2 : ℂ)) :=
    funext fun w => rsD_eq_LSeries k f w
  rw [heq]
  refine (LSeries_differentiableOn _).mono fun w hw => ?_
  simp only [Set.mem_setOf_eq] at hw ⊢
  exact lt_of_le_of_lt (abscissaOfAbsConv_rs_le k f hk) (by exact_mod_cast hw)

include cf in
/-- The Dirichlet-series side is holomorphic on `Re s > 1`. -/
lemma differentiableOn_zeta_mul_rsD (f : F) (hk : 0 < k) :
    DifferentiableOn ℂ (fun s => riemannZeta (2 * s) * rsD f (s + k - 1)) {s : ℂ | 1 < s.re} := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  intro s hs
  simp only [Set.mem_setOf_eq] at hs
  have hζ : DifferentiableAt ℂ (fun s => riemannZeta (2 * s)) s := by
    have h2 : (2 : ℂ) * s ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      rw [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.one_re] at this
      linarith
    exact (differentiableAt_riemannZeta h2).comp s (differentiableAt_id.const_mul 2)
  have hD : DifferentiableAt ℂ (fun s => rsD f (s + k - 1)) s := by
    have hmem : s + k - 1 ∈ {w : ℂ | (k : ℝ) < w.re} := by
      simp only [Set.mem_setOf_eq, shiftk_re]; linarith
    have hopen : IsOpen {w : ℂ | (k : ℝ) < w.re} := isOpen_lt continuous_const Complex.continuous_re
    exact ((differentiableOn_rsD k f hk).differentiableAt (hopen.mem_nhds hmem)).comp s
      ((differentiableAt_id.add_const _).sub_const _)
  exact (hζ.mul hD).differentiableWithinAt

include cf in
/-- **`rsG = ζ(2s) D(s+k−1)` on all of `Re s > 1`** (identity theorem from `1 < Re s < 9/4`). -/
theorem rsG_eq_zeta_mul_rsD' (f : F) (hk : 0 < k) {s : ℂ} (hs : 1 < s.re) :
    rsG k f s = riemannZeta (2 * s) * rsD f (s + k - 1) := by
  set U : Set ℂ := {s : ℂ | 1 < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : Convex ℝ U := convex_halfSpace_re_gt 1
  have hfa : AnalyticOnNhd ℂ (rsG k f) U :=
    DifferentiableOn.analyticOnNhd (fun z hz => (rsG_entire_off_poles k f hk
      (by intro h; rw [h] at hz; have : (1 : ℝ) < (0 : ℂ).re := hz; rw [Complex.zero_re] at this; linarith)
      (by intro h; rw [h] at hz; have : (1 : ℝ) < (1 : ℂ).re := hz; rw [Complex.one_re] at this; linarith)).differentiableWithinAt) hUo
  have hga : AnalyticOnNhd ℂ (fun s => riemannZeta (2 * s) * rsD f (s + k - 1)) U :=
    DifferentiableOn.analyticOnNhd (differentiableOn_zeta_mul_rsD k f hk) hUo
  have h2 : (2 : ℂ) ∈ U := by
    show (1 : ℝ) < (2 : ℂ).re
    rw [Complex.re_ofNat]; norm_num
  have hfreq : ∃ᶠ z in 𝓝[≠] (2 : ℂ), rsG k f z = riemannZeta (2 * z) * rsD f (z + k - 1) := by
    have hev : ∀ᶠ z in 𝓝 (2 : ℂ), rsG k f z = riemannZeta (2 * z) * rsD f (z + k - 1) := by
      have hopen : IsOpen {z : ℂ | 1 < z.re ∧ z.re < 9 / 4} :=
        (isOpen_lt continuous_const Complex.continuous_re).inter
          (isOpen_lt Complex.continuous_re continuous_const)
      filter_upwards [hopen.mem_nhds (by
        show (1 : ℝ) < (2 : ℂ).re ∧ (2 : ℂ).re < 9 / 4
        rw [Complex.re_ofNat]; constructor <;> norm_num)] with z hz
      exact rsG_eq_zeta_mul_rsD k f hk hz.1 hz.2
    exact (hev.filter_mono nhdsWithin_le_nhds).frequently
  exact AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hfa hga hUc.isPreconnected h2 hfreq hs

include cf in
theorem rsG_eq_Gfull_of_one_lt (f : F) (hk : 0 < k) {s : ℂ} (hs : 1 < s.re) :
    rsG k f s = Gfull k f s := by
  rw [rsG_eq_zeta_mul_rsD' k f hk hs, Gfull_eq k f hk hs]

include cf in
/-- **`G ≠ 0` on `Re s > 1`** for a Hecke eigenform (the Euler product is an exponential). -/
theorem Gfull_ne_zero_of_one_lt (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k)
    {s : ℂ} (hs : 1 < s.re) : Gfull k f s ≠ 0 := by
  rw [Gfull_eq k f hk hs, ← dlvpG_rs_eq k f hk hf hs]
  exact Complex.exp_ne_zero _

include cf in
/-- `G` is holomorphic off `{0, 1}` (it equals `rsG` on `Re s < 2` and the Dirichlet series on
`Re s > 1`). -/
theorem differentiableAt_Gfull (f : F) (hk : 0 < k) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (Gfull k f) s := by
  rcases lt_or_ge s.re 2 with h | h
  · have hopen : IsOpen {z : ℂ | z.re < 2} := isOpen_lt Complex.continuous_re continuous_const
    refine (rsG_entire_off_poles k f hk hs0 hs1).congr_of_eventuallyEq ?_
    filter_upwards [hopen.mem_nhds (show s ∈ {z : ℂ | z.re < 2} from h)] with z hz
    show Gfull k f z = rsG k f z
    unfold Gfull; rw [if_pos hz]
  · have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : s ∈ {z : ℂ | 1 < z.re} := by show 1 < s.re; linarith
    refine ((differentiableOn_zeta_mul_rsD k f hk).differentiableAt (hopen.mem_nhds hmem)).congr_of_eventuallyEq ?_
    filter_upwards [hopen.mem_nhds hmem] with z hz
    exact Gfull_eq k f hk hz

include cf in
/-- `‖G‖` on `Re s ≥ 9/8` is bounded by the Dirichlet series. -/
lemma norm_Gfull_le_of_le (f : F) (hk : 0 < k) {s : ℂ} (hs : 9 / 8 ≤ s.re) :
    ‖Gfull k f s‖ ≤ zetaBound (9 / 4) * rsDbound f (9 / 8 + k - 1) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  rw [Gfull_eq k f hk (by linarith), norm_mul]
  have h2re : (2 * s).re = 2 * s.re := by rw [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat]; ring
  have hz : ‖riemannZeta (2 * s)‖ ≤ zetaBound (9 / 4) := by
    have := norm_zeta_le (s := 2 * s) (by rw [h2re]; linarith)
    rw [h2re] at this
    exact this.trans (zetaBound_anti (by norm_num) (by linarith))
  have hre := shiftk_re k s
  have hd : ‖rsD f (s + k - 1)‖ ≤ rsDbound f (9 / 8 + k - 1) := by
    have := norm_rsD_le k f hk (w := s + k - 1) (by rw [hre]; linarith)
    rw [hre] at this
    exact this.trans (rsDbound_anti k f hk (by linarith) (by linarith))
  exact mul_le_mul hz hd (norm_nonneg _) (zetaBound_nonneg _)

include cf in
/-- **Polynomial growth of `G` on every half-strip `−A ≤ Re s`, `|Im s| ≥ 1`**, from the
functional equation `rsLambda s = rsLambda (1 − s)` and the Γ bounds on the left. -/
theorem exists_norm_Gfull_le_halfStrip (f : F) (hk : 0 < k) (A : ℕ) :
    ∃ C : ℝ, ∃ N : ℕ, 0 < C ∧ ∀ s : ℂ, -(A : ℝ) ≤ s.re → 1 ≤ |s.im| →
      ‖Gfull k f s‖ ≤ C * (1 + |s.im|) ^ N := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hm : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk.le
  obtain ⟨C₁, hC₁, hG₁⟩ := exists_norm_rsG_le_strip k f hk
  obtain ⟨Cp, hCp, hpre⟩ := exists_norm_rsPre_le k hk A
  set m : ℕ := k.toNat + A + 1 with hmdef
  obtain ⟨CΓ, hCΓ, hΓ⟩ := exists_norm_Gamma_le m
  have hz0 := zetaBound_nonneg (9 / 4)
  have hd0 := rsDbound_nonneg k f (9 / 8 + k - 1)
  set zD : ℝ := zetaBound (9 / 4) * rsDbound f (9 / 8 + k - 1) with hzD
  have hzD0 : 0 ≤ zD := mul_nonneg hz0 hd0
  -- the exponent, large enough for every region
  set N : ℕ := 2 * k.toNat + 10 + (2 * A + 2) + (2 * m + 2) with hN
  refine ⟨C₁ + zD + 1 + Cp * zD * (2 * CΓ * CΓ), N, by positivity, fun s hA ht => ?_⟩
  have ht0 : 0 ≤ |s.im| := abs_nonneg _
  have hpowN : ∀ j : ℕ, j ≤ N → (1 + |s.im|) ^ j ≤ (1 + |s.im|) ^ N :=
    fun j hj => pow_le_pow_right₀ (by linarith) hj
  have hpow1 : (1 : ℝ) ≤ (1 + |s.im|) ^ N := one_le_pow₀ (by linarith)
  have hCsum : 0 ≤ C₁ + zD + 1 + Cp * zD * (2 * CΓ * CΓ) := by positivity
  rcases le_or_gt (9 / 8 : ℝ) s.re with h98 | h98
  · -- right: Dirichlet series
    calc ‖Gfull k f s‖ ≤ zD := norm_Gfull_le_of_le k f hk h98
      _ ≤ (C₁ + zD + 1 + Cp * zD * (2 * CΓ * CΓ)) * (1 + |s.im|) ^ N := by
          have : zD ≤ C₁ + zD + 1 + Cp * zD * (2 * CΓ * CΓ) := by
            have : 0 ≤ Cp * zD * (2 * CΓ * CΓ) := by positivity
            linarith
          calc zD = zD * 1 := by ring
            _ ≤ (C₁ + zD + 1 + Cp * zD * (2 * CΓ * CΓ)) * (1 + |s.im|) ^ N :=
                mul_le_mul this hpow1 zero_le_one hCsum
  rcases le_or_gt (-1 / 8 : ℝ) s.re with h18 | h18
  · -- middle: the certified strip
    have hG' : Gfull k f s = rsG k f s := by unfold Gfull; rw [if_pos (by linarith)]
    rw [hG']
    calc ‖rsG k f s‖ ≤ C₁ * (1 + |s.im|) ^ (2 * k.toNat + 10) := hG₁ s h18 h98.le ht
      _ ≤ (C₁ + zD + 1 + Cp * zD * (2 * CΓ * CΓ)) * (1 + |s.im|) ^ N := by
          refine mul_le_mul ?_ (hpowN _ (by omega)) (by positivity) hCsum
          have : 0 ≤ Cp * zD * (2 * CΓ * CΓ) := by positivity
          linarith
  · -- left: the functional equation
    have hs0 : s ≠ 0 := by intro h; rw [h, Complex.zero_re] at h18; norm_num at h18
    have hs1 : s ≠ 1 := by intro h; rw [h, Complex.one_re] at h18; norm_num at h18
    have hG' : Gfull k f s = rsG k f s := by unfold Gfull; rw [if_pos (by linarith)]
    have h1s_re : (1 - s).re = 1 - s.re := by simp
    have h1s_im : |(1 - s).im| = |s.im| := by rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
    have h1s_pos : 0 < (1 - s).re := by rw [h1s_re]; linarith
    -- `rsLambda s = rsLambda (1 − s) = rsG (1 − s) · rsPre (1 − s)⁻¹`
    have hΛ : rsLambda k f s = rsG k f (1 - s) * (rsPre k (1 - s))⁻¹ := by
      rw [rsLambdaRS_functional_equation k f s, rsLambda_eq_rsG_mul_inv k f hk h1s_pos]
    -- `‖rsG (1 − s)‖ ≤ zD`
    have hG1s : ‖rsG k f (1 - s)‖ ≤ zD := by
      rw [rsG_eq_Gfull_of_one_lt k f hk (by rw [h1s_re]; linarith)]
      exact norm_Gfull_le_of_le k f hk (by rw [h1s_re]; linarith)
    -- `‖rsPre (1 − s)⁻¹‖ ≤ 2 ‖Γ(1 − s + k − 1)‖ ‖Γ(1 − s)‖`, each Γ with the sharp bound
    have hinv := norm_inv_rsPre_le k hk h1s_pos.le
    have hG1 : ‖Complex.Gamma (1 - s + k - 1)‖
        ≤ CΓ * (1 + |s.im|) ^ (m + 1) * Real.exp (-(π * |s.im| / 2)) := by
      have := hΓ (1 - s + k - 1) (by rw [shiftk_re, h1s_re]; linarith)
        (by rw [shiftk_re, h1s_re, hmdef]; push_cast; rw [hm]; linarith)
      rwa [shiftk_im, h1s_im] at this
    have hG2 : ‖Complex.Gamma (1 - s)‖
        ≤ CΓ * (1 + |s.im|) ^ (m + 1) * Real.exp (-(π * |s.im| / 2)) := by
      have := hΓ (1 - s) (by rw [h1s_re]; linarith)
        (by rw [h1s_re, hmdef]; push_cast; linarith [(Nat.cast_nonneg k.toNat : (0 : ℝ) ≤ k.toNat)])
      rwa [h1s_im] at this
    have hE : Real.exp (-(π * |s.im| / 2)) * Real.exp (-(π * |s.im| / 2)) = Real.exp (-(π * |s.im|)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hE2 : Real.exp (π * |s.im|) * Real.exp (-(π * |s.im|)) = 1 := by
      rw [← Real.exp_add]; simp
    have hΛn : ‖rsLambda k f s‖
        ≤ zD * (2 * CΓ * CΓ) * (1 + |s.im|) ^ (2 * m + 2) * Real.exp (-(π * |s.im|)) := by
      rw [hΛ, norm_mul]
      calc ‖rsG k f (1 - s)‖ * ‖(rsPre k (1 - s))⁻¹‖
          ≤ zD * (2 * ‖Complex.Gamma (1 - s + k - 1)‖ * ‖Complex.Gamma (1 - s)‖) :=
            mul_le_mul hG1s hinv (norm_nonneg _) hzD0
        _ ≤ zD * (2 * (CΓ * (1 + |s.im|) ^ (m + 1) * Real.exp (-(π * |s.im| / 2)))
              * (CΓ * (1 + |s.im|) ^ (m + 1) * Real.exp (-(π * |s.im| / 2)))) := by
            gcongr
        _ = zD * (2 * CΓ * CΓ) * (1 + |s.im|) ^ (2 * m + 2)
              * (Real.exp (-(π * |s.im| / 2)) * Real.exp (-(π * |s.im| / 2))) := by ring
        _ = zD * (2 * CΓ * CΓ) * (1 + |s.im|) ^ (2 * m + 2) * Real.exp (-(π * |s.im|)) := by
            rw [hE]
    have hpre' : ‖rsPre k s‖ ≤ Cp * (1 + |s.im|) ^ (2 * A + 2) * Real.exp (π * |s.im|) :=
      hpre s hA (by linarith)
    rw [hG', rsG_eq_rsPre_mul_rsLambda, norm_mul]
    calc ‖rsPre k s‖ * ‖rsLambda k f s‖
        ≤ (Cp * (1 + |s.im|) ^ (2 * A + 2) * Real.exp (π * |s.im|))
            * (zD * (2 * CΓ * CΓ) * (1 + |s.im|) ^ (2 * m + 2) * Real.exp (-(π * |s.im|))) :=
          mul_le_mul hpre' hΛn (norm_nonneg _) (by positivity)
      _ = Cp * zD * (2 * CΓ * CΓ) * (1 + |s.im|) ^ (2 * A + 2 + (2 * m + 2))
            * (Real.exp (π * |s.im|) * Real.exp (-(π * |s.im|))) := by ring
      _ = Cp * zD * (2 * CΓ * CΓ) * (1 + |s.im|) ^ (2 * A + 2 + (2 * m + 2)) := by
          rw [hE2, mul_one]
      _ ≤ (C₁ + zD + 1 + Cp * zD * (2 * CΓ * CΓ)) * (1 + |s.im|) ^ N := by
          refine mul_le_mul ?_ (hpowN _ (by omega)) (by positivity) hCsum
          linarith

end RankinSelbergDelta.RankinSelberg
