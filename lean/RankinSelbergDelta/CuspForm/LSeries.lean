import Mathlib

/-!
# The L-function of a level-one cusp form

A level-one cusp form `f` of weight `k` gives the self-dual pair `(F, F, k, i^k)` with
`F(y) = f(iy)`, as a Mathlib `StrongFEPair` (`LSeries/AbstractFuncEq.lean`). Its Mellin transform
is the completed L-function: entire, with the functional equation `Λ(k − s) = i^k Λ(s)`.
-/
namespace RankinSelbergDelta.CuspForm

open Complex UpperHalfPlane ModularForm SlashInvariantForm CongruenceSubgroup ModularFormClass
open Function Filter Asymptotics Subgroup

noncomputable section

/- A level-1 cusp form of weight `k`, as an abstract bundled function `F`. The `CuspFormClass`
   instance is over the `GL(2,ℝ)`-image of the level-1 group `Γ(1)`. -/
variable {F : Type*} [FunLike F ℍ ℂ] {k : ℤ}
  [cf : CuspFormClass F (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ(1)) k]

/-- The imaginary-axis restriction `F(y) = f(i·y)` of a level-1 cusp form (and `0` for `y ≤ 0`). -/
def axisRestrict (f : F) (y : ℝ) : ℂ :=
  if h : 0 < y then f ((⟨y, h⟩ : {x : ℝ // 0 < x}) • UpperHalfPlane.I) else 0

/-- **The functional equation of the axis restriction**: from the slash action of `S : z ↦ -1/z`,
    `F(1/y) = I^k · y^k · F(y)`. -/
lemma axisRestrict_functional_equation (f : F) {y : ℝ} (hy : 0 < y) :
    axisRestrict f (1 / y) = Complex.I ^ k * (y : ℂ) ^ k * axisRestrict f y := by
  have hy' : (0 : ℝ) < 1 / y := by positivity
  have hyne : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hpt : (⟨1 / y, hy'⟩ : {x : ℝ // 0 < x}) • UpperHalfPlane.I
      = ModularGroup.S • ((⟨y, hy⟩ : {x : ℝ // 0 < x}) • UpperHalfPlane.I) := by
    apply UpperHalfPlane.ext
    simp only [modular_S_smul, UpperHalfPlane.coe_mk, UpperHalfPlane.coe_pos_real_smul,
      UpperHalfPlane.coe_I, Complex.real_smul, one_div, Complex.ofReal_inv]
    field_simp
    ring_nf
    simp [Complex.I_sq]
  rw [axisRestrict, dif_pos hy', axisRestrict, dif_pos hy, hpt,
    slash_action_eqn_SL'' f (mem_Gamma_one ModularGroup.S), ModularGroup.denom_S]
  simp only [UpperHalfPlane.coe_pos_real_smul, UpperHalfPlane.coe_I, Complex.real_smul]
  rw [show ((y : ℂ) * Complex.I) ^ k = Complex.I ^ k * (y : ℂ) ^ k by
    rw [mul_comm, mul_zpow]]

/-- **The strong FE-pair** of a positive-weight level-1 cusp form `f`: the self-dual pair
    `(F, F, k, I^k)` with `F = axisRestrict f`. Provides (Mathlib `StrongFEPair`) the entire
    completed L-function `Λ` and its functional equation `Λ(k-s) = I^k • Λ(s)`. -/
noncomputable def fePair (f : F) (hk : 0 < k) : StrongFEPair ℂ where
  f := axisRestrict f
  g := axisRestrict f
  k := (k : ℝ)
  ε := Complex.I ^ k
  f₀ := 0
  g₀ := 0
  hf₀ := rfl
  hg₀ := rfl
  hk := by exact_mod_cast hk
  hε := zpow_ne_zero k Complex.I_ne_zero
  hf_int := by
    refine ContinuousOn.locallyIntegrableOn ?_ measurableSet_Ioi
    rw [continuousOn_iff_continuous_restrict]
    have heq : (Set.Ioi (0 : ℝ)).restrict (axisRestrict f)
        = fun y => f ((⟨y.1, y.2⟩ : {x : ℝ // 0 < x}) • UpperHalfPlane.I) := by
      funext y; simp only [Set.restrict_apply]; exact dif_pos y.2
    rw [heq]
    refine (ModularFormClass.continuous f).comp ?_
    rw [continuous_induced_rng]
    simp only [Function.comp_def, UpperHalfPlane.coe_pos_real_smul, UpperHalfPlane.coe_I,
      Complex.real_smul]
    fun_prop
  hg_int := by
    refine ContinuousOn.locallyIntegrableOn ?_ measurableSet_Ioi
    rw [continuousOn_iff_continuous_restrict]
    have heq : (Set.Ioi (0 : ℝ)).restrict (axisRestrict f)
        = fun y => f ((⟨y.1, y.2⟩ : {x : ℝ // 0 < x}) • UpperHalfPlane.I) := by
      funext y; simp only [Set.restrict_apply]; exact dif_pos y.2
    rw [heq]
    refine (ModularFormClass.continuous f).comp ?_
    rw [continuous_induced_rng]
    simp only [Function.comp_def, UpperHalfPlane.coe_pos_real_smul, UpperHalfPlane.coe_I,
      Complex.real_smul]
    fun_prop
  hf_top := by
    obtain ⟨c, hc, hdecay⟩ := CuspFormClass.exp_decay_atImInfty' f
    have hax : axisRestrict f =O[Filter.atTop] fun y : ℝ => Real.exp (-c * y) := by
      rw [Asymptotics.isBigO_iff] at hdecay ⊢
      obtain ⟨C, hC⟩ := hdecay
      rw [Filter.eventually_iff, UpperHalfPlane.atImInfty_mem] at hC
      obtain ⟨A, hA⟩ := hC
      refine ⟨C, Filter.eventually_atTop.2 ⟨max A 1, fun y hy => ?_⟩⟩
      have hy0 : 0 < y := lt_of_lt_of_le one_pos (le_trans (le_max_right A 1) hy)
      have hpt : ((⟨y, hy0⟩ : {x : ℝ // 0 < x}) • UpperHalfPlane.I).im = y := by
        simp [UpperHalfPlane.pos_real_im]
      have hb := hA ((⟨y, hy0⟩ : {x : ℝ // 0 < x}) • UpperHalfPlane.I) (by rw [hpt]; exact le_trans (le_max_left A 1) hy)
      simp only [Set.mem_setOf_eq] at hb
      rw [hpt] at hb
      rwa [axisRestrict, dif_pos hy0]
    intro r
    simpa using hax.trans (isLittleO_exp_neg_mul_rpow_atTop hc r).isBigO
  hg_top := by
    obtain ⟨c, hc, hdecay⟩ := CuspFormClass.exp_decay_atImInfty' f
    have hax : axisRestrict f =O[Filter.atTop] fun y : ℝ => Real.exp (-c * y) := by
      rw [Asymptotics.isBigO_iff] at hdecay ⊢
      obtain ⟨C, hC⟩ := hdecay
      rw [Filter.eventually_iff, UpperHalfPlane.atImInfty_mem] at hC
      obtain ⟨A, hA⟩ := hC
      refine ⟨C, Filter.eventually_atTop.2 ⟨max A 1, fun y hy => ?_⟩⟩
      have hy0 : 0 < y := lt_of_lt_of_le one_pos (le_trans (le_max_right A 1) hy)
      have hpt : ((⟨y, hy0⟩ : {x : ℝ // 0 < x}) • UpperHalfPlane.I).im = y := by
        simp [UpperHalfPlane.pos_real_im]
      have hb := hA ((⟨y, hy0⟩ : {x : ℝ // 0 < x}) • UpperHalfPlane.I) (by rw [hpt]; exact le_trans (le_max_left A 1) hy)
      simp only [Set.mem_setOf_eq] at hb
      rw [hpt] at hb
      rwa [axisRestrict, dif_pos hy0]
    intro r
    simpa using hax.trans (isLittleO_exp_neg_mul_rpow_atTop hc r).isBigO
  h_feq := by
    intro x hx
    rw [smul_eq_mul, axisRestrict_functional_equation f hx, Real.rpow_intCast,
      Complex.ofReal_zpow]

/-- **The completed L-function** `Λ` of a level-1 cusp form (entire, by Mathlib's Mellin
    machinery through the FE-pair). -/
noncomputable def completedLSeries (f : F) (hk : 0 < k) : ℂ → ℂ := (fePair f hk).Λ

/-- **F8a**: the completed L-function of a level-1 cusp form is entire. -/
theorem differentiable_completedLSeries (f : F) (hk : 0 < k) :
    Differentiable ℂ (completedLSeries f hk) :=
  (fePair f hk).differentiable_Λ

/-- **F8b**: the functional equation `Λ(k-s) = I^k • Λ(s)` (self-dual, since `f = g`). -/
theorem completedLSeries_functional_equation (f : F) (hk : 0 < k) (s : ℂ) :
    completedLSeries f hk ((k : ℝ) - s) = Complex.I ^ k • completedLSeries f hk s :=
  (fePair f hk).functional_equation s

/-- The group of my File 1 has `1` as a strict period (level 1). -/
private lemma one_mem_strictPeriods_myGroup :
    (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ(1)).strictPeriods := by
  simp

/-- `𝕢 1 (i·y) = exp(-2π y)` as a complex number. -/
private lemma qParam_one_axis {y : ℝ} (hy : 0 < y) :
    Periodic.qParam 1 (((⟨y, hy⟩ : {x : ℝ // 0 < x}) • UpperHalfPlane.I : ℍ) : ℂ)
      = (Real.exp (-(2 * Real.pi) * y) : ℂ) := by
  have hco : (((⟨y, hy⟩ : {x : ℝ // 0 < x}) • UpperHalfPlane.I : ℍ) : ℂ) = (y : ℂ) * Complex.I := by
    rw [UpperHalfPlane.coe_pos_real_smul, UpperHalfPlane.coe_I, Complex.real_smul]
  have harg : (2 * (Real.pi : ℂ) * Complex.I * ((y : ℂ) * Complex.I) / ((1 : ℝ) : ℂ))
      = ((-(2 * Real.pi) * y : ℝ) : ℂ) := by
    rw [show (2 * (Real.pi : ℂ) * Complex.I * ((y : ℂ) * Complex.I))
        = 2 * (Real.pi : ℂ) * (y : ℂ) * (Complex.I * Complex.I) by ring, Complex.I_mul_I]
    push_cast; ring
  rw [Periodic.qParam, hco, harg, Complex.ofReal_exp]

include cf in
/-- **The q-expansion of the axis restriction**: for `y > 0`,
    `F(y) = Σ_n a(n) exp(-2π n y)`, where `a(n)` are the q-expansion coefficients. -/
theorem hasSum_axisRestrict (f : F) {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℕ ↦ (qExpansion 1 f).coeff n * (Real.exp (-(2 * Real.pi * n) * y) : ℂ))
      (axisRestrict f y) := by
  have hqe := ModularFormClass.hasSum_qExpansion (k := k) f one_pos one_mem_strictPeriods_myGroup
    ((⟨y, hy⟩ : {x : ℝ // 0 < x}) • UpperHalfPlane.I)
  rw [axisRestrict, dif_pos hy]
  have hfun : (fun n : ℕ ↦ (qExpansion 1 f).coeff n * (Real.exp (-(2 * Real.pi * n) * y) : ℂ))
      = fun m : ℕ ↦ (qExpansion 1 f).coeff m
          • Periodic.qParam 1 (((⟨y, hy⟩ : {x : ℝ // 0 < x}) • UpperHalfPlane.I : ℍ) : ℂ) ^ m := by
    funext n
    rw [qParam_one_axis hy, smul_eq_mul, ← Complex.ofReal_pow, ← Real.exp_nat_mul]
    congr 2
    ring
  rw [hfun]
  exact hqe

include cf in
/-- The `0`-th q-expansion coefficient of a cusp form vanishes. -/
lemma qExpansion_coeff_zero_cusp (f : F) : (qExpansion 1 f).coeff 0 = 0 := by
  rw [ModularFormClass.qExpansion_coeff_zero (f := f) (k := k) one_pos one_mem_strictPeriods_myGroup]
  exact (CuspFormClass.zero_at_infty f).valueAtInfty_eq_zero

/-- `strictWidthInfty` of the level-1 group is `1`. -/
private lemma strictWidthInfty_myGroup :
    (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ(1)).strictWidthInfty = 1 :=
  Subgroup.strictWidthInfty_eq_one_of_T_mem (mem_Gamma_one ModularGroup.T)

include cf in
/-- **Summability**: the Dirichlet series of the q-expansion coefficients converges for
    `Re s > k/2 + 1` (Hecke's bound `a(n) = O(n^{k/2})`). -/
theorem summable_coeff_div (f : F) {s : ℂ} (hs : (k : ℝ) / 2 + 1 < s.re) :
    Summable (fun n : ℕ ↦ ‖(qExpansion 1 f).coeff n‖ / (2 * Real.pi * (n : ℝ)) ^ s.re) := by
  have hbd : (fun n : ℕ ↦ (qExpansion 1 f).coeff n) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ ((k : ℝ) / 2) := by
    have := CuspFormClass.qExpansion_isBigO (k := k) f
    rwa [strictWidthInfty_myGroup] at this
  refine summable_of_isBigO_nat
    (g := fun n : ℕ ↦ (n : ℝ) ^ ((k : ℝ) / 2 - s.re)) ?_ ?_
  · rw [Real.summable_nat_rpow]; linarith
  have e1 : (fun n : ℕ ↦ ‖(qExpansion 1 f).coeff n‖ / (2 * Real.pi * (n : ℝ)) ^ s.re)
      =ᶠ[atTop] fun n : ℕ ↦ (((2 * Real.pi) ^ (-s.re)) * ‖(qExpansion 1 f).coeff n‖)
          * (n : ℝ) ^ (-s.re) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [Real.mul_rpow (by positivity) hnpos.le, Real.rpow_neg (by positivity),
      Real.rpow_neg hnpos.le, div_eq_mul_inv, mul_inv]
    ring
  have hA : (fun n : ℕ ↦ ((2 * Real.pi) ^ (-s.re)) * ‖(qExpansion 1 f).coeff n‖)
      =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ ((k : ℝ) / 2) :=
    hbd.norm_left.const_mul_left _
  have hB := hA.mul (isBigO_refl (fun n : ℕ ↦ (n : ℝ) ^ (-s.re)) atTop)
  refine hB.congr' e1.symm ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [← Real.rpow_add hnpos, sub_eq_add_neg]

include cf in
/-- **The completed L-function as an explicit Dirichlet series**: for `Re s > k/2 + 1`,
    `Λ(s) = (2π)^{-s} Γ(s) L(f, s)`, where `L(f,s) = Σ a(n) n^{-s}` is the Dirichlet series of
    the q-expansion coefficients. -/
theorem completedLSeries_eq_dirichlet (f : F) (hk : 0 < k) {s : ℂ}
    (hs : (k : ℝ) / 2 + 1 < s.re) :
    (fePair f hk).Λ s
      = ((2 * Real.pi : ℝ) : ℂ) ^ (-s) * Complex.Gamma s
          * LSeries (fun n ↦ (qExpansion 1 f).coeff n) s := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hs0 : 0 < s.re := by linarith
  have hsne : s ≠ 0 := by rintro rfl; simp at hs0
  have hp : ∀ n : ℕ, (qExpansion 1 f).coeff n = 0 ∨ 0 < 2 * Real.pi * (n : ℝ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exact Or.inl (hn ▸ qExpansion_coeff_zero_cusp f)
    · refine Or.inr ?_
      have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      positivity
  have hF : ∀ t ∈ Set.Ioi (0 : ℝ),
      HasSum (fun n : ℕ ↦ (qExpansion 1 f).coeff n
          * (Real.exp (-(2 * Real.pi * (n : ℝ)) * t) : ℂ)) (axisRestrict f t) :=
    fun t ht ↦ hasSum_axisRestrict f (Set.mem_Ioi.mp ht)
  have hM := hasSum_mellin hp hs0 hF (summable_coeff_div f hs)
  have hΛ : (fePair f hk).Λ s = mellin (axisRestrict f) s := rfl
  rw [hΛ, ← hM.tsum_eq, LSeries, ← tsum_mul_left]
  refine tsum_congr (fun n ↦ ?_)
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [qExpansion_coeff_zero_cusp f, LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero (by exact_mod_cast hn.ne')]
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hbase : ((2 * Real.pi : ℝ) : ℂ) ^ s ≠ 0 := by
      rw [Complex.cpow_ne_zero_iff_of_exponent_ne_zero hsne, Complex.ofReal_ne_zero]; positivity
    have hnbase : ((n : ℂ)) ^ s ≠ 0 := by
      rw [Complex.cpow_ne_zero_iff_of_exponent_ne_zero hsne]; exact_mod_cast hn.ne'
    rw [Complex.ofReal_mul, mul_cpow_ofReal_nonneg (by positivity) hnpos.le,
      Complex.ofReal_natCast, Complex.cpow_neg]
    field_simp

end

end RankinSelbergDelta.CuspForm
