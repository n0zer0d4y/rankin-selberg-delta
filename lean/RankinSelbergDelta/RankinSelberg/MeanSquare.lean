import RankinSelbergDelta.CuspForm.LSeries

/-!
# The mean square of a cusp form along a horocycle

For a level-one cusp form `f` and `y > 0`,
`∫₀¹ |f(x + iy)|² dx = Σ_n |a(n)|² e^{−4πny}` (`integral_sq_eq_tsum`), and `D(w)` converges for
`Re w > k + 1` (`summable_rsDirichlet`).
-/

namespace RankinSelbergDelta.RankinSelberg

open Complex UpperHalfPlane ModularForm SlashInvariantForm CongruenceSubgroup ModularFormClass
open Function Filter Asymptotics Topology Set Real

noncomputable section

variable {F : Type*} [FunLike F ℍ ℂ] {k : ℤ}
  [cf : CuspFormClass F (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ(1)) k]

/-- The Rankin–Selberg Dirichlet series `D(w) = Σ_{n≥1} |a(n)|² n^{-w}` of a level-1 cusp form. -/
def rsDirichlet (f : F) (w : ℂ) : ℂ := ∑' n : ℕ, (‖(qExpansion 1 f).coeff n‖ ^ 2 : ℂ) / (n : ℂ) ^ w

/-- `strictWidthInfty` of the level-1 group is `1`. -/
private lemma strictWidthInfty_myGroup' :
    (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ(1)).strictWidthInfty = 1 :=
  Subgroup.strictWidthInfty_eq_one_of_T_mem (mem_Gamma_one ModularGroup.T)

include cf in
/-- `D(w)` converges absolutely for `Re w > k + 1` (Hecke's bound `a(n) = O(n^{k/2})`). -/
theorem summable_rsDirichlet (f : F) {w : ℂ} (hw : (k : ℝ) + 1 < w.re) :
    Summable fun n : ℕ => ‖(qExpansion 1 f).coeff n‖ ^ 2 / (n : ℝ) ^ w.re := by
  have hbd : (fun n : ℕ => (qExpansion 1 f).coeff n) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ ((k : ℝ) / 2) := by
    have := CuspFormClass.qExpansion_isBigO (k := k) f
    rwa [strictWidthInfty_myGroup'] at this
  have hsq : (fun n : ℕ => ‖(qExpansion 1 f).coeff n‖ ^ 2) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (k : ℝ) := by
    have h2 := (hbd.norm_left.mul hbd.norm_left)
    refine h2.congr' (by filter_upwards with n; rw [sq]) ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [← Real.rpow_add hnpos]
    congr 1
    ring
  refine summable_of_isBigO_nat
    (g := fun n : ℕ => (n : ℝ) ^ ((k : ℝ) - w.re)) ?_ ?_
  · rw [Real.summable_nat_rpow]; linarith
  have e1 : (fun n : ℕ => ‖(qExpansion 1 f).coeff n‖ ^ 2 / (n : ℝ) ^ w.re)
      =ᶠ[atTop] fun n : ℕ => ‖(qExpansion 1 f).coeff n‖ ^ 2 * (n : ℝ) ^ (-w.re) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [Real.rpow_neg hnpos.le, div_eq_mul_inv]
  have hB := hsq.mul (isBigO_refl (fun n : ℕ => (n : ℝ) ^ (-w.re)) atTop)
  refine hB.congr' e1.symm ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [← Real.rpow_add hnpos, sub_eq_add_neg]

/-- The imaginary-shift of a cusp form, `g_y(x) = f(x + iy)` as a function of the real `x`. -/
def shift (f : F) {y : ℝ} (hy : 0 < y) (x : ℝ) : ℂ := f ((⟨⟨x, y⟩, hy⟩ : ℍ))

/-! ### The `q`-expansion of the shift -/

/-- `1` is a strict period of the level-1 group. -/
private lemma one_mem_strictPeriods_level_one :
    (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ(1)).strictPeriods := by
  simp

/-- `𝕢 1 (x + iy) = e^{-2π y} · e^{2π i x}`. -/
lemma qParam_shift (x y : ℝ) :
    Function.Periodic.qParam 1 ((⟨x, y⟩ : ℂ))
      = (Real.exp (-(2 * Real.pi) * y) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * x) := by
  rw [Function.Periodic.qParam, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  rw [Complex.mk_eq_add_mul_I x y]
  push_cast
  linear_combination (2 * (Real.pi : ℂ) * (y : ℂ)) * Complex.I_sq

lemma qpow_shift (m : ℕ) (x y : ℝ) :
    ((Real.exp (-(2 * Real.pi) * y) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * x)) ^ m
      = (Real.exp (-(2 * Real.pi * m) * y) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * m * x) := by
  rw [mul_pow, ← Complex.ofReal_pow, ← Real.exp_nat_mul, ← Complex.exp_nat_mul,
    show (m : ℝ) * (-(2 * Real.pi) * y) = -(2 * Real.pi * m) * y by ring,
    show (m : ℂ) * (2 * Real.pi * Complex.I * x) = 2 * Real.pi * Complex.I * m * x by ring]

include cf in
/-- The `q`-expansion of `x ↦ f(x + iy)`: `f(x+iy) = Σ_m a(m) e^{-2π m y} e^{2π i m x}`. -/
lemma hasSum_shift (f : F) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    HasSum (fun m : ℕ => (qExpansion 1 f).coeff m
        * ((Real.exp (-(2 * Real.pi * m) * y) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * m * x)))
      (shift f hy x) := by
  have h : HasSum (fun m : ℕ => (qExpansion 1 f).coeff m
      • Function.Periodic.qParam 1 ((⟨x, y⟩ : ℂ)) ^ m) (shift f hy x) :=
    ModularFormClass.hasSum_qExpansion (k := k) f one_pos one_mem_strictPeriods_level_one
      (⟨⟨x, y⟩, hy⟩ : ℍ)
  simp only [smul_eq_mul, qParam_shift, qpow_shift] at h
  exact h

include cf in
/-- Absolute convergence of that expansion: `Σ_m ‖a(m)‖ e^{-2π m y} < ∞`. -/
lemma summable_norm_shift_term (f : F) {y : ℝ} (hy : 0 < y) :
    Summable fun m : ℕ => ‖(qExpansion 1 f).coeff m‖ * Real.exp (-(2 * Real.pi * m) * y) := by
  have h := summable_norm_iff.mpr (hasSum_shift f hy 0).summable
  refine h.congr fun m => ?_
  simp [Complex.norm_exp]

/-! ### Fourier coefficients of the shift -/

/-- The summand after multiplying by `e^{-2π i n x}`. -/
private def fterm (f : F) (y : ℝ) (n : ℤ) (m : ℕ) (x : ℝ) : ℂ :=
  (qExpansion 1 f).coeff m * (Real.exp (-(2 * Real.pi * m) * y) : ℂ)
    * Complex.exp (2 * Real.pi * Complex.I * ((m : ℤ) - n : ℤ) * x)

include cf in
private lemma fourier_mul_shift_eq_tsum (f : F) {y : ℝ} (hy : 0 < y) (n : ℤ) (x : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * ((-n : ℤ) : ℂ) * x) * shift f hy x
      = ∑' m : ℕ, fterm f y n m x := by
  rw [← (hasSum_shift f hy x).tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  have e1 : ∀ c d a b : ℂ, Complex.exp a * (c * (d * Complex.exp b)) = c * d * Complex.exp (a + b) := by
    intro c d a b; rw [Complex.exp_add]; ring
  rw [e1, fterm]
  congr 2
  push_cast
  ring

private lemma continuous_fterm (f : F) (y : ℝ) (n : ℤ) (m : ℕ) : Continuous (fterm f y n m) := by
  unfold fterm
  fun_prop

private lemma norm_fterm (f : F) (y : ℝ) (n : ℤ) (m : ℕ) (x : ℝ) :
    ‖fterm f y n m x‖ = ‖(qExpansion 1 f).coeff m‖ * Real.exp (-(2 * Real.pi * m) * y) := by
  simp [fterm, Complex.norm_exp]

/-- `∫₀¹ e^{2π i k x} dx = [k = 0]`. -/
lemma integral_exp_two_pi_I_int (k : ℤ) :
    ∫ x : ℝ in (0 : ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * x) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst hk
    simp
  · have hc : (2 * Real.pi * Complex.I * (k : ℂ)) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero) ?_
      · exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      · exact_mod_cast hk
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (1 : ℝ)) = 1 := by
      rw [show (2 * Real.pi * Complex.I * (k : ℂ) * ((1 : ℝ) : ℂ)) = (k : ℂ) * (2 * Real.pi * Complex.I) by
        push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I k
    rw [h1]
    simp

private lemma integral_fterm (f : F) (y : ℝ) (n : ℤ) (m : ℕ) :
    ∫ x : ℝ in (0 : ℝ)..1, fterm f y n m x
      = if (m : ℤ) = n then (qExpansion 1 f).coeff m * (Real.exp (-(2 * Real.pi * m) * y) : ℂ) else 0 := by
  unfold fterm
  rw [intervalIntegral.integral_const_mul, integral_exp_two_pi_I_int]
  by_cases h : (m : ℤ) = n
  · simp [h, sub_self]
  · have h' : ((m : ℤ) - n) ≠ 0 := sub_ne_zero.mpr h
    simp [h, h']

include cf in
/-- The `n`-th Fourier coefficient of `x ↦ f(x+iy)` on `[0,1]`: `a(n) e^{-2π n y}` for `n ≥ 0`,
    and `0` for `n < 0` (the cusp form is holomorphic, no negative Fourier modes). -/
theorem fourierCoeffOn_shift (f : F) {y : ℝ} (hy : 0 < y) (n : ℤ) :
    fourierCoeffOn (by norm_num : (0 : ℝ) < 1) (shift f hy) n
      = if 0 ≤ n then (qExpansion 1 f).coeff n.toNat * Real.exp (-(2 * Real.pi * n) * y) else 0 := by
  rw [fourierCoeffOn_eq_integral]
  have key : ∀ x : ℝ, fourier (-n) (x : AddCircle ((1 : ℝ) - 0)) • shift f hy x
      = ∑' m : ℕ, fterm f y n m x := by
    intro x
    rw [fourier_coe_apply, smul_eq_mul, sub_zero, Complex.ofReal_one, div_one]
    exact fourier_mul_shift_eq_tsum f hy n x
  simp only [key, sub_zero, div_one, one_smul]
  -- swap the integral and the sum
  have hint : ∀ m : ℕ, MeasureTheory.Integrable (fterm f y n m)
      (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    fun m => (continuous_fterm f y n m).integrableOn_Ioc
  have hnorm : Summable fun m : ℕ =>
      ∫ x in Set.Ioc (0 : ℝ) 1, ‖fterm f y n m x‖ := by
    refine (summable_norm_shift_term f hy).congr fun m => ?_
    simp only [norm_fterm]
    rw [MeasureTheory.integral_const]
    simp [MeasureTheory.measureReal_def, Real.volume_Ioc]
  have hswap := MeasureTheory.hasSum_integral_of_summable_integral_norm hint hnorm
  rw [intervalIntegral.integral_of_le zero_le_one, ← hswap.tsum_eq]
  -- each term integrates to a Kronecker delta
  have hterm : ∀ m : ℕ, (∫ x in Set.Ioc (0 : ℝ) 1, fterm f y n m x)
      = if (m : ℤ) = n then (qExpansion 1 f).coeff m * (Real.exp (-(2 * Real.pi * m) * y) : ℂ) else 0 := by
    intro m
    rw [← intervalIntegral.integral_of_le zero_le_one, integral_fterm f y n m]
  simp only [hterm]
  split_ifs with hn
  · have hcond : ∀ m : ℕ, ((m : ℤ) = n) ↔ (m = n.toNat) := by
      intro m
      constructor
      · intro h; rw [← h, Int.toNat_natCast]
      · intro h; rw [h, Int.toNat_of_nonneg hn]
    simp only [hcond]
    rw [tsum_ite_eq]
    have hcast : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by
      have := Int.toNat_of_nonneg hn
      exact_mod_cast this
    rw [hcast]
  · have hnone : ∀ m : ℕ, ¬ ((m : ℤ) = n) := by
      intro m h
      apply hn
      rw [← h]
      exact Int.natCast_nonneg m
    simp [hnone]

include cf in
/-- `x ↦ f(x+iy)` is square-integrable on `(0,1]` (it is continuous). -/
theorem memLp_shift (f : F) {y : ℝ} (hy : 0 < y) :
    MeasureTheory.MemLp (shift f hy) 2 (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  have hpt : Continuous fun x : ℝ => ((⟨⟨x, y⟩, hy⟩ : ℍ)) := by
    rw [continuous_induced_rng]
    have : ((fun z : ℍ => (z : ℂ)) ∘ fun x : ℝ => ((⟨⟨x, y⟩, hy⟩ : ℍ)))
        = fun x : ℝ => (x : ℂ) + (y : ℂ) * Complex.I := by
      funext x
      exact Complex.mk_eq_add_mul_I x y
    rw [this]
    fun_prop
  have hcont : Continuous (shift f hy) := (ModularFormClass.continuous f).comp hpt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hcont.continuousOn (s := Set.Icc (0 : ℝ) 1))
  refine MeasureTheory.MemLp.of_bound hcont.aestronglyMeasurable C ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
  exact hC x (Set.Ioc_subset_Icc_self hx)

include cf in
/-- **The mean-square / `x`-average identity**: `∫₀¹ |f(x+iy)|² dx = Σ_n |a(n)|² e^{-4π n y}`. -/
theorem integral_sq_eq_tsum (f : F) {y : ℝ} (hy : 0 < y) :
    ∫ x : ℝ in (0 : ℝ)..1, ‖f ((⟨⟨x, y⟩, hy⟩ : ℍ))‖ ^ 2
      = ∑' n : ℕ, ‖(qExpansion 1 f).coeff n‖ ^ 2 * Real.exp (-(4 * Real.pi * n) * y) := by
  have hpar := hasSum_sq_fourierCoeffOn (by norm_num : (0 : ℝ) < 1) (memLp_shift f hy)
  rw [sub_zero, inv_one, one_smul] at hpar
  rw [show (∫ x : ℝ in (0 : ℝ)..1, ‖f ((⟨⟨x, y⟩, hy⟩ : ℍ))‖ ^ 2)
      = ∫ x : ℝ in (0 : ℝ)..1, ‖shift f hy x‖ ^ 2 from rfl, ← hpar.tsum_eq]
  -- reindex ℤ → ℕ: only n ≥ 0 contribute, ‖a(n) e^{-2πny}‖² = ‖a(n)‖² e^{-4πny}
  have hterm : ∀ i : ℤ, ‖fourierCoeffOn (by norm_num : (0 : ℝ) < 1) (shift f hy) i‖ ^ 2
      = if 0 ≤ i then ‖(qExpansion 1 f).coeff i.toNat‖ ^ 2 * Real.exp (-(4 * Real.pi * i) * y)
        else 0 := by
    intro i
    rw [fourierCoeffOn_shift f hy i]
    split_ifs with h
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _), mul_pow,
        sq (Real.exp _), ← Real.exp_add]
      congr 2
      ring
    · simp
  rw [tsum_congr hterm]
  -- the ℤ-indexed function is `Int.rec h 0`
  set h : ℕ → ℝ := fun n => ‖(qExpansion 1 f).coeff n‖ ^ 2 * Real.exp (-(4 * Real.pi * n) * y)
    with hh
  have hfun : (fun i : ℤ => if 0 ≤ i then ‖(qExpansion 1 f).coeff i.toNat‖ ^ 2
      * Real.exp (-(4 * Real.pi * i) * y) else 0) = Int.rec h (fun _ => 0) := by
    funext i
    cases i with
    | ofNat n => simp [hh]
    | negSucc n => simp
  have hsumZ : Summable fun i : ℤ => if 0 ≤ i then ‖(qExpansion 1 f).coeff i.toNat‖ ^ 2
      * Real.exp (-(4 * Real.pi * i) * y) else 0 := by
    have := hpar.summable
    exact (this.congr hterm)
  have hsumN : Summable h := by
    have := hsumZ.comp_injective (Nat.cast_injective (R := ℤ))
    refine this.congr fun n => ?_
    simp [hh]
  rw [hfun, (hsumN.hasSum.int_rec hasSum_zero).tsum_eq, add_zero]

end

end RankinSelbergDelta.RankinSelberg
