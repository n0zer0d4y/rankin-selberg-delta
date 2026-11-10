import RankinSelbergDelta.RankinSelberg.RSPole
import RankinSelbergDelta.RankinSelberg.TRS
import RankinSelbergDelta.RankinSelberg.TRSInputs
import RankinSelbergDelta.RankinSelberg.HeckeEuler

/-!
# The continuation of the Rankin–Selberg square near `Re s = 1`

Rankin's mean-square bound (`D(w)` converges absolutely for `Re w > k`), the holomorphy of the
truncated integral `J` and of `G` on the strip `0 < Re s < 9/4` away from `s = 1`, and the simple
pole of `G` at `s = 1` (`rsD_continuation`).
-/

open MeasureTheory Filter
open scoped NNReal MatrixGroups Pointwise

noncomputable section

namespace RankinSelbergDelta.RankinSelberg

open Complex UpperHalfPlane MeasureTheory Set RankinSelbergDelta.Eisenstein
open scoped ENNReal Modular NNReal

noncomputable section

variable {F : Type*} [FunLike F ℍ ℂ] (k : ℤ)
  [cf : CuspFormClass F (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma 1)) k]

open Filter Topology

/-! ### Rankin's mean-square bound, `D(w)` converges absolutely for `Re w > k` -/

include cf in
/-- `meanSq f y ≤ C y^{-k}`: the mean square is controlled by the Petersson bound. -/
lemma meanSq_le (f : F) : ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 < y → meanSq f y ≤ C * y ^ (-k) := by
  obtain ⟨Cφ, hCφ⟩ := phi_bounded k f
  refine ⟨max Cφ 0, le_max_right _ _, fun y hy => ?_⟩
  rw [meanSq_eq k f hy]
  have hpt' : Continuous fun x : ℝ => ((⟨⟨x, y⟩, hy⟩ : ℍ)) := by
    rw [continuous_induced_rng]
    have : ((fun z : ℍ => (z : ℂ)) ∘ fun x : ℝ => ((⟨⟨x, y⟩, hy⟩ : ℍ)))
        = fun x : ℝ => (x : ℂ) + (y : ℂ) * Complex.I := by
      funext x
      exact Complex.mk_eq_add_mul_I x y
    rw [this]
    fun_prop
  have hint : IntervalIntegrable (fun x : ℝ => ‖f ((⟨⟨x, y⟩, hy⟩ : ℍ))‖ ^ 2) volume 0 1 :=
    (((ModularFormClass.continuous f).comp hpt').norm.pow 2).intervalIntegrable 0 1
  have hpt : ∀ x ∈ Icc (0 : ℝ) 1, ‖f ((⟨⟨x, y⟩, hy⟩ : ℍ))‖ ^ 2 ≤ max Cφ 0 * y ^ (-k) := by
    intro x _
    have h := hCφ ((⟨⟨x, y⟩, hy⟩ : ℍ))
    rw [phi, Complex.normSq_eq_norm_sq] at h
    have him : ((⟨⟨x, y⟩, hy⟩ : ℍ)).im = y := rfl
    rw [him] at h
    have hyk : 0 < y ^ k := zpow_pos hy k
    rw [zpow_neg, ← div_eq_mul_inv, le_div_iff₀ hyk]
    exact h.trans (le_max_left _ _)
  calc ∫ x in (0 : ℝ)..1, ‖f ((⟨⟨x, y⟩, hy⟩ : ℍ))‖ ^ 2
      ≤ ∫ x in (0 : ℝ)..1, max Cφ 0 * y ^ (-k) :=
        intervalIntegral.integral_mono_on zero_le_one hint intervalIntegrable_const hpt
    _ = max Cφ 0 * y ^ (-k) := by simp

include cf in
/-- **Rankin's bound**: `Σ_n |a_n|² n^{-σ}` converges for real `σ > k`. -/
theorem summable_rsDirichlet' (f : F) (hk : 0 < k) {σ : ℝ} (hσ : (k : ℝ) < σ) :
    Summable fun n : ℕ => ‖(ModularFormClass.qExpansion 1 f).coeff n‖ ^ 2 / (n : ℝ) ^ σ := by
  obtain ⟨C, hC0, hC⟩ := meanSq_le k f
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set a : ℕ → ℝ := fun n => ‖(ModularFormClass.qExpansion 1 f).coeff n‖ ^ 2 with ha
  have ha0 : ∀ n, 0 ≤ a n := fun n => by simp only [ha]; positivity
  have ha_zero : a 0 = 0 := by
    simp only [ha, RankinSelbergDelta.CuspForm.qExpansion_coeff_zero_cusp f, norm_zero]
    norm_num
  -- the theta identity in `ℝ≥0∞`
  have hT : ∀ y : ℝ, 0 < y →
      (∑' n : ℕ, ENNReal.ofReal (a n * Real.exp (-(4 * Real.pi * n) * y)))
        = ENNReal.ofReal (meanSq f y) := by
    intro y hy
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) (summable_sq_exp k f hy)]
    congr 1
    have h := hasSum_meanSq k f hy
    have h' : (fun n : ℕ => (‖(ModularFormClass.qExpansion 1 f).coeff n‖ ^ 2 : ℂ)
          * (Real.exp (-(4 * Real.pi * (n : ℝ)) * y) : ℂ))
        = fun n : ℕ => ((a n * Real.exp (-(4 * Real.pi * n) * y) : ℝ) : ℂ) := by
      funext n
      simp only [ha]
      push_cast
      ring
    rw [h'] at h
    exact (Complex.hasSum_ofReal.mp h).tsum_eq
  have hmeasE : ∀ n : ℕ, Measurable fun y : ℝ =>
      ENNReal.ofReal (Real.exp (-(4 * Real.pi * n) * y) * y ^ (σ - 1)) := fun n =>
    ENNReal.measurable_ofReal.comp
      ((Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
        (measurable_id.pow_const _))
  -- the lower bound of the inner integral for `n ≥ 1`
  have hlow : ∀ n : ℕ, 1 ≤ n →
      ENNReal.ofReal (Real.exp (-(4 * Real.pi)) * (2 * n : ℝ) ^ (-σ))
        ≤ ∫⁻ y in Ioc (0 : ℝ) 1,
            ENNReal.ofReal (Real.exp (-(4 * Real.pi * n) * y) * y ^ (σ - 1)) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have h2n : (0 : ℝ) < 2 * n := by positivity
    have hsub : Icc (1 / (2 * (n : ℝ))) (1 / (n : ℝ)) ⊆ Ioc (0 : ℝ) 1 := by
      intro y hy
      refine ⟨lt_of_lt_of_le (by positivity) hy.1, hy.2.trans ?_⟩
      rw [div_le_one hn0]
      exact_mod_cast hn
    refine le_trans ?_ (lintegral_mono_set hsub)
    calc ENNReal.ofReal (Real.exp (-(4 * Real.pi)) * (2 * n : ℝ) ^ (-σ))
        = ENNReal.ofReal (Real.exp (-(4 * Real.pi)) * (1 / (2 * n : ℝ)) ^ (σ - 1))
            * ENNReal.ofReal (1 / (n : ℝ) - 1 / (2 * (n : ℝ))) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [show (1 : ℝ) / n - 1 / (2 * n) = 1 / (2 * n) by field_simp; ring, mul_assoc,
            ← Real.rpow_add_one (by positivity : (1 : ℝ) / (2 * n) ≠ 0), sub_add_cancel, one_div,
            Real.inv_rpow h2n.le, ← Real.rpow_neg h2n.le]
      _ = ∫⁻ y in Icc (1 / (2 * (n : ℝ))) (1 / (n : ℝ)),
            ENNReal.ofReal (Real.exp (-(4 * Real.pi)) * (1 / (2 * n : ℝ)) ^ (σ - 1)) := by
          rw [setLIntegral_const, Real.volume_Icc]
      _ ≤ ∫⁻ y in Icc (1 / (2 * (n : ℝ))) (1 / (n : ℝ)),
            ENNReal.ofReal (Real.exp (-(4 * Real.pi * n) * y) * y ^ (σ - 1)) := by
          refine setLIntegral_mono' measurableSet_Icc fun y hy => ?_
          apply ENNReal.ofReal_le_ofReal
          have hy1 : 1 / (2 * (n : ℝ)) ≤ y := hy.1
          have hy2 : y ≤ 1 / (n : ℝ) := hy.2
          have hny : (n : ℝ) * y ≤ 1 := by
            rw [le_div_iff₀ hn0] at hy2
            linarith
          have he : Real.exp (-(4 * Real.pi)) ≤ Real.exp (-(4 * Real.pi * n) * y) := by
            apply Real.exp_le_exp.mpr
            nlinarith [Real.pi_pos, hny]
          have hp : (1 / (2 * n : ℝ)) ^ (σ - 1) ≤ y ^ (σ - 1) :=
            Real.rpow_le_rpow (by positivity) hy1 (by linarith)
          exact mul_le_mul he hp (by positivity) (Real.exp_nonneg _)
  -- finiteness of the outer integral
  have hfin : (∫⁻ y in Ioc (0 : ℝ) 1, ENNReal.ofReal (meanSq f y) * ENNReal.ofReal (y ^ (σ - 1)))
      < ⊤ := by
    calc (∫⁻ y in Ioc (0 : ℝ) 1, ENNReal.ofReal (meanSq f y) * ENNReal.ofReal (y ^ (σ - 1)))
        ≤ ∫⁻ y in Ioc (0 : ℝ) 1, ENNReal.ofReal (C * y ^ (σ - 1 - k)) := by
          refine setLIntegral_mono' measurableSet_Ioc fun y hy => ?_
          rw [← ENNReal.ofReal_mul (meanSq_nonneg k f y)]
          apply ENNReal.ofReal_le_ofReal
          have hy0 : 0 < y := hy.1
          calc meanSq f y * y ^ (σ - 1) ≤ C * y ^ (-k) * y ^ (σ - 1) :=
                mul_le_mul_of_nonneg_right (hC y hy0) (Real.rpow_nonneg hy0.le _)
            _ = C * y ^ (σ - 1 - k) := by
                rw [mul_assoc, ← Real.rpow_intCast, ← Real.rpow_add hy0]
                congr 2
                push_cast
                ring
      _ < ⊤ := by
          have hint : IntegrableOn (fun y : ℝ => C * y ^ (σ - 1 - k)) (Ioc (0 : ℝ) 1) := by
            have h' : IntegrableOn (fun y : ℝ => y ^ (σ - 1 - k)) (Ioo (0 : ℝ) 1) :=
              (intervalIntegral.integrableOn_Ioo_rpow_iff one_pos).mpr (by linarith)
            exact ((integrableOn_Ioc_iff_integrableOn_Ioo (f := fun y : ℝ => y ^ (σ - 1 - k))
              (a := 0) (b := 1) (μ := volume) enorm_ne_top).mpr h').const_mul C
          exact hint.lintegral_lt_top
  -- the swap
  have hswap : (∫⁻ y in Ioc (0 : ℝ) 1, ENNReal.ofReal (meanSq f y) * ENNReal.ofReal (y ^ (σ - 1)))
      = ∑' n : ℕ, ENNReal.ofReal (a n)
          * ∫⁻ y in Ioc (0 : ℝ) 1, ENNReal.ofReal (Real.exp (-(4 * Real.pi * n) * y) * y ^ (σ - 1)) := by
    have h1 : ∀ y ∈ Ioc (0 : ℝ) 1, ENNReal.ofReal (meanSq f y) * ENNReal.ofReal (y ^ (σ - 1))
        = ∑' n : ℕ, ENNReal.ofReal (a n)
            * ENNReal.ofReal (Real.exp (-(4 * Real.pi * n) * y) * y ^ (σ - 1)) := by
      intro y hy
      rw [← hT y hy.1, ← ENNReal.tsum_mul_right]
      refine tsum_congr fun n => ?_
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (ha0 n), mul_assoc]
    rw [setLIntegral_congr_fun measurableSet_Ioc h1,
      lintegral_tsum fun n => (measurable_const.mul (hmeasE n)).aemeasurable]
    refine tsum_congr fun n => ?_
    rw [lintegral_const_mul _ (hmeasE n)]
  have hsum_lt : (∑' n : ℕ, ENNReal.ofReal (a n * (Real.exp (-(4 * Real.pi)) * (2 * n : ℝ) ^ (-σ))))
      < ⊤ := by
    calc (∑' n : ℕ, ENNReal.ofReal (a n * (Real.exp (-(4 * Real.pi)) * (2 * n : ℝ) ^ (-σ))))
        ≤ ∑' n : ℕ, ENNReal.ofReal (a n)
            * ∫⁻ y in Ioc (0 : ℝ) 1,
                ENNReal.ofReal (Real.exp (-(4 * Real.pi * n) * y) * y ^ (σ - 1)) := by
          refine ENNReal.tsum_le_tsum fun n => ?_
          rw [ENNReal.ofReal_mul (ha0 n)]
          rcases Nat.eq_zero_or_pos n with rfl | hn
          · simp [ha_zero]
          · exact mul_le_mul_left' (hlow n hn) _
      _ = _ := hswap.symm
      _ < ⊤ := hfin
  have hs : Summable fun n : ℕ => a n * (Real.exp (-(4 * Real.pi)) * (2 * n : ℝ) ^ (-σ)) := by
    have := ENNReal.summable_toReal hsum_lt.ne
    refine this.congr fun n => ?_
    rw [ENNReal.toReal_ofReal (by positivity)]
  -- compare
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (hs.mul_left (Real.exp (4 * Real.pi) * (2 : ℝ) ^ σ))
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [ha_zero, Nat.cast_zero]
    rw [RankinSelbergDelta.CuspForm.qExpansion_coeff_zero_cusp f, norm_zero]
    simp
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    show a n / (n : ℝ) ^ σ ≤ _
    have h2 : (2 * n : ℝ) ^ (-σ) = (2 : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) :=
      Real.mul_rpow (by norm_num) hn0.le
    have hE : Real.exp (4 * Real.pi) * Real.exp (-(4 * Real.pi)) = 1 := by
      rw [← Real.exp_add]; simp
    have h2' : (2 : ℝ) ^ σ * (2 : ℝ) ^ (-σ) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; simp
    rw [h2, Real.rpow_neg hn0.le, div_eq_mul_inv]
    refine le_of_eq ?_
    calc a n * ((n : ℝ) ^ σ)⁻¹
        = (Real.exp (4 * Real.pi) * Real.exp (-(4 * Real.pi)))
            * ((2 : ℝ) ^ σ * (2 : ℝ) ^ (-σ)) * (a n * ((n : ℝ) ^ σ)⁻¹) := by
          rw [hE, h2']; ring
      _ = Real.exp (4 * Real.pi) * (2 : ℝ) ^ σ
            * (a n * (Real.exp (-(4 * Real.pi)) * ((2 : ℝ) ^ (-σ) * ((n : ℝ) ^ σ)⁻¹))) := by ring

include cf in
/-- The `L`-series form of `D`: `D(w) = LSeries (‖a_n‖²) w`. -/
lemma rsD_eq_LSeries (f : F) (w : ℂ) :
    rsD f w = LSeries (fun n => (‖(ModularFormClass.qExpansion 1 f).coeff n‖ ^ 2 : ℂ)) w := by
  unfold rsD LSeries
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_zero, RankinSelbergDelta.CuspForm.qExpansion_coeff_zero_cusp f]
  · rw [LSeries.term_of_ne_zero hn]

include cf in
/-- `LSeriesSummable` of the Rankin–Selberg coefficients for `Re w > k`. -/
lemma LSeriesSummable_rs (f : F) (hk : 0 < k) {w : ℂ} (hw : (k : ℝ) < w.re) :
    LSeriesSummable (fun n => (‖(ModularFormClass.qExpansion 1 f).coeff n‖ ^ 2 : ℂ)) w := by
  have h := summable_rsDirichlet' k f hk hw
  refine Summable.of_norm (h.congr fun n => ?_)
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · subst hn
    simp [RankinSelbergDelta.CuspForm.qExpansion_coeff_zero_cusp f]
  · rw [norm_pow, Complex.norm_real, norm_norm]

include cf in
/-- The abscissa of absolute convergence of the Rankin–Selberg coefficients is at most `k`. -/
lemma abscissaOfAbsConv_rs_le (f : F) (hk : 0 < k) :
    LSeries.abscissaOfAbsConv (fun n => (‖(ModularFormClass.qExpansion 1 f).coeff n‖ ^ 2 : ℂ))
      ≤ (k : ℝ) :=
  LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
    LSeriesSummable_rs k f hk (by simpa using hy)

/-! ### continuity of the theta tail integral `thetaM z s` in `z` -/

/-- The explicit positive-definiteness constant `c_z = y / (x² + y² + 1)` of `Q_z`. -/
def czLB (z : ℍ) : ℝ := z.im / (z.re ^ 2 + z.im ^ 2 + 1)

lemma czLB_pos (z : ℍ) : 0 < czLB z := by
  unfold czLB
  have := z.im_pos
  positivity

lemma continuous_czLB : Continuous czLB := by
  unfold czLB
  exact UpperHalfPlane.continuous_im.div
    (((UpperHalfPlane.continuous_re.pow 2).add (UpperHalfPlane.continuous_im.pow 2)).add
      continuous_const)
    fun z => by have := z.im_pos; positivity

/-- `c_z (m² + n²) ≤ Q_z(m, n)` with the explicit constant (the bound, made explicit). -/
lemma Qform_ge_czLB (z : ℍ) (m n : ℤ) :
    czLB z * ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) ≤ Qform z m n := by
  rw [Qform_eq, czLB]
  set X := z.re with hX
  set Y := z.im with hY
  have hY0 : 0 < Y := z.im_pos
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hY0]
  have key : (Y ^ 2) * ((m : ℝ) ^ 2 + (n : ℝ) ^ 2)
      ≤ (X ^ 2 + Y ^ 2 + 1) * (((n : ℝ) + m * X) ^ 2 + (m : ℝ) ^ 2 * Y ^ 2) := by
    nlinarith [sq_nonneg ((X ^ 2 + 1) * (n : ℝ) + (X ^ 2 + Y ^ 2 + 1) * X * m),
      sq_nonneg (Y ^ 2 * (m : ℝ)), sq_nonneg X, sq_nonneg Y, hY0]
  nlinarith [key]

lemma continuous_Qform (m n : ℤ) : Continuous fun z : ℍ => Qform z m n := by
  unfold Qform
  exact (((continuous_const.mul UpperHalfPlane.continuous_coe).add continuous_const).norm.pow 2).div
    UpperHalfPlane.continuous_im fun z => z.im_ne_zero

/-- `z ↦ θ_z(t)` is continuous on `ℍ`, for every `t > 0`. -/
lemma continuous_thetaQ_z {t : ℝ} (ht : 0 < t) : Continuous fun z : ℍ => thetaQ z t := by
  rw [continuous_iff_continuousAt]
  intro z₀
  set c₀ := czLB z₀ / 2 with hc₀
  have hc₀pos : 0 < c₀ := by rw [hc₀]; exact half_pos (czLB_pos z₀)
  have hU : IsOpen {z : ℍ | c₀ < czLB z} := isOpen_lt continuous_const continuous_czLB
  have hz₀ : z₀ ∈ {z : ℍ | c₀ < czLB z} := by
    show c₀ < czLB z₀
    rw [hc₀]
    linarith [czLB_pos z₀]
  have ha : (0 : ℝ) < t * c₀ := mul_pos ht hc₀pos
  have hcont : ContinuousOn (fun z : ℍ => thetaQ z t) {z : ℍ | c₀ < czLB z} := by
    rw [show (fun z : ℍ => thetaQ z t) = fun z => ∑' p : ℤ × ℤ,
        (Real.exp (-Real.pi * t * Qform z p.1 p.2) : ℂ) from rfl]
    refine continuousOn_tsum
      (f := fun (p : ℤ × ℤ) (z : ℍ) => (Real.exp (-Real.pi * t * Qform z p.1 p.2) : ℂ))
      (u := fun p : ℤ × ℤ => Real.exp (-Real.pi * (t * c₀) * (p.1 : ℝ) ^ 2)
          * Real.exp (-Real.pi * (t * c₀) * (p.2 : ℝ) ^ 2))
      (fun p => (Complex.continuous_ofReal.comp
        (Real.continuous_exp.comp (continuous_const.mul (continuous_Qform p.1 p.2)))).continuousOn)
      ((summable_exp_neg_sq ha).mul_of_nonneg (summable_exp_neg_sq ha)
          (fun _ => Real.exp_nonneg _) (fun _ => Real.exp_nonneg _))
      (fun p z hz => ?_)
    have hz : c₀ < czLB z := hz
    dsimp only
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hb := Qform_ge_czLB z p.1 p.2
    have hpt : (0 : ℝ) ≤ Real.pi * t := by positivity
    have hmn : (0 : ℝ) ≤ (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 := by positivity
    have h1 : Real.pi * t * (c₀ * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))
        ≤ Real.pi * t * Qform z p.1 p.2 :=
      mul_le_mul_of_nonneg_left (le_trans (mul_le_mul_of_nonneg_right hz.le hmn) hb) hpt
    linarith [h1]
  exact hcont.continuousAt (hU.mem_nhds hz₀)

/-- The integrand bound behind `norm_thetaM_le_fd`, as a standalone lemma: for `c (m²+n²) ≤ Q_z`, `Re s ≤ 3`,
`t > 1`: `‖t^{s-1}(θ_z(t) − 1)‖ ≤ (1 + 4/b)² (32/b²) e^{−bt/4}`, `b = π c`. -/
lemma norm_theta_integrand_le (z : ℍ) {c : ℝ} (hc : 0 < c)
    (hcle : ∀ m n : ℤ, c * ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) ≤ Qform z m n) {s : ℂ} (hs : s.re ≤ 3)
    {t : ℝ} (ht1 : 1 < t) :
    ‖(t : ℂ) ^ (s - 1) * (thetaQ z t - 1)‖
      ≤ (1 + 4 / (Real.pi * c)) ^ 2 * (32 / (Real.pi * c) ^ 2)
          * Real.exp (-(Real.pi * c / 4) * t) := by
  set b := Real.pi * c with hb
  have hb0 : 0 < b := by positivity
  set K := (1 + 4 / b) ^ 2 * (32 / b ^ 2) with hK
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

lemma continuousOn_theta_integrand (z : ℍ) (s : ℂ) :
    ContinuousOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * (thetaQ z t - 1)) (Ioi 1) := by
  intro t ht
  have ht0 : (0 : ℝ) < t := lt_trans one_pos ht
  refine ContinuousAt.continuousWithinAt ?_
  refine (Complex.continuousAt_ofReal_cpow_const t (s - 1) (Or.inr ht0.ne')).mul ?_
  exact ((continuousOn_thetaQ z).continuousAt (Ioi_mem_nhds ht0)).sub continuousAt_const

/-- `z ↦ thetaM z s` is continuous on `ℍ` for `Re s ≤ 3`. -/
lemma continuous_thetaM {s : ℂ} (hs : s.re ≤ 3) : Continuous fun z : ℍ => thetaM z s := by
  rw [continuous_iff_continuousAt]
  intro z₀
  set c₀ := czLB z₀ / 2 with hc₀
  have hc₀pos : 0 < c₀ := by rw [hc₀]; exact half_pos (czLB_pos z₀)
  have hU : IsOpen {z : ℍ | c₀ < czLB z} := isOpen_lt continuous_const continuous_czLB
  have hz₀ : z₀ ∈ {z : ℍ | c₀ < czLB z} := by
    show c₀ < czLB z₀
    rw [hc₀]
    linarith [czLB_pos z₀]
  set b := Real.pi * c₀ with hb
  have hb0 : 0 < b := by positivity
  set K := (1 + 4 / b) ^ 2 * (32 / b ^ 2) with hK
  have hint : IntegrableOn (fun t : ℝ => K * Real.exp (-(b / 4) * t)) (Ioi 1) :=
    (exp_neg_integrableOn_Ioi 1 (by positivity : 0 < b / 4)).const_mul K
  unfold thetaM
  refine continuousAt_of_dominated (bound := fun t => K * Real.exp (-(b / 4) * t)) ?_ ?_ hint ?_
  · exact Filter.Eventually.of_forall fun z =>
      (continuousOn_theta_integrand z s).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [hU.mem_nhds hz₀] with z hz
    have hz : c₀ < czLB z := hz
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    have hcle : ∀ m n : ℤ, c₀ * ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) ≤ Qform z m n := fun m n =>
      le_trans (mul_le_mul_of_nonneg_right hz.le (by positivity)) (Qform_ge_czLB z m n)
    exact norm_theta_integrand_le z hc₀pos hcle hs ht
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    have ht : (0 : ℝ) < t := lt_trans one_pos ht
    exact (continuous_const.mul ((continuous_thetaQ_z ht).sub continuous_const)).continuousAt

/-! ### `Λ₀` on `𝒟` uniformly for `−2 ≤ Re s ≤ 3`; holomorphy of `J` and of `G` -/

lemma norm_epsteinΛ₀_le_fd {z : ℍ} (hz : z ∈ (𝒟 : Set ℍ)) {s : ℂ} (hs1 : -2 ≤ s.re)
    (hs2 : s.re ≤ 3) : ‖epsteinΛ₀ z s‖ ≤ 4096 * (1 + z.im) ^ 5 := by
  rw [epsteinΛ₀_eq]
  refine (norm_add_le _ _).trans ?_
  have h1 := norm_thetaM_le_fd hz hs2
  have h2 := norm_thetaM_le_fd hz (s := 1 - s)
    (by simp only [Complex.sub_re, Complex.one_re]; linarith)
  linarith

lemma continuous_epsteinΛ₀_z {s : ℂ} (hs1 : -2 ≤ s.re) (hs2 : s.re ≤ 3) :
    Continuous fun z : ℍ => epsteinΛ₀ z s := by
  simp_rw [epsteinΛ₀_eq]
  exact (continuous_thetaM hs2).add
    (continuous_thetaM (s := 1 - s) (by simp only [Complex.sub_re, Complex.one_re]; linarith))

/-- Cauchy estimate: for `z ∈ 𝒟` and `−3/2 ≤ Re s ≤ 5/2`, `‖Λ₀_z'(s)‖ ≤ 8192 (1 + y)⁵`. -/
lemma norm_deriv_epsteinΛ₀_le {z : ℍ} (hz : z ∈ (𝒟 : Set ℍ)) {s : ℂ} (hs1 : -3 / 2 ≤ s.re)
    (hs2 : s.re ≤ 5 / 2) : ‖deriv (epsteinΛ₀ z) s‖ ≤ 8192 * (1 + z.im) ^ 5 := by
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := s) (R := 1 / 2)
    (C := 4096 * (1 + z.im) ^ 5) (f := epsteinΛ₀ z) (by norm_num)
    (differentiable_epsteinΛ₀ z).diffContOnCl ?_
  · calc ‖deriv (epsteinΛ₀ z) s‖ ≤ 4096 * (1 + z.im) ^ 5 / (1 / 2) := h
      _ = 8192 * (1 + z.im) ^ 5 := by ring
  · intro w hw
    rw [Metric.mem_sphere, Complex.dist_eq] at hw
    have hre : |w.re - s.re| ≤ 1 / 2 := by
      rw [← Complex.sub_re]
      exact (Complex.abs_re_le_norm _).trans hw.le
    rw [abs_le] at hre
    exact norm_epsteinΛ₀_le_fd hz (by linarith [hre.1]) (by linarith [hre.2])

/-- `z ↦ Λ₀_z'(s)` is measurable: a pointwise limit of difference quotients continuous in `z`. -/
lemma measurable_deriv_epsteinΛ₀ {s : ℂ} (hs1 : -2 ≤ s.re) (hs2 : s.re < 3) :
    Measurable fun z : ℍ => deriv (epsteinΛ₀ z) s := by
  set ε : ℝ := 3 - s.re with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  set h : ℕ → ℂ := fun n => ((ε * (1 / ((n : ℝ) + 1)) : ℝ) : ℂ) with hh
  have hpos : ∀ n : ℕ, 0 < ε * (1 / ((n : ℝ) + 1)) := fun n => by positivity
  have hle : ∀ n : ℕ, ε * (1 / ((n : ℝ) + 1)) ≤ ε := fun n => by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    nlinarith [this, hε0]
  have hne : ∀ n, h n ≠ 0 := fun n => by
    simp only [hh]
    exact Complex.ofReal_ne_zero.mpr (hpos n).ne'
  have hre : ∀ n : ℕ, (s + h n).re = s.re + ε * (1 / ((n : ℝ) + 1)) := fun n => by
    simp only [hh, Complex.add_re, Complex.ofReal_re]
  have htend : Tendsto h atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
      (Filter.Eventually.of_forall hne)
    have h1 : Tendsto (fun n : ℕ => ε * (1 / ((n : ℝ) + 1))) atTop (𝓝 (ε * 0)) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ε
    rw [mul_zero] at h1
    have := (Complex.continuous_ofReal.tendsto 0).comp h1
    simpa [hh, Function.comp_def] using this
  refine measurable_of_tendsto_metrizable
    (f := fun n (z : ℍ) => (h n)⁻¹ * (epsteinΛ₀ z (s + h n) - epsteinΛ₀ z s)) (fun n => ?_) ?_
  · exact (continuous_const.mul
      ((continuous_epsteinΛ₀_z (by rw [hre]; linarith [hpos n]) (by rw [hre]; linarith [hle n])).sub
        (continuous_epsteinΛ₀_z hs1 hs2.le))).measurable
  · rw [tendsto_pi_nhds]
    intro z
    exact (differentiable_epsteinΛ₀ z s).hasDerivAt.tendsto_slope_zero.comp htend

include cf in
/-- `J(s) = ∫_𝒟 Φ(z) Λ₀_z(s) dμ`. -/
def rsJ (f : F) (s : ℂ) : ℂ := ∫ z in (𝒟 : Set ℍ), (phi k f z : ℂ) * epsteinΛ₀ z s

include cf in
lemma integrableOn_phi_mul_Λ₀ (f : F) (hk : 0 < k) {s : ℂ} (hs1 : -2 ≤ s.re) (hs2 : s.re ≤ 3) :
    IntegrableOn (fun z : ℍ => (phi k f z : ℂ) * epsteinΛ₀ z s) (𝒟 : Set ℍ) := by
  obtain ⟨M, hM⟩ := phi_mul_pow_bounded k f hk 5
  refine Measure.integrableOn_of_bounded volume_fd_lt_top.ne
    ((Complex.continuous_ofReal.comp (continuous_phi k f)).mul
      (continuous_epsteinΛ₀_z hs1 hs2)).aestronglyMeasurable
    (M := 4096 * M) (ae_restrict_of_forall_mem measurableSet_fd fun z hz => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (phi_nonneg k f z)]
  calc phi k f z * ‖epsteinΛ₀ z s‖ ≤ phi k f z * (4096 * (1 + z.im) ^ 5) :=
        mul_le_mul_of_nonneg_left (norm_epsteinΛ₀_le_fd hz hs1 hs2) (phi_nonneg k f z)
    _ = 4096 * (phi k f z * (1 + z.im) ^ 5) := by ring
    _ ≤ 4096 * M := by linarith [hM z hz]

/-- The strip on which `J` is shown holomorphic. -/
def rsStrip : Set ℂ := {s | 0 < s.re ∧ s.re < 9 / 4}

lemma isOpen_rsStrip : IsOpen rsStrip :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

include cf in
theorem hasDerivAt_rsJ (f : F) (hk : 0 < k) {s₀ : ℂ} (hs₀ : s₀ ∈ rsStrip) :
    HasDerivAt (rsJ k f) (∫ z in (𝒟 : Set ℍ), (phi k f z : ℂ) * deriv (epsteinΛ₀ z) s₀) s₀ := by
  obtain ⟨hs₀1, hs₀2⟩ := hs₀
  obtain ⟨M, hM⟩ := phi_mul_pow_bounded k f hk 5
  have hball : ∀ s ∈ Metric.ball s₀ (1 / 4), -1 / 4 < s.re ∧ s.re < 5 / 2 := by
    intro s hs
    rw [Metric.mem_ball, Complex.dist_eq] at hs
    have := (Complex.abs_re_le_norm (s - s₀)).trans_lt hs
    rw [Complex.sub_re, abs_lt] at this
    constructor <;> linarith [this.1, this.2]
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (𝒟 : Set ℍ))
    (F := fun s (z : ℍ) => (phi k f z : ℂ) * epsteinΛ₀ z s)
    (F' := fun s (z : ℍ) => (phi k f z : ℂ) * deriv (epsteinΛ₀ z) s)
    (bound := fun z => phi k f z * (8192 * (1 + z.im) ^ 5))
    (Metric.ball_mem_nhds s₀ (by norm_num : (0 : ℝ) < 1 / 4)) ?_ ?_ ?_ ?_ ?_ ?_
  · exact key.2
  · filter_upwards [Metric.ball_mem_nhds s₀ (by norm_num : (0 : ℝ) < 1 / 4)] with s hs
    obtain ⟨h1, h2⟩ := hball s hs
    exact ((Complex.continuous_ofReal.comp (continuous_phi k f)).mul
      (continuous_epsteinΛ₀_z (by linarith) (by linarith))).aestronglyMeasurable
  · exact integrableOn_phi_mul_Λ₀ k f hk (by linarith) (by linarith)
  · exact ((Complex.continuous_ofReal.comp (continuous_phi k f)).measurable.mul
      (measurable_deriv_epsteinΛ₀ (by linarith) (by linarith))).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_fd fun z hz s hs => ?_
    obtain ⟨h1, h2⟩ := hball s hs
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (phi_nonneg k f z)]
    exact mul_le_mul_of_nonneg_left (norm_deriv_epsteinΛ₀_le hz (by linarith) (by linarith))
      (phi_nonneg k f z)
  · refine Measure.integrableOn_of_bounded volume_fd_lt_top.ne
      ((continuous_phi k f).mul (continuous_const.mul
        ((continuous_const.add UpperHalfPlane.continuous_im).pow 5))).aestronglyMeasurable
      (M := 8192 * M) (ae_restrict_of_forall_mem measurableSet_fd fun z hz => ?_)
    rw [Real.norm_of_nonneg (by have := phi_nonneg k f z; positivity)]
    calc phi k f z * (8192 * (1 + z.im) ^ 5) = 8192 * (phi k f z * (1 + z.im) ^ 5) := by ring
      _ ≤ 8192 * M := by linarith [hM z hz]
  · exact Filter.Eventually.of_forall fun z s _ =>
      ((differentiable_epsteinΛ₀ z s).hasDerivAt).const_mul _

/-- The entire prefactor `(4π)^{s+k−1} π^s / (2 Γ(s+k−1) Γ(s))`. -/
def rsPre (s : ℂ) : ℂ :=
  ((4 * Real.pi : ℝ) : ℂ) ^ (s + k - 1) * (Real.pi : ℂ) ^ s
    * ((Complex.Gamma (s + k - 1))⁻¹ * (Complex.Gamma s)⁻¹) / 2

lemma differentiable_rsPre : Differentiable ℂ (rsPre k) := by
  have h4 : (((4 * Real.pi : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hπ : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h1 : Differentiable ℂ fun s : ℂ => ((4 * Real.pi : ℝ) : ℂ) ^ (s + k - 1) := fun s =>
    ((differentiableAt_id.add_const _).sub_const _).const_cpow (Or.inl h4)
  have h2 : Differentiable ℂ fun s : ℂ => (Real.pi : ℂ) ^ s := fun s =>
    differentiableAt_id.const_cpow (Or.inl hπ)
  have h3 : Differentiable ℂ fun s : ℂ => (Complex.Gamma (s + k - 1))⁻¹ :=
    Complex.differentiable_one_div_Gamma.comp ((differentiable_id.add_const _).sub_const _)
  have h4' : Differentiable ℂ fun s : ℂ => (Complex.Gamma s)⁻¹ := Complex.differentiable_one_div_Gamma
  exact ((h1.mul h2).mul (h3.mul h4')).div_const 2

include cf in
/-- `G(s) = rsPre(s) · (J(s) − (1/s + 1/(1−s)) ∫_𝒟 Φ)`: the continuation of `ζ(2s) D(s+k−1)`. -/
def rsG (f : F) (s : ℂ) : ℂ :=
  rsPre k s * (rsJ k f s - (1 / s + 1 / (1 - s)) * ((∫ z in (𝒟 : Set ℍ), phi k f z : ℝ) : ℂ))

include cf in
theorem differentiableAt_rsG (f : F) (hk : 0 < k) {s : ℂ} (hs : s ∈ rsStrip) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (rsG k f) s := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp [rsStrip] at hs
  have hJ : DifferentiableAt ℂ (rsJ k f) s := (hasDerivAt_rsJ k f hk hs).differentiableAt
  have hpre : DifferentiableAt ℂ (rsPre k) s := differentiable_rsPre k s
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  unfold rsG
  refine hpre.mul (hJ.sub (DifferentiableAt.mul_const ?_ _))
  exact ((differentiableAt_const _).div differentiableAt_id hs0).add
    ((differentiableAt_const _).div ((differentiableAt_const _).sub differentiableAt_id) h1s)

include cf in
/-- For real `σ ∈ (1, 3)`: `∫_𝒟 Φ Σ' eisTermR = eisPre σ (J σ − (1/σ + 1/(1−σ)) ∫Φ)`. -/
lemma integral_eisSum_eq (f : F) (hk : 0 < k) {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ < 3) :
    ((∫ z in (𝒟 : Set ℍ), phi k f z * ∑' d : CosetPSL, eisTermR z σ d : ℝ) : ℂ)
      = eisPre σ * (rsJ k f σ
          - (1 / (σ : ℂ) + 1 / (1 - σ)) * ((∫ z in (𝒟 : Set ℍ), phi k f z : ℝ) : ℂ)) := by
  have hpt : ∀ z : ℍ, ((phi k f z * ∑' d : CosetPSL, eisTermR z σ d : ℝ) : ℂ)
      = eisPre σ * ((phi k f z : ℂ) * epsteinΛ₀ z σ)
        - eisPre σ * (1 / (σ : ℂ) + 1 / (1 - σ)) * (phi k f z : ℂ) := by
    intro z
    rw [Complex.ofReal_mul, ← eisensteinE_eq_ofReal_tsum z hσ1, eisensteinE_eq_pre, epsteinΛ_eq_Λ₀]
    ring
  have hI1 : Integrable (fun z : ℍ => eisPre σ * ((phi k f z : ℂ) * epsteinΛ₀ z σ))
      (volume.restrict (𝒟 : Set ℍ)) :=
    (integrableOn_phi_mul_Λ₀ k f hk (by simp only [Complex.ofReal_re]; linarith)
      (by simp only [Complex.ofReal_re]; linarith)).const_mul _
  have hI2 : Integrable (fun z : ℍ => eisPre σ * (1 / (σ : ℂ) + 1 / (1 - σ)) * (phi k f z : ℂ))
      (volume.restrict (𝒟 : Set ℍ)) :=
    (integrableOn_phi_fd k f).ofReal.const_mul _
  have h0 : ((∫ z in (𝒟 : Set ℍ), phi k f z * ∑' d : CosetPSL, eisTermR z σ d : ℝ) : ℂ)
      = ∫ z in (𝒟 : Set ℍ), ((phi k f z * ∑' d : CosetPSL, eisTermR z σ d : ℝ) : ℂ) :=
    integral_ofReal.symm
  have h3 : (∫ z in (𝒟 : Set ℍ), (phi k f z : ℂ)) = ((∫ z in (𝒟 : Set ℍ), phi k f z : ℝ) : ℂ) :=
    integral_ofReal
  rw [h0]
  simp_rw [hpt]
  rw [integral_sub hI1 hI2, integral_const_mul, integral_const_mul, h3, rsJ]
  ring

include cf in
/-- For real `σ ∈ (2, 3)`: `G(σ) = ζ(2σ) D(σ + k − 1)`. -/
theorem rsG_eq_zeta_mul_rsD_real (f : F) (hk : 0 < k) {σ : ℝ} (hσ1 : 2 < σ) (hσ2 : σ < 3) :
    rsG k f σ = riemannZeta (2 * σ) * rsD f ((σ : ℂ) + k - 1) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 := rs_integral_eq k f hk hσ1
  rw [integral_eisSum_eq k f hk (by linarith) hσ2] at h1
  have hw : ((σ + k - 1 : ℝ) : ℂ) = (σ : ℂ) + k - 1 := by push_cast; ring
  rw [hw] at h1
  have hΓs : Complex.Gamma (σ : ℂ) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp only [Complex.ofReal_re]; linarith)
  have hΓw : Complex.Gamma ((σ : ℂ) + k - 1) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos
      (by simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.intCast_re,
        Complex.one_re]; linarith)
  have hζ : riemannZeta (2 * σ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re
      (by simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; norm_num; linarith)
  have h4 : ((4 * Real.pi : ℝ) : ℂ) ^ ((σ : ℂ) + k - 1) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    left
    exact Complex.ofReal_ne_zero.mpr (by positivity)
  have hπ : (Real.pi : ℂ) ^ (σ : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    left
    exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [Complex.cpow_neg] at h1
  -- h1 : eisPre σ * X = ((4π)^w)⁻¹ * Γ w * rsD w
  set X := rsJ k f σ - (1 / (σ : ℂ) + 1 / (1 - σ)) * ((∫ z in (𝒟 : Set ℍ), phi k f z : ℝ) : ℂ)
    with hX
  have h1' : ((4 * Real.pi : ℝ) : ℂ) ^ ((σ : ℂ) + k - 1) / Complex.Gamma ((σ : ℂ) + k - 1)
      * (eisPre σ * X) = rsD f ((σ : ℂ) + k - 1) := by
    rw [h1]
    field_simp
  calc rsG k f σ
      = riemannZeta (2 * σ) * (((4 * Real.pi : ℝ) : ℂ) ^ ((σ : ℂ) + k - 1)
          / Complex.Gamma ((σ : ℂ) + k - 1) * (eisPre σ * X)) := by
        unfold rsG rsPre eisPre
        rw [← hX]
        have hring : riemannZeta (2 * σ) * (((4 * Real.pi : ℝ) : ℂ) ^ ((σ : ℂ) + k - 1)
            / Complex.Gamma ((σ : ℂ) + k - 1)
            * ((Real.pi : ℂ) ^ (σ : ℂ) / Complex.Gamma σ / (2 * riemannZeta (2 * σ)) * X))
            = ((4 * Real.pi : ℝ) : ℂ) ^ ((σ : ℂ) + k - 1) * (Real.pi : ℂ) ^ (σ : ℂ)
              * ((Complex.Gamma ((σ : ℂ) + k - 1))⁻¹ * (Complex.Gamma σ)⁻¹) / 2 * X
              * (riemannZeta (2 * σ) / riemannZeta (2 * σ)) := by ring
        rw [hring, div_self hζ, mul_one]
    _ = riemannZeta (2 * σ) * rsD f ((σ : ℂ) + k - 1) := by rw [h1']

include cf in
/-- **`G = ζ(2s) D(s + k − 1)` on the strip `1 < Re s < 9/4`** (identity theorem from the real
segment `(2, 9/4)`). -/
theorem rsG_eq_zeta_mul_rsD (f : F) (hk : 0 < k) {s : ℂ} (hs1 : 1 < s.re) (hs2 : s.re < 9 / 4) :
    rsG k f s = riemannZeta (2 * s) * rsD f (s + k - 1) := by
  set U : Set ℂ := {s | 1 < s.re ∧ s.re < 9 / 4} with hU
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hUc : Convex ℝ U := (convex_halfSpace_re_gt 1).inter (convex_halfSpace_re_lt (9 / 4))
  have hf : AnalyticOnNhd ℂ (rsG k f) U := by
    refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) hUo
    have hs' : s ∈ rsStrip := ⟨by linarith [hs.1], hs.2⟩
    have hs1' : s ≠ 1 := by
      have h1 := hs.1
      rintro rfl
      simp at h1
    exact (differentiableAt_rsG k f hk hs' hs1').differentiableWithinAt
  have hg : AnalyticOnNhd ℂ (fun s => riemannZeta (2 * s) * rsD f (s + k - 1)) U := by
    refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) hUo
    refine DifferentiableAt.differentiableWithinAt ?_
    have hζ : DifferentiableAt ℂ (fun s : ℂ => riemannZeta (2 * s)) s := by
      refine (differentiableAt_riemannZeta ?_).comp s ((differentiableAt_const _).mul differentiableAt_id)
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith [hs.1]
    have hD : DifferentiableAt ℂ (fun s : ℂ => rsD f (s + k - 1)) s := by
      rw [show (fun s : ℂ => rsD f (s + k - 1)) = fun s => LSeries
          (fun n => (‖(ModularFormClass.qExpansion 1 f).coeff n‖ ^ 2 : ℂ)) (s + k - 1) from
        funext fun s => rsD_eq_LSeries k f _]
      have habs : LSeries.abscissaOfAbsConv
          (fun n => (‖(ModularFormClass.qExpansion 1 f).coeff n‖ ^ 2 : ℂ)) < (s + k - 1).re := by
        refine lt_of_le_of_lt (abscissaOfAbsConv_rs_le k f hk) ?_
        simp only [Complex.sub_re, Complex.add_re, Complex.intCast_re, Complex.one_re]
        exact_mod_cast (by linarith [hs.1] : (k : ℝ) < s.re + k - 1)
      exact (LSeries_hasDerivAt habs).differentiableAt.comp s
        ((differentiableAt_id.add_const _).sub_const _)
    exact hζ.mul hD
  have hz₀ : ((17 / 8 : ℝ) : ℂ) ∈ U := by
    simp only [hU, Set.mem_setOf_eq, Complex.ofReal_re]
    norm_num
  refine (hf.eqOn_of_preconnected_of_frequently_eq hg hUc.isPreconnected hz₀ ?_) ⟨hs1, hs2⟩
  have hreal : ∀ᶠ σ : ℝ in 𝓝[≠] (17 / 8 : ℝ),
      rsG k f σ = riemannZeta (2 * σ) * rsD f ((σ : ℂ) + k - 1) := by
    have hev : ∀ᶠ σ : ℝ in 𝓝 (17 / 8 : ℝ), σ ∈ Ioo (2 : ℝ) 3 :=
      Ioo_mem_nhds (by norm_num) (by norm_num)
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds] with σ hσ
    exact rsG_eq_zeta_mul_rsD_real k f hk hσ.1 hσ.2
  have hmap : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[≠] (17 / 8 : ℝ)) (𝓝[≠] ((17 / 8 : ℝ) : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((Complex.continuous_ofReal.tendsto _).mono_left nhdsWithin_le_nhds) ?_
    refine eventually_mem_nhdsWithin.mono fun σ hσ => ?_
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hσ ⊢
    exact fun h => hσ (Complex.ofReal_injective h)
  exact hmap.frequently hreal.frequently

/-! ### the simple pole of `G` at `s = 1` (complex), its `O(1/x)` form, regularity on
the line `Re s = 1` off the pole, and the main theorem -/

open Asymptotics

include cf in
/-- **The complex residue of `G` at `s = 1`**: `(s − 1) G(s) → rsPre(1) · ∫_𝒟 Φ` as `s → 1`,
`s ≠ 1` (from the continuity of `rsPre` and of `J` at `1`). -/
theorem tendsto_rsG_residue (f : F) (hk : 0 < k) :
    Tendsto (fun s : ℂ => (s - 1) * rsG k f s) (𝓝[≠] (1 : ℂ))
      (𝓝 (rsPre k 1 * ((∫ z in (𝒟 : Set ℍ), phi k f z : ℝ) : ℂ))) := by
  set c : ℂ := ((∫ z in (𝒟 : Set ℍ), phi k f z : ℝ) : ℂ) with hc
  have hJ : ContinuousAt (rsJ k f) 1 :=
    (hasDerivAt_rsJ k f hk ⟨by norm_num, by norm_num⟩).continuousAt
  have hpre : ContinuousAt (rsPre k) 1 := (differentiable_rsPre k 1).continuousAt
  have heq : ∀ s : ℂ, s ≠ 1 → s ≠ 0 →
      (s - 1) * rsG k f s = rsPre k s * ((s - 1) * rsJ k f s - ((s - 1) / s) * c + c) := by
    intro s hs hs0
    unfold rsG
    rw [← hc]
    have h1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
    field_simp
    ring
  have hlim : Tendsto (fun s : ℂ => rsPre k s * ((s - 1) * rsJ k f s - ((s - 1) / s) * c + c))
      (𝓝 1) (𝓝 (rsPre k 1 * ((1 - 1) * rsJ k f 1 - ((1 - 1) / 1) * c + c))) :=
    (hpre.mul ((((continuousAt_id.sub continuousAt_const).mul hJ).sub
      (((continuousAt_id.sub continuousAt_const).div continuousAt_id one_ne_zero).mul
        continuousAt_const)).add continuousAt_const)).tendsto
  have hval : rsPre k 1 * ((1 - 1) * rsJ k f 1 - ((1 - 1) / 1) * c + c) = rsPre k 1 * c := by ring
  rw [hval] at hlim
  refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [eventually_mem_nhdsWithin,
    (eventually_ne_nhds (one_ne_zero : (1 : ℂ) ≠ 0)).filter_mono nhdsWithin_le_nhds] with s hs hs0
  exact (heq s hs hs0).symm

include cf in
/-- `H2` for `G`: `G(1 + x) = O(1/x)` as `x → 0⁺`. -/
theorem rsG_isBigO_one_div (f : F) (hk : 0 < k) :
    (fun x : ℝ => rsG k f (1 + x)) =O[𝓝[>] 0] fun x : ℝ => (1 : ℂ) / x :=
  dlVP_pole_isBigO (tendsto_rsG_residue k f hk)

lemma one_add_I_mul_mem_rsStrip (y : ℝ) : (1 + Complex.I * y) ∈ rsStrip := by
  simp only [rsStrip, Set.mem_setOf_eq, Complex.add_re, Complex.one_re, Complex.mul_re,
    Complex.I_re, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im]
  norm_num

lemma one_add_two_I_mul_mem_rsStrip (y : ℝ) : (1 + 2 * Complex.I * y) ∈ rsStrip := by
  simp only [rsStrip, Set.mem_setOf_eq, Complex.add_re, Complex.one_re, Complex.mul_re,
    Complex.I_re, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, Complex.re_ofNat,
    Complex.im_ofNat]
  norm_num

include cf in
/-- `H3` for `G`: differentiable at `1 + iy` for `y ≠ 0`. -/
theorem differentiableAt_rsG_line (f : F) (hk : 0 < k) {y : ℝ} (hy : y ≠ 0) :
    DifferentiableAt ℂ (rsG k f) (1 + Complex.I * y) := by
  refine differentiableAt_rsG k f hk (one_add_I_mul_mem_rsStrip y) ?_
  intro h
  have := congrArg Complex.im h
  simp at this
  exact hy this

include cf in
/-- `H4` for `G`: continuous at `1 + 2iy` for `y ≠ 0`. -/
theorem continuousAt_rsG_line2 (f : F) (hk : 0 < k) {y : ℝ} (hy : y ≠ 0) :
    ContinuousAt (rsG k f) (1 + 2 * Complex.I * y) := by
  refine (differentiableAt_rsG k f hk (one_add_two_I_mul_mem_rsStrip y) ?_).continuousAt
  intro h
  have := congrArg Complex.im h
  simp at this
  exact hy this

include cf in
/-- **the continuation**: `G(s) = rsPre(s)(J(s) − (1/s + 1/(1−s)) ∫_𝒟 Φ)` is holomorphic on
the strip `0 < Re s < 9/4` away from `s = 1`, equals `ζ(2s) D(s + k − 1)` for `1 < Re s < 9/4`,
and has a simple pole at `s = 1` with residue `rsPre(1) ∫_𝒟 Φ`. In particular `D(w)` continues
meromorphically to the strip `k − 1 < Re w < k + 5/4` with its only pole at `w = k`. -/
theorem rsD_continuation (f : F) (hk : 0 < k) :
    (∀ s : ℂ, 1 < s.re → s.re < 9 / 4 → rsG k f s = riemannZeta (2 * s) * rsD f (s + k - 1)) ∧
    (∀ s : ℂ, s ∈ rsStrip → s ≠ 1 → DifferentiableAt ℂ (rsG k f) s) ∧
    Tendsto (fun s : ℂ => (s - 1) * rsG k f s) (𝓝[≠] (1 : ℂ))
      (𝓝 (rsPre k 1 * ((∫ z in (𝒟 : Set ℍ), phi k f z : ℝ) : ℂ))) :=
  ⟨fun _ h1 h2 => rsG_eq_zeta_mul_rsD k f hk h1 h2, fun _ hs hs1 => differentiableAt_rsG k f hk hs hs1,
    tendsto_rsG_residue k f hk⟩

/-- `rsPre(1) ≠ 0` for `k ≥ 1`, so the residue is nonzero whenever `∫_𝒟 Φ ≠ 0` (i.e. `f ≠ 0`). -/
lemma rsPre_one_ne_zero (hk : 0 < k) : rsPre k 1 ≠ 0 := by
  unfold rsPre
  have h4 : ((4 * Real.pi : ℝ) : ℂ) ^ ((1 : ℂ) + k - 1) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    left
    exact Complex.ofReal_ne_zero.mpr (by positivity)
  have hπ : (Real.pi : ℂ) ^ (1 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    left
    exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hΓ1 : (Complex.Gamma 1)⁻¹ ≠ 0 := by rw [Complex.Gamma_one]; norm_num
  have hΓk : (Complex.Gamma ((1 : ℂ) + k - 1))⁻¹ ≠ 0 := by
    refine inv_ne_zero (Complex.Gamma_ne_zero_of_re_pos ?_)
    simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.intCast_re]
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  exact div_ne_zero (mul_ne_zero (mul_ne_zero h4 hπ) (mul_ne_zero hΓk hΓ1)) two_ne_zero

include cf in
/-- The residue of `G` at `s = 1` is nonzero for a nonzero cusp form. -/
theorem rsG_residue_ne_zero (f : F) (hk : 0 < k) (hf : (⇑f : ℍ → ℂ) ≠ 0) :
    rsPre k 1 * ((∫ z in (𝒟 : Set ℍ), phi k f z : ℝ) : ℂ) ≠ 0 :=
  mul_ne_zero (rsPre_one_ne_zero k hk)
    (Complex.ofReal_ne_zero.mpr (integral_phi_pos_of_ne_zero k f hf).ne')

end

end RankinSelbergDelta.RankinSelberg
