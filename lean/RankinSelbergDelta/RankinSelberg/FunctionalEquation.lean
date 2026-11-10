import RankinSelbergDelta.RankinSelberg.EdgeNonvanishing

/-!
# The functional equation of the Rankin–Selberg square

The functional equation and the meromorphy of `G` on the whole plane, from the functional
equations of the Eisenstein series and of the completed Rankin–Selberg integral.
-/

open MeasureTheory Filter
open scoped NNReal MatrixGroups Pointwise

noncomputable section


/-! ## The functional equation and meromorphy of the Rankin–Selberg square -/

namespace RankinSelbergDelta.RankinSelberg

open Complex UpperHalfPlane MeasureTheory Set RankinSelbergDelta.Eisenstein Filter Topology Asymptotics
open scoped ENNReal Modular NNReal

noncomputable section

/-! ### the theta-tail bound with the strip width explicit, `Re s ≤ n + 1` -/

/-- `t^n e^{−bt/2} ≤ n! (4/b)^n e^{−bt/4}` for `b > 0`, `t ≥ 0` (from `x^n/n! ≤ e^x`). -/
lemma pow_mul_exp_neg_le (n : ℕ) {b t : ℝ} (hb : 0 < b) (ht : 0 ≤ t) :
    t ^ n * Real.exp (-(b * t) / 2)
      ≤ (n.factorial : ℝ) * (4 / b) ^ n * Real.exp (-(b / 4) * t) := by
  have hx := Real.pow_div_factorial_le_exp (b * t / 4) (by positivity) n
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < n.factorial)] at hx
  have hb' : b ≠ 0 := hb.ne'
  have hprod : (4 / b) ^ n * (b * t / 4) ^ n = t ^ n := by
    rw [← mul_pow]
    congr 1
    field_simp
  have ht2 : t ^ n ≤ (n.factorial : ℝ) * (4 / b) ^ n * Real.exp (b * t / 4) := by
    calc t ^ n = (4 / b) ^ n * (b * t / 4) ^ n := hprod.symm
      _ ≤ (4 / b) ^ n * (Real.exp (b * t / 4) * n.factorial) :=
          mul_le_mul_of_nonneg_left hx (by positivity)
      _ = (n.factorial : ℝ) * (4 / b) ^ n * Real.exp (b * t / 4) := by ring
  have hexp : Real.exp (-(b * t) / 2) = Real.exp (-(b / 4) * t) * Real.exp (-(b * t / 4)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hE : Real.exp (b * t / 4) * Real.exp (-(b * t / 4)) = 1 := by
    rw [← Real.exp_add]; simp
  rw [hexp]
  calc t ^ n * (Real.exp (-(b / 4) * t) * Real.exp (-(b * t / 4)))
      ≤ (n.factorial : ℝ) * (4 / b) ^ n * Real.exp (b * t / 4)
          * (Real.exp (-(b / 4) * t) * Real.exp (-(b * t / 4))) :=
        mul_le_mul_of_nonneg_right ht2 (by positivity)
    _ = (n.factorial : ℝ) * (4 / b) ^ n * Real.exp (-(b / 4) * t)
          * (Real.exp (b * t / 4) * Real.exp (-(b * t / 4))) := by ring
    _ = (n.factorial : ℝ) * (4 / b) ^ n * Real.exp (-(b / 4) * t) := by rw [hE, mul_one]

/-- The integrand bound with the strip width explicit: for `c (m²+n²) ≤ Q_z`, `Re s ≤ n + 1`,
`t > 1`: `‖t^{s-1}(θ_z(t) − 1)‖ ≤ (1 + 4/b)² · n! (4/b)^n · e^{−bt/4}`, `b = πc`. -/
lemma norm_theta_integrand_le' (z : ℍ) {c : ℝ} (hc : 0 < c)
    (hcle : ∀ m n : ℤ, c * ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) ≤ Qform z m n) (n : ℕ) {s : ℂ}
    (hs : s.re ≤ n + 1) {t : ℝ} (ht1 : 1 < t) :
    ‖(t : ℂ) ^ (s - 1) * (thetaQ z t - 1)‖
      ≤ (1 + 4 / (Real.pi * c)) ^ 2 * ((n.factorial : ℝ) * (4 / (Real.pi * c)) ^ n)
          * Real.exp (-(Real.pi * c / 4) * t) := by
  set b := Real.pi * c with hb
  have hb0 : 0 < b := by positivity
  have ht0 : 0 < t := by linarith
  have hθ0 : 0 ≤ thetaR z t - 1 := thetaR_sub_one_nonneg z ht0
  have hnorm : ‖thetaQ z t - 1‖ = thetaR z t - 1 := by
    rw [thetaQ_eq_ofReal, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_of_nonneg hθ0]
  rw [norm_mul, hnorm, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re, Complex.one_re]
  have hθ := thetaR_sub_one_le z ht0 hc hcle
  have hpow : t ^ (s.re - 1) ≤ t ^ (n : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le ht1.le (by linarith)
  rw [Real.rpow_natCast] at hpow
  have ha : Real.pi * t * c = b * t := by rw [hb]; ring
  rw [ha] at hθ
  have h1 : (1 + 4 / (b * t)) ^ 2 ≤ (1 + 4 / b) ^ 2 := by
    have hdiv : 4 / (b * t) ≤ 4 / b :=
      div_le_div_of_nonneg_left (by norm_num) hb0 (by nlinarith)
    have h0 : 0 ≤ 1 + 4 / (b * t) := by positivity
    gcongr
  have h2 := pow_mul_exp_neg_le n hb0 ht0.le
  calc t ^ (s.re - 1) * (thetaR z t - 1)
      ≤ t ^ n * (Real.exp (-(b * t) / 2) * (1 + 4 / (b * t)) ^ 2) :=
        mul_le_mul hpow hθ hθ0 (by positivity)
    _ = (t ^ n * Real.exp (-(b * t) / 2)) * (1 + 4 / (b * t)) ^ 2 := by ring
    _ ≤ ((n.factorial : ℝ) * (4 / b) ^ n * Real.exp (-(b / 4) * t)) * (1 + 4 / b) ^ 2 :=
        mul_le_mul h2 h1 (by positivity) (by positivity)
    _ = (1 + 4 / b) ^ 2 * ((n.factorial : ℝ) * (4 / b) ^ n) * Real.exp (-(b / 4) * t) := by ring

/-- `z ↦ thetaM z s` is continuous on `ℍ` for `Re s ≤ n + 1`. -/
lemma continuous_thetaM' (n : ℕ) {s : ℂ} (hs : s.re ≤ n + 1) :
    Continuous fun z : ℍ => thetaM z s := by
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
  set K := (1 + 4 / b) ^ 2 * ((n.factorial : ℝ) * (4 / b) ^ n) with hK
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
    exact norm_theta_integrand_le' z hc₀pos hcle n hs ht
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    have ht : (0 : ℝ) < t := lt_trans one_pos ht
    exact (continuous_const.mul ((continuous_thetaQ_z ht).sub continuous_const)).continuousAt

/-- The one-sided integral bound with the strip width explicit. -/
lemma norm_thetaM_le_of_lower_bound' (z : ℍ) {c : ℝ} (hc : 0 < c)
    (hcle : ∀ m n : ℤ, c * ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) ≤ Qform z m n) (n : ℕ) {s : ℂ}
    (hs : s.re ≤ n + 1) :
    ‖thetaM z s‖
      ≤ 4 * ((n.factorial : ℝ) * (4 / (Real.pi * c)) ^ n) * (1 + 4 / (Real.pi * c)) ^ 2
          / (Real.pi * c) := by
  set b := Real.pi * c with hb
  have hb0 : 0 < b := by positivity
  set K := (1 + 4 / b) ^ 2 * ((n.factorial : ℝ) * (4 / b) ^ n) with hK
  have hint : IntegrableOn (fun t : ℝ => K * Real.exp (-(b / 4) * t)) (Ioi 1) :=
    (exp_neg_integrableOn_Ioi 1 (by positivity : 0 < b / 4)).const_mul K
  have hbound : ∀ t ∈ Ioi (1 : ℝ),
      ‖(t : ℂ) ^ (s - 1) * (thetaQ z t - 1)‖ ≤ K * Real.exp (-(b / 4) * t) :=
    fun t ht => norm_theta_integrand_le' z hc hcle n hs ht
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
  calc (1 + 4 / b) ^ 2 * ((n.factorial : ℝ) * (4 / b) ^ n) * (Real.exp (-(b / 4) * 1) * (4 / b))
      ≤ (1 + 4 / b) ^ 2 * ((n.factorial : ℝ) * (4 / b) ^ n) * (1 * (4 / b)) := by gcongr
    _ = 4 * ((n.factorial : ℝ) * (4 / b) ^ n) * (1 + 4 / b) ^ 2 / b := by
        field_simp

/-- The constant of the uniform theta bound at width `n`: `64 · n! · 4^n`. -/
def thetaC (n : ℕ) : ℝ := 64 * (n.factorial : ℝ) * 4 ^ n

lemma thetaC_pos (n : ℕ) : 0 < thetaC n := by unfold thetaC; positivity

/-- **The uniform bound on `𝒟` with the strip width explicit**:
`‖M_z(s)‖ ≤ thetaC n · (1 + Im z)^(n+3)` for `z ∈ 𝒟` and `Re s ≤ n + 1`. -/
theorem norm_thetaM_le_fd' (n : ℕ) {z : ℍ} (hz : z ∈ (𝒟 : Set ℍ)) {s : ℂ} (hs : s.re ≤ n + 1) :
    ‖thetaM z s‖ ≤ thetaC n * (1 + z.im) ^ (n + 3) := by
  have hy : 0 < z.im := z.im_pos
  have hc : 0 < 1 / (3 * z.im) := by positivity
  refine (norm_thetaM_le_of_lower_bound' z hc (Qform_lower_bound_fd hz) n hs).trans ?_
  set y := z.im with hy_def
  set b := Real.pi * (1 / (3 * y)) with hb
  have hb0 : 0 < b := by positivity
  have hπ3 : 3 < Real.pi := Real.pi_gt_three
  have hu : b⁻¹ ≤ y := by
    rw [hb, show Real.pi * (1 / (3 * y)) = Real.pi / (3 * y) by ring, inv_div,
      div_le_iff₀ Real.pi_pos]
    nlinarith
  have hu0 : 0 ≤ b⁻¹ := inv_nonneg.mpr hb0.le
  have hrw : 4 * ((n.factorial : ℝ) * (4 / b) ^ n) * (1 + 4 / b) ^ 2 / b
      = 4 * (n.factorial : ℝ) * (4 * b⁻¹) ^ n * (1 + 4 * b⁻¹) ^ 2 * b⁻¹ := by
    field_simp
  rw [hrw]
  have hA : (1 + 4 * b⁻¹) ^ 2 ≤ (4 * (1 + y)) ^ 2 := by gcongr; linarith
  have hB : (4 * b⁻¹) ^ n ≤ (4 * (1 + y)) ^ n := by gcongr; linarith
  have hC : b⁻¹ ≤ 1 + y := by linarith
  calc 4 * (n.factorial : ℝ) * (4 * b⁻¹) ^ n * (1 + 4 * b⁻¹) ^ 2 * b⁻¹
      ≤ 4 * (n.factorial : ℝ) * (4 * (1 + y)) ^ n * (4 * (1 + y)) ^ 2 * (1 + y) := by
        have h1 : 4 * (n.factorial : ℝ) * (4 * b⁻¹) ^ n
            ≤ 4 * (n.factorial : ℝ) * (4 * (1 + y)) ^ n :=
          mul_le_mul_of_nonneg_left hB (by positivity)
        have h2 := mul_le_mul h1 hA (by positivity) (by positivity)
        exact mul_le_mul h2 hC hu0 (by positivity)
    _ = thetaC n * (1 + y) ^ (n + 3) := by
        simp only [thetaC, mul_pow, pow_add]
        ring

/-! ### `Λ₀` on `𝒟` for `−n ≤ Re s ≤ n + 1`; `J` is entire -/

lemma norm_epsteinΛ₀_le_fd' (n : ℕ) {z : ℍ} (hz : z ∈ (𝒟 : Set ℍ)) {s : ℂ}
    (hs1 : -(n : ℝ) ≤ s.re) (hs2 : s.re ≤ n + 1) :
    ‖epsteinΛ₀ z s‖ ≤ 2 * thetaC n * (1 + z.im) ^ (n + 3) := by
  rw [epsteinΛ₀_eq]
  refine (norm_add_le _ _).trans ?_
  have h1 := norm_thetaM_le_fd' n hz hs2
  have h2 := norm_thetaM_le_fd' n hz (s := 1 - s)
    (by simp only [Complex.sub_re, Complex.one_re]; linarith)
  linarith

lemma continuous_epsteinΛ₀_z' (n : ℕ) {s : ℂ} (hs1 : -(n : ℝ) ≤ s.re) (hs2 : s.re ≤ n + 1) :
    Continuous fun z : ℍ => epsteinΛ₀ z s := by
  simp_rw [epsteinΛ₀_eq]
  exact (continuous_thetaM' n hs2).add
    (continuous_thetaM' n (s := 1 - s) (by simp only [Complex.sub_re, Complex.one_re]; linarith))

/-- Cauchy estimate at width `n`: for `z ∈ 𝒟` and `−n + 1/2 ≤ Re s ≤ n + 1/2`,
`‖Λ₀_z'(s)‖ ≤ 4 · thetaC n · (1 + y)^(n+3)`. -/
lemma norm_deriv_epsteinΛ₀_le' (n : ℕ) {z : ℍ} (hz : z ∈ (𝒟 : Set ℍ)) {s : ℂ}
    (hs1 : -(n : ℝ) + 1 / 2 ≤ s.re) (hs2 : s.re ≤ n + 1 / 2) :
    ‖deriv (epsteinΛ₀ z) s‖ ≤ 4 * thetaC n * (1 + z.im) ^ (n + 3) := by
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := s) (R := 1 / 2)
    (C := 2 * thetaC n * (1 + z.im) ^ (n + 3)) (f := epsteinΛ₀ z) (by norm_num)
    (differentiable_epsteinΛ₀ z).diffContOnCl ?_
  · calc ‖deriv (epsteinΛ₀ z) s‖ ≤ 2 * thetaC n * (1 + z.im) ^ (n + 3) / (1 / 2) := h
      _ = 4 * thetaC n * (1 + z.im) ^ (n + 3) := by ring
  · intro w hw
    rw [Metric.mem_sphere, Complex.dist_eq] at hw
    have hre : |w.re - s.re| ≤ 1 / 2 := by
      rw [← Complex.sub_re]
      exact (Complex.abs_re_le_norm _).trans hw.le
    rw [abs_le] at hre
    exact norm_epsteinΛ₀_le_fd' n hz (by linarith [hre.1]) (by linarith [hre.2])

/-- `z ↦ Λ₀_z'(s)` is measurable at width `n`. -/
lemma measurable_deriv_epsteinΛ₀' (n : ℕ) {s : ℂ} (hs1 : -(n : ℝ) ≤ s.re) (hs2 : s.re < n + 1) :
    Measurable fun z : ℍ => deriv (epsteinΛ₀ z) s := by
  set ε : ℝ := (n : ℝ) + 1 - s.re with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  set h : ℕ → ℂ := fun m => ((ε * (1 / ((m : ℝ) + 1)) : ℝ) : ℂ) with hh
  have hpos : ∀ m : ℕ, 0 < ε * (1 / ((m : ℝ) + 1)) := fun m => by positivity
  have hle : ∀ m : ℕ, ε * (1 / ((m : ℝ) + 1)) ≤ ε := fun m => by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have : 1 / ((m : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    nlinarith [this, hε0]
  have hne : ∀ m, h m ≠ 0 := fun m => by
    simp only [hh]
    exact Complex.ofReal_ne_zero.mpr (hpos m).ne'
  have hre : ∀ m : ℕ, (s + h m).re = s.re + ε * (1 / ((m : ℝ) + 1)) := fun m => by
    simp only [hh, Complex.add_re, Complex.ofReal_re]
  have htend : Tendsto h atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
      (Filter.Eventually.of_forall hne)
    have h1 : Tendsto (fun m : ℕ => ε * (1 / ((m : ℝ) + 1))) atTop (𝓝 (ε * 0)) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ε
    rw [mul_zero] at h1
    have := (Complex.continuous_ofReal.tendsto 0).comp h1
    simpa [hh, Function.comp_def] using this
  refine measurable_of_tendsto_metrizable
    (f := fun m (z : ℍ) => (h m)⁻¹ * (epsteinΛ₀ z (s + h m) - epsteinΛ₀ z s)) (fun m => ?_) ?_
  · exact (continuous_const.mul
      ((continuous_epsteinΛ₀_z' n (by rw [hre]; linarith [hpos m]) (by rw [hre]; linarith [hle m])).sub
        (continuous_epsteinΛ₀_z' n hs1 hs2.le))).measurable
  · rw [tendsto_pi_nhds]
    intro z
    exact (differentiable_epsteinΛ₀ z s).hasDerivAt.tendsto_slope_zero.comp htend

variable {F : Type*} [FunLike F ℍ ℂ] (k : ℤ)
  [cf : CuspFormClass F (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma 1)) k]

include cf in
lemma integrableOn_phi_mul_Λ₀' (f : F) (hk : 0 < k) (n : ℕ) {s : ℂ} (hs1 : -(n : ℝ) ≤ s.re)
    (hs2 : s.re ≤ n + 1) :
    IntegrableOn (fun z : ℍ => (phi k f z : ℂ) * epsteinΛ₀ z s) (𝒟 : Set ℍ) := by
  obtain ⟨M, hM⟩ := phi_mul_pow_bounded k f hk (n + 3)
  have hC := thetaC_pos n
  refine Measure.integrableOn_of_bounded volume_fd_lt_top.ne
    ((Complex.continuous_ofReal.comp (continuous_phi k f)).mul
      (continuous_epsteinΛ₀_z' n hs1 hs2)).aestronglyMeasurable
    (M := 2 * thetaC n * M) (ae_restrict_of_forall_mem measurableSet_fd fun z hz => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (phi_nonneg k f z)]
  calc phi k f z * ‖epsteinΛ₀ z s‖ ≤ phi k f z * (2 * thetaC n * (1 + z.im) ^ (n + 3)) :=
        mul_le_mul_of_nonneg_left (norm_epsteinΛ₀_le_fd' n hz hs1 hs2) (phi_nonneg k f z)
    _ = 2 * thetaC n * (phi k f z * (1 + z.im) ^ (n + 3)) := by ring
    _ ≤ 2 * thetaC n * M := by nlinarith [hM z hz]

include cf in
/-- **`J` is differentiable everywhere**, with the derivative under the integral sign. -/
theorem hasDerivAt_rsJ' (f : F) (hk : 0 < k) (s₀ : ℂ) :
    HasDerivAt (rsJ k f) (∫ z in (𝒟 : Set ℍ), (phi k f z : ℂ) * deriv (epsteinΛ₀ z) s₀) s₀ := by
  set n : ℕ := ⌈|s₀.re|⌉₊ + 1 with hn
  have hn1 : |s₀.re| + 1 ≤ (n : ℝ) := by
    rw [hn]
    push_cast
    linarith [Nat.le_ceil |s₀.re|]
  have hlo : -|s₀.re| ≤ s₀.re := neg_abs_le s₀.re
  have hhi : s₀.re ≤ |s₀.re| := le_abs_self s₀.re
  obtain ⟨M, hM⟩ := phi_mul_pow_bounded k f hk (n + 3)
  have hC := thetaC_pos n
  have hball : ∀ s ∈ Metric.ball s₀ (1 / 4), -(n : ℝ) + 1 / 2 ≤ s.re ∧ s.re ≤ n + 1 / 2 := by
    intro s hs
    rw [Metric.mem_ball, Complex.dist_eq] at hs
    have := (Complex.abs_re_le_norm (s - s₀)).trans_lt hs
    rw [Complex.sub_re, abs_lt] at this
    constructor <;> linarith [this.1, this.2]
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (𝒟 : Set ℍ))
    (F := fun s (z : ℍ) => (phi k f z : ℂ) * epsteinΛ₀ z s)
    (F' := fun s (z : ℍ) => (phi k f z : ℂ) * deriv (epsteinΛ₀ z) s)
    (bound := fun z => phi k f z * (4 * thetaC n * (1 + z.im) ^ (n + 3)))
    (Metric.ball_mem_nhds s₀ (by norm_num : (0 : ℝ) < 1 / 4)) ?_ ?_ ?_ ?_ ?_ ?_
  · exact key.2
  · filter_upwards [Metric.ball_mem_nhds s₀ (by norm_num : (0 : ℝ) < 1 / 4)] with s hs
    obtain ⟨h1, h2⟩ := hball s hs
    exact ((Complex.continuous_ofReal.comp (continuous_phi k f)).mul
      (continuous_epsteinΛ₀_z' n (by linarith) (by linarith))).aestronglyMeasurable
  · exact integrableOn_phi_mul_Λ₀' k f hk n (by linarith) (by linarith)
  · exact ((Complex.continuous_ofReal.comp (continuous_phi k f)).measurable.mul
      (measurable_deriv_epsteinΛ₀' n (by linarith) (by linarith))).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_fd fun z hz s hs => ?_
    obtain ⟨h1, h2⟩ := hball s hs
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (phi_nonneg k f z)]
    exact mul_le_mul_of_nonneg_left (norm_deriv_epsteinΛ₀_le' n hz h1 h2) (phi_nonneg k f z)
  · refine Measure.integrableOn_of_bounded volume_fd_lt_top.ne
      ((continuous_phi k f).mul (continuous_const.mul
        ((continuous_const.add UpperHalfPlane.continuous_im).pow (n + 3)))).aestronglyMeasurable
      (M := 4 * thetaC n * M) (ae_restrict_of_forall_mem measurableSet_fd fun z hz => ?_)
    rw [Real.norm_of_nonneg (by have := phi_nonneg k f z; positivity)]
    calc phi k f z * (4 * thetaC n * (1 + z.im) ^ (n + 3))
        = 4 * thetaC n * (phi k f z * (1 + z.im) ^ (n + 3)) := by ring
      _ ≤ 4 * thetaC n * M := by nlinarith [hM z hz]
  · exact Filter.Eventually.of_forall fun z s _ =>
      ((differentiable_epsteinΛ₀ z s).hasDerivAt).const_mul _

include cf in
theorem differentiable_rsJ (f : F) (hk : 0 < k) : Differentiable ℂ (rsJ k f) :=
  fun s => (hasDerivAt_rsJ' k f hk s).differentiableAt

/-! ### the completed Rankin–Selberg square, its functional equation, its poles -/

include cf in
/-- `rsJ(s) = rsJ(1 − s)`: the unfolded integral is symmetric because `Λ₀_z` is. -/
theorem rsJ_symm (f : F) (s : ℂ) : rsJ k f s = rsJ k f (1 - s) := by
  unfold rsJ
  refine MeasureTheory.setIntegral_congr_fun measurableSet_fd fun z _ => ?_
  rw [epsteinΛ₀_eq, epsteinΛ₀_eq, sub_sub_cancel, add_comm]

include cf in
/-- **The completed Rankin–Selberg square** `Λ_RS(s) = rsJ(s) − (1/s + 1/(1−s)) ∫_𝒟 Φ`, so that
`G(s) = rsPre(s) · Λ_RS(s)` (`rsG_eq_rsPre_mul_rsLambda`). -/
def rsLambda (f : F) (s : ℂ) : ℂ :=
  rsJ k f s - (1 / s + 1 / (1 - s)) * ((∫ z in (𝒟 : Set ℍ), phi k f z : ℝ) : ℂ)

include cf in
lemma rsG_eq_rsPre_mul_rsLambda (f : F) (s : ℂ) : rsG k f s = rsPre k s * rsLambda k f s := rfl

include cf in
/-- **(i) The functional equation** `Λ_RS(s) = Λ_RS(1 − s)`, for every `s`. -/
theorem rsLambdaRS_functional_equation (f : F) (s : ℂ) :
    rsLambda k f s = rsLambda k f (1 - s) := by
  unfold rsLambda
  rw [rsJ_symm k f s, sub_sub_cancel, add_comm (1 / s)]

include cf in
/-- The functional equation of `G` itself: `rsPre(1−s) G(s) = rsPre(s) G(1−s)`. -/
theorem rsG_functional_equation (f : F) (s : ℂ) :
    rsPre k (1 - s) * rsG k f s = rsPre k s * rsG k f (1 - s) := by
  rw [rsG_eq_rsPre_mul_rsLambda, rsG_eq_rsPre_mul_rsLambda, rsLambdaRS_functional_equation k f s]
  ring

include cf in
/-- **(ii) `Λ_RS` is holomorphic off `{0, 1}`.** -/
theorem rsLambdaRS_entire_off_poles (f : F) (hk : 0 < k) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (rsLambda k f) s := by
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  unfold rsLambda
  refine (differentiable_rsJ k f hk s).sub (DifferentiableAt.mul_const ?_ _)
  exact ((differentiableAt_const _).div differentiableAt_id hs0).add
    ((differentiableAt_const _).div ((differentiableAt_const _).sub differentiableAt_id) h1s)

include cf in
/-- `G` is holomorphic off `{0, 1}` (on all of `ℂ`, not only the strip). -/
theorem rsG_entire_off_poles (f : F) (hk : 0 < k) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (rsG k f) s := by
  have h : rsG k f = fun s => rsPre k s * rsLambda k f s := rfl
  rw [h]
  exact (differentiable_rsPre k s).mul (rsLambdaRS_entire_off_poles k f hk hs0 hs1)

include cf in
/-- **(ii) The simple pole at `s = 1`**: `(s − 1) Λ_RS(s) → ∫_𝒟 Φ`. -/
theorem rsLambdaRS_simplePole_one (f : F) (hk : 0 < k) :
    Tendsto (fun s : ℂ => (s - 1) * rsLambda k f s) (𝓝[≠] (1 : ℂ))
      (𝓝 ((∫ z in (𝒟 : Set ℍ), phi k f z : ℝ) : ℂ)) := by
  set c : ℂ := ((∫ z in (𝒟 : Set ℍ), phi k f z : ℝ) : ℂ) with hc
  have hJ : ContinuousAt (rsJ k f) 1 := (differentiable_rsJ k f hk 1).continuousAt
  have heq : ∀ s : ℂ, s ≠ 1 → s ≠ 0 →
      (s - 1) * rsLambda k f s = (s - 1) * rsJ k f s - ((s - 1) / s) * c + c := by
    intro s hs hs0
    unfold rsLambda
    rw [← hc]
    have h1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
    field_simp
    ring
  have hlim : Tendsto (fun s : ℂ => (s - 1) * rsJ k f s - ((s - 1) / s) * c + c)
      (𝓝 1) (𝓝 ((1 - 1) * rsJ k f 1 - ((1 - 1) / 1) * c + c)) :=
    ((((continuousAt_id.sub continuousAt_const).mul hJ).sub
      (((continuousAt_id.sub continuousAt_const).div continuousAt_id one_ne_zero).mul
        continuousAt_const)).add continuousAt_const).tendsto
  have hval : (1 - 1) * rsJ k f 1 - ((1 - 1) / 1) * c + c = c := by ring
  rw [hval] at hlim
  refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [eventually_mem_nhdsWithin,
    (eventually_ne_nhds (one_ne_zero : (1 : ℂ) ≠ 0)).filter_mono nhdsWithin_le_nhds] with s hs hs0
  exact (heq s hs hs0).symm

include cf in
/-- **(ii) The simple pole at `s = 0`**: `s Λ_RS(s) → −∫_𝒟 Φ`. -/
theorem rsLambdaRS_simplePole_zero (f : F) (hk : 0 < k) :
    Tendsto (fun s : ℂ => s * rsLambda k f s) (𝓝[≠] (0 : ℂ))
      (𝓝 (-((∫ z in (𝒟 : Set ℍ), phi k f z : ℝ) : ℂ))) := by
  set c : ℂ := ((∫ z in (𝒟 : Set ℍ), phi k f z : ℝ) : ℂ) with hc
  have hJ : ContinuousAt (rsJ k f) 0 := (differentiable_rsJ k f hk 0).continuousAt
  have heq : ∀ s : ℂ, s ≠ 0 → s ≠ 1 →
      s * rsLambda k f s = s * rsJ k f s - (s / (1 - s)) * c - c := by
    intro s hs0 hs1
    unfold rsLambda
    rw [← hc]
    have h1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
    field_simp
    ring
  have hlim : Tendsto (fun s : ℂ => s * rsJ k f s - (s / (1 - s)) * c - c)
      (𝓝 0) (𝓝 ((0 : ℂ) * rsJ k f 0 - ((0 : ℂ) / (1 - 0)) * c - c)) :=
    (((continuousAt_id.mul hJ).sub
      ((continuousAt_id.div (continuousAt_const.sub continuousAt_id) (by norm_num)).mul
        continuousAt_const)).sub continuousAt_const).tendsto
  have hval : (0 : ℂ) * rsJ k f 0 - ((0 : ℂ) / (1 - 0)) * c - c = -c := by ring
  rw [hval] at hlim
  refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [eventually_mem_nhdsWithin,
    (eventually_ne_nhds (zero_ne_one : (0 : ℂ) ≠ 1)).filter_mono nhdsWithin_le_nhds] with s hs0 hs1
  exact (heq s hs0 hs1).symm

include cf in
/-- The residue is nonzero for a nonzero cusp form: the poles are genuine. -/
theorem rsLambdaRS_residue_ne_zero (f : F) (hk : 0 < k) (hf : (⇑f : ℍ → ℂ) ≠ 0) :
    ((∫ z in (𝒟 : Set ℍ), phi k f z : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (integral_phi_pos_of_ne_zero k f hf).ne'

include cf in
/-- **(iii) `Λ_RS` is meromorphic on `ℂ`.** -/
theorem rsLambdaRS_meromorphicOn (f : F) (hk : 0 < k) :
    MeromorphicOn (rsLambda k f) Set.univ := by
  intro s _
  have hJ : MeromorphicAt (rsJ k f) s := ((differentiable_rsJ k f hk).analyticAt s).meromorphicAt
  have h1 : MeromorphicAt (fun s : ℂ => 1 / s) s :=
    (MeromorphicAt.const (1 : ℂ) s).div (MeromorphicAt.id s)
  have h2 : MeromorphicAt (fun s : ℂ => 1 / (1 - s)) s :=
    (MeromorphicAt.const (1 : ℂ) s).div ((MeromorphicAt.const (1 : ℂ) s).sub (MeromorphicAt.id s))
  exact hJ.sub ((h1.add h2).mul
    (MeromorphicAt.const ((∫ z in (𝒟 : Set ℍ), phi k f z : ℝ) : ℂ) s))

include cf in
/-- **(iii) `G` is meromorphic on `ℂ`**: `L(f×f̄, s)` continues to a meromorphic function. -/
theorem rsG_meromorphic (f : F) (hk : 0 < k) : MeromorphicOn (rsG k f) Set.univ := by
  intro s hs
  exact ((differentiable_rsPre k).analyticAt s).meromorphicAt.mul
    (rsLambdaRS_meromorphicOn k f hk s hs)

end

end RankinSelbergDelta.RankinSelberg
