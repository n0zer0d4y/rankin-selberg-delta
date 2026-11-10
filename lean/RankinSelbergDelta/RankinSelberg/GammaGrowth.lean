import RankinSelbergDelta.RankinSelberg.FunctionalEquation

/-!
# Bounds for the Gamma function on vertical strips

Gamma bounds that avoid Stirling's formula, a Phragmén–Lindelöf principle on strips, and the upper
bound `‖Γ(w)‖ ≤ 48 (1 + |Im w|) e^{−π |Im w| / 2}` on the strip `1/2 ≤ Re w ≤ 3/2`
(`norm_Gamma_le_strip`).
-/

open MeasureTheory Filter
open scoped NNReal MatrixGroups Pointwise

noncomputable section


/-! ## Growth bounds on vertical lines: the Stirling-free Γ bounds and
polynomial growth of `L(f, w)` on the edge strip `−1/8 ≤ Re w ≤ 9/8` -/

/-! ## Growth bounds on vertical lines -/

namespace RankinSelbergDelta.RankinSelberg

open Complex MeasureTheory Set
open scoped Real

/-! ### `‖sin z‖ ≤ e^{|Im z|}` -/

lemma norm_sin_le_exp (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  have e1 : ‖Complex.exp (-z * Complex.I)‖ = Real.exp z.im := by
    rw [Complex.norm_exp]
    congr 1
    simp
  have e2 : ‖Complex.exp (z * Complex.I)‖ = Real.exp (-z.im) := by
    rw [Complex.norm_exp]
    congr 1
    simp
  have h1 : Real.exp z.im ≤ Real.exp |z.im| := Real.exp_le_exp.mpr (le_abs_self _)
  have h2 : Real.exp (-z.im) ≤ Real.exp |z.im| := Real.exp_le_exp.mpr (neg_le_abs _)
  rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat]
  calc ‖Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)‖ / 2
      ≤ (‖Complex.exp (-z * Complex.I)‖ + ‖Complex.exp (z * Complex.I)‖) / 2 := by
        gcongr
        exact norm_sub_le _ _
    _ = (Real.exp z.im + Real.exp (-z.im)) / 2 := by rw [e1, e2]
    _ ≤ Real.exp |z.im| := by linarith

/-! ### `‖Γ(u)‖ ≤ 1 + Γ(B + 1)` for `1 ≤ Re u ≤ B` -/

lemma norm_Gamma_le_of_re_mem {u : ℂ} {B : ℝ} (h1 : 1 ≤ u.re) (hB : u.re ≤ B) :
    ‖Complex.Gamma u‖ ≤ 1 + Real.Gamma (B + 1) := by
  have hu : 0 < u.re := by linarith
  have hB1 : (0 : ℝ) < B + 1 := by linarith
  rw [Complex.Gamma_eq_integral hu, Complex.GammaIntegral]
  have hint1 : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ ((1 : ℝ) - 1)) (Ioi 0) :=
    Real.GammaIntegral_convergent one_pos
  have hint2 : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ (B + 1 - 1)) (Ioi 0) :=
    Real.GammaIntegral_convergent hB1
  have hbound : ∀ x ∈ Ioi (0 : ℝ),
      ‖((Real.exp (-x) : ℝ) : ℂ) * (x : ℂ) ^ (u - 1)‖
        ≤ Real.exp (-x) * x ^ ((1 : ℝ) - 1) + Real.exp (-x) * x ^ (B + 1 - 1) := by
    intro x hx
    have hx0 : 0 < x := hx
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.sub_re, Complex.one_re]
    have hpow : x ^ (u.re - 1) ≤ x ^ ((1 : ℝ) - 1) + x ^ (B + 1 - 1) := by
      rcases le_or_gt x 1 with hx1 | hx1
      · have h : x ^ (u.re - 1) ≤ x ^ ((1 : ℝ) - 1) :=
          Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by linarith)
        have h0 : 0 ≤ x ^ (B + 1 - 1) := by positivity
        linarith
      · have h : x ^ (u.re - 1) ≤ x ^ (B + 1 - 1) :=
          Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
        have h0 : 0 ≤ x ^ ((1 : ℝ) - 1) := by positivity
        linarith
    calc Real.exp (-x) * x ^ (u.re - 1)
        ≤ Real.exp (-x) * (x ^ ((1 : ℝ) - 1) + x ^ (B + 1 - 1)) :=
          mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
      _ = Real.exp (-x) * x ^ ((1 : ℝ) - 1) + Real.exp (-x) * x ^ (B + 1 - 1) := by ring
  calc ‖∫ x in Ioi (0 : ℝ), ((Real.exp (-x) : ℝ) : ℂ) * (x : ℂ) ^ (u - 1)‖
      ≤ ∫ x in Ioi (0 : ℝ), (Real.exp (-x) * x ^ ((1 : ℝ) - 1) + Real.exp (-x) * x ^ (B + 1 - 1)) :=
        norm_integral_le_of_norm_le (hint1.add hint2)
          (ae_restrict_of_forall_mem measurableSet_Ioi hbound)
    _ = Real.Gamma 1 + Real.Gamma (B + 1) := by
        rw [integral_add hint1 hint2, Real.Gamma_eq_integral one_pos, Real.Gamma_eq_integral hB1]
    _ = 1 + Real.Gamma (B + 1) := by rw [Real.Gamma_one]

/-! ### the exact modulus `‖Γ(1/2 + it)‖² = π / cosh(π t)` and its lower bound -/

lemma one_sub_half_add_eq_conj (t : ℝ) :
    (1 : ℂ) - (1 / 2 + t * Complex.I) = (starRingEnd ℂ) (1 / 2 + t * Complex.I) := by
  apply Complex.ext <;> simp <;> ring

lemma sin_pi_mul_half_add (t : ℝ) :
    Complex.sin ((π : ℂ) * (1 / 2 + t * Complex.I)) = ((Real.cosh (π * t) : ℝ) : ℂ) := by
  rw [show (π : ℂ) * (1 / 2 + t * Complex.I) = ((π * t : ℝ) : ℂ) * Complex.I + π / 2 by
    push_cast; ring, Complex.sin_add_pi_div_two, Complex.cos_mul_I, Complex.ofReal_cosh]

theorem norm_Gamma_half_add_sq (t : ℝ) :
    ‖Complex.Gamma (1 / 2 + t * Complex.I)‖ ^ 2 = π / Real.cosh (π * t) := by
  have h := Complex.Gamma_mul_Gamma_one_sub (1 / 2 + t * Complex.I)
  rw [one_sub_half_add_eq_conj, Complex.Gamma_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    sin_pi_mul_half_add] at h
  exact_mod_cast h

lemma cosh_le_exp_abs (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  rw [Real.cosh_eq]
  have h1 : Real.exp x ≤ Real.exp |x| := Real.exp_le_exp.mpr (le_abs_self _)
  have h2 : Real.exp (-x) ≤ Real.exp |x| := Real.exp_le_exp.mpr (neg_le_abs _)
  linarith

/-- **The lower bound on the line `Re = 1/2`**: `π e^{−π|t|} ≤ ‖Γ(1/2 + it)‖²`. -/
theorem norm_Gamma_half_add_sq_ge (t : ℝ) :
    π * Real.exp (-(π * |t|)) ≤ ‖Complex.Gamma (1 / 2 + t * Complex.I)‖ ^ 2 := by
  rw [norm_Gamma_half_add_sq]
  have hc : 0 < Real.cosh (π * t) := Real.cosh_pos _
  have hle : Real.cosh (π * t) ≤ Real.exp (π * |t|) := by
    have := cosh_le_exp_abs (π * t)
    rwa [abs_mul, abs_of_pos Real.pi_pos] at this
  rw [Real.exp_neg, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_left Real.pi_pos.le hc hle

end RankinSelbergDelta.RankinSelberg

/-! ### the Stirling-type bound `‖1/Γ(w)‖ ≤ 8 e^{π|Im w|/2}` on `1/2 ≤ Re w ≤ 3/2`,
by Phragmén–Lindelöf from the exact values on the two boundary lines -/

namespace RankinSelbergDelta.RankinSelberg

open Complex MeasureTheory Set Filter
open scoped Real Topology

/-- `‖Γ(u)‖ ≤ Γ(a) + Γ(B + 1)` for `0 < a ≤ Re u ≤ B`. -/
lemma norm_Gamma_le_of_re_mem' {u : ℂ} {a B : ℝ} (ha : 0 < a) (h1 : a ≤ u.re) (hB : u.re ≤ B) :
    ‖Complex.Gamma u‖ ≤ Real.Gamma a + Real.Gamma (B + 1) := by
  have hu : 0 < u.re := by linarith
  have hB1 : (0 : ℝ) < B + 1 := by linarith
  rw [Complex.Gamma_eq_integral hu, Complex.GammaIntegral]
  have hint1 : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ (a - 1)) (Ioi 0) :=
    Real.GammaIntegral_convergent ha
  have hint2 : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ (B + 1 - 1)) (Ioi 0) :=
    Real.GammaIntegral_convergent hB1
  have hbound : ∀ x ∈ Ioi (0 : ℝ),
      ‖((Real.exp (-x) : ℝ) : ℂ) * (x : ℂ) ^ (u - 1)‖
        ≤ Real.exp (-x) * x ^ (a - 1) + Real.exp (-x) * x ^ (B + 1 - 1) := by
    intro x hx
    have hx0 : 0 < x := hx
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.sub_re, Complex.one_re]
    have hpow : x ^ (u.re - 1) ≤ x ^ (a - 1) + x ^ (B + 1 - 1) := by
      rcases le_or_gt x 1 with hx1 | hx1
      · have h : x ^ (u.re - 1) ≤ x ^ (a - 1) :=
          Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by linarith)
        have h0 : 0 ≤ x ^ (B + 1 - 1) := by positivity
        linarith
      · have h : x ^ (u.re - 1) ≤ x ^ (B + 1 - 1) :=
          Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
        have h0 : 0 ≤ x ^ (a - 1) := by positivity
        linarith
    calc Real.exp (-x) * x ^ (u.re - 1)
        ≤ Real.exp (-x) * (x ^ (a - 1) + x ^ (B + 1 - 1)) :=
          mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
      _ = Real.exp (-x) * x ^ (a - 1) + Real.exp (-x) * x ^ (B + 1 - 1) := by ring
  calc ‖∫ x in Ioi (0 : ℝ), ((Real.exp (-x) : ℝ) : ℂ) * (x : ℂ) ^ (u - 1)‖
      ≤ ∫ x in Ioi (0 : ℝ), (Real.exp (-x) * x ^ (a - 1) + Real.exp (-x) * x ^ (B + 1 - 1)) :=
        norm_integral_le_of_norm_le (hint1.add hint2)
          (ae_restrict_of_forall_mem measurableSet_Ioi hbound)
    _ = Real.Gamma a + Real.Gamma (B + 1) := by
        rw [integral_add hint1 hint2, Real.Gamma_eq_integral ha, Real.Gamma_eq_integral hB1]

/-- `1/Γ(w) = Γ(2 − w) · sin(πw) / (π (1 − w))` when `w ≠ 1` and `sin(πw) ≠ 0`. -/
lemma inv_Gamma_eq_of_sin_ne_zero {w : ℂ} (hw : w ≠ 1) (hs : Complex.sin (π * w) ≠ 0) :
    (Complex.Gamma w)⁻¹ = Complex.Gamma (2 - w) * Complex.sin (π * w) / (π * (1 - w)) := by
  have h1w : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hrefl := Complex.Gamma_mul_Gamma_one_sub w
  have hprod : Complex.Gamma w * Complex.Gamma (1 - w) ≠ 0 := by
    rw [hrefl]; exact div_ne_zero hπ hs
  have hΓ : Complex.Gamma w ≠ 0 := left_ne_zero_of_mul hprod
  have hshift : Complex.Gamma (2 - w) = (1 - w) * Complex.Gamma (1 - w) := by
    rw [show (2 : ℂ) - w = (1 - w) + 1 by ring, Complex.Gamma_add_one _ h1w]
  rw [eq_div_iff hs] at hrefl
  rw [hshift, eq_div_iff (mul_ne_zero hπ h1w), inv_mul_eq_iff_eq_mul₀ hΓ]
  linear_combination (w - 1) * hrefl

/-- The zeros of `sin(πw)` are the integers; on the strip `1/2 ≤ Re w ≤ 3/2` the only one is `1`. -/
lemma sin_pi_mul_ne_zero_of_strip {w : ℂ} (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 3 / 2)
    (hw : 1 / 4 ≤ ‖w - 1‖) : Complex.sin (π * w) ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hwk : w = (k : ℂ) := by
    have : (π : ℂ) * w = (π : ℂ) * k := by rw [hk]; ring
    exact mul_left_cancel₀ hπ this
  have hre : (k : ℝ) = w.re := by rw [hwk]; simp
  have hk1 : k = 1 := by
    have hk' : (1 : ℝ) / 2 ≤ k ∧ (k : ℝ) ≤ 3 / 2 := by rw [hre]; exact ⟨h1, h2⟩
    have hlo : (0 : ℤ) < k := by exact_mod_cast (by linarith [hk'.1] : (0 : ℝ) < k)
    have hhi : k < 2 := by exact_mod_cast (by linarith [hk'.2] : (k : ℝ) < 2)
    omega
  rw [hwk, hk1] at hw
  norm_num at hw

/-- The a-priori constant. -/
noncomputable def gammaK0 : ℝ := (Real.Gamma (1 / 2) + Real.Gamma (5 / 2)) * 4 / π

lemma gammaK0_pos : 0 < gammaK0 := by
  unfold gammaK0
  have h1 : 0 < Real.Gamma (1 / 2) := Real.Gamma_pos_of_pos (by norm_num)
  have h2 : 0 < Real.Gamma (5 / 2) := Real.Gamma_pos_of_pos (by norm_num)
  positivity

lemma im_pi_mul (w : ℂ) : ((π : ℂ) * w).im = π * w.im := by simp

/-- The a-priori bound away from `w = 1`. -/
lemma norm_inv_Gamma_le_of_dist {w : ℂ} (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 3 / 2)
    (hw : 1 / 4 ≤ ‖w - 1‖) :
    ‖(Complex.Gamma w)⁻¹‖ ≤ gammaK0 * Real.exp (π * |w.im|) := by
  have hw1 : w ≠ 1 := by
    intro h; rw [h, sub_self, norm_zero] at hw; linarith
  have hs := sin_pi_mul_ne_zero_of_strip h1 h2 hw
  rw [inv_Gamma_eq_of_sin_ne_zero hw1 hs, norm_div, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le]
  have hΓ : ‖Complex.Gamma (2 - w)‖ ≤ Real.Gamma (1 / 2) + Real.Gamma (5 / 2) := by
    have := norm_Gamma_le_of_re_mem' (u := 2 - w) (a := 1 / 2) (B := 3 / 2) (by norm_num)
      (by simp only [Complex.sub_re, Complex.re_ofNat]; linarith)
      (by simp only [Complex.sub_re, Complex.re_ofNat]; linarith)
    rwa [show (3 : ℝ) / 2 + 1 = 5 / 2 by norm_num] at this
  have hsin : ‖Complex.sin (π * w)‖ ≤ Real.exp (π * |w.im|) := by
    have := norm_sin_le_exp ((π : ℂ) * w)
    rwa [im_pi_mul, abs_mul, abs_of_pos Real.pi_pos] at this
  have hden : 1 / 4 ≤ ‖(1 : ℂ) - w‖ := by rwa [norm_sub_rev]
  have hdenpos : 0 < ‖(1 : ℂ) - w‖ := by linarith
  have hG0 : 0 ≤ Real.Gamma (1 / 2) + Real.Gamma (5 / 2) := by
    have h1 : 0 < Real.Gamma (1 / 2) := Real.Gamma_pos_of_pos (by norm_num)
    have h2 : 0 < Real.Gamma (5 / 2) := Real.Gamma_pos_of_pos (by norm_num)
    linarith
  rw [div_le_iff₀ (mul_pos Real.pi_pos hdenpos)]
  calc ‖Complex.Gamma (2 - w)‖ * ‖Complex.sin (π * w)‖
      ≤ (Real.Gamma (1 / 2) + Real.Gamma (5 / 2)) * Real.exp (π * |w.im|) :=
        mul_le_mul hΓ hsin (norm_nonneg _) hG0
    _ = gammaK0 * Real.exp (π * |w.im|) * (π * (1 / 4)) := by
        unfold gammaK0; field_simp; try ring
    _ ≤ gammaK0 * Real.exp (π * |w.im|) * (π * ‖(1 : ℂ) - w‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hden Real.pi_pos.le)
          (mul_pos gammaK0_pos (Real.exp_pos _)).le

/-- The a-priori constant including the disc around `1`. -/
noncomputable def gammaK : ℝ := gammaK0 * Real.exp (π / 4)

lemma gammaK_pos : 0 < gammaK := mul_pos gammaK0_pos (Real.exp_pos _)

/-- **The a-priori bound on the strip**: `‖1/Γ(w)‖ ≤ gammaK · e^{π|Im w|}` for `1/2 ≤ Re w ≤ 3/2`. -/
theorem norm_inv_Gamma_le_apriori {w : ℂ} (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 3 / 2) :
    ‖(Complex.Gamma w)⁻¹‖ ≤ gammaK * Real.exp (π * |w.im|) := by
  have hK0 : 1 ≤ Real.exp (π / 4) := Real.one_le_exp (by positivity)
  rcases le_or_gt (1 / 4 : ℝ) ‖w - 1‖ with hw | hw
  · calc ‖(Complex.Gamma w)⁻¹‖ ≤ gammaK0 * Real.exp (π * |w.im|) :=
          norm_inv_Gamma_le_of_dist h1 h2 hw
      _ ≤ gammaK * Real.exp (π * |w.im|) := by
          unfold gammaK
          have hK := gammaK0_pos.le
          calc gammaK0 * Real.exp (π * |w.im|) = gammaK0 * 1 * Real.exp (π * |w.im|) := by ring
            _ ≤ gammaK0 * Real.exp (π / 4) * Real.exp (π * |w.im|) := by gcongr
  · -- maximum modulus on the disc of radius `1/4` around `1`
    have hball : w ∈ closure (Metric.ball (1 : ℂ) (1 / 4)) := by
      rw [closure_ball (1 : ℂ) (by norm_num), Metric.mem_closedBall, Complex.dist_eq]
      exact hw.le
    have hC : ∀ z ∈ frontier (Metric.ball (1 : ℂ) (1 / 4)),
        ‖(Complex.Gamma z)⁻¹‖ ≤ gammaK := by
      intro z hz
      rw [frontier_ball (1 : ℂ) (by norm_num), Metric.mem_sphere, Complex.dist_eq] at hz
      have hre : |z.re - 1| ≤ 1 / 4 := by
        have := Complex.abs_re_le_norm (z - 1)
        rw [Complex.sub_re, Complex.one_re] at this
        linarith
      have him : |z.im| ≤ 1 / 4 := by
        have := Complex.abs_im_le_norm (z - 1)
        rw [Complex.sub_im, Complex.one_im, sub_zero] at this
        linarith
      rw [abs_le] at hre
      have hz1 : 1 / 2 ≤ z.re := by linarith [hre.1]
      have hz2 : z.re ≤ 3 / 2 := by linarith [hre.2]
      calc ‖(Complex.Gamma z)⁻¹‖ ≤ gammaK0 * Real.exp (π * |z.im|) :=
            norm_inv_Gamma_le_of_dist hz1 hz2 hz.ge
        _ ≤ gammaK0 * Real.exp (π / 4) := by
            have hle : π * |z.im| ≤ π / 4 := by
              have := mul_le_mul_of_nonneg_left him Real.pi_pos.le
              linarith
            exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) gammaK0_pos.le
        _ = gammaK := rfl
    have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball
      (Complex.differentiable_one_div_Gamma.diffContOnCl) hC hball
    calc ‖(Complex.Gamma w)⁻¹‖ ≤ gammaK := hmax
      _ ≤ gammaK * Real.exp (π * |w.im|) := by
          have := gammaK_pos
          nlinarith [Real.one_le_exp (by positivity : (0 : ℝ) ≤ π * |w.im|)]

/-! #### The weight `φ(w) = cos(π (w − 1) / 2)` -/

lemma norm_cos_le_exp (z : ℂ) : ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  have e1 : ‖Complex.exp (z * Complex.I)‖ = Real.exp (-z.im) := by
    rw [Complex.norm_exp]; congr 1; simp
  have e2 : ‖Complex.exp (-z * Complex.I)‖ = Real.exp z.im := by
    rw [Complex.norm_exp]; congr 1; simp
  have h1 : Real.exp z.im ≤ Real.exp |z.im| := Real.exp_le_exp.mpr (le_abs_self _)
  have h2 : Real.exp (-z.im) ≤ Real.exp |z.im| := Real.exp_le_exp.mpr (neg_le_abs _)
  rw [Complex.cos, norm_div, Complex.norm_ofNat]
  calc ‖Complex.exp (z * Complex.I) + Complex.exp (-z * Complex.I)‖ / 2
      ≤ (‖Complex.exp (z * Complex.I)‖ + ‖Complex.exp (-z * Complex.I)‖) / 2 := by
        gcongr; exact norm_add_le _ _
    _ = (Real.exp (-z.im) + Real.exp z.im) / 2 := by rw [e1, e2]
    _ ≤ Real.exp |z.im| := by linarith

/-- The weight. -/
noncomputable def gammaPhi (w : ℂ) : ℂ := Complex.cos ((π : ℂ) * (w - 1) / 2)

lemma gammaPhi_arg (w : ℂ) :
    (π : ℂ) * (w - 1) / 2 = ((π * (w.re - 1) / 2 : ℝ) : ℂ) + ((π * w.im / 2 : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;> simp <;> ring

lemma norm_gammaPhi_le (w : ℂ) : ‖gammaPhi w‖ ≤ Real.exp (π * |w.im| / 2) := by
  have := norm_cos_le_exp ((π : ℂ) * (w - 1) / 2)
  have him : ((π : ℂ) * (w - 1) / 2).im = π * w.im / 2 := by simp
  rw [him, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_two] at this
  simpa [gammaPhi] using this

lemma cos_ge_half_of_abs_le {x : ℝ} (hx : |x| ≤ π / 4) : 1 / 2 ≤ Real.cos x := by
  have h := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg x) (by linarith [Real.pi_pos] : π / 4 ≤ π) hx
  rw [Real.cos_pi_div_four, Real.cos_abs] at h
  have : (1 : ℝ) / 2 ≤ √2 / 2 := by
    have h2 : (1 : ℝ) ≤ √2 := by
      rw [show (1 : ℝ) = √1 by simp]
      exact Real.sqrt_le_sqrt (by norm_num)
    linarith
  linarith

lemma norm_gammaPhi_ge {w : ℂ} (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 3 / 2) :
    Real.exp (π * |w.im| / 2) / 4 ≤ ‖gammaPhi w‖ := by
  set x : ℝ := π * (w.re - 1) / 2 with hx
  set y : ℝ := π * w.im / 2 with hy
  have hre : (gammaPhi w).re = Real.cos x * Real.cosh y := by
    rw [gammaPhi, gammaPhi_arg, ← hx, ← hy, Complex.cos_add_mul_I]
    simp [← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sin, ← Complex.ofReal_sinh]
  have hxabs : |x| ≤ π / 4 := by
    rw [hx, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_two]
    have : |w.re - 1| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
    calc π * |w.re - 1| / 2 ≤ π * (1 / 2) / 2 := by gcongr
      _ = π / 4 := by ring
  have hcos : 1 / 2 ≤ Real.cos x := cos_ge_half_of_abs_le hxabs
  have hcosh : Real.exp |y| / 2 ≤ Real.cosh y := by
    rw [Real.cosh_eq]
    rcases le_or_gt 0 y with hy0 | hy0
    · rw [abs_of_nonneg hy0]; linarith [Real.exp_pos (-y)]
    · rw [abs_of_neg hy0]; linarith [Real.exp_pos y]
  have hyabs : |y| = π * |w.im| / 2 := by
    rw [hy, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_two]
  calc Real.exp (π * |w.im| / 2) / 4 = (1 / 2) * (Real.exp |y| / 2) := by rw [hyabs]; ring
    _ ≤ Real.cos x * Real.cosh y :=
        mul_le_mul hcos hcosh (by positivity) (by linarith)
    _ = (gammaPhi w).re := hre.symm
    _ ≤ |(gammaPhi w).re| := le_abs_self _
    _ ≤ ‖gammaPhi w‖ := Complex.abs_re_le_norm _

lemma gammaPhi_ne_zero {w : ℂ} (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 3 / 2) : gammaPhi w ≠ 0 := by
  intro h
  have := norm_gammaPhi_ge h1 h2
  rw [h, norm_zero] at this
  linarith [Real.exp_pos (π * |w.im| / 2)]

/-! #### The boundary lines -/

lemma re_half_add (t : ℝ) : ((1 : ℂ) / 2 + t * Complex.I).re = 1 / 2 := by
  simp <;> norm_num

lemma re_three_half_add (t : ℝ) : ((3 : ℂ) / 2 + t * Complex.I).re = 3 / 2 := by
  simp <;> norm_num

lemma norm_inv_Gamma_half (t : ℝ) :
    ‖(Complex.Gamma (1 / 2 + t * Complex.I))⁻¹‖ ≤ Real.exp (π * |t| / 2) := by
  have hsq := norm_Gamma_half_add_sq t
  have hΓ : Complex.Gamma (1 / 2 + t * Complex.I) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by rw [re_half_add]; norm_num)
  have hpos : 0 < ‖Complex.Gamma (1 / 2 + t * Complex.I)‖ := norm_pos_iff.mpr hΓ
  have hc : 0 < Real.cosh (π * t) := Real.cosh_pos _
  rw [norm_inv]
  have key : (‖Complex.Gamma (1 / 2 + t * Complex.I)‖⁻¹) ^ 2 ≤ (Real.exp (π * |t| / 2)) ^ 2 := by
    rw [inv_pow, hsq, ← Real.exp_nat_mul]
    have hle : Real.cosh (π * t) ≤ Real.exp (π * |t|) := by
      have := cosh_le_exp_abs (π * t)
      rwa [abs_mul, abs_of_pos Real.pi_pos] at this
    rw [inv_div, div_le_iff₀ Real.pi_pos]
    push_cast
    calc Real.cosh (π * t) ≤ Real.exp (π * |t|) := hle
      _ ≤ Real.exp (π * |t|) * π := by
          have := Real.pi_gt_three
          nlinarith [Real.exp_pos (π * |t|)]
      _ = Real.exp (2 * (π * |t| / 2)) * π := by congr 2; ring
  first
    | exact (pow_le_pow_iff_left₀ (by positivity) (Real.exp_pos _).le two_ne_zero).mp key
    | exact le_of_pow_le_pow_left two_ne_zero (Real.exp_pos _).le key
    | exact (pow_le_pow_iff_left (by positivity) (Real.exp_pos _).le two_ne_zero).mp key

lemma norm_inv_Gamma_three_half (t : ℝ) :
    ‖(Complex.Gamma (3 / 2 + t * Complex.I))⁻¹‖ ≤ 2 * Real.exp (π * |t| / 2) := by
  have hne : (1 / 2 : ℂ) + t * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [re_half_add, Complex.zero_re] at this
    norm_num at this
  have hshift : Complex.Gamma (3 / 2 + t * Complex.I)
      = (1 / 2 + t * Complex.I) * Complex.Gamma (1 / 2 + t * Complex.I) := by
    rw [show (3 / 2 : ℂ) + t * Complex.I = (1 / 2 + t * Complex.I) + 1 by ring,
      Complex.Gamma_add_one _ hne]
  have hnorm : 1 / 2 ≤ ‖(1 / 2 : ℂ) + t * Complex.I‖ := by
    have := Complex.abs_re_le_norm ((1 / 2 : ℂ) + t * Complex.I)
    rw [re_half_add, abs_of_pos (by norm_num)] at this
    exact this
  rw [hshift, mul_inv, norm_mul, norm_inv]
  have hinv : ‖(1 / 2 : ℂ) + t * Complex.I‖⁻¹ ≤ 2 := by
    calc ‖(1 / 2 : ℂ) + t * Complex.I‖⁻¹ ≤ ((1 : ℝ) / 2)⁻¹ := inv_anti₀ (by norm_num) hnorm
      _ = 2 := by norm_num
  calc ‖(1 / 2 : ℂ) + t * Complex.I‖⁻¹ * ‖(Complex.Gamma (1 / 2 + t * Complex.I))⁻¹‖
      ≤ 2 * Real.exp (π * |t| / 2) :=
        mul_le_mul hinv (norm_inv_Gamma_half t) (norm_nonneg _) (by norm_num)

/-! #### Phragmén–Lindelöf -/

/-- The strip `1/2 ≤ Re ≤ 3/2` is closed. -/
lemma closure_strip_subset :
    closure (Complex.re ⁻¹' Ioo (1 / 2 : ℝ) (3 / 2)) ⊆ {w : ℂ | 1 / 2 ≤ w.re ∧ w.re ≤ 3 / 2} := by
  refine closure_minimal (fun w hw => ⟨hw.1.le, hw.2.le⟩) ?_
  exact (isClosed_le continuous_const Complex.continuous_re).inter
    (isClosed_le Complex.continuous_re continuous_const)

/-- The weighted function `h(z) = (Γ z)⁻¹ · (φ z)⁻¹`. -/
noncomputable def gammaH (z : ℂ) : ℂ := (Complex.Gamma z)⁻¹ * (gammaPhi z)⁻¹

lemma norm_gammaH_le {z : ℂ} (hz1 : 1 / 2 ≤ z.re) (hz2 : z.re ≤ 3 / 2) :
    ‖gammaH z‖ ≤ ‖(Complex.Gamma z)⁻¹‖ * (4 * Real.exp (-(π * |z.im| / 2))) := by
  unfold gammaH
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [norm_inv]
  have hpos := norm_gammaPhi_ge hz1 hz2
  have hE : 0 < Real.exp (π * |z.im| / 2) := Real.exp_pos _
  have hne : 0 < ‖gammaPhi z‖ := norm_pos_iff.mpr (gammaPhi_ne_zero hz1 hz2)
  rw [Real.exp_neg]
  calc ‖gammaPhi z‖⁻¹ ≤ (Real.exp (π * |z.im| / 2) / 4)⁻¹ := inv_anti₀ (by positivity) hpos
    _ = 4 * (Real.exp (π * |z.im| / 2))⁻¹ := by rw [inv_div]; ring

lemma differentiable_gammaPhi : Differentiable ℂ gammaPhi := by
  show Differentiable ℂ (Complex.cos ∘ fun z : ℂ => (π : ℂ) * (z - 1) / 2)
  exact Complex.differentiable_cos.comp
    (((differentiable_id.sub_const _).const_mul _).div_const _)

lemma differentiableOn_gammaH :
    DifferentiableOn ℂ gammaH {w : ℂ | 1 / 2 ≤ w.re ∧ w.re ≤ 3 / 2} := by
  unfold gammaH
  refine (Complex.differentiable_one_div_Gamma.differentiableOn).mul ?_
  exact DifferentiableOn.inv differentiable_gammaPhi.differentiableOn
    fun z hz => gammaPhi_ne_zero hz.1 hz.2

lemma norm_gammaH_le_left {z : ℂ} (hz : z.re = 1 / 2) : ‖gammaH z‖ ≤ 8 := by
  have hz' : z = 1 / 2 + z.im * Complex.I := by
    apply Complex.ext <;> simp [hz]
  have hΓ : ‖(Complex.Gamma z)⁻¹‖ ≤ Real.exp (π * |z.im| / 2) := by
    have := norm_inv_Gamma_half z.im
    rwa [← hz'] at this
  have hphi := norm_gammaH_le (z := z) (by linarith) (by linarith)
  have hE : Real.exp (π * |z.im| / 2) * Real.exp (-(π * |z.im| / 2)) = 1 := by
    rw [← Real.exp_add]; simp
  calc ‖gammaH z‖ ≤ ‖(Complex.Gamma z)⁻¹‖ * (4 * Real.exp (-(π * |z.im| / 2))) := hphi
    _ ≤ Real.exp (π * |z.im| / 2) * (4 * Real.exp (-(π * |z.im| / 2))) :=
        mul_le_mul_of_nonneg_right hΓ (by positivity)
    _ = 4 * (Real.exp (π * |z.im| / 2) * Real.exp (-(π * |z.im| / 2))) := by ring
    _ = 4 := by rw [hE, mul_one]
    _ ≤ 8 := by norm_num

lemma norm_gammaH_le_right {z : ℂ} (hz : z.re = 3 / 2) : ‖gammaH z‖ ≤ 8 := by
  have hz' : z = 3 / 2 + z.im * Complex.I := by
    apply Complex.ext <;> simp [hz]
  have hΓ : ‖(Complex.Gamma z)⁻¹‖ ≤ 2 * Real.exp (π * |z.im| / 2) := by
    have := norm_inv_Gamma_three_half z.im
    rwa [← hz'] at this
  have hphi := norm_gammaH_le (z := z) (by linarith) (by linarith)
  have hE : Real.exp (π * |z.im| / 2) * Real.exp (-(π * |z.im| / 2)) = 1 := by
    rw [← Real.exp_add]; simp
  calc ‖gammaH z‖ ≤ ‖(Complex.Gamma z)⁻¹‖ * (4 * Real.exp (-(π * |z.im| / 2))) := hphi
    _ ≤ 2 * Real.exp (π * |z.im| / 2) * (4 * Real.exp (-(π * |z.im| / 2))) :=
        mul_le_mul_of_nonneg_right hΓ (by positivity)
    _ = 8 * (Real.exp (π * |z.im| / 2) * Real.exp (-(π * |z.im| / 2))) := by ring
    _ = 8 := by rw [hE, mul_one]

lemma gammaH_isBigO :
    gammaH =O[Filter.comap (fun z : ℂ => |z.im|) Filter.atTop ⊓
        Filter.principal (Complex.re ⁻¹' Ioo (1 / 2 : ℝ) (3 / 2))]
      fun z => Real.exp (π * Real.exp (1 * |z.im|)) := by
  refine Asymptotics.IsBigO.of_bound (4 * gammaK) ?_
  rw [Filter.eventually_inf_principal]
  refine Filter.Eventually.of_forall fun z hz => ?_
  have hz1 : 1 / 2 ≤ z.re := hz.1.le
  have hz2 : z.re ≤ 3 / 2 := hz.2.le
  have hap := norm_inv_Gamma_le_apriori hz1 hz2
  have hphi := norm_gammaH_le hz1 hz2
  have hE : Real.exp (π * |z.im|) * Real.exp (-(π * |z.im| / 2)) = Real.exp (π * |z.im| / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hgrow : Real.exp (π * |z.im| / 2) ≤ Real.exp (π * Real.exp (1 * |z.im|)) := by
    refine Real.exp_le_exp.mpr ?_
    have h1 := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (1 * |z.im|)) Real.pi_pos.le
    have h2 := mul_nonneg Real.pi_pos.le (abs_nonneg z.im)
    linarith [Real.pi_pos]
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc ‖gammaH z‖ ≤ ‖(Complex.Gamma z)⁻¹‖ * (4 * Real.exp (-(π * |z.im| / 2))) := hphi
    _ ≤ gammaK * Real.exp (π * |z.im|) * (4 * Real.exp (-(π * |z.im| / 2))) :=
        mul_le_mul_of_nonneg_right hap (by positivity)
    _ = 4 * gammaK * (Real.exp (π * |z.im|) * Real.exp (-(π * |z.im| / 2))) := by ring
    _ = 4 * gammaK * Real.exp (π * |z.im| / 2) := by rw [hE]
    _ ≤ 4 * gammaK * Real.exp (π * Real.exp (1 * |z.im|)) :=
        mul_le_mul_of_nonneg_left hgrow (by have := gammaK_pos; positivity)

/-- Phragmén–Lindelöf on the strip: `‖h‖ ≤ 8` throughout. -/
theorem norm_gammaH_le_strip {w : ℂ} (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 3 / 2) :
    ‖gammaH w‖ ≤ 8 := by
  refine PhragmenLindelof.vertical_strip (a := 1 / 2) (b := 3 / 2) ?_ ?_ ?_ ?_ h1 h2
  · exact DifferentiableOn.diffContOnCl
      (differentiableOn_gammaH.mono closure_strip_subset)
  · refine ⟨1, ?_, π, gammaH_isBigO⟩
    rw [show (3 / 2 : ℝ) - 1 / 2 = 1 by norm_num, div_one]
    linarith [Real.pi_gt_three]
  · intro z hz
    exact norm_gammaH_le_left hz
  · intro z hz
    exact norm_gammaH_le_right hz

/-- **The Stirling-type bound for `1/Γ` on `1/2 ≤ Re w ≤ 3/2`.** -/
theorem norm_inv_Gamma_le_strip {w : ℂ} (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 3 / 2) :
    ‖(Complex.Gamma w)⁻¹‖ ≤ 8 * Real.exp (π * |w.im| / 2) := by
  have hphi_ne : gammaPhi w ≠ 0 := gammaPhi_ne_zero h1 h2
  have hw' : ‖(Complex.Gamma w)⁻¹‖ = ‖gammaH w‖ * ‖gammaPhi w‖ := by
    unfold gammaH
    rw [norm_mul, norm_inv, norm_inv, mul_assoc, inv_mul_cancel₀ (norm_pos_iff.mpr hphi_ne).ne',
      mul_one]
  rw [hw']
  exact mul_le_mul (norm_gammaH_le_strip h1 h2) (norm_gammaPhi_le w) (norm_nonneg _) (by norm_num)

end RankinSelbergDelta.RankinSelberg

/-! ### the sharp upper bound `‖Γ(w)‖ ≤ 48 (1 + |Im w|) e^{−π|Im w|/2}` on
`1/2 ≤ Re w ≤ 3/2`, and the integer shifts of both bounds to arbitrary vertical strips -/

namespace RankinSelbergDelta.RankinSelberg

open Complex MeasureTheory Set Filter
open scoped Real Topology

lemma le_of_sq_le_sq' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  calc a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha).symm
    _ ≤ Real.sqrt (b ^ 2) := Real.sqrt_le_sqrt h
    _ = b := Real.sqrt_sq hb

/-- `‖Γ(1/2 + it)‖ ≤ 3 e^{−π|t|/2}` (from the exact modulus `π / cosh(πt)` and `2π ≤ 9`). -/
lemma norm_Gamma_half_le (t : ℝ) :
    ‖Complex.Gamma (1 / 2 + t * Complex.I)‖ ≤ 3 * Real.exp (-(π * |t| / 2)) := by
  have hsq := norm_Gamma_half_add_sq t
  have hc : 0 < Real.cosh (π * t) := Real.cosh_pos _
  have hcosh : Real.exp (π * |t|) / 2 ≤ Real.cosh (π * t) := by
    rw [Real.cosh_eq]
    rcases le_or_gt 0 t with ht | ht
    · rw [abs_of_nonneg ht]; linarith [Real.exp_pos (-(π * t))]
    · rw [abs_of_neg ht]
      have : -(π * t) = π * -t := by ring
      rw [this]; linarith [Real.exp_pos (π * t)]
  have key : ‖Complex.Gamma (1 / 2 + t * Complex.I)‖ ^ 2 ≤ (3 * Real.exp (-(π * |t| / 2))) ^ 2 := by
    rw [hsq, mul_pow, ← Real.exp_nat_mul]
    push_cast
    have hE : Real.exp (2 * -(π * |t| / 2)) = (Real.exp (π * |t|))⁻¹ := by
      rw [← Real.exp_neg]; congr 1; ring
    rw [hE, div_le_iff₀ hc]
    have hpi : π ≤ 4 := Real.pi_le_four
    have hEpos : 0 < Real.exp (π * |t|) := Real.exp_pos _
    calc π ≤ 9 / 2 := by linarith
      _ = 3 ^ 2 * (Real.exp (π * |t|))⁻¹ * (Real.exp (π * |t|) / 2) := by
          field_simp
          try norm_num
      _ ≤ 3 ^ 2 * (Real.exp (π * |t|))⁻¹ * Real.cosh (π * t) := by
          gcongr
  exact le_of_sq_le_sq' (norm_nonneg _) (by positivity) key

/-- The weighted function `g(w) = Γ(w) φ(w) / (w + 2)`. -/
noncomputable def gammaG (w : ℂ) : ℂ := Complex.Gamma w * gammaPhi w / (w + 2)

lemma norm_add_two_ge {w : ℂ} (h1 : 1 / 2 ≤ w.re) : 5 / 2 ≤ ‖w + 2‖ := by
  have := Complex.abs_re_le_norm (w + 2)
  rw [Complex.add_re, Complex.re_ofNat] at this
  have h : |w.re + 2| = w.re + 2 := abs_of_pos (by linarith)
  linarith

lemma norm_add_two_le {w : ℂ} (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 3 / 2) :
    ‖w + 2‖ ≤ 4 * (1 + |w.im|) := by
  have h := Complex.norm_le_abs_re_add_abs_im (w + 2)
  rw [Complex.add_re, Complex.add_im, Complex.re_ofNat, Complex.im_ofNat, add_zero] at h
  have hre : |w.re + 2| ≤ 7 / 2 := by rw [abs_le]; constructor <;> linarith
  linarith [abs_nonneg w.im]

lemma norm_add_two_ne_zero {w : ℂ} (h1 : 1 / 2 ≤ w.re) : w + 2 ≠ 0 := by
  intro h
  have := norm_add_two_ge h1
  rw [h, norm_zero] at this
  linarith

lemma norm_gammaG_le_left {z : ℂ} (hz : z.re = 1 / 2) : ‖gammaG z‖ ≤ 3 := by
  have hz' : z = 1 / 2 + z.im * Complex.I := by
    apply Complex.ext <;> simp [hz]
  have hΓ : ‖Complex.Gamma z‖ ≤ 3 * Real.exp (-(π * |z.im| / 2)) := by
    have := norm_Gamma_half_le z.im
    rwa [← hz'] at this
  have hphi := norm_gammaPhi_le z
  have hden := norm_add_two_ge (w := z) (by linarith)
  have hE : Real.exp (-(π * |z.im| / 2)) * Real.exp (π * |z.im| / 2) = 1 := by
    rw [← Real.exp_add]; simp
  unfold gammaG
  rw [norm_div, norm_mul, div_le_iff₀ (by linarith)]
  calc ‖Complex.Gamma z‖ * ‖gammaPhi z‖
      ≤ 3 * Real.exp (-(π * |z.im| / 2)) * Real.exp (π * |z.im| / 2) :=
        mul_le_mul hΓ hphi (norm_nonneg _) (by positivity)
    _ = 3 := by rw [mul_assoc, hE, mul_one]
    _ ≤ 3 * ‖z + 2‖ := by nlinarith

lemma norm_gammaG_le_right {z : ℂ} (hz : z.re = 3 / 2) : ‖gammaG z‖ ≤ 3 := by
  have hz' : z = 3 / 2 + z.im * Complex.I := by
    apply Complex.ext <;> simp [hz]
  have hne : (1 / 2 : ℂ) + z.im * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [re_half_add, Complex.zero_re] at this
    norm_num at this
  have hshift : Complex.Gamma (3 / 2 + z.im * Complex.I)
      = (1 / 2 + z.im * Complex.I) * Complex.Gamma (1 / 2 + z.im * Complex.I) := by
    rw [show (3 / 2 : ℂ) + z.im * Complex.I = (1 / 2 + z.im * Complex.I) + 1 by ring,
      Complex.Gamma_add_one _ hne]
  have hΓ : ‖Complex.Gamma z‖
      ≤ ‖(1 / 2 : ℂ) + z.im * Complex.I‖ * (3 * Real.exp (-(π * |z.im| / 2))) := by
    have h := norm_Gamma_half_le z.im
    have hΓ' : ‖Complex.Gamma (3 / 2 + z.im * Complex.I)‖
        ≤ ‖(1 / 2 : ℂ) + z.im * Complex.I‖ * (3 * Real.exp (-(π * |z.im| / 2))) := by
      rw [hshift, norm_mul]
      exact mul_le_mul_of_nonneg_left h (norm_nonneg _)
    rwa [← hz'] at hΓ'
  -- `‖1/2 + it‖ ≤ ‖z + 2‖ = ‖7/2 + it‖`
  have hcmp : ‖(1 / 2 : ℂ) + z.im * Complex.I‖ ≤ ‖z + 2‖ := by
    have e1 : ‖(1 / 2 : ℂ) + z.im * Complex.I‖ ^ 2 = (1 / 2) ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, re_half_add]
      simp <;> ring
    have e2 : ‖z + 2‖ ^ 2 = (7 / 2) ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im, hz]
      simp <;> ring
    have : ‖(1 / 2 : ℂ) + z.im * Complex.I‖ ^ 2 ≤ ‖z + 2‖ ^ 2 := by
      rw [e1, e2]; linarith
    exact le_of_sq_le_sq' (norm_nonneg _) (norm_nonneg _) this
  have hphi := norm_gammaPhi_le z
  have hden := norm_add_two_ge (w := z) (by linarith)
  have hE : Real.exp (-(π * |z.im| / 2)) * Real.exp (π * |z.im| / 2) = 1 := by
    rw [← Real.exp_add]; simp
  unfold gammaG
  rw [norm_div, norm_mul, div_le_iff₀ (by linarith)]
  calc ‖Complex.Gamma z‖ * ‖gammaPhi z‖
      ≤ (‖(1 / 2 : ℂ) + z.im * Complex.I‖ * (3 * Real.exp (-(π * |z.im| / 2))))
          * Real.exp (π * |z.im| / 2) :=
        mul_le_mul hΓ hphi (norm_nonneg _) (by positivity)
    _ = 3 * ‖(1 / 2 : ℂ) + z.im * Complex.I‖
          * (Real.exp (-(π * |z.im| / 2)) * Real.exp (π * |z.im| / 2)) := by ring
    _ = 3 * ‖(1 / 2 : ℂ) + z.im * Complex.I‖ := by rw [hE, mul_one]
    _ ≤ 3 * ‖z + 2‖ := by gcongr

lemma differentiableOn_gammaG :
    DifferentiableOn ℂ gammaG {w : ℂ | 1 / 2 ≤ w.re ∧ w.re ≤ 3 / 2} := by
  unfold gammaG
  refine DifferentiableOn.div ?_ ((differentiable_id.add_const _).differentiableOn)
    fun z hz => norm_add_two_ne_zero hz.1
  refine DifferentiableOn.mul ?_ differentiable_gammaPhi.differentiableOn
  intro z hz
  exact (Complex.differentiableAt_Gamma z fun m => by
    intro h
    have := congrArg Complex.re h
    rw [Complex.neg_re, Complex.natCast_re] at this
    linarith [hz.1, (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]).differentiableWithinAt

lemma gammaG_isBigO :
    gammaG =O[Filter.comap (fun z : ℂ => |z.im|) Filter.atTop ⊓
        Filter.principal (Complex.re ⁻¹' Ioo (1 / 2 : ℝ) (3 / 2))]
      fun z => Real.exp (π * Real.exp (1 * |z.im|)) := by
  refine Asymptotics.IsBigO.of_bound (Real.Gamma (1 / 2) + Real.Gamma (5 / 2)) ?_
  rw [Filter.eventually_inf_principal]
  refine Filter.Eventually.of_forall fun z hz => ?_
  have hz1 : 1 / 2 ≤ z.re := hz.1.le
  have hz2 : z.re ≤ 3 / 2 := hz.2.le
  have hΓ : ‖Complex.Gamma z‖ ≤ Real.Gamma (1 / 2) + Real.Gamma (5 / 2) := by
    have := norm_Gamma_le_of_re_mem' (u := z) (a := 1 / 2) (B := 3 / 2) (by norm_num) hz1 hz2
    rwa [show (3 : ℝ) / 2 + 1 = 5 / 2 by norm_num] at this
  have hG0 : 0 ≤ Real.Gamma (1 / 2) + Real.Gamma (5 / 2) := by
    have h1 : 0 < Real.Gamma (1 / 2) := Real.Gamma_pos_of_pos (by norm_num)
    have h2 : 0 < Real.Gamma (5 / 2) := Real.Gamma_pos_of_pos (by norm_num)
    linarith
  have hphi := norm_gammaPhi_le z
  have hden := norm_add_two_ge hz1
  have hgrow : Real.exp (π * |z.im| / 2) ≤ Real.exp (π * Real.exp (1 * |z.im|)) := by
    refine Real.exp_le_exp.mpr ?_
    have h1 := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (1 * |z.im|)) Real.pi_pos.le
    have h2 := mul_nonneg Real.pi_pos.le (abs_nonneg z.im)
    linarith [Real.pi_pos]
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  unfold gammaG
  rw [norm_div, norm_mul, div_le_iff₀ (by linarith)]
  calc ‖Complex.Gamma z‖ * ‖gammaPhi z‖
      ≤ (Real.Gamma (1 / 2) + Real.Gamma (5 / 2)) * Real.exp (π * |z.im| / 2) :=
        mul_le_mul hΓ hphi (norm_nonneg _) hG0
    _ ≤ (Real.Gamma (1 / 2) + Real.Gamma (5 / 2)) * Real.exp (π * Real.exp (1 * |z.im|)) :=
        mul_le_mul_of_nonneg_left hgrow hG0
    _ ≤ (Real.Gamma (1 / 2) + Real.Gamma (5 / 2)) * Real.exp (π * Real.exp (1 * |z.im|))
          * ‖z + 2‖ := by
        have hA : 0 ≤ (Real.Gamma (1 / 2) + Real.Gamma (5 / 2)) * Real.exp (π * Real.exp (1 * |z.im|)) :=
          by positivity
        nlinarith

theorem norm_gammaG_le_strip {w : ℂ} (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 3 / 2) :
    ‖gammaG w‖ ≤ 3 := by
  refine PhragmenLindelof.vertical_strip (a := 1 / 2) (b := 3 / 2) ?_ ?_ ?_ ?_ h1 h2
  · exact DifferentiableOn.diffContOnCl
      (differentiableOn_gammaG.mono closure_strip_subset)
  · refine ⟨1, ?_, π, gammaG_isBigO⟩
    rw [show (3 / 2 : ℝ) - 1 / 2 = 1 by norm_num, div_one]
    linarith [Real.pi_gt_three]
  · intro z hz
    exact norm_gammaG_le_left hz
  · intro z hz
    exact norm_gammaG_le_right hz

/-- **The sharp upper bound for `Γ` on `1/2 ≤ Re w ≤ 3/2`.** -/
theorem norm_Gamma_le_strip {w : ℂ} (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 3 / 2) :
    ‖Complex.Gamma w‖ ≤ 48 * (1 + |w.im|) * Real.exp (-(π * |w.im| / 2)) := by
  have hphi_ne : gammaPhi w ≠ 0 := gammaPhi_ne_zero h1 h2
  have hden_ne : w + 2 ≠ 0 := norm_add_two_ne_zero h1
  have hw' : Complex.Gamma w = gammaG w * (w + 2) / gammaPhi w := by
    unfold gammaG; field_simp
  have hG := norm_gammaG_le_strip h1 h2
  have hden := norm_add_two_le h1 h2
  have hphi := norm_gammaPhi_ge h1 h2
  have hphipos : 0 < ‖gammaPhi w‖ := norm_pos_iff.mpr hphi_ne
  have hE : 0 < Real.exp (π * |w.im| / 2) := Real.exp_pos _
  rw [hw', norm_div, norm_mul, div_le_iff₀ hphipos]
  calc ‖gammaG w‖ * ‖w + 2‖ ≤ 3 * (4 * (1 + |w.im|)) :=
        mul_le_mul hG hden (norm_nonneg _) (by norm_num)
    _ = 48 * (1 + |w.im|) * Real.exp (-(π * |w.im| / 2)) * (Real.exp (π * |w.im| / 2) / 4) := by
        rw [Real.exp_neg]; field_simp; try ring
    _ ≤ 48 * (1 + |w.im|) * Real.exp (-(π * |w.im| / 2)) * ‖gammaPhi w‖ := by
        gcongr

/-! #### Integer shifts -/

/-- `1/Γ(s) = s (s+1) ⋯ (s+n−1) / Γ(s+n)`, valid for every `s` (Mathlib's convention `Γ(−m) = 0`). -/
lemma inv_Gamma_eq_prod_mul (s : ℂ) (n : ℕ) :
    (Complex.Gamma s)⁻¹ = (∏ j ∈ Finset.range n, (s + j)) * (Complex.Gamma (s + n))⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (s + n)]
    push_cast
    rw [show s + ((n : ℂ) + 1) = s + n + 1 by ring]
    ring

lemma norm_add_nat_le (s : ℂ) (j : ℕ) : ‖s + j‖ ≤ ‖s‖ + j := by
  calc ‖s + j‖ ≤ ‖s‖ + ‖(j : ℂ)‖ := norm_add_le _ _
    _ = ‖s‖ + j := by rw [Complex.norm_natCast]

lemma norm_le_abs_re_add_one_mul {s : ℂ} {A : ℝ} (hA : |s.re| ≤ A) (hA0 : 0 ≤ A) :
    ‖s‖ ≤ (A + 1) * (1 + |s.im|) := by
  have h := Complex.norm_le_abs_re_add_abs_im s
  nlinarith [abs_nonneg s.im]

/-- `1/Γ` on `1/2 ≤ Re u ≤ 3/2 + m` (shift down to the fundamental strip). -/
theorem norm_inv_Gamma_le_of_re_mem_right (m : ℕ) :
    ∀ u : ℂ, 1 / 2 ≤ u.re → u.re ≤ 3 / 2 + m →
      ‖(Complex.Gamma u)⁻¹‖ ≤ 2 ^ m * 8 * Real.exp (π * |u.im| / 2) := by
  induction m with
  | zero =>
    intro u h1 h2
    simp only [Nat.cast_zero, add_zero] at h2
    simpa using norm_inv_Gamma_le_strip h1 h2
  | succ m ih =>
    intro u h1 h2
    rcases le_or_gt u.re (3 / 2) with h3 | h3
    · have := norm_inv_Gamma_le_strip h1 h3
      have hpow : (8 : ℝ) ≤ 2 ^ (m + 1) * 8 := by
        have : (1 : ℝ) ≤ 2 ^ (m + 1) := one_le_pow₀ (by norm_num)
        nlinarith
      calc ‖(Complex.Gamma u)⁻¹‖ ≤ 8 * Real.exp (π * |u.im| / 2) := this
        _ ≤ 2 ^ (m + 1) * 8 * Real.exp (π * |u.im| / 2) :=
            mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    · -- `1/Γ(u) = (1/Γ(u−1)) / (u−1)`, with `‖u − 1‖ ≥ 1/2`
      have hre : (u - 1).re = u.re - 1 := by simp
      have him : (u - 1).im = u.im := by simp
      have h1' : 1 / 2 ≤ (u - 1).re := by rw [hre]; linarith
      have h2' : (u - 1).re ≤ 3 / 2 + m := by rw [hre]; push_cast at h2; linarith
      have hih := ih (u - 1) h1' h2'
      rw [him] at hih
      have hshift := Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (u - 1)
      rw [sub_add_cancel] at hshift
      have hne : u - 1 ≠ 0 := by
        intro h
        have := congrArg Complex.re h
        rw [hre, Complex.zero_re] at this
        linarith
      have hnorm : 1 / 2 ≤ ‖u - 1‖ := by
        have := Complex.abs_re_le_norm (u - 1)
        rw [hre, abs_of_pos (by linarith)] at this
        linarith
      have hu : (Complex.Gamma u)⁻¹ = (Complex.Gamma (u - 1))⁻¹ / (u - 1) := by
        rw [hshift, mul_div_cancel_left₀ _ hne]
      rw [hu, norm_div, div_le_iff₀ (by linarith)]
      calc ‖(Complex.Gamma (u - 1))⁻¹‖ ≤ 2 ^ m * 8 * Real.exp (π * |u.im| / 2) := hih
        _ = 2 ^ (m + 1) * 8 * Real.exp (π * |u.im| / 2) * (1 / 2) := by ring
        _ ≤ 2 ^ (m + 1) * 8 * Real.exp (π * |u.im| / 2) * ‖u - 1‖ := by gcongr

/-- `Γ` on `1/2 ≤ Re u ≤ 3/2 + m` (shift down to the fundamental strip). -/
theorem norm_Gamma_le_of_re_mem_right (m : ℕ) :
    ∀ u : ℂ, 1 / 2 ≤ u.re → u.re ≤ 3 / 2 + m →
      ‖Complex.Gamma u‖ ≤ 48 * (m + 1) ^ m * (1 + |u.im|) ^ (m + 1) * Real.exp (-(π * |u.im| / 2)) := by
  induction m with
  | zero =>
    intro u h1 h2
    simp only [Nat.cast_zero, add_zero] at h2
    simpa using norm_Gamma_le_strip h1 h2
  | succ m ih =>
    intro u h1 h2
    have ht0 : 0 ≤ |u.im| := abs_nonneg _
    rcases le_or_gt u.re (3 / 2) with h3 | h3
    · have := norm_Gamma_le_strip h1 h3
      have hpow1 : (1 : ℝ) ≤ (1 + |u.im|) ^ (m + 1) := one_le_pow₀ (by linarith)
      have hpow2 : (1 : ℝ) ≤ ((m + 1 : ℕ) + 1 : ℝ) ^ (m + 1) :=
        one_le_pow₀ (by push_cast; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
      calc ‖Complex.Gamma u‖ ≤ 48 * (1 + |u.im|) * Real.exp (-(π * |u.im| / 2)) := this
        _ = 48 * 1 * ((1 + |u.im|) * 1) * Real.exp (-(π * |u.im| / 2)) := by ring
        _ ≤ 48 * ((m + 1 : ℕ) + 1 : ℝ) ^ (m + 1) * ((1 + |u.im|) * (1 + |u.im|) ^ (m + 1))
              * Real.exp (-(π * |u.im| / 2)) := by
            have hE := (Real.exp_pos (-(π * |u.im| / 2))).le
            have e1 : (48 : ℝ) * 1 ≤ 48 * ((m + 1 : ℕ) + 1 : ℝ) ^ (m + 1) := by linarith
            have e2 : (1 + |u.im|) * 1 ≤ (1 + |u.im|) * (1 + |u.im|) ^ (m + 1) :=
              mul_le_mul_of_nonneg_left hpow1 (by linarith)
            exact mul_le_mul (mul_le_mul e1 e2 (by positivity) (by positivity)) le_rfl hE
              (by positivity)
        _ = 48 * ((m + 1 : ℕ) + 1 : ℝ) ^ (m + 1) * (1 + |u.im|) ^ (m + 1 + 1)
              * Real.exp (-(π * |u.im| / 2)) := by ring
    · have hre : (u - 1).re = u.re - 1 := by simp
      have him : (u - 1).im = u.im := by simp
      have h1' : 1 / 2 ≤ (u - 1).re := by rw [hre]; linarith
      have h2' : (u - 1).re ≤ 3 / 2 + m := by rw [hre]; push_cast at h2; linarith
      have hih := ih (u - 1) h1' h2'
      rw [him] at hih
      have hne : u - 1 ≠ 0 := by
        intro h
        have := congrArg Complex.re h
        rw [hre, Complex.zero_re] at this
        linarith
      have hu : Complex.Gamma u = (u - 1) * Complex.Gamma (u - 1) := by
        rw [← Complex.Gamma_add_one _ hne, sub_add_cancel]
      -- `‖u − 1‖ ≤ (m + 2)(1 + |t|)`
      have hnorm : ‖u - 1‖ ≤ ((m + 1 : ℕ) + 1 : ℝ) * (1 + |u.im|) := by
        have h := Complex.norm_le_abs_re_add_abs_im (u - 1)
        rw [hre, him] at h
        have hre' : |u.re - 1| ≤ (m + 1 : ℕ) + 1 := by
          rw [abs_le]; push_cast at h2 ⊢; constructor <;> linarith
        have : (0 : ℝ) ≤ (m + 1 : ℕ) + 1 := by positivity
        nlinarith
      have hpow : ((m : ℝ) + 1) ^ m ≤ ((m + 1 : ℕ) + 1 : ℝ) ^ m :=
        pow_le_pow_left₀ (by positivity) (by push_cast; linarith) m
      rw [hu, norm_mul]
      calc ‖u - 1‖ * ‖Complex.Gamma (u - 1)‖
          ≤ (((m + 1 : ℕ) + 1 : ℝ) * (1 + |u.im|))
              * (48 * (m + 1) ^ m * (1 + |u.im|) ^ (m + 1) * Real.exp (-(π * |u.im| / 2))) :=
            mul_le_mul hnorm hih (norm_nonneg _) (by positivity)
        _ ≤ (((m + 1 : ℕ) + 1 : ℝ) * (1 + |u.im|))
              * (48 * ((m + 1 : ℕ) + 1 : ℝ) ^ m * (1 + |u.im|) ^ (m + 1)
                * Real.exp (-(π * |u.im| / 2))) := by gcongr
        _ = 48 * ((m + 1 : ℕ) + 1 : ℝ) ^ (m + 1) * (1 + |u.im|) ^ (m + 1 + 1)
              * Real.exp (-(π * |u.im| / 2)) := by ring

/-- **`1/Γ` on an arbitrary vertical strip `−A ≤ Re s ≤ B`**: polynomial times `e^{π|t|/2}`. -/
theorem exists_norm_inv_Gamma_le (A B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, -(A : ℝ) ≤ s.re → s.re ≤ B →
      ‖(Complex.Gamma s)⁻¹‖ ≤ C * (1 + |s.im|) ^ (A + 1) * Real.exp (π * |s.im| / 2) := by
  refine ⟨(2 * A + 2) ^ (A + 1) * 2 ^ (A + B) * 8, by positivity, fun s hA hB => ?_⟩
  have ht0 : 0 ≤ |s.im| := abs_nonneg _
  have hpow1 : (1 : ℝ) ≤ (1 + |s.im|) ^ (A + 1) := one_le_pow₀ (by linarith)
  rcases le_or_gt (1 / 2 : ℝ) s.re with h1 | h1
  · -- right of the fundamental strip: shift down only
    have h2 : s.re ≤ 3 / 2 + B := by linarith
    have := norm_inv_Gamma_le_of_re_mem_right B s h1 h2
    have hc : (2 : ℝ) ^ B * 8 ≤ (2 * A + 2) ^ (A + 1) * 2 ^ (A + B) * 8 := by
      have e1 : (1 : ℝ) ≤ (2 * A + 2) ^ (A + 1) := one_le_pow₀ (by linarith [(Nat.cast_nonneg A : (0:ℝ) ≤ A)])
      have e2 : (2 : ℝ) ^ B ≤ 2 ^ (A + B) := pow_le_pow_right₀ (by norm_num) (by omega)
      calc (2 : ℝ) ^ B * 8 ≤ 2 ^ (A + B) * 8 := by gcongr
        _ = 1 * 2 ^ (A + B) * 8 := by ring
        _ ≤ (2 * A + 2) ^ (A + 1) * 2 ^ (A + B) * 8 := by gcongr
    calc ‖(Complex.Gamma s)⁻¹‖ ≤ 2 ^ B * 8 * Real.exp (π * |s.im| / 2) := this
      _ ≤ (2 * A + 2) ^ (A + 1) * 2 ^ (A + B) * 8 * Real.exp (π * |s.im| / 2) :=
          mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
      _ = (2 * A + 2) ^ (A + 1) * 2 ^ (A + B) * 8 * 1 * Real.exp (π * |s.im| / 2) := by ring
      _ ≤ (2 * A + 2) ^ (A + 1) * 2 ^ (A + B) * 8 * (1 + |s.im|) ^ (A + 1)
            * Real.exp (π * |s.im| / 2) := by gcongr
  · -- left: shift up by `n = A + 1`
    set n : ℕ := A + 1 with hn
    have hre : (s + n).re = s.re + n := by simp
    have him : (s + n).im = s.im := by simp
    have h1' : 1 / 2 ≤ (s + n).re := by rw [hre, hn]; push_cast; linarith
    have h2' : (s + n).re ≤ 3 / 2 + A := by rw [hre, hn]; push_cast; linarith
    have hsh := norm_inv_Gamma_le_of_re_mem_right A (s + n) h1' h2'
    rw [him] at hsh
    rw [inv_Gamma_eq_prod_mul s n, norm_mul]
    -- each factor: `‖s + j‖ ≤ ‖s‖ + j ≤ (A + 1)(1 + |t|) + A ≤ (2A + 2)(1 + |t|)`
    have hfac : ∀ j ∈ Finset.range n, ‖s + j‖ ≤ (2 * A + 2) * (1 + |s.im|) := by
      intro j hj
      have hj' : (j : ℝ) ≤ A := by
        have : j < n := Finset.mem_range.mp hj
        exact_mod_cast (show j ≤ A by omega)
      have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg A
      have hs : ‖s‖ ≤ (A + 1 + 1) * (1 + |s.im|) :=
        norm_le_abs_re_add_one_mul (A := A + 1) (by rw [abs_le]; constructor <;> linarith)
          (by positivity)
      calc ‖s + j‖ ≤ ‖s‖ + j := norm_add_nat_le s j
        _ ≤ (A + 1 + 1) * (1 + |s.im|) + A := by linarith
        _ ≤ (2 * A + 2) * (1 + |s.im|) := by nlinarith [mul_nonneg hA0 (abs_nonneg s.im)]
    have hprod : ‖∏ j ∈ Finset.range n, (s + j)‖ ≤ ((2 * A + 2) * (1 + |s.im|)) ^ n := by
      rw [norm_prod]
      calc ∏ j ∈ Finset.range n, ‖s + (j : ℂ)‖
          ≤ ∏ j ∈ Finset.range n, (2 * A + 2) * (1 + |s.im|) :=
            Finset.prod_le_prod (fun j _ => norm_nonneg _) hfac
        _ = ((2 * A + 2) * (1 + |s.im|)) ^ n := by rw [Finset.prod_const, Finset.card_range]
    have hc : (2 : ℝ) ^ A ≤ 2 ^ (A + B) := pow_le_pow_right₀ (by norm_num) (by omega)
    calc ‖∏ j ∈ Finset.range n, (s + j)‖ * ‖(Complex.Gamma (s + n))⁻¹‖
        ≤ ((2 * A + 2) * (1 + |s.im|)) ^ n * (2 ^ A * 8 * Real.exp (π * |s.im| / 2)) :=
          mul_le_mul hprod hsh (norm_nonneg _) (by positivity)
      _ ≤ ((2 * A + 2) * (1 + |s.im|)) ^ n * (2 ^ (A + B) * 8 * Real.exp (π * |s.im| / 2)) := by
          gcongr
      _ = (2 * A + 2) ^ (A + 1) * 2 ^ (A + B) * 8 * (1 + |s.im|) ^ (A + 1)
            * Real.exp (π * |s.im| / 2) := by rw [hn, mul_pow]; ring

/-- **`Γ` on a right vertical strip `1/2 ≤ Re u ≤ 3/2 + m`**, with the sharp decay. -/
theorem exists_norm_Gamma_le (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℂ, 1 / 2 ≤ u.re → u.re ≤ 3 / 2 + m →
      ‖Complex.Gamma u‖ ≤ C * (1 + |u.im|) ^ (m + 1) * Real.exp (-(π * |u.im| / 2)) :=
  ⟨48 * (m + 1) ^ m, by positivity, fun u h1 h2 => norm_Gamma_le_of_re_mem_right m u h1 h2⟩

end RankinSelbergDelta.RankinSelberg
