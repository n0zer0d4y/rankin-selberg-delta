import RankinSelbergDelta.RankinSelberg.ZeroCountPrimeSide

/-!
# The explicit formula on a rectangle

The argument principle applied to `(s − 1) G(s)` (`rsHent`) on a rectangle: the sum over its zeros
of `ĝ` equals a contour integral, which splits into the prime side and the archimedean side.
-/

open MeasureTheory Filter
open scoped NNReal MatrixGroups Pointwise

noncomputable section


/-! ### The truncated explicit formula of `G` on a rectangle, and prime-side positivity

The generic argument principle (namespace `RankinSelbergDelta.ArgPrinciple`) is applied to the pole-free `rsHfull = (s − 1)·G`:
for a closed rectangle in `Re s > 0` with `G ≠ 0` on its boundary and any analytic weight `h`,
`2πi ∑_ρ m_ρ h(ρ) = ∮ (G'/G)·h + 2πi h(1)` (the pole term when `1` is inside). The prime side gives
`∑_j c_j · (−Re G'/G(σ + i m_j t)) ≥ 0` for every nonnegative cosine polynomial `∑ c_j cos(m_j θ)`,
the generalised 3-4-1 inequality. -/

namespace RankinSelbergDelta.ArgPrinciple

open Complex Set Filter Topology Metric MeasureTheory
open scoped Interval

/-! ### A. The rectangle boundary integral and its algebra -/

/-- Mathlib's rectangle boundary integral (the left-hand side of
`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`), counter-clockwise. -/
noncomputable def rectBoundaryIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
    I • (∫ y : ℝ in z.im..w.im, f (re w + y * I)) -
    I • (∫ y : ℝ in z.im..w.im, f (re z + y * I))

/-- The closed rectangle with corners `z` and `w`. -/
def closedRect (z w : ℂ) : Set ℂ := [[z.re, w.re]] ×ℂ [[z.im, w.im]]

/-- The boundary of the rectangle. -/
def rectBoundary (z w : ℂ) : Set ℂ :=
  {s | s ∈ closedRect z w ∧ (s.re = z.re ∨ s.re = w.re ∨ s.im = z.im ∨ s.im = w.im)}

lemma rectBoundary_subset (z w : ℂ) : rectBoundary z w ⊆ closedRect z w := fun _ hs => hs.1

lemma bottom_mem_rectBoundary {z w : ℂ} {x : ℝ} (hx : x ∈ [[z.re, w.re]]) :
    ((x : ℂ) + z.im * I) ∈ rectBoundary z w := by
  refine ⟨?_, Or.inr (Or.inr (Or.inl (by simp)))⟩
  rw [closedRect, Complex.mem_reProdIm]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, Complex.add_im, Complex.mul_im, zero_add]
  exact ⟨hx, Set.left_mem_uIcc⟩

lemma top_mem_rectBoundary {z w : ℂ} {x : ℝ} (hx : x ∈ [[z.re, w.re]]) :
    ((x : ℂ) + w.im * I) ∈ rectBoundary z w := by
  refine ⟨?_, Or.inr (Or.inr (Or.inr (by simp)))⟩
  rw [closedRect, Complex.mem_reProdIm]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, Complex.add_im, Complex.mul_im, zero_add]
  exact ⟨hx, Set.right_mem_uIcc⟩

lemma right_mem_rectBoundary {z w : ℂ} {y : ℝ} (hy : y ∈ [[z.im, w.im]]) :
    ((re w : ℂ) + y * I) ∈ rectBoundary z w := by
  refine ⟨?_, Or.inr (Or.inl (by simp))⟩
  rw [closedRect, Complex.mem_reProdIm]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, Complex.add_im, Complex.mul_im, zero_add]
  exact ⟨Set.right_mem_uIcc, hy⟩

lemma left_mem_rectBoundary {z w : ℂ} {y : ℝ} (hy : y ∈ [[z.im, w.im]]) :
    ((re z : ℂ) + y * I) ∈ rectBoundary z w := by
  refine ⟨?_, Or.inl (by simp)⟩
  rw [closedRect, Complex.mem_reProdIm]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, Complex.add_im, Complex.mul_im, zero_add]
  exact ⟨Set.left_mem_uIcc, hy⟩

/-- Interval integrability of `F` on the four edges. -/
def EdgeIntegrable (F : ℂ → ℂ) (z w : ℂ) : Prop :=
  IntervalIntegrable (fun x : ℝ => F (x + z.im * I)) volume z.re w.re ∧
  IntervalIntegrable (fun x : ℝ => F (x + w.im * I)) volume z.re w.re ∧
  IntervalIntegrable (fun y : ℝ => F (re w + y * I)) volume z.im w.im ∧
  IntervalIntegrable (fun y : ℝ => F (re z + y * I)) volume z.im w.im

lemma EdgeIntegrable.of_continuousOn {F : ℂ → ℂ} {z w : ℂ}
    (hF : ContinuousOn F (rectBoundary z w)) : EdgeIntegrable F z w := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply ContinuousOn.intervalIntegrable
  · exact hF.comp (Continuous.continuousOn (by fun_prop)) fun x hx => bottom_mem_rectBoundary hx
  · exact hF.comp (Continuous.continuousOn (by fun_prop)) fun x hx => top_mem_rectBoundary hx
  · exact hF.comp (Continuous.continuousOn (by fun_prop)) fun y hy => right_mem_rectBoundary hy
  · exact hF.comp (Continuous.continuousOn (by fun_prop)) fun y hy => left_mem_rectBoundary hy

lemma rectBoundaryIntegral_congr {F G : ℂ → ℂ} {z w : ℂ}
    (h : ∀ s ∈ rectBoundary z w, F s = G s) :
    rectBoundaryIntegral F z w = rectBoundaryIntegral G z w := by
  unfold rectBoundaryIntegral
  beta_reduce
  rw [intervalIntegral.integral_congr (fun x hx => h _ (bottom_mem_rectBoundary hx)),
    intervalIntegral.integral_congr (fun x hx => h _ (top_mem_rectBoundary hx)),
    intervalIntegral.integral_congr (fun y hy => h _ (right_mem_rectBoundary hy)),
    intervalIntegral.integral_congr (fun y hy => h _ (left_mem_rectBoundary hy))]

lemma rectBoundaryIntegral_add {F G : ℂ → ℂ} {z w : ℂ} (hF : EdgeIntegrable F z w)
    (hG : EdgeIntegrable G z w) :
    rectBoundaryIntegral (fun s => F s + G s) z w
      = rectBoundaryIntegral F z w + rectBoundaryIntegral G z w := by
  unfold rectBoundaryIntegral
  beta_reduce
  rw [intervalIntegral.integral_add hF.1 hG.1, intervalIntegral.integral_add hF.2.1 hG.2.1,
    intervalIntegral.integral_add hF.2.2.1 hG.2.2.1, intervalIntegral.integral_add hF.2.2.2 hG.2.2.2]
  simp only [smul_eq_mul]
  ring

lemma rectBoundaryIntegral_const_mul (c : ℂ) (F : ℂ → ℂ) (z w : ℂ) :
    rectBoundaryIntegral (fun s => c * F s) z w = c * rectBoundaryIntegral F z w := by
  unfold rectBoundaryIntegral
  beta_reduce
  simp only [intervalIntegral.integral_const_mul, smul_eq_mul]
  ring

lemma rectBoundaryIntegral_sum {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) (z w : ℂ)
    (h : ∀ i ∈ s, EdgeIntegrable (F i) z w) :
    rectBoundaryIntegral (fun x => ∑ i ∈ s, F i x) z w = ∑ i ∈ s, rectBoundaryIntegral (F i) z w := by
  unfold rectBoundaryIntegral
  beta_reduce
  rw [intervalIntegral.integral_finset_sum (fun i hi => (h i hi).1),
    intervalIntegral.integral_finset_sum (fun i hi => (h i hi).2.1),
    intervalIntegral.integral_finset_sum (fun i hi => (h i hi).2.2.1),
    intervalIntegral.integral_finset_sum (fun i hi => (h i hi).2.2.2)]
  simp only [smul_eq_mul, Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib]

lemma EdgeIntegrable_sum {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) {z w : ℂ}
    (h : ∀ i ∈ s, EdgeIntegrable (F i) z w) : EdgeIntegrable (fun x => ∑ i ∈ s, F i x) z w := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := IntervalIntegrable.sum s (fun i hi => (h i hi).1); simpa [Finset.sum_fn] using this
  · have := IntervalIntegrable.sum s (fun i hi => (h i hi).2.1); simpa [Finset.sum_fn] using this
  · have := IntervalIntegrable.sum s (fun i hi => (h i hi).2.2.1); simpa [Finset.sum_fn] using this
  · have := IntervalIntegrable.sum s (fun i hi => (h i hi).2.2.2); simpa [Finset.sum_fn] using this

lemma rectBoundaryIntegral_eq_zero_of_differentiableOn {F : ℂ → ℂ} {z w : ℂ}
    (hF : DifferentiableOn ℂ F (closedRect z w)) : rectBoundaryIntegral F z w = 0 := by
  unfold rectBoundaryIntegral
  beta_reduce
  exact Complex.integral_boundary_rect_eq_zero_of_differentiableOn F z w hF

/-! ### B. The winding number of a rectangle about an interior point -/

lemma log_neg_of_im_pos {x : ℂ} (hx : 0 < x.im) :
    Complex.log (-x) = Complex.log x - Real.pi * I := by
  apply Complex.ext
  · simp only [Complex.log_re, norm_neg, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, mul_one, sub_zero]
  · simp only [Complex.log_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, add_zero]
    exact Complex.arg_neg_eq_arg_sub_pi_of_im_pos hx

lemma log_neg_of_im_neg {x : ℂ} (hx : x.im < 0) :
    Complex.log (-x) = Complex.log x + Real.pi * I := by
  apply Complex.ext
  · simp only [Complex.log_re, norm_neg, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
  · simp only [Complex.log_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, add_zero]
    exact Complex.arg_neg_eq_arg_add_pi_of_im_neg hx

/-- Horizontal edge at height `c ≠ Im u`: `∫_a^b (x + ci − u)⁻¹ dx = log(b + ci − u) − log(a + ci − u)`. -/
lemma integral_horizontal_inv_sub {u : ℂ} {a b c : ℝ} (hc : c ≠ u.im) :
    ∫ x : ℝ in a..b, ((x : ℂ) + c * I - u)⁻¹
      = Complex.log ((b : ℂ) + c * I - u) - Complex.log ((a : ℂ) + c * I - u) := by
  have hslit : ∀ x : ℝ, ((x : ℂ) + c * I - u) ∈ slitPlane := by
    intro x
    rw [Complex.mem_slitPlane_iff]
    right
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
    exact sub_ne_zero.mpr hc
  have hne : ∀ x : ℝ, ((x : ℂ) + c * I - u) ≠ 0 := fun x => Complex.slitPlane_ne_zero (hslit x)
  have hderiv : ∀ x : ℝ, HasDerivAt (fun x : ℝ => Complex.log ((x : ℂ) + c * I - u))
      (((x : ℂ) + c * I - u)⁻¹) x := by
    intro x
    have h1 : HasDerivAt (fun s : ℂ => s + c * I - u) 1 (x : ℂ) :=
      ((hasDerivAt_id _).add_const _).sub_const _
    have h2 := ((Complex.hasStrictDerivAt_log (hslit x)).hasDerivAt).comp (x : ℂ) h1
    have h3 := h2.comp_ofReal
    simpa [Function.comp, mul_one] using h3
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x) ?_
  apply ContinuousOn.intervalIntegrable
  apply Continuous.continuousOn
  exact (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + c * I - u).inv₀ hne

/-- Right edge at abscissa `b > Re u`: `∫_c^d (b + yi − u)⁻¹ dy = −i (log(b + di − u) − log(b + ci − u))`. -/
lemma integral_vertical_inv_sub_right {u : ℂ} {b c d : ℝ} (hb : u.re < b) :
    ∫ y : ℝ in c..d, ((b : ℂ) + y * I - u)⁻¹
      = -I * (Complex.log ((b : ℂ) + d * I - u) - Complex.log ((b : ℂ) + c * I - u)) := by
  have hslit : ∀ y : ℝ, ((b : ℂ) + y * I - u) ∈ slitPlane := by
    intro y
    rw [Complex.mem_slitPlane_iff]
    left
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
    linarith
  have hne : ∀ y : ℝ, ((b : ℂ) + y * I - u) ≠ 0 := fun y => Complex.slitPlane_ne_zero (hslit y)
  have hderiv : ∀ y : ℝ, HasDerivAt (fun y : ℝ => -I * Complex.log ((b : ℂ) + y * I - u))
      (((b : ℂ) + y * I - u)⁻¹) y := by
    intro y
    have h1 : HasDerivAt (fun s : ℂ => (b : ℂ) + s * I - u) I (y : ℂ) := by
      have := ((hasDerivAt_id (y : ℂ)).mul_const I).const_add (b : ℂ) |>.sub_const u
      simpa using this
    have h2 := ((Complex.hasStrictDerivAt_log (hslit y)).hasDerivAt).comp (y : ℂ) h1
    have h3 := (h2.comp_ofReal).const_mul (-I)
    convert h3 using 1
    linear_combination (((b : ℂ) + y * I - u)⁻¹) * Complex.I_mul_I
  rw [show -I * (Complex.log ((b : ℂ) + d * I - u) - Complex.log ((b : ℂ) + c * I - u))
      = (fun y : ℝ => -I * Complex.log ((b : ℂ) + y * I - u)) d
        - (fun y : ℝ => -I * Complex.log ((b : ℂ) + y * I - u)) c by beta_reduce; ring]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hderiv y) ?_
  apply ContinuousOn.intervalIntegrable
  apply Continuous.continuousOn
  exact (by fun_prop : Continuous fun y : ℝ => (b : ℂ) + y * I - u).inv₀ hne

/-- Left edge at abscissa `a < Re u`: with the primitive `−i log(u − s)` (off the slit since
`Re(u − s) > 0`): `∫_c^d (a + yi − u)⁻¹ dy = −i (log(u − a − di) − log(u − a − ci))`. -/
lemma integral_vertical_inv_sub_left {u : ℂ} {a c d : ℝ} (ha : a < u.re) :
    ∫ y : ℝ in c..d, ((a : ℂ) + y * I - u)⁻¹
      = -I * (Complex.log (u - ((a : ℂ) + d * I)) - Complex.log (u - ((a : ℂ) + c * I))) := by
  have hslit : ∀ y : ℝ, (u - ((a : ℂ) + y * I)) ∈ slitPlane := by
    intro y
    rw [Complex.mem_slitPlane_iff]
    left
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
    linarith
  have hne : ∀ y : ℝ, ((a : ℂ) + y * I - u) ≠ 0 := by
    intro y h
    have := Complex.slitPlane_ne_zero (hslit y)
    apply this
    rw [← neg_sub, h, neg_zero]
  have hderiv : ∀ y : ℝ, HasDerivAt (fun y : ℝ => -I * Complex.log (u - ((a : ℂ) + y * I)))
      (((a : ℂ) + y * I - u)⁻¹) y := by
    intro y
    have h1 : HasDerivAt (fun s : ℂ => u - ((a : ℂ) + s * I)) (-I) (y : ℂ) := by
      have := (((hasDerivAt_id (y : ℂ)).mul_const I).const_add (a : ℂ)).const_sub u
      simpa using this
    have h2 := ((Complex.hasStrictDerivAt_log (hslit y)).hasDerivAt).comp (y : ℂ) h1
    have h3 := (h2.comp_ofReal).const_mul (-I)
    convert h3 using 1
    rw [show ((a : ℂ) + y * I - u)⁻¹ = -(u - ((a : ℂ) + y * I))⁻¹ from
      (by rw [← inv_neg, neg_sub])]
    linear_combination (-(u - ((a : ℂ) + y * I))⁻¹) * Complex.I_mul_I
  rw [show -I * (Complex.log (u - ((a : ℂ) + d * I)) - Complex.log (u - ((a : ℂ) + c * I)))
      = (fun y : ℝ => -I * Complex.log (u - ((a : ℂ) + y * I))) d
        - (fun y : ℝ => -I * Complex.log (u - ((a : ℂ) + y * I))) c by beta_reduce; ring]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hderiv y) ?_
  apply ContinuousOn.intervalIntegrable
  apply Continuous.continuousOn
  exact (by fun_prop : Continuous fun y : ℝ => (a : ℂ) + y * I - u).inv₀ hne

/-- **The winding number**: for `u` in the open rectangle, `∮ (s − u)⁻¹ ds = 2πi`. -/
theorem rectBoundaryIntegral_inv_sub {z w u : ℂ}
    (hu : z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im) :
    rectBoundaryIntegral (fun s => (s - u)⁻¹) z w = 2 * Real.pi * I := by
  unfold rectBoundaryIntegral
  beta_reduce
  rw [integral_horizontal_inv_sub (ne_of_lt hu.2.2.1), integral_horizontal_inv_sub (ne_of_gt hu.2.2.2),
    integral_vertical_inv_sub_right hu.2.1, integral_vertical_inv_sub_left hu.1]
  have h1 : Complex.log (u - ((z.re : ℂ) + w.im * I))
      = Complex.log ((z.re : ℂ) + w.im * I - u) - Real.pi * I := by
    rw [← neg_sub, log_neg_of_im_pos]
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
    linarith [hu.2.2.2]
  have h2 : Complex.log (u - ((z.re : ℂ) + z.im * I))
      = Complex.log ((z.re : ℂ) + z.im * I - u) + Real.pi * I := by
    rw [← neg_sub, log_neg_of_im_neg]
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
    linarith [hu.2.2.1]
  rw [h1, h2]
  simp only [smul_eq_mul]
  have hI : ∀ X : ℂ, I * (-I * X) = X := fun X => by
    rw [← mul_assoc, mul_neg, Complex.I_mul_I]; ring
  rw [hI, hI]
  ring

/-! ### C. The Cauchy integral formula on the rectangle -/

lemma mem_closedRect_of_interior {z w u : ℂ}
    (hu : z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im) : u ∈ closedRect z w := by
  rw [closedRect, Complex.mem_reProdIm]
  exact ⟨Set.mem_uIcc.mpr (Or.inl ⟨hu.1.le, hu.2.1.le⟩),
    Set.mem_uIcc.mpr (Or.inl ⟨hu.2.2.1.le, hu.2.2.2.le⟩)⟩

lemma ne_of_mem_rectBoundary_of_interior {z w u : ℂ}
    (hu : z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im) {s : ℂ}
    (hs : s ∈ rectBoundary z w) : s ≠ u := by
  intro heq
  subst heq
  rcases hs.2 with h | h | h | h <;> linarith [hu.1, hu.2.1, hu.2.2.1, hu.2.2.2]

/-- **Cauchy's integral formula on a rectangle**: `∮ h(s)/(s − u) ds = 2πi h(u)` for `u` inside. -/
theorem rectBoundaryIntegral_div_sub {z w u : ℂ} {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h (closedRect z w))
    (hu : z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im) :
    rectBoundaryIntegral (fun s => h s / (s - u)) z w = 2 * Real.pi * I * h u := by
  set V : Set ℂ := {x | AnalyticAt ℂ h x} with hV
  have hVo : IsOpen V := isOpen_analyticAt ℂ h
  have hKV : closedRect z w ⊆ V := fun x hx => hh x hx
  have huV : V ∈ 𝓝 u := hVo.mem_nhds (hKV (mem_closedRect_of_interior hu))
  have hd : DifferentiableOn ℂ (dslope h u) V :=
    (Complex.differentiableOn_dslope huV).mpr
      (fun x hx => (hx : AnalyticAt ℂ h x).differentiableAt.differentiableWithinAt)
  have hne : ∀ s ∈ rectBoundary z w, s ≠ u := fun s hs => ne_of_mem_rectBoundary_of_interior hu hs
  have hsplit : ∀ s ∈ rectBoundary z w, h s / (s - u) = dslope h u s + h u * (s - u)⁻¹ := by
    intro s hs
    rw [dslope_of_ne h (hne s hs), slope_def_field]
    have : s - u ≠ 0 := sub_ne_zero.mpr (hne s hs)
    field_simp
    ring
  have hE1 : EdgeIntegrable (dslope h u) z w :=
    EdgeIntegrable.of_continuousOn (hd.continuousOn.mono fun s hs => hKV hs.1)
  have hE2 : EdgeIntegrable (fun s => h u * (s - u)⁻¹) z w :=
    EdgeIntegrable.of_continuousOn (continuousOn_const.mul
      ((continuousOn_id.sub continuousOn_const).inv₀ fun s hs => sub_ne_zero.mpr (hne s hs)))
  rw [rectBoundaryIntegral_congr hsplit, rectBoundaryIntegral_add hE1 hE2,
    rectBoundaryIntegral_eq_zero_of_differentiableOn (hd.mono hKV),
    rectBoundaryIntegral_const_mul, rectBoundaryIntegral_inv_sub hu]
  ring

/-- For `u` outside the closed rectangle the integrand is analytic there and the integral vanishes. -/
theorem rectBoundaryIntegral_div_sub_of_notMem {z w u : ℂ} {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h (closedRect z w)) (hu : u ∉ closedRect z w) :
    rectBoundaryIntegral (fun s => h s / (s - u)) z w = 0 := by
  apply rectBoundaryIntegral_eq_zero_of_differentiableOn
  intro s hs
  have hsu : s - u ≠ 0 := sub_ne_zero.mpr fun heq => hu (heq ▸ hs)
  exact ((hh s hs).div (analyticAt_id.sub analyticAt_const) hsu).differentiableAt.differentiableWithinAt

/-! ### D. The argument principle -/

lemma isLinearMap_re : IsLinearMap ℝ (fun z : ℂ => z.re) :=
  ⟨fun x y => Complex.add_re x y, fun c z => by simp⟩

lemma isLinearMap_im : IsLinearMap ℝ (fun z : ℂ => z.im) :=
  ⟨fun x y => Complex.add_im x y, fun c z => by simp⟩

lemma convex_closedRect (z w : ℂ) : Convex ℝ (closedRect z w) := by
  have : closedRect z w = (fun z : ℂ => z.re) ⁻¹' [[z.re, w.re]] ∩ (fun z : ℂ => z.im) ⁻¹' [[z.im, w.im]] := by
    ext s; simp [closedRect, Complex.mem_reProdIm]
  rw [this]
  exact ((convex_uIcc _ _).is_linear_preimage isLinearMap_re).inter
    ((convex_uIcc _ _).is_linear_preimage isLinearMap_im)

lemma isCompact_closedRect (z w : ℂ) : IsCompact (closedRect z w) :=
  isCompact_uIcc.reProdIm isCompact_uIcc

lemma corner_mem_rectBoundary (z w : ℂ) : z ∈ rectBoundary z w := by
  refine ⟨?_, Or.inl rfl⟩
  rw [closedRect, Complex.mem_reProdIm]
  exact ⟨Set.left_mem_uIcc, Set.left_mem_uIcc⟩

/-- A zero of `f` in the closed rectangle, with `f ≠ 0` on the boundary, is an interior point. -/
lemma interior_of_zero {z w u : ℂ} {f : ℂ → ℂ} (hzw : z.re < w.re ∧ z.im < w.im)
    (hne : ∀ s ∈ rectBoundary z w, f s ≠ 0) (huK : u ∈ closedRect z w) (hfu : f u = 0) :
    z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im := by
  have hK := huK
  rw [closedRect, Complex.mem_reProdIm, Set.uIcc_of_le hzw.1.le, Set.uIcc_of_le hzw.2.le] at hK
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hK
  by_contra hcon
  apply hne u ⟨huK, ?_⟩ hfu
  push_neg at hcon
  rcases eq_or_lt_of_le h1 with e | e
  · exact Or.inl e.symm
  rcases eq_or_lt_of_le h2 with e2 | e2
  · exact Or.inr (Or.inl e2)
  rcases eq_or_lt_of_le h3 with e3 | e3
  · exact Or.inr (Or.inr (Or.inl e3.symm))
  rcases eq_or_lt_of_le h4 with e4 | e4
  · exact Or.inr (Or.inr (Or.inr e4))
  exact absurd (hcon e e2 e3) (not_le.mpr e4)

lemma finprod_eq_finset_prod {d : ℂ → ℤ} (hd : d.support.Finite) (x : ℂ) :
    (∏ᶠ u, (· - u) ^ d u) x = ∏ u ∈ hd.toFinset, (x - u) ^ d u := by
  rw [finprod_eq_prod_of_mulSupport_subset (s := hd.toFinset)]
  · rw [Finset.prod_apply]
    rfl
  · rw [Function.FactorizedRational.mulSupport]
    intro u hu
    simpa using hu

/-- **The weighted argument principle on a rectangle.** -/
theorem rectBoundaryIntegral_logDeriv_mul (f h : ℂ → ℂ) (z w : ℂ) (hzw : z.re < w.re ∧ z.im < w.im)
    (hf : AnalyticOnNhd ℂ f (closedRect z w)) (hh : AnalyticOnNhd ℂ h (closedRect z w))
    (hne : ∀ s ∈ rectBoundary z w, f s ≠ 0) :
    rectBoundaryIntegral (fun s => logDeriv f s * h s) z w
      = 2 * Real.pi * I * ∑ᶠ u, ((MeromorphicOn.divisor f (closedRect z w)) u : ℂ) * h u := by
  classical
  set K : Set ℂ := closedRect z w with hKdef
  have hKc : IsCompact K := isCompact_closedRect z w
  -- an open convex thickening `U` of `K` on which `f` is analytic
  set Vf : Set ℂ := {x | AnalyticAt ℂ f x} with hVf
  have hVfo : IsOpen Vf := isOpen_analyticAt ℂ f
  have hKVf : K ⊆ Vf := fun x hx => hf x hx
  obtain ⟨δ, hδ, hcth⟩ := hKc.exists_cthickening_subset_open hVfo hKVf
  set U : Set ℂ := thickening δ K with hUdef
  have hUo : IsOpen U := isOpen_thickening
  have hKU : K ⊆ U := self_subset_thickening hδ K
  have hUV : U ⊆ Vf := (thickening_subset_cthickening δ K).trans hcth
  have hUconv : Convex ℝ U := (convex_closedRect z w).thickening δ
  have hfa : AnalyticOnNhd ℂ f U := fun x hx => hUV hx
  have hzK : z ∈ K := (corner_mem_rectBoundary z w).1
  have hzU : z ∈ U := hKU hzK
  have hfz : f z ≠ 0 := hne z (corner_mem_rectBoundary z w)
  -- the order of `f` is finite everywhere on `U` (identity theorem)
  have hord : ∀ u ∈ U, meromorphicOrderAt f u ≠ ⊤ := by
    intro u hu h
    rw [meromorphicOrderAt_eq_top_iff] at h
    have : EqOn f 0 U :=
      hfa.eqOn_zero_of_preconnected_of_frequently_eq_zero hUconv.isPreconnected hu h.frequently
    exact hfz (this hzU)
  -- the divisor on `U` and its finite support
  set D := MeromorphicOn.divisor f U with hDdef
  have hfm : MeromorphicOn f U := AnalyticOnNhd.meromorphicOn hfa
  have hD0 : ∀ u, 0 ≤ D u := fun u => by
    have := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfa u
    simpa using this
  have hDapply : ∀ u ∈ U, D u = (meromorphicOrderAt f u).untop₀ := fun u hu =>
    MeromorphicOn.divisor_apply hfm hu
  have hDfin : D.support.Finite := by
    have hKc' : IsCompact (cthickening δ K) := hKc.cthickening
    have hfK' : AnalyticOnNhd ℂ f (cthickening δ K) := fun x hx => hcth hx
    have hfK : MeromorphicOn f (cthickening δ K) := hfK'.meromorphicOn
    have hfin := (MeromorphicOn.divisor f (cthickening δ K)).finiteSupport hKc'
    refine hfin.subset fun u hu => ?_
    have huU : u ∈ U := D.supportWithinDomain hu
    rw [Function.mem_support] at hu ⊢
    rwa [MeromorphicOn.divisor_apply hfK (thickening_subset_cthickening δ K huU), ← hDapply u huU]
  -- the zeros of `f` in `U` are exactly the support of `D`
  have hzero : ∀ u ∈ U, (f u = 0 ↔ D u ≠ 0) := by
    intro u hu
    have hne' : meromorphicOrderAt f u ≠ ⊤ := hord u hu
    have hm := (hfa u hu).meromorphicOrderAt_eq
    have h0' : analyticOrderAt f u = 0 ↔ f u ≠ 0 := by
      rw [analyticOrderAt_eq_zero]
      exact ⟨fun h => h.resolve_left (not_not.mpr (hfa u hu)), Or.inr⟩
    rcases hn : analyticOrderAt f u with _ | n
    · exfalso; apply hne'; rw [hm, hn]; rfl
    · have hDn : D u = n := by
        rw [hDapply u hu, hm, hn]
        first | rfl | simp [WithTop.map_coe, ENat.map_coe, WithTop.untop₀_coe]
      rw [hDn]
      rw [hn] at h0'
      constructor
      · intro hfu hD
        have hn0 : n = 0 := by exact_mod_cast hD
        exact (h0'.mp (by rw [hn0]; exact Nat.cast_zero)) hfu
      · intro hD
        by_contra hfu
        have : (n : ℕ∞) = 0 := h0'.mpr hfu
        exact hD (by exact_mod_cast this)
  -- extract the zeros: `f = P • g` on `U` with `g` analytic and nonvanishing
  obtain ⟨g, hga, hg0, hfg⟩ := hfm.extract_zeros_poles (fun u => hord u u.2) hDfin
  set P : ℂ → ℂ := ∏ᶠ u, (· - u) ^ D u with hPdef
  have hPa : AnalyticOnNhd ℂ P univ := fun x _ =>
    Function.FactorizedRational.analyticAt (hD0 x)
  have hfPg : EqOn f (fun z => P z * g z) U := by
    refine AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hfa
      ((hPa.mono (subset_univ _)).mul hga) hUconv.isPreconnected hzU ?_
    have h1 : {x | f x = (P • g) x} ∪ Uᶜ ∈ 𝓝[≠] z :=
      (mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hfg) z hzU
    have h2 : U ∈ 𝓝[≠] z := nhdsWithin_le_nhds (hUo.mem_nhds hzU)
    have h4 : ∀ᶠ x in 𝓝[≠] z, f x = P x * g x := by
      filter_upwards [h1, h2] with x hx1 hx2
      rcases hx1 with hx1 | hx1
      · simpa [Pi.smul_apply, smul_eq_mul] using hx1
      · exact absurd hx2 hx1
    exact h4.frequently
  have hPeq : P = fun x => ∏ u ∈ hDfin.toFinset, (x - u) ^ D u := by
    funext x; exact finprod_eq_finset_prod hDfin x
  -- on the boundary: `logDeriv f = ∑ D u / (s − u) + logDeriv g`
  have hsplit : ∀ s ∈ rectBoundary z w, logDeriv f s * h s
      = (∑ u ∈ hDfin.toFinset, (D u : ℂ) * (h s / (s - u))) + logDeriv g s * h s := by
    intro s hs
    have hsK : s ∈ K := hs.1
    have hsU : s ∈ U := hKU hsK
    have hfs : f s ≠ 0 := hne s hs
    have hPs : P s * g s ≠ 0 := by rw [← show f s = P s * g s from hfPg hsU]; exact hfs
    have hPs' : P s ≠ 0 := left_ne_zero_of_mul hPs
    have hgs : g s ≠ 0 := right_ne_zero_of_mul hPs
    have hfev : f =ᶠ[𝓝 s] fun z => P z * g z := eventuallyEq_of_mem (hUo.mem_nhds hsU) hfPg
    have hlog : logDeriv f s = logDeriv P s + logDeriv g s := by
      rw [show logDeriv f s = logDeriv (fun z => P z * g z) s from
        (by rw [logDeriv_apply, logDeriv_apply, hfev.deriv_eq, hfev.eq_of_nhds])]
      exact logDeriv_mul s hPs' hgs (hPa s (mem_univ _)).differentiableAt
        (hga s hsU).differentiableAt
    have hne' : ∀ u ∈ hDfin.toFinset, s - u ≠ 0 := by
      intro u hu heq
      have hu' : D u ≠ 0 := by simpa using hu
      have hsu : s = u := sub_eq_zero.mp heq
      subst hsu
      exact hfs ((hzero s hsU).mpr hu')
    have hlogP : logDeriv P s = ∑ u ∈ hDfin.toFinset, (D u : ℂ) / (s - u) := by
      have hprod := logDeriv_prod (f := fun u x => (x - u) ^ D u) (x := s) (s := hDfin.toFinset)
        (fun u hu => zpow_ne_zero _ (hne' u hu))
        (fun u _ => (differentiableAt_id.sub_const u).zpow (Or.inr (hD0 u)))
      beta_reduce at hprod
      rw [hPeq, hprod]
      refine Finset.sum_congr rfl fun u hu => ?_
      have hz := logDeriv_fun_zpow (f := fun x => x - u) (x := s)
        (differentiableAt_id.sub_const u) (D u)
      beta_reduce at hz
      rw [hz, logDeriv_apply, deriv_sub_const, deriv_id'']
      ring
    rw [hlog, hlogP, add_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun u hu => ?_
    have := hne' u hu
    field_simp
  -- the per-zero integrals
  have hterm : ∀ u ∈ hDfin.toFinset,
      rectBoundaryIntegral (fun s => (D u : ℂ) * (h s / (s - u))) z w
        = (D u : ℂ) * (2 * Real.pi * I * (if u ∈ K then h u else 0)) := by
    intro u hu
    rw [rectBoundaryIntegral_const_mul]
    congr 1
    by_cases huK : u ∈ K
    · rw [if_pos huK]
      have hu' : D u ≠ 0 := by simpa using hu
      have hfu : f u = 0 := (hzero u (hKU huK)).mpr hu'
      exact rectBoundaryIntegral_div_sub hh (interior_of_zero hzw hne huK hfu)
    · rw [if_neg huK, mul_zero]
      exact rectBoundaryIntegral_div_sub_of_notMem hh huK
  have hEterm : ∀ u ∈ hDfin.toFinset, EdgeIntegrable (fun s => (D u : ℂ) * (h s / (s - u))) z w := by
    intro u hu
    have hu' : D u ≠ 0 := by simpa using hu
    have hsu : ∀ s ∈ rectBoundary z w, s - u ≠ 0 := by
      intro s hs heq
      have : s = u := sub_eq_zero.mp heq
      subst this
      exact hne s hs ((hzero s (hKU hs.1)).mpr hu')
    refine EdgeIntegrable.of_continuousOn (continuousOn_const.mul ?_)
    exact (hh.continuousOn.mono (rectBoundary_subset z w)).div
      (continuousOn_id.sub continuousOn_const) hsu
  have hEg : EdgeIntegrable (fun s => logDeriv g s * h s) z w := by
    refine EdgeIntegrable.of_continuousOn ?_
    intro s hs
    have hsU : s ∈ U := hKU hs.1
    apply ContinuousAt.continuousWithinAt
    exact ((hga s hsU).deriv.continuousAt.div (hga s hsU).continuousAt (hg0 ⟨s, hsU⟩)).mul
      (hh s hs.1).continuousAt
  have hgint : rectBoundaryIntegral (fun s => logDeriv g s * h s) z w = 0 := by
    apply rectBoundaryIntegral_eq_zero_of_differentiableOn
    intro s hs
    have hsU : s ∈ U := hKU hs
    have h1 : AnalyticAt ℂ (fun x => deriv g x / g x) s :=
      (hga s hsU).deriv.div (hga s hsU) (hg0 ⟨s, hsU⟩)
    have h2 : AnalyticAt ℂ (fun x => logDeriv g x * h x) s := by
      have : (fun x => logDeriv g x * h x) = fun x => (deriv g x / g x) * h x := by funext x; rfl
      rw [this]
      exact h1.mul (hh s hs)
    exact h2.differentiableAt.differentiableWithinAt
  rw [rectBoundaryIntegral_congr hsplit,
    rectBoundaryIntegral_add (EdgeIntegrable_sum hDfin.toFinset _ hEterm) hEg,
    rectBoundaryIntegral_sum _ _ _ _ hEterm, hgint, add_zero, Finset.sum_congr rfl hterm]
  -- identify with the divisor on `K`
  have hDK : ∀ u, ((MeromorphicOn.divisor f K) u : ℂ) * h u
      = if u ∈ K then (D u : ℂ) * h u else 0 := by
    intro u
    by_cases huK : u ∈ K
    · rw [if_pos huK, MeromorphicOn.divisor_apply (hf.meromorphicOn) huK, hDapply u (hKU huK)]
    · rw [if_neg huK]
      have : (MeromorphicOn.divisor f K) u = 0 :=
        Function.notMem_support.mp fun hs => huK ((MeromorphicOn.divisor f K).supportWithinDomain hs)
      rw [this]; simp
  have hsupp : (fun u => ((MeromorphicOn.divisor f K) u : ℂ) * h u).support ⊆ hDfin.toFinset := by
    intro u hu
    rw [Function.mem_support, hDK] at hu
    rw [Set.Finite.coe_toFinset, Function.mem_support]
    by_cases huK : u ∈ K
    · rw [if_pos huK] at hu
      intro hD
      apply hu; rw [hD]; simp
    · rw [if_neg huK] at hu; exact absurd rfl hu
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [hDK]
  split_ifs <;> ring

end RankinSelbergDelta.ArgPrinciple

namespace RankinSelbergDelta.RankinSelberg

open Complex UpperHalfPlane MeasureTheory Set Filter RankinSelbergDelta.Eisenstein RankinSelbergDelta.ArgPrinciple
open scoped Real Topology Modular

variable {F : Type*} [FunLike F ℍ ℂ] (k : ℤ)
  [cf : CuspFormClass F (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma 1)) k]

/-- `G = rsG` everywhere (the two branches of `Gfull` agree on `Re s ≥ 2`). -/
lemma Gfull_eq_rsG (f : F) (hk : 0 < k) (s : ℂ) : Gfull k f s = rsG k f s := by
  unfold Gfull
  split_ifs with h
  · rfl
  · have := rsG_eq_Gfull_of_one_lt k f hk (by linarith : 1 < s.re)
    unfold Gfull at this
    rw [if_neg h] at this
    exact this.symm

/-- `G` is analytic off `{0, 1}`. -/
lemma analyticAt_Gfull (f : F) (hk : 0 < k) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    AnalyticAt ℂ (Gfull k f) s := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  filter_upwards [eventually_ne_nhds hs0, eventually_ne_nhds hs1] with w hw0 hw1
  exact differentiableAt_Gfull k f hk hw0 hw1

/-- The pole-free function `(s − 1)·G(s)`, as a global definition. -/
noncomputable def rsHfull (f : F) (s : ℂ) : ℂ :=
  rsPre k s * ((s - 1) * rsJ k f s - ((s - 1) / s - 1) * ((∫ z in (𝒟 : Set ℍ), phi k f z : ℝ) : ℂ))

lemma rsHfull_eq (f : F) (hk : 0 < k) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    rsHfull k f s = (s - 1) * Gfull k f s := by
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  rw [Gfull_eq_rsG k f hk, rsG_eq_rsPre_mul_rsLambda]
  unfold rsLambda rsHfull
  field_simp
  ring

lemma differentiableAt_rsHfull (f : F) (hk : 0 < k) {s : ℂ} (hs : s ≠ 0) :
    DifferentiableAt ℂ (rsHfull k f) s := by
  have h1 : DifferentiableAt ℂ (fun s : ℂ => (s - 1) * rsJ k f s) s :=
    (differentiableAt_id.sub_const 1).mul (differentiable_rsJ k f hk s)
  have h2 : DifferentiableAt ℂ (fun s : ℂ => ((s - 1) / s - 1)
      * ((∫ z in (𝒟 : Set ℍ), phi k f z : ℝ) : ℂ)) s :=
    (((differentiableAt_id.sub_const 1).div differentiableAt_id hs).sub_const 1).mul_const _
  exact (differentiable_rsPre k s).mul (h1.sub h2)

lemma analyticAt_rsHfull (f : F) (hk : 0 < k) {s : ℂ} (hs : s ≠ 0) :
    AnalyticAt ℂ (rsHfull k f) s := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  filter_upwards [eventually_ne_nhds hs] with w hw
  exact differentiableAt_rsHfull k f hk hw

include cf in
lemma rsHfull_one_ne_zero (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k) :
    rsHfull k f 1 ≠ 0 := by
  have hf0 : (⇑f : ℍ → ℂ) ≠ 0 := ne_zero_of_isHeckeEigenCoeffs k f hf
  have hI₀ne : ((∫ z in (𝒟 : Set ℍ), phi k f z : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (integral_phi_pos_of_ne_zero k f hf0).ne'
  have hpre : rsPre k 1 ≠ 0 := rsPre_ne_zero k hk (by simp)
  unfold rsHfull
  simp only [sub_self, zero_mul, zero_div, zero_sub, neg_mul, one_mul, sub_neg_eq_add, zero_add]
  exact mul_ne_zero hpre hI₀ne

/-- On the boundary of a rectangle in `Re s > 0` where `G ≠ 0` and `s ≠ 1`:
`H'/H = G'/G + 1/(s − 1)`. -/
lemma logDeriv_rsHfull_eq (f : F) (hk : 0 < k) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hG : Gfull k f s ≠ 0) :
    logDeriv (rsHfull k f) s = logDeriv (Gfull k f) s + (s - 1)⁻¹ := by
  have hev : rsHfull k f =ᶠ[𝓝 s] fun t => (t - 1) * Gfull k f t := by
    filter_upwards [eventually_ne_nhds hs0, eventually_ne_nhds hs1] with t ht0 ht1
    exact rsHfull_eq k f hk ht0 ht1
  rw [show logDeriv (rsHfull k f) s = logDeriv (fun t => (t - 1) * Gfull k f t) s from
    (by rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds])]
  rw [logDeriv_mul (f := fun t => t - 1) (g := Gfull k f) s (sub_ne_zero.mpr hs1) hG
    (differentiableAt_id.sub_const 1) (differentiableAt_Gfull k f hk hs0 hs1), add_comm]
  congr 1
  rw [logDeriv_apply, deriv_sub_const, deriv_id'', one_div]

open scoped Classical in
include cf in
/-- **The truncated explicit formula on a rectangle (the contour identity with the pole term).**
For a closed rectangle `K` in `Re s > 0` on whose boundary `G ≠ 0` and `s ≠ 1`, and any `h` analytic
on a neighbourhood of `K`: `2πi ∑_ρ m_ρ h(ρ) = ∮_{∂K} (G'/G)·h + 2πi·h(1)·[1 ∈ K]`, the sum over the
zeros `ρ` of `(s − 1)G(s)` in `K` (= the zeros of `G` in `K`), with multiplicity. -/
theorem explicitFormula_Gfull_rect (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k)
    (z w : ℂ) (hzw : z.re < w.re ∧ z.im < w.im) (hz0 : 0 < z.re) (h : ℂ → ℂ)
    (hh : AnalyticOnNhd ℂ h (closedRect z w))
    (hne : ∀ s ∈ rectBoundary z w, Gfull k f s ≠ 0) (h1 : (1 : ℂ) ∉ rectBoundary z w) :
    2 * Real.pi * Complex.I * ∑ᶠ u, ((MeromorphicOn.divisor (rsHfull k f) (closedRect z w)) u : ℂ) * h u
      = rectBoundaryIntegral (fun s => logDeriv (Gfull k f) s * h s) z w
        + (if (1 : ℂ) ∈ closedRect z w then 2 * Real.pi * Complex.I * h 1 else 0) := by
  have hre : ∀ s ∈ closedRect z w, z.re ≤ s.re := by
    intro s hs
    rw [closedRect, Complex.mem_reProdIm, Set.uIcc_of_le hzw.1.le] at hs
    exact hs.1.1
  have hs0 : ∀ s ∈ closedRect z w, s ≠ 0 := by
    intro s hs heq
    have := hre s hs
    rw [heq, Complex.zero_re] at this
    linarith
  have hfa : AnalyticOnNhd ℂ (rsHfull k f) (closedRect z w) := fun s hs =>
    analyticAt_rsHfull k f hk (hs0 s hs)
  have hneH : ∀ s ∈ rectBoundary z w, rsHfull k f s ≠ 0 := by
    intro s hs
    have hs1 : s ≠ 1 := fun heq => h1 (heq ▸ hs)
    rw [rsHfull_eq k f hk (hs0 s hs.1) hs1]
    exact mul_ne_zero (sub_ne_zero.mpr hs1) (hne s hs)
  rw [← rectBoundaryIntegral_logDeriv_mul (rsHfull k f) h z w hzw hfa hh hneH]
  -- split the integrand on the boundary
  have hsplit : ∀ s ∈ rectBoundary z w, logDeriv (rsHfull k f) s * h s
      = logDeriv (Gfull k f) s * h s + h s / (s - 1) := by
    intro s hs
    have hs1 : s ≠ 1 := fun heq => h1 (heq ▸ hs)
    rw [logDeriv_rsHfull_eq k f hk (hs0 s hs.1) hs1 (hne s hs)]
    rw [div_eq_mul_inv]; ring
  have hE1 : EdgeIntegrable (fun s => logDeriv (Gfull k f) s * h s) z w := by
    refine EdgeIntegrable.of_continuousOn ?_
    intro s hs
    have hs1 : s ≠ 1 := fun heq => h1 (heq ▸ hs)
    have hG := analyticAt_Gfull k f hk (hs0 s hs.1) hs1
    apply ContinuousAt.continuousWithinAt
    exact (hG.deriv.continuousAt.div hG.continuousAt (hne s hs)).mul (hh s hs.1).continuousAt
  have hE2 : EdgeIntegrable (fun s => h s / (s - 1)) z w := by
    refine EdgeIntegrable.of_continuousOn ?_
    refine (hh.continuousOn.mono (rectBoundary_subset z w)).div
      (continuousOn_id.sub continuousOn_const) ?_
    intro s hs
    exact sub_ne_zero.mpr fun heq => h1 (heq ▸ hs)
  rw [rectBoundaryIntegral_congr hsplit, rectBoundaryIntegral_add hE1 hE2]
  congr 1
  by_cases hK : (1 : ℂ) ∈ closedRect z w
  · rw [if_pos hK]
    -- `1` is an interior point
    have hint : z.re < (1 : ℂ).re ∧ (1 : ℂ).re < w.re ∧ z.im < (1 : ℂ).im ∧ (1 : ℂ).im < w.im := by
      have hK' := hK
      rw [closedRect, Complex.mem_reProdIm, Set.uIcc_of_le hzw.1.le, Set.uIcc_of_le hzw.2.le] at hK'
      obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ := hK'
      refine ⟨lt_of_le_of_ne a1 ?_, lt_of_le_of_ne a2 ?_, lt_of_le_of_ne a3 ?_, lt_of_le_of_ne a4 ?_⟩
      · exact fun e => h1 ⟨hK, Or.inl e.symm⟩
      · exact fun e => h1 ⟨hK, Or.inr (Or.inl e)⟩
      · exact fun e => h1 ⟨hK, Or.inr (Or.inr (Or.inl e.symm))⟩
      · exact fun e => h1 ⟨hK, Or.inr (Or.inr (Or.inr e))⟩
    exact rectBoundaryIntegral_div_sub hh hint
  · rw [if_neg hK]
    exact rectBoundaryIntegral_div_sub_of_notMem hh hK

include cf in
/-- **Prime-side positivity (the generalised 3-4-1 inequality).** For a nonnegative cosine
polynomial `K(θ) = ∑_j c_j cos(m_j θ)` and `σ > 1`: `∑_j c_j · (−Re G'/G(σ + i m_j t)) ≥ 0`,
because `−G'/G(σ + i m t) = ∑_n Λ_G(n) n^{−σ} e^{−i m t log n}` with `Λ_G ≥ 0`. -/
theorem cosinePositivity_logDeriv_Gfull (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k)
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (m : ι → ℕ)
    (hK : ∀ θ : ℝ, 0 ≤ ∑ j ∈ s, c j * Real.cos (m j * θ)) {σ t : ℝ} (hσ : 1 < σ) :
    0 ≤ ∑ j ∈ s, c j * (-(logDeriv (Gfull k f) ((σ : ℂ) + (m j : ℂ) * t * Complex.I)).re) := by
  set Λ := rsVonMangoldt (rsCoeff f) k with hΛdef
  have hΛ : ∀ n, 0 ≤ Λ n := rsVonMangoldt_nonneg _ _
  set ε : ℝ := σ - 1 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hmaj : Summable fun n => (2 / ε) * ‖dlvpTerm Λ ((1 + ε / 2 : ℝ) : ℂ) n‖ :=
    (summable_norm_iff.mpr (summable_dlvpTerm_rs k f hk hf (s := ((1 + ε / 2 : ℝ) : ℂ))
      (by simp only [Complex.ofReal_re]; linarith))).mul_left _
  -- the point `σ + i m t` has real part `σ = 1 + ε`
  have hpt_re : ∀ j, ((σ : ℂ) + (m j : ℂ) * t * Complex.I).re = σ := by
    intro j
    simp [Complex.add_re, Complex.mul_re, Complex.mul_im]
  have hpt_im : ∀ j, ((σ : ℂ) + (m j : ℂ) * t * Complex.I).im = m j * t := by
    intro j
    simp [Complex.add_im, Complex.mul_re, Complex.mul_im]
  have hsum : ∀ j, Summable fun n => vmTerm Λ ((σ : ℂ) + (m j : ℂ) * t * Complex.I) n := fun j =>
    Summable.of_norm_bounded hmaj
      (fun n => norm_vmTerm_le_majorant Λ hΛ hεpos (by rw [hpt_re]; linarith) n)
  have hsumre : ∀ j, Summable fun n => (vmTerm Λ ((σ : ℂ) + (m j : ℂ) * t * Complex.I) n).re := fun j =>
    Summable.of_norm_bounded hmaj (fun n => by
      rw [Real.norm_eq_abs]
      exact (Complex.abs_re_le_norm _).trans
        (norm_vmTerm_le_majorant Λ hΛ hεpos (by rw [hpt_re]; linarith) n))
  -- the real part of each term
  have hre : ∀ j n, (vmTerm Λ ((σ : ℂ) + (m j : ℂ) * t * Complex.I) n).re
      = if 2 ≤ n then Λ n * Real.exp (-(σ * Real.log n)) * Real.cos (m j * (t * Real.log n))
        else 0 := by
    intro j n
    unfold vmTerm
    split_ifs with hn
    · rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.exp_re]
      have h1 : (-(((σ : ℂ) + (m j : ℂ) * t * Complex.I) * (Real.log n : ℂ))).re = -(σ * Real.log n) := by
        rw [Complex.neg_re, Complex.mul_re, hpt_re, hpt_im, Complex.ofReal_re, Complex.ofReal_im,
          mul_zero, sub_zero]
      have h2 : (-(((σ : ℂ) + (m j : ℂ) * t * Complex.I) * (Real.log n : ℂ))).im = -(m j * t * Real.log n) := by
        rw [Complex.neg_im, Complex.mul_im, hpt_re, hpt_im, Complex.ofReal_re, Complex.ofReal_im,
          mul_zero, zero_add]
      rw [h1, h2, Real.cos_neg, mul_assoc, mul_assoc]
    · simp
  -- rewrite each term through the prime side
  have hterm : ∀ j ∈ s, c j * (-(logDeriv (Gfull k f) ((σ : ℂ) + (m j : ℂ) * t * Complex.I)).re)
      = ∑' n, c j * (vmTerm Λ ((σ : ℂ) + (m j : ℂ) * t * Complex.I) n).re := by
    intro j _
    rw [logDeriv_Gfull_eq_neg_tsum k f hk hf (by rw [hpt_re]; exact hσ), Complex.neg_re, neg_neg,
      Complex.re_tsum (hsum j), tsum_mul_left]
  rw [Finset.sum_congr rfl hterm,
    ← (hasSum_sum (fun j _ => ((hsumre j).mul_left (c j)).hasSum)).tsum_eq]
  apply tsum_nonneg
  intro n
  rw [Finset.sum_congr rfl fun j _ => by rw [hre j n]]
  by_cases hn : 2 ≤ n
  · simp only [if_pos hn]
    have : ∑ j ∈ s, c j * (Λ n * Real.exp (-(σ * Real.log n)) * Real.cos (m j * (t * Real.log n)))
        = Λ n * Real.exp (-(σ * Real.log n)) * ∑ j ∈ s, c j * Real.cos (m j * (t * Real.log n)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [this]
    exact mul_nonneg (mul_nonneg (hΛ n) (Real.exp_pos _).le) (hK (t * Real.log n))
  · simp only [if_neg hn, mul_zero, Finset.sum_const_zero, le_refl]

end RankinSelbergDelta.RankinSelberg
