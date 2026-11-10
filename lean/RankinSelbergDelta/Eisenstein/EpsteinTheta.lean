import Mathlib

/-!
# The lattice theta function and its functional equation

The theta function of the binary quadratic form `Q_z(m, n) = |mz + n|² / Im z` (determinant 1)
satisfies the Jacobi functional equation `θ_z(1/t) = t · θ_z(t)`. This is the analytic input from
which the continuation and pole of the Epstein zeta function follow through Mathlib's
`WeakFEPair`.
-/

namespace RankinSelbergDelta.Eisenstein

open Complex UpperHalfPlane Filter Asymptotics Topology Set Real

noncomputable section

/-- The binary quadratic form `Q_z(m,n) = |m z + n|^2 / Im z` of determinant 1. -/
def Qform (z : ℍ) (m n : ℤ) : ℝ := ‖(m : ℂ) * z + n‖ ^ 2 / z.im

/-- The lattice theta function `θ_z(t) = Σ_{(m,n)} exp(-π t Q_z(m,n))`. -/
def thetaQ (z : ℍ) (t : ℝ) : ℂ :=
  ∑' p : ℤ × ℤ, (Real.exp (-Real.pi * t * Qform z p.1 p.2) : ℂ)

/-- `Q_z(m,n) = ((n + m x)^2 + m^2 y^2)/y` (completing the square). -/
lemma Qform_eq (z : ℍ) (m n : ℤ) :
    Qform z m n = (((n : ℝ) + m * z.re) ^ 2 + (m : ℝ) ^ 2 * z.im ^ 2) / z.im := by
  rw [Qform, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.intCast_re, Complex.intCast_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring

/-- `Q_z` is bounded below by a positive multiple of `m^2 + n^2` (for summability).
    Uses the positive-definite bound `Y²(m²+n²) ≤ (X²+Y²+1)((n+mX)²+m²Y²)`. -/
lemma Qform_lower_bound (z : ℍ) :
    ∃ c > 0, ∀ m n : ℤ, c * ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) ≤ Qform z m n := by
  set X := z.re with hX
  set Y := z.im with hY
  have hY0 : 0 < Y := z.im_pos
  refine ⟨Y / (X ^ 2 + Y ^ 2 + 1), by positivity, fun m n => ?_⟩
  rw [Qform_eq, ← hX, ← hY, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hY0]
  -- goal: Y * (m²+n²) * Y ≤ ((n+mX)²+m²Y²) * (X²+Y²+1)
  have key : (Y ^ 2) * ((m : ℝ) ^ 2 + (n : ℝ) ^ 2)
      ≤ (X ^ 2 + Y ^ 2 + 1) * (((n : ℝ) + m * X) ^ 2 + (m : ℝ) ^ 2 * Y ^ 2) := by
    nlinarith [sq_nonneg ((X ^ 2 + 1) * (n : ℝ) + (X ^ 2 + Y ^ 2 + 1) * X * m),
      sq_nonneg (Y ^ 2 * (m : ℝ)), sq_nonneg X, sq_nonneg Y, hY0]
  nlinarith [key]

/-- A 1-D Gaussian sum over `ℤ` is summable (from the Jacobi theta term). -/
lemma summable_exp_neg_sq {a : ℝ} (ha : 0 < a) :
    Summable fun m : ℤ => Real.exp (-Real.pi * a * (m : ℝ) ^ 2) := by
  rw [← Complex.summable_ofReal]
  have hτ : 0 < (Complex.I * (a : ℂ)).im := by simp [ha]
  refine ((summable_jacobiTheta₂_term_iff 0 (Complex.I * (a : ℂ))).mpr hτ).congr fun m => ?_
  rw [jacobiTheta₂_term]
  rw [show (2 * π * Complex.I * (m : ℂ) * 0 + π * Complex.I * (m : ℂ) ^ 2 * (Complex.I * (a : ℂ)))
      = ((-π * a * (m : ℝ) ^ 2 : ℝ) : ℂ) by
    push_cast
    rw [show (2 * (π : ℂ) * Complex.I * (m : ℂ) * 0 + π * Complex.I * (m : ℂ) ^ 2 * (Complex.I * a))
        = π * (m : ℂ) ^ 2 * a * (Complex.I * Complex.I) by ring, Complex.I_mul_I]
    ring]
  rw [Complex.ofReal_exp]

/-- The theta sum is summable for `t > 0`. -/
lemma summable_thetaQ (z : ℍ) {t : ℝ} (ht : 0 < t) :
    Summable fun p : ℤ × ℤ => (Real.exp (-Real.pi * t * Qform z p.1 p.2) : ℂ) := by
  rw [Complex.summable_ofReal]
  obtain ⟨c, hc, hcle⟩ := Qform_lower_bound z
  have htc : 0 < t * c := mul_pos ht hc
  have hprod : Summable fun p : ℤ × ℤ =>
      Real.exp (-Real.pi * (t * c) * (p.1 : ℝ) ^ 2) * Real.exp (-Real.pi * (t * c) * (p.2 : ℝ) ^ 2) :=
    (summable_exp_neg_sq htc).mul_of_nonneg (summable_exp_neg_sq htc)
      (fun _ => Real.exp_nonneg _) (fun _ => Real.exp_nonneg _)
  refine Summable.of_nonneg_of_le (fun p => Real.exp_nonneg _) (fun p => ?_) hprod
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hb := hcle p.1 p.2
  have hpt : (0 : ℝ) ≤ Real.pi * t := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hb hpt]

/-- (0) Pointwise factorisation: the lattice term is the product of the `m`-Gaussian
`exp(-π (t y) m²)` and the shifted `n`-Gaussian `exp(-π (t/y) (n + m x)²)`, in `cexp` form. -/
lemma term_eq (z : ℍ) (t : ℝ) (m n : ℤ) :
    (Real.exp (-Real.pi * t * Qform z m n) : ℂ)
      = cexp (-(π : ℂ) * ((t * z.im : ℝ) : ℂ) * (m : ℂ) ^ 2)
        * cexp (-(π : ℂ) * ((t / z.im : ℝ) : ℂ) * ((n : ℂ) + (m : ℂ) * (z.re : ℂ)) ^ 2) := by
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  rw [Qform_eq]
  have hy : (z.im : ℂ) ≠ 0 := by exact_mod_cast z.im_pos.ne'
  push_cast
  field_simp
  ring

/-- The summand after the inner Poisson step: `exp(-π t y m²) · exp(-π (y/t) k²) · e(k m x)`. -/
def G (z : ℍ) (t : ℝ) (m k : ℤ) : ℂ :=
  cexp (-(π : ℂ) * ((t * z.im : ℝ) : ℂ) * (m : ℂ) ^ 2)
    * (cexp (-(π : ℂ) * ((z.im / t : ℝ) : ℂ) * (k : ℂ) ^ 2)
        * cexp (2 * (π : ℂ) * Complex.I * (k : ℂ) * (m : ℂ) * (z.re : ℂ)))

/-- `(k + Complex.I b)² = k² + 2 Complex.I b k - b²`: the one place `Complex.I² = -1` enters. -/
lemma sq_add_I_mul (k b : ℂ) : (k + Complex.I * b) ^ 2 = k ^ 2 + 2 * Complex.I * b * k - b ^ 2 := by
  linear_combination (b ^ 2) * Complex.I_sq

/-- (2) Inner Poisson: `Complex.tsum_exp_neg_quadratic` with `a = t/y`, `b = -a m x`. -/
lemma inner_poisson (z : ℍ) {t : ℝ} (ht : 0 < t) (m : ℤ) :
    ∑' n : ℤ, cexp (-(π : ℂ) * ((t / z.im : ℝ) : ℂ) * ((n : ℂ) + (m : ℂ) * (z.re : ℂ)) ^ 2)
      = 1 / ((t / z.im : ℝ) : ℂ) ^ (1 / 2 : ℂ)
        * ∑' k : ℤ, cexp (-(π : ℂ) * ((z.im / t : ℝ) : ℂ) * (k : ℂ) ^ 2)
            * cexp (2 * (π : ℂ) * Complex.I * (k : ℂ) * (m : ℂ) * (z.re : ℂ)) := by
  have hy0 : 0 < z.im := z.im_pos
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hy' : (z.im : ℂ) ≠ 0 := by exact_mod_cast hy0.ne'
  have ha_re : 0 < (((t / z.im : ℝ) : ℂ)).re := by rw [Complex.ofReal_re]; positivity
  have h1 : ∀ n : ℤ, cexp (-(π : ℂ) * ((t / z.im : ℝ) : ℂ) * ((n : ℂ) + (m : ℂ) * (z.re : ℂ)) ^ 2)
      = cexp (-(π : ℂ) * ((t / z.im : ℝ) : ℂ) * (m : ℂ) ^ 2 * (z.re : ℂ) ^ 2)
        * cexp (-(π : ℂ) * ((t / z.im : ℝ) : ℂ) * (n : ℂ) ^ 2
            + 2 * (π : ℂ) * (-((t / z.im : ℝ) : ℂ) * (m : ℂ) * (z.re : ℂ)) * (n : ℂ)) := by
    intro n; rw [← Complex.exp_add]; congr 1; ring
  simp_rw [h1]
  rw [tsum_mul_left, Complex.tsum_exp_neg_quadratic ha_re, ← mul_assoc,
    mul_comm (cexp _) (1 / _), mul_assoc, ← tsum_mul_left]
  refine congrArg₂ (fun a b : ℂ => a * b) (by norm_num) (tsum_congr fun k => ?_)
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [sq_add_I_mul]
  push_cast
  field_simp
  ring

/-- (3) Joint summability of `G` on `ℤ × ℤ`, by the product-Gaussian bound (`‖e(·)‖ = 1`). -/
lemma summable_G (z : ℍ) {t : ℝ} (ht : 0 < t) : Summable (Function.uncurry (G z t)) := by
  have hy0 : 0 < z.im := z.im_pos
  refine Summable.of_norm_bounded
    (g := fun p : ℤ × ℤ => Real.exp (-Real.pi * (t * z.im) * (p.1 : ℝ) ^ 2)
      * Real.exp (-Real.pi * (z.im / t) * (p.2 : ℝ) ^ 2)) ?_ ?_
  · exact (summable_exp_neg_sq (by positivity)).mul_of_nonneg (summable_exp_neg_sq (by positivity))
      (fun _ => Real.exp_nonneg _) (fun _ => Real.exp_nonneg _)
  · rintro ⟨m, k⟩
    have e1 : cexp (-(π : ℂ) * ((t * z.im : ℝ) : ℂ) * (m : ℂ) ^ 2)
        = (Real.exp (-Real.pi * (t * z.im) * (m : ℝ) ^ 2) : ℂ) := by
      rw [Complex.ofReal_exp]; congr 1; push_cast; ring
    have e2 : cexp (-(π : ℂ) * ((z.im / t : ℝ) : ℂ) * (k : ℂ) ^ 2)
        = (Real.exp (-Real.pi * (z.im / t) * (k : ℝ) ^ 2) : ℂ) := by
      rw [Complex.ofReal_exp]; congr 1; push_cast; ring
    have e3 : ‖cexp (2 * (π : ℂ) * Complex.I * (k : ℂ) * (m : ℂ) * (z.re : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      simp [Complex.mul_re, Complex.mul_im]
    simp only [Function.uncurry_apply_pair, G]
    rw [norm_mul, norm_mul, e1, e2, e3, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_nonneg _), Real.norm_of_nonneg (Real.exp_nonneg _), mul_one]

/-- (4) Outer Poisson for a fixed `k`: `Complex.tsum_exp_neg_quadratic` with `a = t y`,
`b = Complex.I k x`. -/
lemma outer_poisson (z : ℍ) {t : ℝ} (ht : 0 < t) (k : ℤ) :
    ∑' m : ℤ, G z t m k
      = cexp (-(π : ℂ) * ((z.im / t : ℝ) : ℂ) * (k : ℂ) ^ 2)
        * (1 / ((t * z.im : ℝ) : ℂ) ^ (1 / 2 : ℂ)
          * ∑' j : ℤ, cexp (-(π : ℂ) / ((t * z.im : ℝ) : ℂ)
              * ((j : ℂ) - (k : ℂ) * (z.re : ℂ)) ^ 2)) := by
  have hy0 : 0 < z.im := z.im_pos
  have ha_re : 0 < (((t * z.im : ℝ) : ℂ)).re := by rw [Complex.ofReal_re]; positivity
  have h : ∀ m : ℤ, G z t m k = cexp (-(π : ℂ) * ((z.im / t : ℝ) : ℂ) * (k : ℂ) ^ 2)
      * cexp (-(π : ℂ) * ((t * z.im : ℝ) : ℂ) * (m : ℂ) ^ 2
          + 2 * (π : ℂ) * (Complex.I * (k : ℂ) * (z.re : ℂ)) * (m : ℂ)) := by
    intro m; simp only [G]; rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  simp_rw [h]
  rw [tsum_mul_left, Complex.tsum_exp_neg_quadratic ha_re]
  congr 2
  refine tsum_congr fun j => ?_
  congr 1
  rw [show (j : ℂ) + Complex.I * (Complex.I * (k : ℂ) * (z.re : ℂ)) = (j : ℂ) - (k : ℂ) * (z.re : ℂ) by
    linear_combination ((k : ℂ) * (z.re : ℂ)) * Complex.I_sq]

/-- (5) The two `cpow` factors combine to `1/t` (through `ℝ`). -/
lemma cpow_factor {t y : ℝ} (ht : 0 < t) (hy : 0 < y) :
    1 / ((t / y : ℝ) : ℂ) ^ (1 / 2 : ℂ) * (1 / ((t * y : ℝ) : ℂ) ^ (1 / 2 : ℂ)) = 1 / (t : ℂ) := by
  have h1 : (((t / y) ^ (1 / 2 : ℝ) : ℝ) : ℂ) = ((t / y : ℝ) : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Complex.ofReal_cpow (by positivity)]; norm_num
  have h2 : (((t * y) ^ (1 / 2 : ℝ) : ℝ) : ℂ) = ((t * y : ℝ) : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Complex.ofReal_cpow (by positivity)]; norm_num
  have h3 : (t / y) ^ (1 / 2 : ℝ) * (t * y) ^ (1 / 2 : ℝ) = t := by
    rw [← Real.mul_rpow (by positivity) (by positivity),
      show t / y * (t * y) = t ^ 2 by field_simp, ← Real.sqrt_eq_rpow, Real.sqrt_sq ht.le]
  rw [← h1, ← h2, div_mul_div_comm, one_mul, ← Complex.ofReal_mul, h3]

/-- (6) Reindex `j ↦ -j` (`Equiv.neg ℤ`) and match the exponent at `1/t`. -/
lemma reindex_neg (z : ℍ) {t : ℝ} (ht : 0 < t) (k : ℤ) :
    ∑' j : ℤ, cexp (-(π : ℂ) / ((t * z.im : ℝ) : ℂ) * ((j : ℂ) - (k : ℂ) * (z.re : ℂ)) ^ 2)
      = ∑' j : ℤ, cexp (-(π : ℂ) * ((1 / t / z.im : ℝ) : ℂ)
          * ((j : ℂ) + (k : ℂ) * (z.re : ℂ)) ^ 2) := by
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hy' : (z.im : ℂ) ≠ 0 := by exact_mod_cast z.im_pos.ne'
  conv_lhs => rw [← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun j => ?_
  simp only [Equiv.neg_apply, Int.cast_neg]
  congr 1
  push_cast
  field_simp
  ring

/-- **The Jacobi functional equation** `θ_z(1/t) = t · θ_z(t)` for `t > 0`
    (determinant of `Q_z` is 1). -/
theorem thetaQ_functional_equation (z : ℍ) {t : ℝ} (ht : 0 < t) :
    thetaQ z (1 / t) = (t : ℂ) * thetaQ z t := by
  have hy0 : 0 < z.im := z.im_pos
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have ht1 : 0 < 1 / t := by positivity
  have step1 : thetaQ z t = ∑' m : ℤ, ∑' n : ℤ,
      cexp (-(π : ℂ) * ((t * z.im : ℝ) : ℂ) * (m : ℂ) ^ 2)
        * cexp (-(π : ℂ) * ((t / z.im : ℝ) : ℂ) * ((n : ℂ) + (m : ℂ) * (z.re : ℂ)) ^ 2) := by
    rw [thetaQ, (summable_thetaQ z ht).tsum_prod' (fun m => (summable_thetaQ z ht).prod_factor m)]
    exact tsum_congr fun m => tsum_congr fun n => term_eq z t m n
  have step2 : thetaQ z t
      = 1 / ((t / z.im : ℝ) : ℂ) ^ (1 / 2 : ℂ) * ∑' m : ℤ, ∑' k : ℤ, G z t m k := by
    rw [step1, ← tsum_mul_left]
    refine tsum_congr fun m => ?_
    rw [tsum_mul_left, inner_poisson z ht m]
    simp only [G]
    rw [tsum_mul_left]
    ring
  have hG := summable_G z ht
  have step3 : ∑' m : ℤ, ∑' k : ℤ, G z t m k = ∑' k : ℤ, ∑' m : ℤ, G z t m k :=
    (Summable.tsum_comm' hG (fun m => hG.prod_factor m)
      (fun k => hG.prod_symm.prod_factor k)).symm
  have step5 : thetaQ z (1 / t) = ∑' k : ℤ, ∑' j : ℤ,
      cexp (-(π : ℂ) * ((z.im / t : ℝ) : ℂ) * (k : ℂ) ^ 2)
        * cexp (-(π : ℂ) * ((1 / t / z.im : ℝ) : ℂ) * ((j : ℂ) + (k : ℂ) * (z.re : ℂ)) ^ 2) := by
    rw [thetaQ, (summable_thetaQ z ht1).tsum_prod' (fun m => (summable_thetaQ z ht1).prod_factor m)]
    refine tsum_congr fun k => tsum_congr fun j => ?_
    rw [show (Real.exp (-Real.pi * (1 / t) * Qform z (k, j).1 (k, j).2) : ℂ)
        = (Real.exp (-Real.pi * (1 / t) * Qform z k j) : ℂ) from rfl, term_eq]
    congr 2
    push_cast
    ring
  have key : thetaQ z t = 1 / (t : ℂ) * thetaQ z (1 / t) := by
    rw [step2, step3, step5, ← cpow_factor ht hy0, mul_assoc]
    congr 1
    rw [← tsum_mul_left]
    refine tsum_congr fun k => ?_
    rw [outer_poisson z ht k, reindex_neg z ht k, tsum_mul_left]
    ring
  rw [key, ← mul_assoc, mul_one_div_cancel ht', one_mul]

/-- `Q_z(0,0) = 0`. -/
lemma Qform_zero (z : ℍ) : Qform z 0 0 = 0 := by simp [Qform]

/-- `Q_z(m,n) ≥ 0`. -/
lemma Qform_nonneg (z : ℍ) (m n : ℤ) : 0 ≤ Qform z m n :=
  div_nonneg (pow_nonneg (norm_nonneg _) 2) z.im_pos.le

/-- For `p ≠ (0,0)`, `c ≤ Q_z(p)` (where `c` is the positive-definite constant). -/
lemma Qform_ge_of_ne (z : ℍ) {c : ℝ} (hc : 0 < c)
    (hcle : ∀ m n : ℤ, c * ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) ≤ Qform z m n)
    (p : ℤ × ℤ) (hp : p ≠ (0, 0)) : c ≤ Qform z p.1 p.2 := by
  have hmn : (1 : ℝ) ≤ (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 := by
    rw [ne_eq, Prod.ext_iff, not_and_or] at hp
    rcases hp with h | h
    · have hz : (1 : ℤ) ≤ p.1 ^ 2 := by nlinarith [Int.one_le_abs h, sq_abs p.1]
      have : (1 : ℝ) ≤ (p.1 : ℝ) ^ 2 := by exact_mod_cast hz
      nlinarith [sq_nonneg (p.2 : ℝ)]
    · have hz : (1 : ℤ) ≤ p.2 ^ 2 := by nlinarith [Int.one_le_abs h, sq_abs p.2]
      have : (1 : ℝ) ≤ (p.2 : ℝ) ^ 2 := by exact_mod_cast hz
      nlinarith [sq_nonneg (p.1 : ℝ)]
  nlinarith [hcle p.1 p.2, hmn, hc]

set_option maxHeartbeats 1000000 in
/-- The constant term: `θ_z(t) → 1` as `t → ∞` (the `(0,0)` term), faster than any power. -/
lemma thetaQ_sub_one_isBigO_atTop (z : ℍ) (r : ℝ) :
    (fun t : ℝ => thetaQ z t - 1) =O[atTop] fun t : ℝ => t ^ r := by
  obtain ⟨c, hc, hcle⟩ := Qform_lower_bound z
  have hπc : 0 < Real.pi * c := mul_pos Real.pi_pos hc
  have hM : Summable fun p : ℤ × ℤ => Real.exp (-Real.pi * 1 * Qform z p.1 p.2) := by
    have h := summable_thetaQ z (by norm_num : (0 : ℝ) < 1)
    rwa [Complex.summable_ofReal] at h
  have hbig : (fun t : ℝ => thetaQ z t - 1) =O[atTop]
      fun t : ℝ => Real.exp (-(Real.pi * c) * t) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨Real.exp (Real.pi * c)
        * ∑' p : ℤ × ℤ, Real.exp (-Real.pi * 1 * Qform z p.1 p.2), ?_⟩
    filter_upwards [Filter.eventually_ge_atTop 1] with t ht
    have ht0 : (0 : ℝ) < t := by linarith
    have hsumC := summable_thetaQ z ht0
    have hsumR : Summable fun p : ℤ × ℤ => Real.exp (-Real.pi * t * Qform z p.1 p.2) := by
      rwa [Complex.summable_ofReal] at hsumC
    set g : ℤ × ℤ → ℝ := fun p => if p = (0, 0) then 0
        else Real.exp (-Real.pi * t * Qform z p.1 p.2) with hg
    have hg_le : ∀ p, g p ≤ Real.exp (-Real.pi * t * Qform z p.1 p.2) := by
      intro p; simp only [hg]; split_ifs with h
      · exact Real.exp_nonneg _
      · rfl
    have hg_nonneg : ∀ p, 0 ≤ g p := by intro p; simp only [hg]; split_ifs <;> positivity
    have hg_summ : Summable g := Summable.of_nonneg_of_le hg_nonneg hg_le hsumR
    have hsplit : thetaQ z t - 1 = ∑' p : ℤ × ℤ, (if p = (0, 0) then (0 : ℂ)
        else (Real.exp (-Real.pi * t * Qform z p.1 p.2) : ℂ)) := by
      rw [thetaQ, hsumC.tsum_eq_add_tsum_ite (0, 0)]
      simp [Qform_zero]
    rw [hsplit]
    -- Step 1: the complex tail's norm is at most the real tail `∑' g`.
    have step1 : ‖∑' p : ℤ × ℤ, (if p = (0, 0) then (0 : ℂ)
        else (Real.exp (-Real.pi * t * Qform z p.1 p.2) : ℂ))‖ ≤ ∑' p, g p := by
      refine (norm_tsum_le_tsum_norm ?_).trans_eq (tsum_congr fun p => ?_)
      · refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_) hg_summ
        simp only [hg]; split_ifs with h <;>
          simp only [norm_zero, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _), le_refl]
      · simp only [hg]; split_ifs with h <;>
          simp only [norm_zero, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
    refine step1.trans ?_
    -- Step 2: dominate each term by `exp(πc)·exp(-(πc)t)·exp(-π·Q)`.
    have hptwise : ∀ p, g p ≤ Real.exp (Real.pi * c) * Real.exp (-(Real.pi * c) * t)
        * Real.exp (-Real.pi * 1 * Qform z p.1 p.2) := by
      intro p; simp only [hg]; split_ifs with h
      · positivity
      · rw [← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hQc := Qform_ge_of_ne z hc hcle p h
        nlinarith [hQc, ht, Real.pi_pos,
          mul_nonneg (by linarith : (0 : ℝ) ≤ t - 1) (by linarith : (0 : ℝ) ≤ Qform z p.1 p.2 - c)]
    have hsumRHS : Summable fun p : ℤ × ℤ => Real.exp (Real.pi * c) * Real.exp (-(Real.pi * c) * t)
        * Real.exp (-Real.pi * 1 * Qform z p.1 p.2) := hM.mul_left _
    calc ∑' p, g p
        ≤ ∑' p : ℤ × ℤ, Real.exp (Real.pi * c) * Real.exp (-(Real.pi * c) * t)
            * Real.exp (-Real.pi * 1 * Qform z p.1 p.2) :=
          Summable.tsum_le_tsum hptwise hg_summ hsumRHS
      _ = Real.exp (Real.pi * c) * Real.exp (-(Real.pi * c) * t)
            * ∑' p : ℤ × ℤ, Real.exp (-Real.pi * 1 * Qform z p.1 p.2) := tsum_mul_left
      _ = Real.exp (Real.pi * c) * (∑' p : ℤ × ℤ, Real.exp (-Real.pi * 1 * Qform z p.1 p.2))
            * ‖Real.exp (-(Real.pi * c) * t)‖ := by
          rw [Real.norm_of_nonneg (Real.exp_nonneg _)]; ring
  simpa using hbig.trans (isLittleO_exp_neg_mul_rpow_atTop hπc r).isBigO

set_option maxHeartbeats 1000000 in
/-- `θ_z` is continuous on `(0, ∞)`. -/
lemma continuousOn_thetaQ (z : ℍ) : ContinuousOn (thetaQ z) (Ioi 0) := by
  obtain ⟨c, hc, hcle⟩ := Qform_lower_bound z
  intro t₀ ht₀
  rw [mem_Ioi] at ht₀
  set a := t₀ / 2 * c with ha
  have ha0 : 0 < a := by positivity
  have hcont : ContinuousOn (thetaQ z) (Ici (t₀ / 2)) := by
    rw [show thetaQ z = fun t => ∑' p : ℤ × ℤ,
        (Real.exp (-Real.pi * t * Qform z p.1 p.2) : ℂ) from rfl]
    refine continuousOn_tsum
      (f := fun (p : ℤ × ℤ) (t : ℝ) => (Real.exp (-Real.pi * t * Qform z p.1 p.2) : ℂ))
      (u := fun p : ℤ × ℤ => Real.exp (-Real.pi * a * (p.1 : ℝ) ^ 2)
          * Real.exp (-Real.pi * a * (p.2 : ℝ) ^ 2))
      (fun p => (Complex.continuous_ofReal.comp (by fun_prop)).continuousOn)
      ((summable_exp_neg_sq ha0).mul_of_nonneg (summable_exp_neg_sq ha0)
          (fun _ => Real.exp_nonneg _) (fun _ => Real.exp_nonneg _))
      (fun p t ht => ?_)
    rw [mem_Ici] at ht
    dsimp only
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hb := hcle p.1 p.2
    have ht' : (0 : ℝ) ≤ t := by linarith
    have hpos : (0 : ℝ) ≤ Real.pi * c * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) :=
      mul_nonneg (mul_nonneg Real.pi_pos.le hc.le) (by positivity)
    have key1 := mul_le_mul_of_nonneg_left hb (mul_nonneg Real.pi_pos.le ht')
    have key2 := mul_le_mul_of_nonneg_left ht hpos
    rw [ha]
    nlinarith [key1, key2]
  exact (hcont.continuousAt (Ici_mem_nhds (by linarith))).continuousWithinAt

/-- **The Epstein-zeta FE-pair**: the self-dual `WeakFEPair (θ_z, θ_z, 1, 1)` with constant
    terms `1`, from which Mathlib's machinery delivers the continuation and the simple pole. -/
noncomputable def epsteinFEPair (z : ℍ) : WeakFEPair ℂ where
  f := thetaQ z
  g := thetaQ z
  k := 1
  ε := 1
  f₀ := 1
  g₀ := 1
  hf_int := (continuousOn_thetaQ z).locallyIntegrableOn measurableSet_Ioi
  hg_int := (continuousOn_thetaQ z).locallyIntegrableOn measurableSet_Ioi
  hk := one_pos
  hε := one_ne_zero
  h_feq := by
    intro x hx
    rw [mem_Ioi] at hx
    rw [thetaQ_functional_equation z hx, Real.rpow_one, one_mul, smul_eq_mul]
  hf_top := thetaQ_sub_one_isBigO_atTop z
  hg_top := thetaQ_sub_one_isBigO_atTop z

end

end RankinSelbergDelta.Eisenstein
