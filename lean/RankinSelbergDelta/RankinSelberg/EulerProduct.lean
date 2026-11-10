import RankinSelbergDelta.RankinSelberg.SimplePole
import RankinSelbergDelta.RankinSelberg.Bridge

/-!
# The Euler product of the Rankin–Selberg square

The Satake parameters of a Hecke eigenform, Rankin's local identity, the logarithmic coefficients
`Λ_G(p^m) = |α_p^m + β_p^m|² log p ≥ 0` (`rsVonMangoldt_nonneg`), the Euler product of
`G(s) = ζ(2s) D(s + k − 1)`, and its nonvanishing on `Re s = 1` (`rs_square_ne_zero`).
-/

open MeasureTheory Filter
open scoped NNReal MatrixGroups Pointwise

noncomputable section


/-! ## The Rankin–Selberg square — Satake parameters, Rankin's local identity, the
Euler-product bridge, and `rs_square_ne_zero` -/

namespace RankinSelbergDelta.RankinSelberg

open Complex UpperHalfPlane MeasureTheory Set RankinSelbergDelta.Eisenstein Filter Topology Asymptotics
open scoped ENNReal Modular NNReal

noncomputable section

/-! ### Satake parameters, the Hecke sequence, Rankin's local identity -/

/-- The normalised Hecke eigenvalue `ã(p) = a(p) / p^{(k-1)/2}`. -/
def heckeNorm (a : ℕ → ℂ) (k : ℤ) (p : ℕ) : ℂ := a p / (p : ℂ) ^ (((k : ℂ) - 1) / 2)

/-- `δ = (ã² − 4)^{1/2}`. -/
def satakeDisc (a : ℕ → ℂ) (k : ℤ) (p : ℕ) : ℂ :=
  (heckeNorm a k p ^ 2 - 4) ^ (((2 : ℕ) : ℂ)⁻¹)

/-- The Satake parameters `α, β = (ã ± δ)/2`, with `α + β = ã` and `αβ = 1`. -/
def satakeα (a : ℕ → ℂ) (k : ℤ) (p : ℕ) : ℂ := (heckeNorm a k p + satakeDisc a k p) / 2
def satakeβ (a : ℕ → ℂ) (k : ℤ) (p : ℕ) : ℂ := (heckeNorm a k p - satakeDisc a k p) / 2

lemma satakeDisc_sq (a : ℕ → ℂ) (k : ℤ) (p : ℕ) :
    satakeDisc a k p ^ 2 = heckeNorm a k p ^ 2 - 4 :=
  Complex.cpow_nat_inv_pow _ two_ne_zero

lemma satake_add (a : ℕ → ℂ) (k : ℤ) (p : ℕ) :
    satakeα a k p + satakeβ a k p = heckeNorm a k p := by
  unfold satakeα satakeβ; ring

lemma satake_mul (a : ℕ → ℂ) (k : ℤ) (p : ℕ) : satakeα a k p * satakeβ a k p = 1 := by
  unfold satakeα satakeβ
  have h := satakeDisc_sq a k p
  linear_combination (-1 / 4 : ℂ) * h

/-- The normalised prime-power coefficients: `h_0 = 1, h_1 = x, h_{e+2} = x h_{e+1} − h_e`. -/
def heckeSeq (x : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => x
  | (e + 2) => x * heckeSeq x (e + 1) - heckeSeq x e

@[simp] lemma heckeSeq_zero (x : ℂ) : heckeSeq x 0 = 1 := rfl
@[simp] lemma heckeSeq_one (x : ℂ) : heckeSeq x 1 = x := rfl
lemma heckeSeq_add_two (x : ℂ) (e : ℕ) :
    heckeSeq x (e + 2) = x * heckeSeq x (e + 1) - heckeSeq x e := rfl

lemma conj_heckeSeq (x : ℂ) (e : ℕ) :
    (starRingEnd ℂ) (heckeSeq x e) = heckeSeq ((starRingEnd ℂ) x) e := by
  induction e using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more e ih1 ih2 => rw [heckeSeq_add_two, heckeSeq_add_two, map_sub, map_mul, ih1, ih2]

/-- `a(p^e) = q^e · h_e(ã)` with `q = p^{(k-1)/2}`, from the Hecke recursion. -/
lemma hecke_coeff_pow {a : ℕ → ℂ} {k : ℤ} (hf : IsHeckeEigenCoeffs a k) {p : ℕ} (hp : p.Prime)
    (e : ℕ) :
    a (p ^ e) = ((p : ℂ) ^ (((k : ℂ) - 1) / 2)) ^ e * heckeSeq (heckeNorm a k p) e := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hq0 : (p : ℂ) ^ (((k : ℂ) - 1) / 2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]; left; exact hp0
  have hq2 : ((p : ℂ) ^ (((k : ℂ) - 1) / 2)) ^ 2 = (p : ℂ) ^ (k - 1) := by
    rw [← Complex.cpow_nat_mul, show ((2 : ℕ) : ℂ) * (((k : ℂ) - 1) / 2) = ((k - 1 : ℤ) : ℂ) by
      push_cast; ring, Complex.cpow_intCast]
  have hap : a p = (p : ℂ) ^ (((k : ℂ) - 1) / 2) * heckeNorm a k p := by
    unfold heckeNorm; field_simp
  induction e using Nat.twoStepInduction with
  | zero => simp [hf.one]
  | one => simp only [pow_one, heckeSeq_one]; exact hap
  | more e ih1 ih2 =>
    rw [hf.recursion p e hp, ih1, ih2, heckeSeq_add_two, ← hq2, hap]
    ring

/-- `u_e = h_e(x) h_e(y)` satisfies the order-4 recurrence with characteristic polynomial
`1 − xyY + (x²+y²−2)Y² − xyY³ + Y⁴`. -/
lemma heckeSq_rec (x y : ℂ) (e : ℕ) :
    heckeSeq x (e + 4) * heckeSeq y (e + 4)
      = x * y * (heckeSeq x (e + 3) * heckeSeq y (e + 3))
        - (x ^ 2 + y ^ 2 - 2) * (heckeSeq x (e + 2) * heckeSeq y (e + 2))
        + x * y * (heckeSeq x (e + 1) * heckeSeq y (e + 1))
        - heckeSeq x e * heckeSeq y e := by
  have h4 : ∀ z : ℂ, heckeSeq z (e + 4) = z * heckeSeq z (e + 3) - heckeSeq z (e + 2) :=
    fun z => heckeSeq_add_two z (e + 2)
  have h3 : ∀ z : ℂ, heckeSeq z (e + 3) = z * heckeSeq z (e + 2) - heckeSeq z (e + 1) :=
    fun z => heckeSeq_add_two z (e + 1)
  have h2 : ∀ z : ℂ, heckeSeq z (e + 2) = z * heckeSeq z (e + 1) - heckeSeq z e :=
    fun z => heckeSeq_add_two z e
  rw [h4 x, h4 y, h3 x, h3 y, h2 x, h2 y]
  ring

/-- `u_e = h_e(x) h_e(y)`. -/
def heckeU (x y : ℂ) (e : ℕ) : ℂ := heckeSeq x e * heckeSeq y e

/-- `shiftSeq u j e = u (e − j)` for `e ≥ j`, else `0`. -/
def shiftSeq (u : ℕ → ℂ) (j e : ℕ) : ℂ := if j ≤ e then u (e - j) else 0

lemma hasSum_shiftSeq {u : ℕ → ℂ} {Y S : ℂ} (hu : HasSum (fun e => u e * Y ^ e) S) (j : ℕ) :
    HasSum (fun e => shiftSeq u j e * Y ^ e) (Y ^ j * S) := by
  refine (hasSum_nat_add_iff' j).mp ?_
  have h0 : ∑ i ∈ Finset.range j, shiftSeq u j i * Y ^ i = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Finset.mem_range] at hi
    simp [shiftSeq, not_le.mpr hi]
  rw [h0, sub_zero]
  have heq : (fun n => shiftSeq u j (n + j) * Y ^ (n + j)) = fun n => Y ^ j * (u n * Y ^ n) := by
    funext n
    simp only [shiftSeq, le_add_iff_nonneg_left, zero_le, if_true, Nat.add_sub_cancel, pow_add]
    ring
  rw [heq]
  exact hu.mul_left (Y ^ j)

/-- The numerator sequence `v_e = u_e − xy u_{e−1} + (x²+y²−2) u_{e−2} − xy u_{e−3} + u_{e−4}`. -/
def heckeNum (x y : ℂ) (e : ℕ) : ℂ :=
  heckeU x y e - x * y * shiftSeq (heckeU x y) 1 e + (x ^ 2 + y ^ 2 - 2) * shiftSeq (heckeU x y) 2 e
    - x * y * shiftSeq (heckeU x y) 3 e + shiftSeq (heckeU x y) 4 e

lemma heckeNum_eq_zero (x y : ℂ) {e : ℕ} (he : 4 ≤ e) : heckeNum x y e = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, e = m + 4 := ⟨e - 4, by omega⟩
  simp only [heckeNum, heckeU, shiftSeq, show 1 ≤ m + 4 by omega, show 2 ≤ m + 4 by omega,
    show 3 ≤ m + 4 by omega, show 4 ≤ m + 4 by omega, if_true, show m + 4 - 1 = m + 3 by omega,
    show m + 4 - 2 = m + 2 by omega, show m + 4 - 3 = m + 1 by omega, show m + 4 - 4 = m by omega]
  rw [heckeSq_rec]
  ring

lemma heckeNum_values (x y : ℂ) :
    heckeNum x y 0 = 1 ∧ heckeNum x y 1 = 0 ∧ heckeNum x y 2 = -1 ∧ heckeNum x y 3 = 0 := by
  have h2 : ∀ z : ℂ, heckeSeq z 2 = z * z - 1 := fun z => by
    rw [heckeSeq_add_two, heckeSeq_one, heckeSeq_zero]
  have h3 : ∀ z : ℂ, heckeSeq z 3 = z * (z * z - 1) - z := fun z => by
    rw [heckeSeq_add_two, h2, heckeSeq_one]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [heckeNum, heckeU, shiftSeq] <;>
    norm_num [h2, h3] <;>
    ring

/-- **Rankin's local identity (generating-function form)**: `(Σ_e u_e Y^e) · P(Y) = 1 − Y²`. -/
theorem heckeSq_genfun (x y Y : ℂ) (hu : Summable fun e => heckeU x y e * Y ^ e) :
    (∑' e, heckeU x y e * Y ^ e)
      * (1 - x * y * Y + (x ^ 2 + y ^ 2 - 2) * Y ^ 2 - x * y * Y ^ 3 + Y ^ 4) = 1 - Y ^ 2 := by
  have h0 := hu.hasSum
  have hj : ∀ j, HasSum (fun e => shiftSeq (heckeU x y) j e * Y ^ e)
      (Y ^ j * ∑' e, heckeU x y e * Y ^ e) := fun j => hasSum_shiftSeq h0 j
  have hv : HasSum (fun e => heckeNum x y e * Y ^ e)
      ((∑' e, heckeU x y e * Y ^ e) - x * y * (Y ^ 1 * ∑' e, heckeU x y e * Y ^ e)
        + (x ^ 2 + y ^ 2 - 2) * (Y ^ 2 * ∑' e, heckeU x y e * Y ^ e)
        - x * y * (Y ^ 3 * ∑' e, heckeU x y e * Y ^ e) + Y ^ 4 * ∑' e, heckeU x y e * Y ^ e) := by
    have := (((h0.sub ((hj 1).mul_left (x * y))).add ((hj 2).mul_left (x ^ 2 + y ^ 2 - 2))).sub
      ((hj 3).mul_left (x * y))).add (hj 4)
    have heq : (fun e => heckeNum x y e * Y ^ e)
        = fun e => heckeU x y e * Y ^ e - x * y * (shiftSeq (heckeU x y) 1 e * Y ^ e)
          + (x ^ 2 + y ^ 2 - 2) * (shiftSeq (heckeU x y) 2 e * Y ^ e)
          - x * y * (shiftSeq (heckeU x y) 3 e * Y ^ e) + shiftSeq (heckeU x y) 4 e * Y ^ e := by
      funext e
      simp only [heckeNum]
      ring
    rw [heq]
    exact this
  have hfin : HasSum (fun e => heckeNum x y e * Y ^ e)
      (∑ e ∈ Finset.range 4, heckeNum x y e * Y ^ e) :=
    hasSum_sum_of_ne_finset_zero fun e he => by
      rw [Finset.mem_range, not_lt] at he
      rw [heckeNum_eq_zero x y he, zero_mul]
  have key := hv.unique hfin
  obtain ⟨v0, v1, v2, v3⟩ := heckeNum_values x y
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    v0, v1, v2, v3] at key
  linear_combination key

/-- `P(Y) = ∏_{i,i'} (1 − α_i ᾱ_{i'} Y)` for `αβ = 1`, `x = α + β`, `y = ᾱ + β̄`. -/
lemma heckeP_eq {α β : ℂ} (hαβ : α * β = 1) (Y : ℂ) :
    1 - (α + β) * ((starRingEnd ℂ) α + (starRingEnd ℂ) β) * Y
      + ((α + β) ^ 2 + ((starRingEnd ℂ) α + (starRingEnd ℂ) β) ^ 2 - 2) * Y ^ 2
      - (α + β) * ((starRingEnd ℂ) α + (starRingEnd ℂ) β) * Y ^ 3 + Y ^ 4
      = (1 - α * (starRingEnd ℂ) α * Y) * (1 - α * (starRingEnd ℂ) β * Y)
        * (1 - β * (starRingEnd ℂ) α * Y) * (1 - β * (starRingEnd ℂ) β * Y) := by
  have hα : α ≠ 0 := left_ne_zero_of_mul_eq_one hαβ
  have hβ : β = α⁻¹ := eq_inv_of_mul_eq_one_right hαβ
  have hcα : (starRingEnd ℂ) α ≠ 0 := (map_ne_zero _).mpr hα
  have hcβ : (starRingEnd ℂ) β = ((starRingEnd ℂ) α)⁻¹ := by rw [hβ, map_inv₀]
  rw [hcβ, hβ]
  field_simp
  ring

/-- `(α − β) h_e(α + β) = α^(e+1) − β^(e+1)` when `αβ = 1`. -/
lemma heckeSeq_closed (α β : ℂ) (hαβ : α * β = 1) (e : ℕ) :
    (α - β) * heckeSeq (α + β) e = α ^ (e + 1) - β ^ (e + 1) := by
  induction e using Nat.twoStepInduction with
  | zero => simp
  | one => simp only [heckeSeq_one]; ring
  | more e ih1 ih2 =>
    rw [heckeSeq_add_two]
    linear_combination (α + β) * ih2 - ih1 + (α ^ (e + 1) - β ^ (e + 1)) * hαβ

/-- **The Satake size bound.** If `Σ_e ‖h_e‖² Y₀^e` converges (`Y₀ > 0`) and `‖α‖ > 1`, then
`‖α‖² Y₀ < 1`. -/
lemma satake_sq_mul_lt_one {α β : ℂ} (hαβ : α * β = 1) (hα : 1 < ‖α‖) {Y₀ : ℝ} (hY : 0 < Y₀)
    (hs : Summable fun e => ‖heckeSeq (α + β) e‖ ^ 2 * Y₀ ^ e) : ‖α‖ ^ 2 * Y₀ < 1 := by
  by_contra hcon
  push_neg at hcon
  have hα0 : α ≠ 0 := left_ne_zero_of_mul_eq_one hαβ
  have hβ : ‖β‖ = ‖α‖⁻¹ := by
    have h := congrArg norm hαβ
    rw [norm_mul, norm_one] at h
    exact eq_inv_of_mul_eq_one_right h
  have hβ1 : ‖β‖ < 1 := by rw [hβ]; exact inv_lt_one_of_one_lt₀ hα
  set r := β / α with hr
  have hr1 : ‖r‖ < 1 := by
    rw [hr, norm_div]
    exact (div_lt_one (by linarith)).mpr (by linarith)
  have hr0 : 0 ≤ 1 - ‖r‖ := by linarith
  have hne : α - β ≠ 0 := by
    intro h
    have : ‖α‖ = ‖β‖ := by rw [sub_eq_zero.mp h]
    linarith
  have hnepos : 0 < ‖α - β‖ := norm_pos_iff.mpr hne
  have hlow : ∀ e, ‖α‖ ^ (e + 1) * (1 - ‖r‖) / ‖α - β‖ ≤ ‖heckeSeq (α + β) e‖ := by
    intro e
    have hcl := heckeSeq_closed α β hαβ e
    have hfac : α ^ (e + 1) - β ^ (e + 1) = α ^ (e + 1) * (1 - r ^ (e + 1)) := by
      rw [hr, div_pow]
      field_simp
    have h1 : ‖(α - β) * heckeSeq (α + β) e‖ = ‖α‖ ^ (e + 1) * ‖1 - r ^ (e + 1)‖ := by
      rw [hcl, hfac, norm_mul, norm_pow]
    have h2 : 1 - ‖r‖ ≤ ‖1 - r ^ (e + 1)‖ := by
      calc 1 - ‖r‖ ≤ 1 - ‖r‖ ^ (e + 1) := by
            have : ‖r‖ ^ (e + 1) ≤ ‖r‖ := pow_le_of_le_one (norm_nonneg _) hr1.le (by omega)
            linarith
        _ = ‖(1 : ℂ)‖ - ‖r ^ (e + 1)‖ := by rw [norm_one, norm_pow]
        _ ≤ ‖1 - r ^ (e + 1)‖ := norm_sub_norm_le _ _
    rw [norm_mul] at h1
    rw [div_le_iff₀ hnepos, mul_comm _ ‖α - β‖, h1]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  set C : ℝ := (‖α‖ * (1 - ‖r‖) / ‖α - β‖) ^ 2 with hC
  have hCpos : 0 < C := by
    have : 0 < 1 - ‖r‖ := by linarith
    rw [hC]; positivity
  have hterm : ∀ e, C ≤ ‖heckeSeq (α + β) e‖ ^ 2 * Y₀ ^ e := by
    intro e
    have h := hlow e
    have hge : C ≤ (‖α‖ ^ (e + 1) * (1 - ‖r‖) / ‖α - β‖) ^ 2 * Y₀ ^ e := by
      have : (‖α‖ ^ (e + 1) * (1 - ‖r‖) / ‖α - β‖) ^ 2 * Y₀ ^ e
          = C * (‖α‖ ^ 2 * Y₀) ^ e := by rw [hC]; ring
      rw [this]
      exact le_mul_of_one_le_right hCpos.le (one_le_pow₀ hcon)
    refine hge.trans ?_
    refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ?_ h 2) (by positivity)
    exact div_nonneg (mul_nonneg (by positivity) hr0) (norm_nonneg _)
  have htend := hs.tendsto_atTop_zero
  obtain ⟨e, he⟩ := (htend.eventually (eventually_lt_nhds hCpos)).exists
  linarith [hterm e]

/-! ### the per-prime log-series, `Λ_RS`, the prime-power term, and the local factor -/

/-- `(n:ℂ)^w = exp(w · log n)` for `n ≥ 1`. -/
lemma natCast_cpow_eq_exp {n : ℕ} (hn : 1 ≤ n) (w : ℂ) :
    (n : ℂ) ^ w = Complex.exp (w * (Real.log n : ℂ)) := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hn)
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    rw [Complex.ofReal_log (by positivity : (0 : ℝ) ≤ (n : ℝ)), Complex.ofReal_natCast]
  rw [Complex.cpow_def_of_ne_zero hn0, hlog, mul_comm]

/-- `‖α^j + β^j‖² = Σ_{i,i'} (α_i ᾱ_{i'})^j` as complex numbers. -/
lemma normSq_pow_add_pow (α β : ℂ) (j : ℕ) :
    ((‖α ^ j + β ^ j‖ ^ 2 : ℝ) : ℂ)
      = (α * (starRingEnd ℂ) α) ^ j + (α * (starRingEnd ℂ) β) ^ j
        + (β * (starRingEnd ℂ) α) ^ j + (β * (starRingEnd ℂ) β) ^ j := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  simp only [map_add, map_pow]
  ring

lemma one_sub_ne_zero_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) : 1 - z ≠ 0 := by
  intro h
  rw [sub_eq_zero] at h
  rw [← h, norm_one] at hz
  exact lt_irrefl _ hz

/-- `Σ_j z^(j+1)/(j+1) = −log(1 − z)` for `‖z‖ < 1`, as a `HasSum`. -/
lemma hasSum_taylor_neg_log {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun j : ℕ => z ^ (j + 1) / ((j : ℂ) + 1)) (-Complex.log (1 - z)) := by
  have h := hasSum_taylorSeries_neg_log hz
  have h2 := (hasSum_nat_add_iff' 1).mpr h
  simp only [Finset.sum_range_one, pow_zero, Nat.cast_zero, div_zero, sub_zero] at h2
  have heq : (fun j : ℕ => z ^ (j + 1) / ((j : ℂ) + 1))
      = fun n : ℕ => z ^ (n + 1) / ((n + 1 : ℕ) : ℂ) := by
    funext n; norm_cast
  rw [heq]
  exact h2

/-- The per-prime log-series term: `‖α^(j+1) + β^(j+1)‖²/(j+1) · Y^(j+1)`. -/
def rsLogTerm (α β Y : ℂ) (j : ℕ) : ℂ :=
  ((‖α ^ (j + 1) + β ^ (j + 1)‖ ^ 2 : ℝ) : ℂ) / ((j : ℂ) + 1) * Y ^ (j + 1)

/-- Its real counterpart at `t = ‖Y‖`. -/
def rsLogR (α β : ℂ) (t : ℝ) (j : ℕ) : ℝ :=
  ‖α ^ (j + 1) + β ^ (j + 1)‖ ^ 2 / ((j : ℝ) + 1) * t ^ (j + 1)

lemma rsLogR_nonneg (α β : ℂ) {t : ℝ} (ht : 0 ≤ t) (j : ℕ) : 0 ≤ rsLogR α β t j := by
  unfold rsLogR; positivity

lemma norm_rsLogTerm (α β Y : ℂ) (j : ℕ) : ‖rsLogTerm α β Y j‖ = rsLogR α β ‖Y‖ j := by
  unfold rsLogTerm rsLogR
  rw [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  congr 2
  rw [show ((j : ℂ) + 1) = ((j + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
  push_cast; ring

lemma rsLogTerm_ofReal (α β : ℂ) {t : ℝ} (ht : 0 ≤ t) (j : ℕ) :
    rsLogTerm α β (t : ℂ) j = ((rsLogR α β t j : ℝ) : ℂ) := by
  unfold rsLogTerm rsLogR
  push_cast
  ring

/-- **The per-prime log-series**: `Σ_j rsLogTerm = −Σ_{i,i'} log(1 − ρ_{ii'} Y)`. -/
lemma hasSum_rsLogTerm {α β Y : ℂ} (h1 : ‖α * (starRingEnd ℂ) α * Y‖ < 1)
    (h2 : ‖α * (starRingEnd ℂ) β * Y‖ < 1) (h3 : ‖β * (starRingEnd ℂ) α * Y‖ < 1)
    (h4 : ‖β * (starRingEnd ℂ) β * Y‖ < 1) :
    HasSum (rsLogTerm α β Y)
      (-(Complex.log (1 - α * (starRingEnd ℂ) α * Y) + Complex.log (1 - α * (starRingEnd ℂ) β * Y)
        + Complex.log (1 - β * (starRingEnd ℂ) α * Y)
        + Complex.log (1 - β * (starRingEnd ℂ) β * Y))) := by
  have e : rsLogTerm α β Y = fun j : ℕ => (α * (starRingEnd ℂ) α * Y) ^ (j + 1) / ((j : ℂ) + 1)
      + (α * (starRingEnd ℂ) β * Y) ^ (j + 1) / ((j : ℂ) + 1)
      + (β * (starRingEnd ℂ) α * Y) ^ (j + 1) / ((j : ℂ) + 1)
      + (β * (starRingEnd ℂ) β * Y) ^ (j + 1) / ((j : ℂ) + 1) := by
    funext j
    rw [rsLogTerm, normSq_pow_add_pow]
    simp only [mul_pow]
    ring
  rw [e]
  have := (((hasSum_taylor_neg_log h1).add (hasSum_taylor_neg_log h2)).add
    (hasSum_taylor_neg_log h3)).add (hasSum_taylor_neg_log h4)
  convert this using 1
  ring

lemma exp_neg_log_four {a b c d : ℂ} (ha : 1 - a ≠ 0) (hb : 1 - b ≠ 0) (hc : 1 - c ≠ 0)
    (hd : 1 - d ≠ 0) :
    Complex.exp (-(Complex.log (1 - a) + Complex.log (1 - b) + Complex.log (1 - c)
      + Complex.log (1 - d)))
      = ((1 - a) * (1 - b) * (1 - c) * (1 - d))⁻¹ := by
  rw [Complex.exp_neg, Complex.exp_add, Complex.exp_add, Complex.exp_add, Complex.exp_log ha,
    Complex.exp_log hb, Complex.exp_log hc, Complex.exp_log hd]

/-- **The local factor**: `exp(Σ_j rsLogTerm) = (Σ_e u_e Y^e) / (1 − Y²)` when `αβ = 1`. -/
lemma exp_rsLog_eq {α β Y : ℂ} (hαβ : α * β = 1) (h1 : ‖α * (starRingEnd ℂ) α * Y‖ < 1)
    (h2 : ‖α * (starRingEnd ℂ) β * Y‖ < 1) (h3 : ‖β * (starRingEnd ℂ) α * Y‖ < 1)
    (h4 : ‖β * (starRingEnd ℂ) β * Y‖ < 1) (hY : ‖Y‖ < 1)
    (hu : Summable fun e => heckeU (α + β) ((starRingEnd ℂ) α + (starRingEnd ℂ) β) e * Y ^ e) :
    Complex.exp (∑' j, rsLogTerm α β Y j)
      = (∑' e, heckeU (α + β) ((starRingEnd ℂ) α + (starRingEnd ℂ) β) e * Y ^ e) / (1 - Y ^ 2) := by
  rw [(hasSum_rsLogTerm h1 h2 h3 h4).tsum_eq,
    exp_neg_log_four (one_sub_ne_zero_of_norm_lt_one h1) (one_sub_ne_zero_of_norm_lt_one h2)
      (one_sub_ne_zero_of_norm_lt_one h3) (one_sub_ne_zero_of_norm_lt_one h4), ← heckeP_eq hαβ Y]
  have hg := heckeSq_genfun (α + β) ((starRingEnd ℂ) α + (starRingEnd ℂ) β) Y hu
  have hY2 : (1 : ℂ) - Y ^ 2 ≠ 0 :=
    one_sub_ne_zero_of_norm_lt_one (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hY two_ne_zero)
  have hPne : (1 - (α + β) * ((starRingEnd ℂ) α + (starRingEnd ℂ) β) * Y
      + ((α + β) ^ 2 + ((starRingEnd ℂ) α + (starRingEnd ℂ) β) ^ 2 - 2) * Y ^ 2
      - (α + β) * ((starRingEnd ℂ) α + (starRingEnd ℂ) β) * Y ^ 3 + Y ^ 4) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hg
    exact hY2 hg.symm
  rw [eq_div_iff hY2, ← hg, mul_comm _ (1 - _ + _ - _ + _), ← mul_assoc, inv_mul_cancel₀ hPne,
    one_mul]

/-- `u_e(x, x̄) = ‖h_e(x)‖²`. -/
lemma heckeU_conj_eq (x : ℂ) (e : ℕ) :
    heckeU x ((starRingEnd ℂ) x) e = ((‖heckeSeq x e‖ ^ 2 : ℝ) : ℂ) := by
  rw [heckeU, ← conj_heckeSeq, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- **The D-factor term**: `‖a(p^e)‖² / (p^e)^(s+k−1) = u_e · (p^{-s})^e`. -/
lemma dfactor_term_eq {a : ℕ → ℂ} {k : ℤ} (hf : IsHeckeEigenCoeffs a k) {p : ℕ} (hp : p.Prime)
    (s : ℂ) (e : ℕ) :
    (‖a (p ^ e)‖ ^ 2 : ℂ) / (((p ^ e : ℕ) : ℂ)) ^ (s + k - 1)
      = heckeU (heckeNorm a k p) ((starRingEnd ℂ) (heckeNorm a k p)) e * ((p : ℂ) ^ (-s)) ^ e := by
  set x := heckeNorm a k p with hx
  set q : ℂ := (p : ℂ) ^ (((k : ℂ) - 1) / 2) with hq
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hpe1 : 1 ≤ p ^ e := Nat.one_le_pow _ _ hp.pos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hcoef : a (p ^ e) = q ^ e * heckeSeq x e := hecke_coeff_pow hf hp e
  have hnq : ‖q‖ ^ 2 = Real.exp (((k : ℝ) - 1) * Real.log p) := by
    rw [hq, Complex.norm_natCast_cpow_of_pos hp.pos, ← Real.rpow_natCast, ← Real.rpow_mul hpR.le,
      Real.rpow_def_of_pos hpR]
    congr 1
    have : ((((k : ℂ) - 1) / 2)).re = ((k : ℝ) - 1) / 2 := by
      simp [Complex.div_re]
    rw [this]
    push_cast
    ring
  have hna : (‖a (p ^ e)‖ ^ 2 : ℝ) = (‖q‖ ^ 2) ^ e * ‖heckeSeq x e‖ ^ 2 := by
    rw [hcoef, norm_mul, norm_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 e]
  have hden : (((p ^ e : ℕ) : ℂ)) ^ (s + k - 1)
      = Complex.exp ((s + k - 1) * ((e : ℝ) * Real.log p : ℝ)) := by
    rw [natCast_cpow_eq_exp hpe1, Nat.cast_pow, Real.log_pow]
  have hY : ((p : ℂ) ^ (-s)) ^ e = Complex.exp (-(s * (Real.log p : ℂ)) * e) := by
    rw [natCast_cpow_neg_eq_exp hp1, ← Complex.exp_nat_mul]
    congr 1
    ring
  rw [heckeU_conj_eq, hden, hY]
  have hlhs : (‖a (p ^ e)‖ ^ 2 : ℂ) = Complex.exp ((e : ℂ) * (((k : ℝ) - 1) * Real.log p : ℝ))
      * ((‖heckeSeq x e‖ ^ 2 : ℝ) : ℂ) := by
    rw [show (‖a (p ^ e)‖ ^ 2 : ℂ) = ((‖a (p ^ e)‖ ^ 2 : ℝ) : ℂ) by push_cast; rfl, hna,
      Complex.ofReal_mul, Complex.ofReal_pow, hnq, Complex.ofReal_exp, ← Complex.exp_nat_mul]
  rw [hlhs, div_eq_iff (Complex.exp_ne_zero _), mul_comm, mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- `Λ_RS(n) = ‖α^j + β^j‖² log p` for `n = p^j` a prime power, `0` otherwise. -/
def rsVonMangoldt (a : ℕ → ℂ) (k : ℤ) (n : ℕ) : ℝ :=
  if IsPrimePow n then
    ‖satakeα a k n.minFac ^ n.factorization n.minFac
      + satakeβ a k n.minFac ^ n.factorization n.minFac‖ ^ 2 * Real.log n.minFac
  else 0

lemma rsVonMangoldt_nonneg (a : ℕ → ℂ) (k : ℤ) (n : ℕ) : 0 ≤ rsVonMangoldt a k n := by
  unfold rsVonMangoldt
  split_ifs
  · exact mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast Nat.minFac_pos n))
  · exact le_rfl

lemma rsVonMangoldt_primePow (a : ℕ → ℂ) (k : ℤ) {p : ℕ} (hp : p.Prime) (j : ℕ) :
    rsVonMangoldt a k (p ^ (j + 1))
      = ‖satakeα a k p ^ (j + 1) + satakeβ a k p ^ (j + 1)‖ ^ 2 * Real.log p := by
  have hpp : IsPrimePow (p ^ (j + 1)) := hp.isPrimePow.pow (Nat.succ_ne_zero j)
  rw [rsVonMangoldt, if_pos hpp, Nat.Prime.pow_minFac hp (Nat.succ_ne_zero j),
    Nat.factorization_pow, Finsupp.smul_apply, hp.factorization_self, smul_eq_mul, mul_one]

/-- **The prime-power term**: `dlvpTerm Λ_RS s (p^(j+1)) = rsLogTerm α_p β_p (p^{-s}) j`. -/
lemma dlvpTerm_rs_primePow (a : ℕ → ℂ) (k : ℤ) {p : ℕ} (hp : p.Prime) (s : ℂ) (j : ℕ) :
    dlvpTerm (rsVonMangoldt a k) s (p ^ (j + 1))
      = rsLogTerm (satakeα a k p) (satakeβ a k p) ((p : ℂ) ^ (-s)) j := by
  have hp2 : 2 ≤ p ^ (j + 1) := le_trans hp.two_le (Nat.le_self_pow (Nat.succ_ne_zero j) _)
  have hplog : (0 : ℝ) < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlogR : Real.log ((p ^ (j + 1) : ℕ) : ℝ) = ((j : ℝ) + 1) * Real.log p := by
    rw [Nat.cast_pow, Real.log_pow]; push_cast; ring
  unfold dlvpTerm rsLogTerm
  rw [if_pos hp2, rsVonMangoldt_primePow a k hp j, hlogR]
  have hcoef : ((‖satakeα a k p ^ (j + 1) + satakeβ a k p ^ (j + 1)‖ ^ 2 * Real.log p : ℝ) : ℂ)
      / ((((j : ℝ) + 1) * Real.log p : ℝ) : ℂ)
      = ((‖satakeα a k p ^ (j + 1) + satakeβ a k p ^ (j + 1)‖ ^ 2 : ℝ) : ℂ) / ((j : ℂ) + 1) := by
    have hL : (Real.log p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hplog.ne'
    have hj : ((j : ℂ) + 1) ≠ 0 := by
      have : ((j : ℂ) + 1) = ((j + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [this]; exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j)
    rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_one,
      Complex.ofReal_natCast, mul_div_mul_right _ _ hL]
  have hexp : Complex.exp (-(s * ((((j : ℝ) + 1) * Real.log p : ℝ) : ℂ)))
      = ((p : ℂ) ^ (-s)) ^ (j + 1) := by
    rw [natCast_cpow_neg_eq_exp hp.one_lt.le, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hcoef, hexp]

variable {F : Type*} [FunLike F ℍ ℂ] (k : ℤ)
  [cf : CuspFormClass F (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma 1)) k]

include cf in
/-- **Rankin's bound at a prime power**: `Σ_e ‖h_e‖² (p^{-σ})^e` converges for `σ > 1`. -/
lemma summable_heckeSeq_sq (f : F) (hk : 0 < k)
    (hf : IsHeckeEigenCoeffs (fun n => (ModularFormClass.qExpansion 1 f).coeff n) k) {p : ℕ}
    (hp : p.Prime) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun e : ℕ =>
      ‖heckeSeq (heckeNorm (fun n => (ModularFormClass.qExpansion 1 f).coeff n) k p) e‖ ^ 2
        * ((p : ℝ) ^ (-σ)) ^ e := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hR := summable_rsDirichlet' k f hk (σ := σ + k - 1) (by linarith)
  have hsub := hR.comp_injective (Nat.pow_right_injective hp.two_le)
  refine hsub.congr fun e => ?_
  have hpR : (0 : ℝ) ≤ p := by positivity
  have h := dfactor_term_eq hf hp (σ : ℂ) e
  -- cast the real identity through `ℂ`
  apply Complex.ofReal_injective
  rw [Function.comp_apply]
  push_cast
  rw [Complex.ofReal_cpow (by positivity) (σ + k - 1), Complex.ofReal_cpow hpR (-σ)]
  push_cast
  rw [heckeU_conj_eq] at h
  simpa using h

/-! ### The Satake bounds for a Hecke eigenform, the fiber sums, convergence over `p` -/

/-- The `q`-expansion coefficients of `f`. -/
def rsCoeff (f : F) : ℕ → ℂ := fun n => (ModularFormClass.qExpansion 1 f).coeff n

/-- The real form of `dfactor_term_eq`. -/
lemma dfactorR_term_eq {a : ℕ → ℂ} {k : ℤ} (hf : IsHeckeEigenCoeffs a k) {p : ℕ} (hp : p.Prime)
    (σ : ℝ) (e : ℕ) :
    ‖heckeSeq (heckeNorm a k p) e‖ ^ 2 * ((p : ℝ) ^ (-σ)) ^ e
      = ‖a (p ^ e)‖ ^ 2 / ((p ^ e : ℕ) : ℝ) ^ (σ + k - 1) := by
  have hpR : (0 : ℝ) ≤ p := by positivity
  have h := dfactor_term_eq hf hp (σ : ℂ) e
  apply Complex.ofReal_injective
  push_cast
  rw [Complex.ofReal_cpow (by positivity) (σ + k - 1), Complex.ofReal_cpow hpR (-σ)]
  push_cast
  rw [heckeU_conj_eq] at h
  simpa using h.symm

include cf in
/-- **The Satake bounds** at `Re s > 1`: `‖α‖² ‖p^{-s}‖ < 1`, `‖β‖² ‖p^{-s}‖ < 1`, `‖p^{-s}‖ < 1`. -/
lemma satake_norm_lt (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k) {p : ℕ}
    (hp : p.Prime) {s : ℂ} (hs : 1 < s.re) :
    ‖satakeα (rsCoeff f) k p‖ ^ 2 * ‖(p : ℂ) ^ (-s)‖ < 1
      ∧ ‖satakeβ (rsCoeff f) k p‖ ^ 2 * ‖(p : ℂ) ^ (-s)‖ < 1 ∧ ‖(p : ℂ) ^ (-s)‖ < 1 := by
  have hY : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
  have hY1 : (p : ℝ) ^ (-s.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
  have hY0 : 0 < (p : ℝ) ^ (-s.re) := by
    have : (0 : ℝ) < p := by exact_mod_cast hp.pos
    positivity
  have hab := satake_mul (rsCoeff f) k p
  have hadd := satake_add (rsCoeff f) k p
  have hsum : Summable fun e =>
      ‖heckeSeq (satakeα (rsCoeff f) k p + satakeβ (rsCoeff f) k p) e‖ ^ 2
        * ((p : ℝ) ^ (-s.re)) ^ e := by
    rw [hadd]
    exact summable_heckeSeq_sq k f hk hf hp hs
  rw [hY]
  refine ⟨?_, ?_, hY1⟩
  · by_cases h : 1 < ‖satakeα (rsCoeff f) k p‖
    · exact satake_sq_mul_lt_one hab h hY0 hsum
    · push_neg at h
      calc ‖satakeα (rsCoeff f) k p‖ ^ 2 * (p : ℝ) ^ (-s.re)
          ≤ 1 * (p : ℝ) ^ (-s.re) :=
            mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) h) hY0.le
        _ < 1 := by rw [one_mul]; exact hY1
  · by_cases h : 1 < ‖satakeβ (rsCoeff f) k p‖
    · have hba : satakeβ (rsCoeff f) k p * satakeα (rsCoeff f) k p = 1 := by
        rw [mul_comm]; exact hab
      have hsum' : Summable fun e =>
          ‖heckeSeq (satakeβ (rsCoeff f) k p + satakeα (rsCoeff f) k p) e‖ ^ 2
            * ((p : ℝ) ^ (-s.re)) ^ e := by
        rw [add_comm]; exact hsum
      exact satake_sq_mul_lt_one hba h hY0 hsum'
    · push_neg at h
      calc ‖satakeβ (rsCoeff f) k p‖ ^ 2 * (p : ℝ) ^ (-s.re)
          ≤ 1 * (p : ℝ) ^ (-s.re) :=
            mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) h) hY0.le
        _ < 1 := by rw [one_mul]; exact hY1

include cf in
/-- The four `‖ρ Y‖ < 1` conditions of `hasSum_rsLogTerm` at `Re s > 1`. -/
lemma rho_norm_lt (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k) {p : ℕ}
    (hp : p.Prime) {s : ℂ} (hs : 1 < s.re) :
    ‖satakeα (rsCoeff f) k p * (starRingEnd ℂ) (satakeα (rsCoeff f) k p) * (p : ℂ) ^ (-s)‖ < 1
    ∧ ‖satakeα (rsCoeff f) k p * (starRingEnd ℂ) (satakeβ (rsCoeff f) k p) * (p : ℂ) ^ (-s)‖ < 1
    ∧ ‖satakeβ (rsCoeff f) k p * (starRingEnd ℂ) (satakeα (rsCoeff f) k p) * (p : ℂ) ^ (-s)‖ < 1
    ∧ ‖satakeβ (rsCoeff f) k p * (starRingEnd ℂ) (satakeβ (rsCoeff f) k p) * (p : ℂ) ^ (-s)‖ < 1 := by
  obtain ⟨hα, hβ, hY⟩ := satake_norm_lt k f hk hf hp hs
  have hab : ‖satakeα (rsCoeff f) k p‖ * ‖satakeβ (rsCoeff f) k p‖ = 1 := by
    rw [← norm_mul, satake_mul, norm_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [norm_mul, norm_mul, Complex.norm_conj, ← sq]; exact hα
  · rw [norm_mul, norm_mul, Complex.norm_conj, hab, one_mul]; exact hY
  · rw [norm_mul, norm_mul, Complex.norm_conj, mul_comm ‖satakeβ _ _ _‖, hab, one_mul]; exact hY
  · rw [norm_mul, norm_mul, Complex.norm_conj, ← sq]; exact hβ

include cf in
/-- Complex summability of the local series `Σ_e u_e (p^{-s})^e` at `Re s > 1`. -/
lemma summable_heckeU_cpow (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k) {p : ℕ}
    (hp : p.Prime) {s : ℂ} (hs : 1 < s.re) :
    Summable fun e => heckeU (heckeNorm (rsCoeff f) k p) ((starRingEnd ℂ) (heckeNorm (rsCoeff f) k p)) e
      * ((p : ℂ) ^ (-s)) ^ e := by
  refine Summable.of_norm ?_
  refine (summable_heckeSeq_sq k f hk hf hp hs).congr fun e => ?_
  rw [heckeU_conj_eq, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
  rfl

/-- The per-prime log-sum `ℓ_p(s) = Σ_j rsLogTerm α_p β_p (p^{-s}) j`. -/
def rsLocal (f : F) (p : ℕ) (s : ℂ) : ℂ :=
  ∑' j, rsLogTerm (satakeα (rsCoeff f) k p) (satakeβ (rsCoeff f) k p) ((p : ℂ) ^ (-s)) j

/-- Its real counterpart at real `σ`. -/
def rsLocalR (f : F) (p : ℕ) (σ : ℝ) : ℝ :=
  ∑' j, rsLogR (satakeα (rsCoeff f) k p) (satakeβ (rsCoeff f) k p) ((p : ℝ) ^ (-σ)) j

include cf in
/-- The fiber sum converges, and `exp ℓ_p = (1 − p^{-2s})^{-1} · Σ_e ‖a(p^e)‖² (p^e)^{-(s+k-1)}`. -/
lemma exp_rsLocal_eq (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k) {p : ℕ}
    (hp : p.Prime) {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (rsLocal k f p s)
      = (1 - (p : ℂ) ^ (-(2 * s)))⁻¹
        * ∑' e : ℕ, (‖rsCoeff f (p ^ e)‖ ^ 2 : ℂ) / (((p ^ e : ℕ) : ℂ)) ^ (s + k - 1) := by
  obtain ⟨h1, h2, h3, h4⟩ := rho_norm_lt k f hk hf hp hs
  have hY := (satake_norm_lt k f hk hf hp hs).2.2
  have hu := summable_heckeU_cpow k f hk hf hp hs
  rw [← satake_add (rsCoeff f) k p] at hu
  have hconj : (starRingEnd ℂ) (satakeα (rsCoeff f) k p + satakeβ (rsCoeff f) k p)
      = (starRingEnd ℂ) (satakeα (rsCoeff f) k p) + (starRingEnd ℂ) (satakeβ (rsCoeff f) k p) :=
    map_add _ _ _
  rw [hconj] at hu
  rw [rsLocal, exp_rsLog_eq (satake_mul (rsCoeff f) k p) h1 h2 h3 h4 hY hu, div_eq_inv_mul]
  congr 1
  · congr 2
    rw [← Complex.cpow_nat_mul]
    congr 1
    push_cast
    ring
  · refine tsum_congr fun e => ?_
    rw [dfactor_term_eq hf hp s e, ← satake_add, hconj]

include cf in
/-- The real fiber sum is `log` of the local factor, hence at most the factor minus one:
`rsLocalR ≤ (4/3)(Σ_e ‖h_{e+1}‖² Y₀^(e+1) + Y₀²)`, `Y₀ = p^{-σ}`. -/
lemma rsLocalR_le (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k) {p : ℕ}
    (hp : p.Prime) {σ : ℝ} (hσ : 1 < σ) :
    rsLocalR k f p σ
      ≤ 4 / 3 * ((∑' e : ℕ, ‖rsCoeff f (p ^ (e + 1))‖ ^ 2 / ((p ^ (e + 1) : ℕ) : ℝ) ^ (σ + k - 1))
          + ((p : ℝ) ^ (-σ)) ^ 2) := by
  set Y₀ : ℝ := (p : ℝ) ^ (-σ) with hY₀
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hY0 : 0 < Y₀ := by rw [hY₀]; positivity
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hYhalf : Y₀ ≤ 1 / 2 := by
    rw [hY₀, Real.rpow_neg hpR.le]
    calc ((p : ℝ) ^ σ)⁻¹ ≤ ((p : ℝ) ^ (1 : ℝ))⁻¹ :=
          inv_anti₀ (by positivity) (Real.rpow_le_rpow_of_exponent_le (by linarith) hσ.le)
      _ ≤ 1 / 2 := by rw [Real.rpow_one, one_div]; exact inv_anti₀ (by norm_num) hp2
  have hsR : (1 : ℂ).re < (σ : ℂ).re := by simp; linarith
  have hs1 : 1 < (σ : ℂ).re := by simpa using hσ
  obtain ⟨h1, h2, h3, h4⟩ := rho_norm_lt k f hk hf hp hs1
  have hcpow : (p : ℂ) ^ (-(σ : ℂ)) = (Y₀ : ℂ) := by
    rw [hY₀, Complex.ofReal_cpow hpR.le, Complex.ofReal_neg, Complex.ofReal_natCast]
  -- the complex log-sum is the real one
  have hT : rsLocal k f p σ = ((rsLocalR k f p σ : ℝ) : ℂ) := by
    rw [rsLocal, rsLocalR, Complex.ofReal_tsum]
    refine tsum_congr fun j => ?_
    rw [hcpow, rsLogTerm_ofReal _ _ hY0.le]
  -- the local factor is real
  have hu := summable_heckeU_cpow k f hk hf hp hs1
  rw [hcpow] at hu
  set S : ℝ := ∑' e, ‖heckeSeq (heckeNorm (rsCoeff f) k p) e‖ ^ 2 * Y₀ ^ e with hS
  have hSsum : Summable fun e => ‖heckeSeq (heckeNorm (rsCoeff f) k p) e‖ ^ 2 * Y₀ ^ e := by
    have := summable_heckeSeq_sq k f hk hf hp hσ
    rwa [← hY₀] at this
  have hSc : (∑' e, heckeU (heckeNorm (rsCoeff f) k p) ((starRingEnd ℂ) (heckeNorm (rsCoeff f) k p)) e
      * (Y₀ : ℂ) ^ e) = ((S : ℝ) : ℂ) := by
    rw [hS, Complex.ofReal_tsum]
    refine tsum_congr fun e => ?_
    rw [heckeU_conj_eq]; push_cast; ring
  have hexp := exp_rsLocal_eq k f hk hf hp hs1
  rw [hT] at hexp
  -- rewrite the right side as the real quotient `S / (1 − Y₀²)`
  have hexp' : Real.exp (rsLocalR k f p σ) = S / (1 - Y₀ ^ 2) := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_exp, hexp]
    have hY2 : (p : ℂ) ^ (-(2 * (σ : ℂ))) = ((Y₀ ^ 2 : ℝ) : ℂ) := by
      rw [show -(2 * (σ : ℂ)) = ((2 : ℕ) : ℂ) * (-(σ : ℂ)) by push_cast; ring,
        Complex.cpow_nat_mul, hcpow]; push_cast; rfl
    rw [hY2]
    have hD : ∀ e : ℕ, (‖rsCoeff f (p ^ e)‖ ^ 2 : ℂ) / (((p ^ e : ℕ) : ℂ)) ^ ((σ : ℂ) + k - 1)
        = ((‖heckeSeq (heckeNorm (rsCoeff f) k p) e‖ ^ 2 * Y₀ ^ e : ℝ) : ℂ) := by
      intro e
      rw [dfactor_term_eq hf hp (σ : ℂ) e, heckeU_conj_eq, hcpow]; push_cast; ring
    simp_rw [hD]
    rw [← Complex.ofReal_tsum, ← hS]
    push_cast
    ring
  have hL0 : 0 < S / (1 - Y₀ ^ 2) := by rw [← hexp']; exact Real.exp_pos _
  have hlog : rsLocalR k f p σ = Real.log (S / (1 - Y₀ ^ 2)) := by
    rw [← hexp', Real.log_exp]
  have hS0 : (∑' e, ‖heckeSeq (heckeNorm (rsCoeff f) k p) (e + 1)‖ ^ 2 * Y₀ ^ (e + 1)) = S - 1 := by
    rw [hS, hSsum.tsum_eq_zero_add]
    simp
  have hden : 3 / 4 ≤ 1 - Y₀ ^ 2 := by nlinarith
  calc rsLocalR k f p σ = Real.log (S / (1 - Y₀ ^ 2)) := hlog
    _ ≤ S / (1 - Y₀ ^ 2) - 1 := Real.log_le_sub_one_of_pos hL0
    _ = ((S - 1) + Y₀ ^ 2) / (1 - Y₀ ^ 2) := by
        rw [div_sub_one (ne_of_gt (by linarith : (0 : ℝ) < 1 - Y₀ ^ 2))]
        ring
    _ ≤ ((S - 1) + Y₀ ^ 2) / (3 / 4) := by
        apply div_le_div_of_nonneg_left _ (by norm_num) hden
        have : 0 ≤ S - 1 := by
          rw [← hS0]; exact tsum_nonneg fun e => by positivity
        positivity
    _ = 4 / 3 * ((S - 1) + Y₀ ^ 2) := by ring
    _ = 4 / 3 * ((∑' e : ℕ, ‖rsCoeff f (p ^ (e + 1))‖ ^ 2 / ((p ^ (e + 1) : ℕ) : ℝ) ^ (σ + k - 1))
          + Y₀ ^ 2) := by
        rw [← hS0]
        congr 3
        funext e
        rw [← dfactorR_term_eq hf hp σ (e + 1)]

/-- The prime-power reindexing of a summable series of nonnegative terms. -/
lemma summable_primePow_of_summable {g : ℕ → ℝ} (hg : Summable g) :
    Summable fun y : Nat.Primes × ℕ => g ((y.1 : ℕ) ^ (y.2 + 1)) := by
  have h := (Equiv.summable_iff Nat.Primes.prodNatEquiv).mpr (hg.subtype {n | IsPrimePow n})
  refine h.congr fun y => ?_
  obtain ⟨p, e⟩ := y
  simp only [Function.comp_apply, Nat.Primes.prodNatEquiv_apply]

include cf in
/-- **Convergence over the primes**: `Σ_p rsLocalR f p σ < ∞` for `σ > 1`. -/
lemma summable_rsLocalR (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k) {σ : ℝ}
    (hσ : 1 < σ) : Summable fun p : Nat.Primes => rsLocalR k f p σ := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hR := summable_rsDirichlet' k f hk (σ := σ + k - 1) (by linarith)
  have hR' : Summable fun n : ℕ => ‖rsCoeff f n‖ ^ 2 / (n : ℝ) ^ (σ + k - 1) := hR
  have hprod := summable_primePow_of_summable hR'
  have hprod_nn : 0 ≤ fun y : Nat.Primes × ℕ =>
      ‖rsCoeff f ((y.1 : ℕ) ^ (y.2 + 1))‖ ^ 2 / (((y.1 : ℕ) ^ (y.2 + 1) : ℕ) : ℝ) ^ (σ + k - 1) :=
    fun y => by positivity
  have hA := ((summable_prod_of_nonneg hprod_nn).mp hprod).2
  have hB : Summable fun p : Nat.Primes => ((p : ℝ) ^ (-σ)) ^ 2 := by
    have := Nat.Primes.summable_rpow.mpr (by linarith : -(2 * σ) < -1)
    refine this.congr fun p => ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1; push_cast; ring
  refine Summable.of_nonneg_of_le (fun p => tsum_nonneg fun j => rsLogR_nonneg _ _ (by positivity) j)
    (fun p => rsLocalR_le k f hk hf p.2 hσ) ((hA.add hB).mul_left (4 / 3))

include cf in
/-- Joint summability of the real `(p, j)`-family. -/
lemma summable_rsLogR_prod (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k) {σ : ℝ}
    (hσ : 1 < σ) :
    Summable fun y : Nat.Primes × ℕ =>
      rsLogR (satakeα (rsCoeff f) k y.1) (satakeβ (rsCoeff f) k y.1) (((y.1 : ℕ) : ℝ) ^ (-σ)) y.2 := by
  have hnn : 0 ≤ fun y : Nat.Primes × ℕ =>
      rsLogR (satakeα (rsCoeff f) k y.1) (satakeβ (rsCoeff f) k y.1) (((y.1 : ℕ) : ℝ) ^ (-σ)) y.2 :=
    fun y => rsLogR_nonneg _ _ (by positivity) _
  refine (summable_prod_of_nonneg hnn).mpr ⟨fun p => ?_, summable_rsLocalR k f hk hf hσ⟩
  have hs1 : 1 < (σ : ℂ).re := by simpa using hσ
  obtain ⟨h1, h2, h3, h4⟩ := rho_norm_lt k f hk hf p.2 hs1
  have h := (hasSum_rsLogTerm h1 h2 h3 h4).summable.norm
  refine h.congr fun j => ?_
  rw [norm_rsLogTerm, Complex.norm_natCast_cpow_of_pos p.2.pos, Complex.neg_re, Complex.ofReal_re]

/-! ### the global Euler-product bridge `dlvpG Λ_RS s = ζ(2s) D(s + k − 1)` -/

include cf in
lemma dlvpTerm_rs_eq_zero (f : F) (s : ℂ) {n : ℕ} (hn : ¬ IsPrimePow n) :
    dlvpTerm (rsVonMangoldt (rsCoeff f) k) s n = 0 := by
  simp [dlvpTerm, rsVonMangoldt, hn]

include cf in
/-- The `(p, j)`-family of the log-series is summable (norms) at `Re s > 1`. -/
lemma summable_dlvpTerm_rs_prod (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k) {s : ℂ}
    (hs : 1 < s.re) :
    Summable fun y : Nat.Primes × ℕ =>
      dlvpTerm (rsVonMangoldt (rsCoeff f) k) s (Nat.Primes.prodNatEquiv y) := by
  refine Summable.of_norm ?_
  refine (summable_rsLogR_prod k f hk hf hs).congr fun y => ?_
  obtain ⟨p, j⟩ := y
  rw [Nat.Primes.prodNatEquiv_apply, dlvpTerm_rs_primePow _ _ p.2, norm_rsLogTerm,
    Complex.norm_natCast_cpow_of_pos p.2.pos, Complex.neg_re]

set_option maxHeartbeats 4000000 in
include cf in
/-- `Σ_n dlvpTerm Λ_RS s n` is summable and equals `Σ_p ℓ_p(s)`. -/
lemma tsum_dlvpTerm_rs (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k) {s : ℂ}
    (hs : 1 < s.re) :
    Summable (dlvpTerm (rsVonMangoldt (rsCoeff f) k) s)
      ∧ ∑' n, dlvpTerm (rsVonMangoldt (rsCoeff f) k) s n = ∑' p : Nat.Primes, rsLocal k f p s := by
  set T := dlvpTerm (rsVonMangoldt (rsCoeff f) k) s with hT
  have hsupp : Function.support T ⊆ {n | IsPrimePow n} := by
    intro n hn
    by_contra hnp
    exact hn (dlvpTerm_rs_eq_zero k f s hnp)
  have hprod := summable_dlvpTerm_rs_prod k f hk hf hs
  have hsub : Summable fun x : {n // IsPrimePow n} => T x.val :=
    (Equiv.summable_iff Nat.Primes.prodNatEquiv).mp hprod
  have hsumT : Summable T := by
    refine (summable_subtype_and_compl (s := {n | IsPrimePow n})).mp ⟨hsub, ?_⟩
    refine summable_zero.congr fun x => ?_
    have hx : ¬ IsPrimePow (x : ℕ) := x.2
    exact (dlvpTerm_rs_eq_zero k f s hx).symm
  refine ⟨hsumT, ?_⟩
  calc ∑' n, T n = ∑' x : {n // IsPrimePow n}, T x.val :=
        (tsum_subtype_eq_of_support_subset hsupp).symm
    _ = ∑' y : Nat.Primes × ℕ, T (Nat.Primes.prodNatEquiv y) :=
        (Equiv.tsum_eq Nat.Primes.prodNatEquiv (fun x => T x.val)).symm
    _ = ∑' p : Nat.Primes, ∑' j : ℕ, T (Nat.Primes.prodNatEquiv (p, j)) :=
        hprod.tsum_prod' fun p => hprod.prod_factor p
    _ = ∑' p : Nat.Primes, rsLocal k f p s := by
        refine tsum_congr fun p => tsum_congr fun j => ?_
        rw [hT, Nat.Primes.prodNatEquiv_apply, dlvpTerm_rs_primePow _ _ p.2]

include cf in
/-- `Σ_p ℓ_p(s)` is summable at `Re s > 1`. -/
lemma summable_rsLocal (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k) {s : ℂ}
    (hs : 1 < s.re) : Summable fun p : Nat.Primes => rsLocal k f p s := by
  have hprod := summable_dlvpTerm_rs_prod k f hk hf hs
  have := hprod.prod
  refine this.congr fun p => ?_
  refine tsum_congr fun j => ?_
  rw [Nat.Primes.prodNatEquiv_apply, dlvpTerm_rs_primePow _ _ p.2]

include cf in
/-- The Euler product of `D(w)` for `Re w > k`, as a `HasProd`. -/
lemma hasProd_rsD (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k) {w : ℂ}
    (hw : (k : ℝ) < w.re) :
    HasProd (fun p : Nat.Primes => ∑' e : ℕ, (‖rsCoeff f ((p : ℕ) ^ e)‖ ^ 2 : ℂ)
        / (((p : ℕ) ^ e : ℕ) : ℂ) ^ w) (rsD f w) := by
  have hmul : ((normSqAF hf).pmul (cpowAF w)).IsMultiplicative :=
    (isMultiplicative_normSq hf).pmul (isMultiplicative_cpowAF w)
  have hval : ∀ n : ℕ, ((normSqAF hf).pmul (cpowAF w)) n = (‖rsCoeff f n‖ ^ 2 : ℂ) / (n : ℂ) ^ w := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [normSqAF, cpowAF, rsCoeff, RankinSelbergDelta.CuspForm.qExpansion_coeff_zero_cusp f]
    · simp only [ArithmeticFunction.pmul_apply, normSqAF, cpowAF, ArithmeticFunction.coe_mk,
        if_neg hn]
      rw [Complex.cpow_neg, div_eq_mul_inv]
  have hgsum : Summable (fun n => ‖((normSqAF hf).pmul (cpowAF w)) n‖) := by
    have hR := summable_rsDirichlet' k f hk (σ := w.re) hw
    refine hR.congr (fun n => ?_)
    rcases eq_or_ne n 0 with rfl | hn
    · simp [normSqAF, cpowAF, rsCoeff, RankinSelbergDelta.CuspForm.qExpansion_coeff_zero_cusp f]
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      simp only [ArithmeticFunction.pmul_apply, normSqAF, cpowAF, ArithmeticFunction.coe_mk,
        if_neg hn, norm_mul]
      rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
        Complex.norm_natCast_cpow_of_pos hnpos, Complex.neg_re, Real.rpow_neg (by positivity),
        div_eq_mul_inv]
      rfl
  have hEP := hmul.eulerProduct_hasProd hgsum
  have htot : (∑' n : ℕ, ((normSqAF hf).pmul (cpowAF w)) n) = rsD f w := by
    rw [rsD]
    exact tsum_congr hval
  rw [htot] at hEP
  have hfun : (fun p : Nat.Primes => ∑' e : ℕ, ((normSqAF hf).pmul (cpowAF w)) ((p : ℕ) ^ e))
      = fun p : Nat.Primes => ∑' e : ℕ, (‖rsCoeff f ((p : ℕ) ^ e)‖ ^ 2 : ℂ)
        / (((p : ℕ) ^ e : ℕ) : ℂ) ^ w := by
    funext p
    exact tsum_congr fun e => hval _
  rw [hfun] at hEP
  exact hEP

/-! ### the bridge `dlvpG Λ_RS s = ζ(2s) D(s + k − 1)` and `rs_square_ne_zero` -/

include cf in
/-- **The Euler-product bridge**: for `Re s > 1`, `dlvpG Λ_RS s = ζ(2s) · D(s + k − 1)`. -/
theorem dlvpG_rs_eq (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k) {s : ℂ}
    (hs : 1 < s.re) :
    dlvpG (rsVonMangoldt (rsCoeff f) k) s = riemannZeta (2 * s) * rsD f (s + k - 1) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h2s : 1 < (2 * s).re := by
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat]; linarith
  have hζ := riemannZeta_eulerProduct_hasProd h2s
  have hD := hasProd_rsD k f hk hf (w := s + k - 1)
    (by simp only [Complex.sub_re, Complex.add_re, Complex.intCast_re, Complex.one_re]; linarith)
  have hsum := summable_rsLocal k f hk hf hs
  rw [dlvpG, (tsum_dlvpTerm_rs k f hk hf hs).2, ← hsum.hasSum.cexp.tprod_eq,
    ← (hζ.mul hD).tprod_eq]
  exact tprod_congr fun p => exp_rsLocal_eq k f hk hf p.2 hs

include cf in
lemma summable_dlvpTerm_rs (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k) {s : ℂ}
    (hs : 1 < s.re) : Summable (dlvpTerm (rsVonMangoldt (rsCoeff f) k) s) :=
  (tsum_dlvpTerm_rs k f hk hf hs).1

/-- The global function: `G = rsG` on `Re s < 2`, the Dirichlet-series form beyond. -/
def Gfull (f : F) (s : ℂ) : ℂ :=
  if s.re < 2 then rsG k f s else riemannZeta (2 * s) * rsD f (s + k - 1)

include cf in
lemma Gfull_eq (f : F) (hk : 0 < k) {s : ℂ} (hs : 1 < s.re) :
    Gfull k f s = riemannZeta (2 * s) * rsD f (s + k - 1) := by
  unfold Gfull
  split_ifs with h
  · exact rsG_eq_zeta_mul_rsD k f hk hs (by linarith)
  · rfl

lemma Gfull_eventuallyEq (f : F) {s₀ : ℂ} (h : s₀.re < 2) : Gfull k f =ᶠ[𝓝 s₀] rsG k f := by
  have hopen : IsOpen {s : ℂ | s.re < 2} := isOpen_lt Complex.continuous_re continuous_const
  filter_upwards [hopen.mem_nhds h] with s hs
  simp only [Gfull, if_pos (show s.re < 2 from hs)]

include cf in
/-- `H2` for `Gfull`. -/
theorem Gfull_isBigO (f : F) (hk : 0 < k) :
    (fun x : ℝ => Gfull k f (1 + x)) =O[𝓝[>] 0] fun x : ℝ => (1 : ℂ) / x := by
  refine (rsG_isBigO_one_div k f hk).congr' ?_ EventuallyEq.rfl
  filter_upwards [(eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
    with x hx
  have hre : ((1 : ℂ) + x).re < 2 := by simp; linarith
  simp only [Gfull, if_pos hre]

include cf in
/-- `H3` for `Gfull`. -/
theorem differentiableAt_Gfull_line (f : F) (hk : 0 < k) {y : ℝ} (hy : y ≠ 0) :
    DifferentiableAt ℂ (Gfull k f) (1 + Complex.I * y) :=
  (differentiableAt_rsG_line k f hk hy).congr_of_eventuallyEq
    (Gfull_eventuallyEq k f (by simp))

include cf in
/-- `H4` for `Gfull`. -/
theorem continuousAt_Gfull_line2 (f : F) (hk : 0 < k) {y : ℝ} (hy : y ≠ 0) :
    ContinuousAt (Gfull k f) (1 + 2 * Complex.I * y) :=
  (continuousAt_rsG_line2 k f hk hy).congr (Gfull_eventuallyEq k f (by simp)).symm

include cf in
/-- `H1` for `Gfull`: the 3-4-1 product bound, from `dlvpProduct_ge_one` through the bridge. -/
theorem Gfull_product_ge_one (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k) (y : ℝ)
    {x : ℝ} (hx : 0 < x) :
    1 ≤ ‖Gfull k f (1 + x) ^ 3 * Gfull k f (1 + x + Complex.I * y) ^ 4
        * Gfull k f (1 + x + 2 * Complex.I * y)‖ := by
  have h0 : 1 < ((1 : ℂ) + x).re := by simp; linarith
  have h1 : 1 < ((1 : ℂ) + x + Complex.I * y).re := by simp; linarith
  have h2 : 1 < ((1 : ℂ) + x + 2 * Complex.I * y).re := by simp; linarith
  rw [Gfull_eq k f hk h0, Gfull_eq k f hk h1, Gfull_eq k f hk h2, ← dlvpG_rs_eq k f hk hf h0,
    ← dlvpG_rs_eq k f hk hf h1, ← dlvpG_rs_eq k f hk hf h2]
  exact dlvpProduct_ge_one (rsVonMangoldt_nonneg _ _) (summable_dlvpTerm_rs k f hk hf h0)
    (summable_dlvpTerm_rs k f hk hf h1) (summable_dlvpTerm_rs k f hk hf h2)

include cf in
/-- **The Rankin–Selberg square does not vanish on the line `Re s = 1`**: for a level-1 weight-`k`
Hecke eigenform `f` and `y ≠ 0`, `G(1 + iy) ≠ 0`, where `G = ζ(2s) D(s + k − 1)` (continued through
`rsG` near the line). -/
theorem rs_square_ne_zero (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k) {y : ℝ}
    (hy : y ≠ 0) : Gfull k f (1 + Complex.I * y) ≠ 0 :=
  trs_ne_zero (G := Gfull k f) (fun x hx => Gfull_product_ge_one k f hk hf y hx)
    (Gfull_isBigO k f hk) (differentiableAt_Gfull_line k f hk hy)
    (continuousAt_Gfull_line2 k f hk hy)

end

end RankinSelbergDelta.RankinSelberg
