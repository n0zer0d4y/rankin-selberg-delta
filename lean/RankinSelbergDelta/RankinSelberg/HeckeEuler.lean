import Mathlib

/-!
# The Euler product of `D(w) = Σ |a(n)|² n^{−w}`

The structure `IsHeckeEigenCoeffs` (the Hecke relations of a normalised eigenform's coefficients)
and its first consequence: `n ↦ |a(n)|²` is multiplicative, so the Rankin–Selberg Dirichlet series
has an Euler product.
-/

namespace RankinSelbergDelta.RankinSelberg

open scoped ArithmeticFunction

noncomputable section

/-- The Hecke-eigenform relations on a coefficient sequence `a : ℕ → ℂ` of weight `k`:
    normalization `a 1 = 1`, multiplicativity on coprime indices, and the prime-power recursion
    `a(p^{r+1}) = a(p) a(p^r) − p^{k-1} a(p^{r-1})`. -/
structure IsHeckeEigenCoeffs (a : ℕ → ℂ) (k : ℤ) : Prop where
  zero : a 0 = 0
  one : a 1 = 1
  mul_coprime : ∀ m n : ℕ, Nat.Coprime m n → a (m * n) = a m * a n
  /-- The prime-power recursion, stated with `r+2 / r+1 / r` so there is no `Nat`-subtraction
      degeneracy: at `r = 0` it reads `a(p²) = a(p)² − p^{k-1}`, the correct base case. -/
  recursion : ∀ (p r : ℕ), p.Prime →
    a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - (p : ℂ) ^ (k - 1) * a (p ^ r)

/-- `n ↦ ‖a n‖²` as an arithmetic function (`0 ↦ 0`). -/
def normSqAF {a : ℕ → ℂ} {k : ℤ} (h : IsHeckeEigenCoeffs a k) : ArithmeticFunction ℂ :=
  ⟨fun n => (‖a n‖ ^ 2 : ℂ), by simp [h.zero]⟩

/-- Under the Hecke relations, `n ↦ ‖a n‖²` is a multiplicative arithmetic function. -/
theorem isMultiplicative_normSq {a : ℕ → ℂ} {k : ℤ} (h : IsHeckeEigenCoeffs a k) :
    (normSqAF h).IsMultiplicative := by
  refine ⟨?_, ?_⟩
  · simp only [normSqAF, ArithmeticFunction.coe_mk, h.one, norm_one]
    norm_num
  · intro m n hmn
    simp only [normSqAF, ArithmeticFunction.coe_mk]
    rw [h.mul_coprime m n hmn, norm_mul]
    push_cast
    ring

/-- `n ↦ n^{-w}` as an arithmetic function (`0 ↦ 0`); it is completely multiplicative because
    `(mn)^{-w} = m^{-w} n^{-w}` for natural `m, n`. This is the completely-multiplicative factor
    that turns the plain multiplicativity of `‖a n‖²` into the Euler product of `D(w)`. -/
def cpowAF (w : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else (n : ℂ) ^ (-w), by simp⟩

/-- `n ↦ n^{-w}` is a multiplicative arithmetic function. -/
theorem isMultiplicative_cpowAF (w : ℂ) : (cpowAF w).IsMultiplicative := by
  refine ⟨?_, ?_⟩
  · simp [cpowAF, Complex.one_cpow]
  · intro m n hmn
    simp only [cpowAF, ArithmeticFunction.coe_mk]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp
    · rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; simp
      · have hmn0 : m * n ≠ 0 := Nat.mul_ne_zero hm.ne' hn.ne'
        rw [if_neg hmn0, if_neg hm.ne', if_neg hn.ne', Nat.cast_mul,
            Complex.natCast_mul_natCast_cpow]

/-- **The Rankin–Selberg Euler product.** For Hecke-eigenform coefficients `a` of weight `k`,
    wherever the Rankin–Selberg Dirichlet series converges absolutely (`hsum`), it factors as an
    Euler product over primes:
    `Σ_n |a(n)|²/n^w = ∏_p Σ_e |a(p^e)|²/p^{ew}`.
    The absolute convergence `hsum` is the analytic input (supplied for a cusp form by
    `summable_rsDirichlet` at `Re w > k+1`); the Hecke relations are the arithmetic input. -/
theorem rsDirichlet_eulerProduct {a : ℕ → ℂ} {k : ℤ} (h : IsHeckeEigenCoeffs a k) {w : ℂ}
    (hsum : Summable fun n : ℕ => ‖a n‖ ^ 2 * (n : ℝ) ^ (-w.re)) :
    ∑' n : ℕ, (‖a n‖ ^ 2 : ℂ) / (n : ℂ) ^ w
      = ∏' p : Nat.Primes, ∑' e : ℕ, (‖a ((p : ℕ) ^ e)‖ ^ 2 : ℂ) / ((p : ℕ) ^ e : ℂ) ^ w := by
  have hmul : ((normSqAF h).pmul (cpowAF w)).IsMultiplicative :=
    (isMultiplicative_normSq h).pmul (isMultiplicative_cpowAF w)
  have hval : ∀ n : ℕ, ((normSqAF h).pmul (cpowAF w)) n = (‖a n‖ ^ 2 : ℂ) / (n : ℂ) ^ w := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [normSqAF, cpowAF, h.zero]
    · simp only [ArithmeticFunction.pmul_apply, normSqAF, cpowAF, ArithmeticFunction.coe_mk,
        if_neg hn]
      rw [Complex.cpow_neg, div_eq_mul_inv]
  have hgsum : Summable (fun n => ‖((normSqAF h).pmul (cpowAF w)) n‖) := by
    refine hsum.congr (fun n => ?_)
    rcases eq_or_ne n 0 with rfl | hn
    · simp [normSqAF, cpowAF, h.zero]
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      simp only [ArithmeticFunction.pmul_apply, normSqAF, cpowAF, ArithmeticFunction.coe_mk,
        if_neg hn, norm_mul]
      rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
          Complex.norm_natCast_cpow_of_pos hnpos, Complex.neg_re]
  have hEP := hmul.eulerProduct_tprod hgsum
  calc ∑' n : ℕ, (‖a n‖ ^ 2 : ℂ) / (n : ℂ) ^ w
      = ∑' n : ℕ, ((normSqAF h).pmul (cpowAF w)) n := (tsum_congr hval).symm
    _ = ∏' p : Nat.Primes, ∑' e : ℕ, ((normSqAF h).pmul (cpowAF w)) ((p : ℕ) ^ e) := hEP.symm
    _ = ∏' p : Nat.Primes, ∑' e : ℕ, (‖a ((p : ℕ) ^ e)‖ ^ 2 : ℂ) / ((p : ℕ) ^ e : ℂ) ^ w := by
          refine tprod_congr fun p => tsum_congr fun e => ?_
          rw [hval ((p : ℕ) ^ e), Nat.cast_pow]

/-- **Satisfiability witness** for `IsHeckeEigenCoeffs`. The Eisenstein coefficient sequence
    `a(n) = σ₁(n)` (the sum-of-divisors function) satisfies all four Hecke-eigenform relations at
    weight `k = 2`: `σ₁(0) = 0`, `σ₁(1) = 1`, multiplicativity on coprime arguments, and the
    prime-power recursion `σ₁(p^{r+2}) = σ₁(p)·σ₁(p^{r+1}) − p·σ₁(p^r)`. Hence the hypothesis is
    consistent and every theorem taking `IsHeckeEigenCoeffs` as a hypothesis is non-vacuous. -/
theorem isHeckeEigenCoeffs_sigma :
    IsHeckeEigenCoeffs (fun n => (ArithmeticFunction.sigma 1 n : ℂ)) 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · intro m n hmn
    simp only [ArithmeticFunction.isMultiplicative_sigma.2 hmn, Nat.cast_mul]
  · intro p r hp
    have hx1 : (p : ℂ) ≠ 1 := by
      rw [Ne, Nat.cast_eq_one]
      exact hp.one_lt.ne'
    have hx1' : (p : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr hx1
    have hsp : (ArithmeticFunction.sigma 1 p : ℂ) = ∑ k ∈ Finset.range 2, (p : ℂ) ^ k := by
      have h := ArithmeticFunction.sigma_one_apply_prime_pow (p := p) (i := 1) hp
      rw [pow_one] at h
      rw [h]; push_cast; ring
    simp only [ArithmeticFunction.sigma_one_apply_prime_pow hp, show ((2 : ℤ) - 1) = 1 by ring,
      zpow_one, Nat.cast_sum, Nat.cast_pow, hsp]
    rw [geom_sum_eq hx1, geom_sum_eq hx1, geom_sum_eq hx1, geom_sum_eq hx1]
    field_simp
    ring

end

end RankinSelbergDelta.RankinSelberg
