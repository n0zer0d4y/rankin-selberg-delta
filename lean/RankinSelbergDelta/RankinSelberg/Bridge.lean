import Mathlib
import RankinSelbergDelta.RankinSelberg.TRSInputs
import RankinSelbergDelta.Continuation.ZetaResidue

/-!
# The Euler product of ζ as an exponential

`∑' n, (Λ(n) / log n) n^{−s} = ∑' p, −log(1 − p^{−s})` for `Re s > 1`, so the abstract de la
Vallée Poussin function built from the von Mangoldt coefficients is `riemannZeta`. Instantiating
`dlvpG_ne_zero` then gives `ζ(1 + iy) ≠ 0`, a check of the abstract theorem on ζ.
-/
namespace RankinSelbergDelta.RankinSelberg

open Complex Filter Topology ArithmeticFunction

/-- `(n:ℂ)^(-s) = exp(-(s·log n))` for `n ≥ 1` — the cpow/exp bridge matching `dlvpTerm`'s form. -/
lemma natCast_cpow_neg_eq_exp {n : ℕ} (hn : 1 ≤ n) {s : ℂ} :
    (n : ℂ) ^ (-s) = Complex.exp (-(s * (Real.log n : ℂ))) := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hn)
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    rw [Complex.ofReal_log (by positivity : (0:ℝ) ≤ (n : ℝ)), Complex.ofReal_natCast]
  rw [Complex.cpow_def_of_ne_zero hn0, hlog]; congr 1; ring

/-- The `dlvpTerm` of the von Mangoldt coefficients at a prime power `p^(k+1)` is
    `(p^{-s})^(k+1)/(k+1)`. -/
lemma dlvpTerm_vonMangoldt_primePow (p : Nat.Primes) (k : ℕ) {s : ℂ} :
    dlvpTerm (fun m => ArithmeticFunction.vonMangoldt m) s ((p : ℕ) ^ (k + 1))
      = ((p : ℂ) ^ (-s)) ^ (k + 1) / ((k : ℂ) + 1) := by
  have hp1 : 1 ≤ (p : ℕ) := p.2.one_lt.le
  have hp2 : 2 ≤ (p : ℕ) ^ (k + 1) :=
    le_trans p.2.two_le (Nat.le_self_pow (Nat.succ_ne_zero k) _)
  have hplog : (0 : ℝ) < Real.log (p : ℕ) := Real.log_pos (by exact_mod_cast p.2.one_lt)
  have hcoeffR : (ArithmeticFunction.vonMangoldt ((p : ℕ) ^ (k + 1))
      / Real.log ((p : ℕ) ^ (k + 1)) : ℝ) = 1 / ((k : ℝ) + 1) := by
    rw [ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero k),
      ArithmeticFunction.vonMangoldt_apply_prime p.2, Real.log_pow,
      Nat.cast_add, Nat.cast_one, mul_comm ((k : ℝ) + 1) (Real.log (p : ℕ)),
      ← div_div, div_self hplog.ne']
  have hlogR : Real.log ((p : ℕ) ^ (k + 1)) = ((k : ℝ) + 1) * Real.log (p : ℕ) := by
    rw [Real.log_pow]; push_cast; ring
  unfold dlvpTerm
  rw [if_pos hp2]
  simp only [Nat.cast_pow]
  rw [← Complex.ofReal_div, hcoeffR, hlogR,
    Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_natCast]
  rw [show -(s * (((k : ℂ) + 1) * (Real.log (p : ℕ) : ℂ)))
        = ((k + 1 : ℕ) : ℂ) * (-(s * (Real.log (p : ℕ) : ℂ))) by push_cast; ring,
    Complex.exp_nat_mul, ← natCast_cpow_neg_eq_exp hp1,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_add, Complex.ofReal_natCast]
  push_cast; ring

/-- The per-prime Taylor sum: `∑' k, (p^{-s})^(k+1)/(k+1) = -log(1 - p^{-s})` for `Re s > 1`. -/
lemma tsum_taylor_primePow (p : Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    ∑' k : ℕ, ((p : ℂ) ^ (-s)) ^ (k + 1) / ((k : ℂ) + 1)
      = -Complex.log (1 - (p : ℂ) ^ (-s)) := by
  set z : ℂ := (p : ℂ) ^ (-s) with hz_def
  have hz : ‖z‖ < 1 := by
    rw [hz_def, show ((p : ℂ)) = (((p : ℕ) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast p.2.pos)]
    simp only [Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.2.one_lt) (by linarith)
  have h := hasSum_taylorSeries_neg_log hz
  have h2 := (hasSum_nat_add_iff' 1).mpr h
  simp only [Finset.sum_range_one, pow_zero, Nat.cast_zero, div_zero, sub_zero] at h2
  rw [← h2.tsum_eq]
  refine tsum_congr (fun k => ?_)
  push_cast; ring

/-- Summability of the per-prime Taylor series (used in the core). -/
lemma summable_taylor_primePow (p : Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun k : ℕ => ((p : ℂ) ^ (-s)) ^ (k + 1) / ((k : ℂ) + 1)) := by
  have hz : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [show ((p : ℂ)) = (((p : ℕ) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast p.2.pos)]
    simp only [Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.2.one_lt) (by linarith)
  have h2 := (hasSum_nat_add_iff' (f := fun n : ℕ => ((p : ℂ) ^ (-s)) ^ n / (n : ℂ)) 1).mpr
    (hasSum_taylorSeries_neg_log hz)
  simp only [Finset.sum_range_one, pow_zero, Nat.cast_zero, div_zero, sub_zero] at h2
  exact h2.summable.congr (fun k => by push_cast; ring)

/-- The core sum identity: the de la Vallée Poussin log-series of the von Mangoldt coefficients
    equals the sum of `-log(1 - p^{-s})` over primes. -/
lemma tsum_dlvpTerm_vonMangoldt {s : ℂ} (hs : 1 < s.re) :
    ∑' n, dlvpTerm (fun m => ArithmeticFunction.vonMangoldt m) s n
      = ∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-s)) := by
  set f : ℕ → ℂ := fun n => dlvpTerm (fun m => ArithmeticFunction.vonMangoldt m) s n with hf
  -- (1) `f` vanishes off prime powers.
  have hsupp : Function.support f ⊆ {n | IsPrimePow n} := by
    intro n hn
    by_contra hnp
    refine hn ?_
    have hΛ : ArithmeticFunction.vonMangoldt n = 0 :=
      not_not.mp fun h => hnp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp h)
    show f n = 0
    simp only [hf, dlvpTerm, hΛ]
    split <;> simp
  -- (2) the reindexed product function equals `f ∘ prodNatEquiv`.
  have hval : ∀ y : Nat.Primes × ℕ, f (Nat.Primes.prodNatEquiv y : ℕ)
      = ((y.1 : ℂ) ^ (-s)) ^ (y.2 + 1) / ((y.2 : ℂ) + 1) := by
    rintro ⟨p, k⟩
    rw [hf, Nat.Primes.prodNatEquiv_apply]
    exact dlvpTerm_vonMangoldt_primePow p k
  -- (3) joint summability (comparison to the von Mangoldt L-series).
  have hsummable_f : Summable f := by
    refine Summable.of_norm_bounded
      ((LSeriesSummable_vonMangoldt hs).norm.mul_left (Real.log 2)⁻¹) ?_
    intro n
    rcases lt_or_ge n 2 with hn | hn
    · simp only [hf, dlvpTerm, if_neg (not_le.mpr hn), norm_zero]
      positivity
    · have hn1 : 1 ≤ n := le_trans (by norm_num) hn
      have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
      have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      have hfn : f n = (Real.log n : ℂ)⁻¹ * LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) s n := by
        rw [hf]
        show dlvpTerm (fun m => ArithmeticFunction.vonMangoldt m) s n = _
        unfold dlvpTerm
        rw [if_pos hn]
        simp only []
        rw [LSeries.term_of_ne_zero (show n ≠ 0 by omega), ← natCast_cpow_neg_eq_exp hn1,
          Complex.cpow_neg]
        ring
      rw [hfn, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg (by exact_mod_cast hn1))]
      gcongr
  have hsummable_prod : Summable (fun y : Nat.Primes × ℕ =>
      ((y.1 : ℂ) ^ (-s)) ^ (y.2 + 1) / ((y.2 : ℂ) + 1)) := by
    refine ((Equiv.summable_iff Nat.Primes.prodNatEquiv).mpr (hsummable_f.subtype _)).congr ?_
    intro y; rw [← hval y]; rfl
  -- (4) assemble.
  calc ∑' n, f n
      = ∑' x : {n // IsPrimePow n}, f x.val := (tsum_subtype_eq_of_support_subset hsupp).symm
    _ = ∑' y : Nat.Primes × ℕ, f (Nat.Primes.prodNatEquiv y : ℕ) :=
        (Equiv.tsum_eq Nat.Primes.prodNatEquiv (fun x => f x.val)).symm
    _ = ∑' y : Nat.Primes × ℕ, ((y.1 : ℂ) ^ (-s)) ^ (y.2 + 1) / ((y.2 : ℂ) + 1) :=
        tsum_congr hval
    _ = ∑' p : Nat.Primes, ∑' k : ℕ, ((p : ℂ) ^ (-s)) ^ (k + 1) / ((k : ℂ) + 1) :=
        hsummable_prod.tsum_prod' (fun p => summable_taylor_primePow p hs)
    _ = ∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-s)) :=
        tsum_congr (fun p => tsum_taylor_primePow p hs)

/-- **The ζ bridge**: `dlvpG vonMangoldt s = riemannZeta s` for `Re s > 1`. -/
theorem dlvpG_vonMangoldt_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    dlvpG (fun n => ArithmeticFunction.vonMangoldt n) s = riemannZeta s := by
  rw [dlvpG, tsum_dlvpTerm_vonMangoldt hs]
  exact riemannZeta_eulerProduct_exp_log hs

/-- `Summable` of the von Mangoldt de la Vallée Poussin log-series for `Re s > 1`
    (comparison to the von Mangoldt L-series). -/
lemma summable_dlvpTerm_vonMangoldt {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n => dlvpTerm (fun m => ArithmeticFunction.vonMangoldt m) s n) := by
  refine Summable.of_norm_bounded
    ((LSeriesSummable_vonMangoldt hs).norm.mul_left (Real.log 2)⁻¹) ?_
  intro n
  rcases lt_or_ge n 2 with hn | hn
  · simp only [dlvpTerm, if_neg (not_le.mpr hn), norm_zero]
    positivity
  · have hn1 : 1 ≤ n := le_trans (by norm_num) hn
    have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hfn : dlvpTerm (fun m => ArithmeticFunction.vonMangoldt m) s n
        = (Real.log n : ℂ)⁻¹ * LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) s n := by
      unfold dlvpTerm
      rw [if_pos hn]
      simp only []
      rw [LSeries.term_of_ne_zero (show n ≠ 0 by omega), ← natCast_cpow_neg_eq_exp hn1,
        Complex.cpow_neg]
      ring
    rw [hfn, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg (Real.log_nonneg (by exact_mod_cast hn1))]
    gcongr

/-- **End-to-end: ζ does not vanish on the line `Re s = 1`, through the toolkit** (`trs_ne_zero`
    with `G = riemannZeta`: the 3-4-1 product bound from the ζ bridge + `dlvpProduct_ge_one`, the
    simple pole from `riemannZeta_residue_one`, regularity off `1` from `differentiableAt_riemannZeta`).
    Reproduces Mathlib's `riemannZeta_ne_zero_of_one_le_re` on the line through the de la Vallée
    Poussin chain — the first end-to-end run of the toolkit on a concrete L-function. -/
theorem riemannZeta_ne_zero_via_toolkit {y : ℝ} (hy : y ≠ 0) :
    riemannZeta (1 + Complex.I * y) ≠ 0 := by
  refine trs_ne_zero (G := riemannZeta) (y := y) (fun x hx => ?_) ?_ ?_ ?_
  · have h0 : 1 < ((1 : ℂ) + x).re := by simp; linarith
    have h1 : 1 < ((1 : ℂ) + x + Complex.I * y).re := by simp; linarith
    have h2 : 1 < ((1 : ℂ) + x + 2 * Complex.I * y).re := by simp; linarith
    rw [← dlvpG_vonMangoldt_eq_riemannZeta h0, ← dlvpG_vonMangoldt_eq_riemannZeta h1,
      ← dlvpG_vonMangoldt_eq_riemannZeta h2]
    exact dlvpProduct_ge_one (fun n => ArithmeticFunction.vonMangoldt_nonneg)
      (summable_dlvpTerm_vonMangoldt h0) (summable_dlvpTerm_vonMangoldt h1)
      (summable_dlvpTerm_vonMangoldt h2)
  · exact dlVP_pole_isBigO riemannZeta_residue_one
  · exact differentiableAt_riemannZeta (by simpa [Complex.ext_iff] using hy)
  · exact (differentiableAt_riemannZeta (by simpa [Complex.ext_iff] using hy)).continuousAt

end RankinSelbergDelta.RankinSelberg
