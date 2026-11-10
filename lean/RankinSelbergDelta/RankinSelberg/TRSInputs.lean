import Mathlib
import RankinSelbergDelta.Shared.MertensLocal
import RankinSelbergDelta.RankinSelberg.TRS

/-!
# Discharging the hypotheses of the abstract nonvanishing theorem

A residue limit `(s − 1) G(s) → c` at `s = 1` gives the pole hypothesis (`dlVP_pole_isBigO`), and
nonnegative logarithmic coefficients give the 3-4-1 product bound (`dlvpProduct_ge_one`); together
they give `dlvpG_ne_zero`.
-/
namespace RankinSelbergDelta.RankinSelberg

open Complex Asymptotics Filter Topology

/-- **The pole input.** If `(s-1)·G(s) → c` as `s → 1` (a simple pole / finite residue at 1),
    then `G(1+x) = O(1/x)` as `x → 0⁺` -- hypothesis `H2` of `trs_ne_zero`. -/
lemma dlVP_pole_isBigO {G : ℂ → ℂ} {c : ℂ}
    (hres : Tendsto (fun s : ℂ ↦ (s - 1) * G s) (𝓝[≠] 1) (𝓝 c)) :
    (fun x : ℝ ↦ G (1 + x)) =O[𝓝[>] 0] fun x : ℝ ↦ (1 : ℂ) / x := by
  have hC : (fun w : ℂ ↦ G (1 + w)) =O[𝓝[≠] 0] (1 / ·) := by
    have H : Tendsto (fun w : ℂ ↦ w * G (1 + w)) (𝓝[≠] 0) (𝓝 c) := by
      convert hres.comp (f := fun w : ℂ ↦ 1 + w) ?_ using 1
      · simp only [Function.comp_def, add_sub_cancel_left]
      · simpa only [tendsto_iff_comap, Homeomorph.coe_addLeft, add_zero, map_le_iff_le_comap]
          using ((Homeomorph.addLeft (1 : ℂ)).map_punctured_nhds_eq 0).le
    exact (isBigO_mul_iff_isBigO_div eventually_mem_nhdsWithin).mp (H.isBigO_one ℂ)
  exact (Complex.isBigO_comp_ofReal_nhds_ne hC).mono (nhdsGT_le_nhdsNE 0)

/-! ### Discharging the product bound H1 from nonnegative von Mangoldt coefficients.

`G` is presented as the exponential of its log-series `∑' n, Λ(n)/(n^s log n)`; then `‖G(s)‖` is
the exponential of the real part of that series, and the 3-4-1 combination of the three real parts
at `1+x`, `1+x+iy`, `1+x+2iy` (which share the real part `1+x`, hence the same weight) is
`∑' w_n (3 + 4cos(y log n) + cos(2y log n)) ≥ 0`, giving `‖product‖ = exp(that) ≥ 1`. -/

/-- The summand of the de la Vallée Poussin log-series: `Λ(n)/log n · e^{-s log n}` for `n ≥ 2`. -/
noncomputable def dlvpTerm (Λ : ℕ → ℝ) (s : ℂ) (n : ℕ) : ℂ :=
  if 2 ≤ n then ((Λ n : ℂ) / (Real.log n : ℂ)) * Complex.exp (-(s * (Real.log n : ℂ))) else 0

/-- The real weight `w_n(σ) = Λ(n)/(n^σ log n)`, nonnegative for `Λ ≥ 0`. -/
noncomputable def dlvpWeight (Λ : ℕ → ℝ) (σ : ℝ) (n : ℕ) : ℝ :=
  if 2 ≤ n then Λ n / ((n : ℝ) ^ σ * Real.log n) else 0

/-- `G = exp(∑ term)`: an Euler product presented as the exponential of its log-series. -/
noncomputable def dlvpG (Λ : ℕ → ℝ) (s : ℂ) : ℂ := Complex.exp (∑' n, dlvpTerm Λ s n)

/-- The real part of the summand is the weight times `cos(s.im · log n)`. -/
lemma re_dlvpTerm (Λ : ℕ → ℝ) (s : ℂ) (n : ℕ) :
    (dlvpTerm Λ s n).re = dlvpWeight Λ s.re n * Real.cos (s.im * Real.log n) := by
  by_cases h : 2 ≤ n
  · have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast h
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hlog : (0 : ℝ) < Real.log n := Real.log_pos hn1
    simp only [dlvpTerm, dlvpWeight, if_pos h]
    rw [← Complex.ofReal_div, Complex.re_ofReal_mul, Complex.exp_re]
    have hzre : (-(s * (Real.log n : ℂ))).re = -(s.re * Real.log n) := by
      rw [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring
    have hzim : (-(s * (Real.log n : ℂ))).im = -(s.im * Real.log n) := by
      rw [Complex.neg_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; ring
    rw [hzre, hzim, Real.cos_neg,
      show Real.exp (-(s.re * Real.log n)) = (n : ℝ) ^ (-s.re) by
        rw [Real.rpow_def_of_pos hnpos]; congr 1; ring,
      Real.rpow_neg hnpos.le]
    field_simp
  · simp [dlvpTerm, dlvpWeight, if_neg h]

/-- `‖G(s)‖ = exp(∑' Re(term))` when the series is summable. -/
lemma norm_dlvpG {Λ : ℕ → ℝ} {s : ℂ} (hsum : Summable (dlvpTerm Λ s)) :
    ‖dlvpG Λ s‖ = Real.exp (∑' n, (dlvpTerm Λ s n).re) := by
  rw [dlvpG, Complex.norm_exp, ← Complex.re_tsum hsum]

/-- The weight is nonnegative when `Λ ≥ 0`. -/
lemma dlvpWeight_nonneg {Λ : ℕ → ℝ} (hΛ : ∀ n, 0 ≤ Λ n) (σ : ℝ) (n : ℕ) :
    0 ≤ dlvpWeight Λ σ n := by
  by_cases h : 2 ≤ n
  · have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast h
    simp only [dlvpWeight, if_pos h]
    exact div_nonneg (hΛ n)
      (mul_nonneg (Real.rpow_nonneg (by linarith) σ) (Real.log_pos hn1).le)
  · simp [dlvpWeight, if_neg h]

/-- **The product bound (H1).** For nonnegative `Λ` with the log-series summable at the three evaluation points,
    the de la Vallée Poussin product bound holds: `1 ≤ ‖G(1+x)³ G(1+x+iy)⁴ G(1+x+2iy)‖`. -/
lemma dlvpProduct_ge_one {Λ : ℕ → ℝ} (hΛ : ∀ n, 0 ≤ Λ n) {x y : ℝ}
    (hs0 : Summable (dlvpTerm Λ (1 + x)))
    (hs1 : Summable (dlvpTerm Λ (1 + x + I * y)))
    (hs2 : Summable (dlvpTerm Λ (1 + x + 2 * I * y))) :
    1 ≤ ‖dlvpG Λ (1 + x) ^ 3 * dlvpG Λ (1 + x + I * y) ^ 4 *
        dlvpG Λ (1 + x + 2 * I * y)‖ := by
  have v0 : ∀ n, (dlvpTerm Λ (1 + x) n).re = dlvpWeight Λ (1 + x) n := by
    intro n
    rw [re_dlvpTerm]
    have : ((1 : ℂ) + (x : ℂ)).re = 1 + x := by simp
    rw [this, show ((1 : ℂ) + (x : ℂ)).im = 0 by simp, zero_mul, Real.cos_zero, mul_one]
  have v1 : ∀ n, (dlvpTerm Λ (1 + x + I * y) n).re
      = dlvpWeight Λ (1 + x) n * Real.cos (y * Real.log n) := by
    intro n
    rw [re_dlvpTerm, show ((1 : ℂ) + (x : ℂ) + I * (y : ℂ)).re = 1 + x by simp,
      show ((1 : ℂ) + (x : ℂ) + I * (y : ℂ)).im = y by simp]
  have v2 : ∀ n, (dlvpTerm Λ (1 + x + 2 * I * y) n).re
      = dlvpWeight Λ (1 + x) n * Real.cos (2 * (y * Real.log n)) := by
    intro n
    rw [re_dlvpTerm, show ((1 : ℂ) + (x : ℂ) + 2 * I * (y : ℂ)).re = 1 + x by simp,
      show ((1 : ℂ) + (x : ℂ) + 2 * I * (y : ℂ)).im = 2 * y by simp, mul_assoc]
  have R0 : Summable (fun n ↦ (dlvpTerm Λ (1 + x) n).re) := (Complex.hasSum_re hs0.hasSum).summable
  have R1 : Summable (fun n ↦ (dlvpTerm Λ (1 + x + I * y) n).re) := (Complex.hasSum_re hs1.hasSum).summable
  have R2 : Summable (fun n ↦ (dlvpTerm Λ (1 + x + 2 * I * y) n).re) := (Complex.hasSum_re hs2.hasSum).summable
  have key : (0 : ℝ) ≤ 3 * (∑' n, (dlvpTerm Λ (1 + x) n).re)
      + 4 * (∑' n, (dlvpTerm Λ (1 + x + I * y) n).re)
      + ∑' n, (dlvpTerm Λ (1 + x + 2 * I * y) n).re := by
    rw [← tsum_mul_left, ← tsum_mul_left,
      ← (R0.mul_left 3).tsum_add (R1.mul_left 4),
      ← ((R0.mul_left 3).add (R1.mul_left 4)).tsum_add R2]
    refine tsum_nonneg (fun n ↦ ?_)
    rw [v0, v1, v2]
    have hwn : 0 ≤ dlvpWeight Λ (1 + x) n := dlvpWeight_nonneg hΛ _ n
    have hm : 0 ≤ 3 + 4 * Real.cos (y * Real.log n) + Real.cos (2 * (y * Real.log n)) :=
      RankinSelbergDelta.Shared.mertens341_nonneg _
    nlinarith [mul_nonneg hwn hm]
  rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_dlvpG hs0, norm_dlvpG hs1, norm_dlvpG hs2,
    ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
  exact Real.one_le_exp (by push_cast; linarith [key])

/-- **de la Vallée Poussin nonvanishing for an exponential Euler product** (the Lean analogue of
    Leung, arXiv:2410.09910, Theorem 2.1 at `σ = 1`). If `Λ ≥ 0`, the log-series is summable at
    `1+x`, `1+x+iy`, `1+x+2iy` for every `x > 0`, `dlvpG Λ` has a finite residue at `s = 1` (a
    simple pole) and is differentiable at `1+iy` and continuous at `1+2iy`, then
    `dlvpG Λ (1+iy) ≠ 0`. Chains `dlvpProduct_ge_one` (H1), `dlVP_pole_isBigO` (H2) and
    `trs_ne_zero`. The residue/regularity hypotheses are exactly what the Rankin–Selberg continuation
    supplies; the product positivity is discharged from `Λ ≥ 0`. -/
theorem dlvpG_ne_zero {Λ : ℕ → ℝ} (hΛ : ∀ n, 0 ≤ Λ n) {y : ℝ} {c : ℂ}
    (hsum : ∀ x : ℝ, 0 < x → Summable (dlvpTerm Λ (1 + x)) ∧
      Summable (dlvpTerm Λ (1 + x + I * y)) ∧ Summable (dlvpTerm Λ (1 + x + 2 * I * y)))
    (hres : Tendsto (fun s : ℂ ↦ (s - 1) * dlvpG Λ s) (𝓝[≠] 1) (𝓝 c))
    (hdiff : DifferentiableAt ℂ (dlvpG Λ) (1 + I * y))
    (hcont : ContinuousAt (dlvpG Λ) (1 + 2 * I * y)) :
    dlvpG Λ (1 + I * y) ≠ 0 := by
  refine trs_ne_zero (G := dlvpG Λ) (fun x hx ↦ ?_) (dlVP_pole_isBigO hres) hdiff hcont
  exact dlvpProduct_ge_one hΛ (hsum x hx).1 (hsum x hx).2.1 (hsum x hx).2.2

end RankinSelbergDelta.RankinSelberg
