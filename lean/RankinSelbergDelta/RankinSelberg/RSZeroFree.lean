import RankinSelbergDelta.RankinSelberg.ArchimedeanKernel
import RankinSelbergDelta.RankinSelberg.ZeroFreeRegion

/-!
# The zero-free region of the Rankin–Selberg square

For a level-one Hecke eigenform `f` of weight `k > 0`, `G(s) = ζ(2s) D(s + k − 1)` has no zero
`β + iγ` with `3/4 < β < 1`, `|γ| ≥ t₀` and `β > 1 − 1/(160 C log |γ|)` (`rs_zero_free_region`).
The four de la Vallée Poussin inputs are assembled through `zero_free_of_logDeriv_341`.
-/

open scoped UpperHalfPlane Topology
open Complex

namespace RankinSelbergDelta.RankinSelberg

/-- The `dlvp` log-series as an `LSeries` coefficient: `c(n) = Λ(n)/log n` for `n ≥ 2`, else `0`. -/
noncomputable def dlvpCoeff (Λ : ℕ → ℝ) (n : ℕ) : ℂ :=
  if 2 ≤ n then (Λ n : ℂ) / (Real.log n : ℂ) else 0

/-- `dlvpTerm` is the `LSeries` term of `dlvpCoeff`. -/
lemma dlvpTerm_eq_term (Λ : ℕ → ℝ) (s : ℂ) (n : ℕ) :
    dlvpTerm Λ s n = LSeries.term (dlvpCoeff Λ) s n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [dlvpTerm, LSeries.term]
  · rw [LSeries.term_of_ne_zero hn.ne', dlvpTerm, dlvpCoeff]
    by_cases h2 : 2 ≤ n
    · rw [if_pos h2, if_pos h2]
      have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
      have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
        rw [← Complex.ofReal_natCast n, ← Complex.ofReal_log (by positivity)]
      have hcpow : (n : ℂ) ^ s = Complex.exp (s * (Real.log n : ℂ)) := by
        rw [Complex.cpow_def_of_ne_zero hn0, hlog, mul_comm]
      rw [hcpow, Complex.exp_neg, ← div_eq_mul_inv]
    · rw [if_neg h2, if_neg h2, zero_div]

/-- `∑' dlvpTerm = LSeries (dlvpCoeff)`. -/
lemma tsum_dlvpTerm_eq_LSeries (Λ : ℕ → ℝ) (s : ℂ) :
    (∑' n, dlvpTerm Λ s n) = LSeries (dlvpCoeff Λ) s :=
  tsum_congr (dlvpTerm_eq_term Λ s)

/-- `dlvpG Λ s = exp(LSeries (dlvpCoeff Λ) s)`. -/
lemma dlvpG_eq_exp_LSeries (Λ : ℕ → ℝ) (s : ℂ) :
    dlvpG Λ s = Complex.exp (LSeries (dlvpCoeff Λ) s) := by
  rw [dlvpG, tsum_dlvpTerm_eq_LSeries]

variable {F : Type*} [FunLike F ℍ ℂ] (k : ℤ)
  [cf : CuspFormClass F (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma 1)) k]

include cf in
/-- The abscissa of absolute convergence of the `dlvp` coefficient of the RS square is `≤ 1`. -/
lemma abscissaOfAbsConv_dlvpCoeff_rs_le (f : F) (hk : 0 < k)
    (hf : IsHeckeEigenCoeffs (rsCoeff f) k) :
    LSeries.abscissaOfAbsConv (dlvpCoeff (rsVonMangoldt (rsCoeff f) k)) ≤ 1 := by
  refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy => ?_
  have hsum := summable_dlvpTerm_rs k f hk hf (s := (y : ℂ)) (by simpa using hy)
  have : Summable (LSeries.term (dlvpCoeff (rsVonMangoldt (rsCoeff f) k)) (y : ℂ)) :=
    hsum.congr (dlvpTerm_eq_term _ _)
  exact this

include cf in
/-- **The Euler-product → log-derivative identity.** -/
lemma neg_logDeriv_dlvpG_rs (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k)
    {s : ℂ} (hs : 1 < s.re) :
    -deriv (dlvpG (rsVonMangoldt (rsCoeff f) k)) s / dlvpG (rsVonMangoldt (rsCoeff f) k) s
      = LSeries (LSeries.logMul (dlvpCoeff (rsVonMangoldt (rsCoeff f) k))) s := by
  set Λ := rsVonMangoldt (rsCoeff f) k with hΛ
  have habs : LSeries.abscissaOfAbsConv (dlvpCoeff Λ) < (s.re : EReal) := by
    refine lt_of_le_of_lt (abscissaOfAbsConv_dlvpCoeff_rs_le k f hk hf) ?_
    exact_mod_cast hs
  have hderiv : HasDerivAt (LSeries (dlvpCoeff Λ))
      (-LSeries (LSeries.logMul (dlvpCoeff Λ)) s) s :=
    LSeries_hasDerivAt habs
  have hG : HasDerivAt (dlvpG Λ)
      (Complex.exp (LSeries (dlvpCoeff Λ) s) * (-LSeries (LSeries.logMul (dlvpCoeff Λ)) s)) s := by
    have hc := hderiv.cexp
    rw [show dlvpG Λ = (fun z => Complex.exp (LSeries (dlvpCoeff Λ) z)) from
      funext (dlvpG_eq_exp_LSeries Λ)]
    exact hc
  rw [hG.deriv, dlvpG_eq_exp_LSeries, div_eq_iff (Complex.exp_ne_zero _)]
  ring

/-- The real part of a real-coefficient Dirichlet term. -/
lemma re_cdiv_cpow (c σ t : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ((c : ℂ) / (n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I)).re
      = c * (n : ℝ) ^ (-σ) * Real.cos (t * Real.log n) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    rw [← Complex.ofReal_natCast n, ← Complex.ofReal_log hnpos.le]
  have hcpow : (n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I)
      = Complex.exp ((Real.log n : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
    rw [Complex.cpow_def_of_ne_zero hn0, hlog]
  rw [hcpow, div_eq_mul_inv, ← Complex.exp_neg, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.exp_re]
  have hw_re : (-((Real.log n : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I))).re
      = -(Real.log n) * σ := by
    simp only [Complex.neg_re, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hw_im : (-((Real.log n : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I))).im
      = -(Real.log n * t) := by
    simp only [Complex.neg_im, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [hw_re, hw_im, Real.cos_neg, zero_mul, sub_zero, Real.rpow_neg hnpos.le,
    Real.rpow_def_of_pos hnpos]
  rw [show Real.log n * σ = σ * Real.log n from by ring]
  rw [show -(Real.log n) * σ = -(σ * Real.log n) from by ring, Real.exp_neg,
    show Real.log n * t = t * Real.log n from by ring]
  ring

/-- `logMul` of the `dlvp` coefficient is the von Mangoldt coefficient. -/
lemma logMul_dlvpCoeff (Λ : ℕ → ℝ) (n : ℕ) :
    LSeries.logMul (dlvpCoeff Λ) n = if 2 ≤ n then (Λ n : ℂ) else 0 := by
  unfold LSeries.logMul dlvpCoeff
  by_cases h2 : 2 ≤ n
  · rw [if_pos h2, if_pos h2]
    have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
      rw [← Complex.ofReal_natCast n, ← Complex.ofReal_log (by positivity)]
    have hlogn : (Real.log n : ℂ) ≠ 0 := by
      have : (1 : ℝ) < n := by exact_mod_cast h2
      exact_mod_cast ne_of_gt (Real.log_pos this)
    rw [hlog, ← mul_div_assoc, mul_comm, mul_div_assoc, div_self hlogn, mul_one]
  · rw [if_neg h2, if_neg h2, mul_zero]

/-- `rsVonMangoldt` vanishes below `2`. -/
lemma rsVonMangoldt_eq_zero_lt_two (a : ℕ → ℂ) (k : ℤ) {n : ℕ} (hn : n < 2) :
    rsVonMangoldt a k n = 0 := by
  have h : ¬ IsPrimePow n := by
    interval_cases n
    · exact not_isPrimePow_zero
    · exact not_isPrimePow_one
  rw [rsVonMangoldt, if_neg h]

include cf in
/-- **The von Mangoldt log-derivative real part as a cosine series.** -/
lemma re_neg_logDeriv_rs (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k)
    (σ t : ℝ) (hσ : 1 < σ) :
    (-deriv (dlvpG (rsVonMangoldt (rsCoeff f) k)) ((σ : ℂ) + (t : ℂ) * Complex.I)
        / dlvpG (rsVonMangoldt (rsCoeff f) k) ((σ : ℂ) + (t : ℂ) * Complex.I)).re
      = ∑' n, rsVonMangoldt (rsCoeff f) k n / (n : ℝ) ^ σ * Real.cos (t * Real.log n) := by
  set Λ := rsVonMangoldt (rsCoeff f) k with hΛ
  have hsre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
  have habs : LSeries.abscissaOfAbsConv (LSeries.logMul (dlvpCoeff Λ))
      < ((σ : ℂ) + (t : ℂ) * Complex.I).re := by
    rw [LSeries.abscissaOfAbsConv_logMul, hsre]
    exact lt_of_le_of_lt (abscissaOfAbsConv_dlvpCoeff_rs_le k f hk hf) (by exact_mod_cast hσ)
  have hsum : Summable (LSeries.term (LSeries.logMul (dlvpCoeff Λ)) ((σ : ℂ) + (t : ℂ) * Complex.I)) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re habs
  rw [neg_logDeriv_dlvpG_rs k f hk hf (s := (σ : ℂ) + (t : ℂ) * Complex.I) (by rw [hsre]; exact hσ),
    LSeries, Complex.re_tsum hsum]
  refine tsum_congr (fun n => ?_)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hz : Λ 0 = 0 := by rw [hΛ]; exact rsVonMangoldt_eq_zero_lt_two (rsCoeff f) k (by norm_num)
    rw [LSeries.term_zero, hz]; simp
  · rw [LSeries.term_of_ne_zero hn.ne', logMul_dlvpCoeff]
    by_cases h2 : 2 ≤ n
    · rw [if_pos h2, re_cdiv_cpow _ σ t hn, Real.rpow_neg (by positivity), div_eq_mul_inv]
    · have hz : Λ n = 0 := by rw [hΛ]; exact rsVonMangoldt_eq_zero_lt_two (rsCoeff f) k (by omega)
      rw [if_neg h2, hz]; simp

include cf in
/-- **`h341` discharged for the concrete RS square** (`dlvpG` form). -/
lemma h341_dlvpG_rs (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k)
    (σ γ : ℝ) (hσ : 1 < σ) :
    0 ≤ 3 * (-deriv (dlvpG (rsVonMangoldt (rsCoeff f) k)) (σ : ℂ)
            / dlvpG (rsVonMangoldt (rsCoeff f) k) (σ : ℂ)).re
        + 4 * (-deriv (dlvpG (rsVonMangoldt (rsCoeff f) k)) ((σ : ℂ) + (γ : ℂ) * Complex.I)
            / dlvpG (rsVonMangoldt (rsCoeff f) k) ((σ : ℂ) + (γ : ℂ) * Complex.I)).re
        + (-deriv (dlvpG (rsVonMangoldt (rsCoeff f) k)) ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I)
            / dlvpG (rsVonMangoldt (rsCoeff f) k) ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I)).re := by
  have hP : (-deriv (dlvpG (rsVonMangoldt (rsCoeff f) k)) (σ : ℂ)
      / dlvpG (rsVonMangoldt (rsCoeff f) k) (σ : ℂ)).re
      = ∑' n, rsVonMangoldt (rsCoeff f) k n / (n : ℝ) ^ σ := by
    have h0 := re_neg_logDeriv_rs k f hk hf σ 0 hσ
    simp only [Complex.ofReal_zero, zero_mul, add_zero, Real.cos_zero, mul_one] at h0
    exact h0
  have hZ := re_neg_logDeriv_rs k f hk hf σ γ hσ
  have hW := re_neg_logDeriv_rs k f hk hf σ (2 * γ) hσ
  have hsum_c : Summable (LSeries.term
      (LSeries.logMul (dlvpCoeff (rsVonMangoldt (rsCoeff f) k))) (σ : ℂ)) := by
    apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
    rw [LSeries.abscissaOfAbsConv_logMul, show ((σ : ℂ)).re = σ from by simp]
    exact lt_of_le_of_lt (abscissaOfAbsConv_dlvpCoeff_rs_le k f hk hf) (by exact_mod_cast hσ)
  have hsummable_real : Summable (fun n => rsVonMangoldt (rsCoeff f) k n / (n : ℝ) ^ σ) := by
    rw [← Complex.summable_ofReal]
    refine hsum_c.congr (fun n => ?_)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [LSeries.term_zero, rsVonMangoldt_eq_zero_lt_two (rsCoeff f) k (by norm_num)]; simp
    · rw [LSeries.term_of_ne_zero hn.ne', logMul_dlvpCoeff]
      by_cases h2 : 2 ≤ n
      · rw [if_pos h2, Complex.ofReal_div, Complex.ofReal_cpow (by positivity),
          Complex.ofReal_natCast]
      · rw [if_neg h2, rsVonMangoldt_eq_zero_lt_two (rsCoeff f) k (by omega)]; simp
  rw [hP, hZ, hW]
  exact three_four_one_vonMangoldt (rsVonMangoldt_nonneg (rsCoeff f) k) σ γ hsummable_real

include cf in
/-- **The `dlvpG ↔ Gfull` conversion for the log-derivative** (`Re s > 1`). -/
lemma neg_re_logDeriv_Gfull_eq (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k)
    {s : ℂ} (hs : 1 < s.re) :
    -(logDeriv (Gfull k f) s).re
      = (-deriv (dlvpG (rsVonMangoldt (rsCoeff f) k)) s
          / dlvpG (rsVonMangoldt (rsCoeff f) k) s).re := by
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : Gfull k f =ᶠ[𝓝 s] dlvpG (rsVonMangoldt (rsCoeff f) k) := by
    filter_upwards [hopen.mem_nhds hs] with z hz
    rw [Gfull_eq k f hk hz, dlvpG_rs_eq k f hk hf hz]
  rw [logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds, neg_div, Complex.neg_re]

include cf in
/-- **`h341` in `logDeriv (Gfull)` form** (the shape the assembly needs). -/
lemma h341_Gfull_rs (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k)
    (σ γ : ℝ) (hσ : 1 < σ) :
    0 ≤ 3 * (-(logDeriv (Gfull k f) (σ : ℂ)).re)
        + 4 * (-(logDeriv (Gfull k f) ((σ : ℂ) + (γ : ℂ) * Complex.I)).re)
        + (-(logDeriv (Gfull k f) ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I)).re) := by
  rw [neg_re_logDeriv_Gfull_eq k f hk hf (s := (σ : ℂ)) (by simpa using hσ),
      neg_re_logDeriv_Gfull_eq k f hk hf (s := (σ : ℂ) + (γ : ℂ) * Complex.I) (by simpa using hσ),
      neg_re_logDeriv_Gfull_eq k f hk hf
        (s := (σ : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I) (by simpa using hσ)]
  exact h341_dlvpG_rs k f hk hf σ γ hσ

include cf in
/-- **The Rankin–Selberg zero-free region (modulo the simple-pole bound `hpole`).** Given the pole
bound `hpole_thm`, every zero `β + iγ` of `G = Gfull k f` with `3/4 < β < 1` and `|γ|` large is pushed
off the line: `β ≤ 1 − 1/(160 C log|γ|)`. -/
theorem rs_zero_free_region_of_pole (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k)
    (hpole_thm : ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      -(logDeriv (Gfull k f) (σ : ℂ)).re ≤ 1 / (σ - 1) + C) :
    ∃ C t₀ : ℝ, 0 < C ∧ 3 ≤ t₀ ∧ ∀ β γ : ℝ, 3 / 4 < β → β < 1 → t₀ ≤ |γ| →
      Gfull k f ((β : ℂ) + Complex.I * γ) = 0 →
      β ≤ 1 - 1 / (20 * (8 * C) * Real.log |γ|) := by
  obtain ⟨Cp, hCp, hpole⟩ := hpole_thm
  obtain ⟨Cw, tw, hCw, htw, hW⟩ := neg_re_logDeriv_Gfull_le k f hk hf
  obtain ⟨Cz, tz, hCz, htz, hzero⟩ := neg_re_logDeriv_Gfull_le_of_zero k f hk hf
  refine ⟨Cp + Cw + Cz, max (max tw tz) 3, by positivity, le_max_right _ _,
    fun β γ hβlo hβ1 hγ hρ => ?_⟩
  have hγtw : tw ≤ |γ| := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hγ
  have hγtz : tz ≤ |γ| := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hγ
  have hγ3 : (3 : ℝ) ≤ |γ| := le_trans (le_max_right _ _) hγ
  have hL : 1 ≤ Real.log |γ| := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact le_trans (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))) hγ3
  have hlognn : 0 ≤ Real.log |γ| := by linarith
  refine zero_free_of_logDeriv_341 hβlo hβ1 (by positivity : (0 : ℝ) < Cp + Cw + Cz) hL
    (fun σ => -(logDeriv (Gfull k f) (σ : ℂ)).re)
    (fun σ => -(logDeriv (Gfull k f) ((σ : ℂ) + (γ : ℂ) * Complex.I)).re)
    (fun σ => -(logDeriv (Gfull k f) ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I)).re)
    (fun σ hσ1 _ => h341_Gfull_rs k f hk hf σ γ hσ1)
    (fun σ hσ1 hσ2 => le_trans (hpole σ hσ1 hσ2) (by linarith)) ?_ ?_
  · intro σ hσ1 hσ2
    have h := hzero β γ hβlo hβ1 hγtz hρ σ hσ1 hσ2
    have hpt : (σ : ℂ) + Complex.I * γ = (σ : ℂ) + (γ : ℂ) * Complex.I := by ring
    rw [hpt] at h
    calc -(logDeriv (Gfull k f) ((σ : ℂ) + (γ : ℂ) * Complex.I)).re
        ≤ -(1 / (σ - β)) + Cz * Real.log |γ| := h
      _ ≤ -(1 / (σ - β)) + (Cp + Cw + Cz) * Real.log |γ| := by nlinarith [hlognn, hCp, hCw]
  · intro σ hσ1 hσ2
    have h := hW γ hγtw σ hσ1 hσ2
    have hpt : (σ : ℂ) + 2 * Complex.I * γ = (σ : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [hpt] at h
    calc -(logDeriv (Gfull k f) ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I)).re
        ≤ Cw * Real.log |γ| := h
      _ ≤ (Cp + Cw + Cz) * Real.log |γ| := by nlinarith [hlognn, hCp, hCz]

include cf in
/-- **The Rankin–Selberg zero-free region (unconditional).** For a level-one weight-`k` Hecke
eigenform `f`, the Rankin–Selberg square `G = Gfull k f = ζ(2s)D(s+k−1)` has a de la Vallée Poussin
zero-free region: there are `C, t₀ > 0` such that every zero `β + iγ` of `G` with `3/4 < β < 1` and
`|γ| ≥ t₀` satisfies `β ≤ 1 − 1/(160 C log|γ|)` — no zeros in `σ ≥ 1 − c/log|t|`. All four de la
Vallée Poussin hypotheses are now proved: `h341` (the Euler-product 3-4-1 inequality), `hW`/`hzero`
(Borel–Carathéodory + Hadamard), and `hpole` (the simple pole at `s=1`). -/
theorem rs_zero_free_region (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k) :
    ∃ C t₀ : ℝ, 0 < C ∧ 3 ≤ t₀ ∧ ∀ β γ : ℝ, 3 / 4 < β → β < 1 → t₀ ≤ |γ| →
      Gfull k f ((β : ℂ) + Complex.I * γ) = 0 →
      β ≤ 1 - 1 / (20 * (8 * C) * Real.log |γ|) :=
  rs_zero_free_region_of_pole k f hk hf (neg_re_logDeriv_Gfull_le_pole k f hk hf)

end RankinSelbergDelta.RankinSelberg
