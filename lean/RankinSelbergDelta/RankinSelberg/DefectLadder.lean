import Mathlib

/-!
# Bounding a zero sum near the critical line

For a self-dual test function the zero side of the Weil form is
`∑_ρ m_ρ ĝ(ρ) conj(ĝ(1 − conj ρ))`. If every zero satisfies `|Re ρ − 1/2| ≤ ε`, then, with
Paley–Wiener bounds centred at the critical line, each zero off the line contributes at most
`e^{2εL} M²`, and at most `e^{2εL} M M₂ / (Im ρ)²` when `Im ρ ≠ 0`. This gives a lower bound for
the zero side.
-/

namespace RankinSelbergDelta.RankinSelberg.DefectLadder

open Finset

/-- The self-dual zero term `ĝ(ρ) · conj(ĝ(1 − conj ρ))`. -/
noncomputable def sdTerm (ghat : ℂ → ℂ) (ρ : ℂ) : ℂ :=
  ghat ρ * (starRingEnd ℂ) (ghat (1 - (starRingEnd ℂ) ρ))

lemma abs_re_one_sub_conj_sub_half (ρ : ℂ) :
    |(1 - (starRingEnd ℂ) ρ).re - 1 / 2| = |ρ.re - 1 / 2| := by
  have : (1 - (starRingEnd ℂ) ρ).re = 1 - ρ.re := by simp
  rw [this, show 1 - ρ.re - 1 / 2 = -(ρ.re - 1 / 2) by ring, abs_neg]

/-- An off-line term with `|Re ρ − 1/2| ≤ ε` is at most `e^{2εL} M²`. -/
theorem norm_sdTerm_le {ghat : ℂ → ℂ} {ε L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hPW : ∀ s : ℂ, ‖ghat s‖ ≤ Real.exp (|s.re - 1 / 2| * L) * M) {ρ : ℂ}
    (hρ : |ρ.re - 1 / 2| ≤ ε) :
    ‖sdTerm ghat ρ‖ ≤ Real.exp (2 * ε * L) * (M * M) := by
  have h1 := hPW ρ
  have h2 := hPW (1 - (starRingEnd ℂ) ρ)
  rw [abs_re_one_sub_conj_sub_half] at h2
  have he : Real.exp (|ρ.re - 1 / 2| * L) ≤ Real.exp (ε * L) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hρ hL)
  rw [sdTerm, norm_mul, Complex.norm_conj]
  calc ‖ghat ρ‖ * ‖ghat (1 - (starRingEnd ℂ) ρ)‖
      ≤ (Real.exp (|ρ.re - 1 / 2| * L) * M) * (Real.exp (|ρ.re - 1 / 2| * L) * M) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ ≤ (Real.exp (ε * L) * M) * (Real.exp (ε * L) * M) :=
        mul_le_mul (mul_le_mul_of_nonneg_right he hM) (mul_le_mul_of_nonneg_right he hM)
          (by positivity) (by positivity)
    _ = Real.exp (2 * ε * L) * (M * M) := by
        rw [show 2 * ε * L = ε * L + ε * L by ring, Real.exp_add]; ring

/-- An off-line term with `|Re ρ − 1/2| ≤ ε` satisfies `‖·‖ (Im ρ)² ≤ e^{2εL} M M₂`. -/
theorem norm_sdTerm_mul_im_sq_le {ghat : ℂ → ℂ} {ε L M M₂ : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hM₂ : 0 ≤ M₂) (hPW : ∀ s : ℂ, ‖ghat s‖ ≤ Real.exp (|s.re - 1 / 2| * L) * M)
    (hPW₂ : ∀ s : ℂ, ‖ghat s‖ * s.im ^ 2 ≤ Real.exp (|s.re - 1 / 2| * L) * M₂) {ρ : ℂ}
    (hρ : |ρ.re - 1 / 2| ≤ ε) :
    ‖sdTerm ghat ρ‖ * ρ.im ^ 2 ≤ Real.exp (2 * ε * L) * (M * M₂) := by
  have h1 := hPW₂ ρ
  have h2 := hPW (1 - (starRingEnd ℂ) ρ)
  rw [abs_re_one_sub_conj_sub_half] at h2
  have he : Real.exp (|ρ.re - 1 / 2| * L) ≤ Real.exp (ε * L) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hρ hL)
  rw [sdTerm, norm_mul, Complex.norm_conj]
  calc ‖ghat ρ‖ * ‖ghat (1 - (starRingEnd ℂ) ρ)‖ * ρ.im ^ 2
      = (‖ghat ρ‖ * ρ.im ^ 2) * ‖ghat (1 - (starRingEnd ℂ) ρ)‖ := by ring
    _ ≤ (Real.exp (|ρ.re - 1 / 2| * L) * M₂) * (Real.exp (|ρ.re - 1 / 2| * L) * M) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ ≤ (Real.exp (ε * L) * M₂) * (Real.exp (ε * L) * M) :=
        mul_le_mul (mul_le_mul_of_nonneg_right he hM₂) (mul_le_mul_of_nonneg_right he hM)
          (by positivity) (by positivity)
    _ = Real.exp (2 * ε * L) * (M * M₂) := by
        rw [show 2 * ε * L = ε * L + ε * L by ring, Real.exp_add]; ring

/-- The bounded off-line part: `‖∑ m_ρ sdTerm ρ‖ ≤ e^{2εL} M² ∑ m_ρ`. -/
theorem norm_sum_sdTerm_le (T : Finset ℂ) (m : ℂ → ℕ) (ghat : ℂ → ℂ) {ε L M : ℝ} (hL : 0 ≤ L)
    (hM : 0 ≤ M) (hPW : ∀ s : ℂ, ‖ghat s‖ ≤ Real.exp (|s.re - 1 / 2| * L) * M)
    (hstrip : ∀ ρ ∈ T, |ρ.re - 1 / 2| ≤ ε) :
    ‖∑ ρ ∈ T, (m ρ : ℂ) * sdTerm ghat ρ‖
      ≤ Real.exp (2 * ε * L) * (M * M) * ∑ ρ ∈ T, (m ρ : ℝ) := by
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun ρ hρ => ?_
  rw [norm_mul, Complex.norm_natCast]
  calc (m ρ : ℝ) * ‖sdTerm ghat ρ‖ ≤ (m ρ : ℝ) * (Real.exp (2 * ε * L) * (M * M)) :=
        mul_le_mul_of_nonneg_left (norm_sdTerm_le hL hM hPW (hstrip ρ hρ)) (by positivity)
    _ = Real.exp (2 * ε * L) * (M * M) * (m ρ : ℝ) := by ring

/-- The tail off-line part (`|Im ρ| > 2`): `‖∑ m_ρ sdTerm ρ‖ ≤ e^{2εL} M M₂ ∑ m_ρ / (Im ρ)²`. -/
theorem norm_sum_sdTerm_tail_le (T : Finset ℂ) (m : ℂ → ℕ) (ghat : ℂ → ℂ) {ε L M M₂ : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hM₂ : 0 ≤ M₂)
    (hPW : ∀ s : ℂ, ‖ghat s‖ ≤ Real.exp (|s.re - 1 / 2| * L) * M)
    (hPW₂ : ∀ s : ℂ, ‖ghat s‖ * s.im ^ 2 ≤ Real.exp (|s.re - 1 / 2| * L) * M₂)
    (hstrip : ∀ ρ ∈ T, |ρ.re - 1 / 2| ≤ ε) (hT : ∀ ρ ∈ T, 2 < |ρ.im|) :
    ‖∑ ρ ∈ T, (m ρ : ℂ) * sdTerm ghat ρ‖
      ≤ Real.exp (2 * ε * L) * (M * M₂) * ∑ ρ ∈ T, (m ρ : ℝ) / ρ.im ^ 2 := by
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun ρ hρ => ?_
  have hb : 0 < ρ.im ^ 2 := by
    have h2 := hT ρ hρ
    have : ρ.im ≠ 0 := fun h => by rw [h, abs_zero] at h2; linarith
    positivity
  rw [norm_mul, Complex.norm_natCast]
  have h := norm_sdTerm_mul_im_sq_le hL hM hM₂ hPW hPW₂ (hstrip ρ hρ)
  have h' : ‖sdTerm ghat ρ‖ ≤ Real.exp (2 * ε * L) * (M * M₂) / ρ.im ^ 2 := by
    rw [le_div_iff₀ hb]; exact h
  calc (m ρ : ℝ) * ‖sdTerm ghat ρ‖
      ≤ (m ρ : ℝ) * (Real.exp (2 * ε * L) * (M * M₂) / ρ.im ^ 2) :=
        mul_le_mul_of_nonneg_left h' (by positivity)
    _ = Real.exp (2 * ε * L) * (M * M₂) * ((m ρ : ℝ) / ρ.im ^ 2) := by ring

/-- **The ladder inequality, generic form.** For a finite zero set `S` with multiplicities `m`,
all zeros with `|Re ρ − 1/2| ≤ ε`, centered Paley–Wiener bounds, and a nonnegative on-line part,
`Re ∑_S m_ρ sdTerm ρ ≥ −e^{2εL} (M² N₂ + M M₂ A)` with `N₂` the multiplicity count of the off-line
zeros of height `≤ 2` and `A` the Abel weight `∑ m_ρ/(Im ρ)²` of the off-line zeros of height `> 2`. -/
theorem re_sum_ge (S : Finset ℂ) (m : ℂ → ℕ) (ghat : ℂ → ℂ) {ε L M M₂ : ℝ} (hL : 0 ≤ L)
    (hM : 0 ≤ M) (hM₂ : 0 ≤ M₂)
    (hPW : ∀ s : ℂ, ‖ghat s‖ ≤ Real.exp (|s.re - 1 / 2| * L) * M)
    (hPW₂ : ∀ s : ℂ, ‖ghat s‖ * s.im ^ 2 ≤ Real.exp (|s.re - 1 / 2| * L) * M₂)
    (hstrip : ∀ ρ ∈ S, |ρ.re - 1 / 2| ≤ ε)
    (hon : 0 ≤ (∑ ρ ∈ S.filter (fun ρ => ρ.re = 1 / 2), (m ρ : ℂ) * sdTerm ghat ρ).re) :
    -(Real.exp (2 * ε * L)
        * ((M * M) * ∑ ρ ∈ (S.filter (fun ρ => ¬ ρ.re = 1 / 2)).filter (fun ρ => ¬ 2 < |ρ.im|),
              (m ρ : ℝ)
          + (M * M₂) * ∑ ρ ∈ (S.filter (fun ρ => ¬ ρ.re = 1 / 2)).filter (fun ρ => 2 < |ρ.im|),
              (m ρ : ℝ) / ρ.im ^ 2))
      ≤ (∑ ρ ∈ S, (m ρ : ℂ) * sdTerm ghat ρ).re := by
  classical
  set T := S.filter (fun ρ => ¬ ρ.re = 1 / 2) with hT
  set T₁ := T.filter (fun ρ => 2 < |ρ.im|) with hT₁
  set T₀ := T.filter (fun ρ => ¬ 2 < |ρ.im|) with hT₀
  have hsplit : (∑ ρ ∈ S, (m ρ : ℂ) * sdTerm ghat ρ)
      = (∑ ρ ∈ S.filter (fun ρ => ρ.re = 1 / 2), (m ρ : ℂ) * sdTerm ghat ρ)
        + ((∑ ρ ∈ T₁, (m ρ : ℂ) * sdTerm ghat ρ) + ∑ ρ ∈ T₀, (m ρ : ℂ) * sdTerm ghat ρ) := by
    rw [← Finset.sum_filter_add_sum_filter_not S (fun ρ => ρ.re = 1 / 2), ← hT,
      ← Finset.sum_filter_add_sum_filter_not T (fun ρ => 2 < |ρ.im|)]
  have hstripT : ∀ ρ ∈ T, |ρ.re - 1 / 2| ≤ ε := fun ρ hρ =>
    hstrip ρ (Finset.mem_filter.mp hρ).1
  have h0 := norm_sum_sdTerm_le T₀ m ghat hL hM hPW
    (fun ρ hρ => hstripT ρ (Finset.mem_filter.mp hρ).1)
  have h1 := norm_sum_sdTerm_tail_le T₁ m ghat hL hM hM₂ hPW hPW₂
    (fun ρ hρ => hstripT ρ (Finset.mem_filter.mp hρ).1)
    (fun ρ hρ => (Finset.mem_filter.mp hρ).2)
  have hre0 := Complex.abs_re_le_norm (∑ ρ ∈ T₀, (m ρ : ℂ) * sdTerm ghat ρ)
  have hre1 := Complex.abs_re_le_norm (∑ ρ ∈ T₁, (m ρ : ℂ) * sdTerm ghat ρ)
  rw [abs_le] at hre0 hre1
  rw [hsplit, Complex.add_re, Complex.add_re]
  linarith [hre0.1, hre1.1, h0, h1, hon]

/-- The hypotheses of `re_sum_ge` are satisfiable: one on-line zero `1/2 + 3i` of multiplicity 1,
`ε = 0`, and the (degenerate) transform `ĝ = 0`, for which both centered bounds hold with
`M = M₂ = 0`; the conclusion is then `0 ≤ 0`. -/
theorem re_sum_ge_hyps_satisfiable :
    ∃ (S : Finset ℂ) (m : ℂ → ℕ) (ghat : ℂ → ℂ) (ε L M M₂ : ℝ), 0 ≤ L ∧ 0 ≤ M ∧ 0 ≤ M₂
      ∧ (∀ s : ℂ, ‖ghat s‖ ≤ Real.exp (|s.re - 1 / 2| * L) * M)
      ∧ (∀ s : ℂ, ‖ghat s‖ * s.im ^ 2 ≤ Real.exp (|s.re - 1 / 2| * L) * M₂)
      ∧ (∀ ρ ∈ S, |ρ.re - 1 / 2| ≤ ε)
      ∧ 0 ≤ (∑ ρ ∈ S.filter (fun ρ => ρ.re = 1 / 2), (m ρ : ℂ) * sdTerm ghat ρ).re
      ∧ S.Nonempty := by
  refine ⟨{(1 / 2 : ℂ) + 3 * Complex.I}, fun _ => 1, fun _ => 0, 0, 1, 0, 0, zero_le_one,
    le_rfl, le_rfl, fun s => by simp, fun s => by simp, ?_, ?_, Finset.singleton_nonempty _⟩
  · intro ρ hρ
    rw [Finset.mem_singleton] at hρ
    subst hρ
    simp
  · simp [sdTerm]

end RankinSelbergDelta.RankinSelberg.DefectLadder
