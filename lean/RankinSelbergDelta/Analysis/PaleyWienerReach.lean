import Mathlib

/-!
# Tails of zero sums for compactly supported test functions

Abel summation for a sum over zeros with a counting bound `∑_{|Im ρ| ≤ t} m_ρ ≤ K t log t`
(`sum_div_im_sq_le`), the resulting tail bound for a zero sum (`norm_tail_sum_le`), and the
resolution height of a Weil form whose test function has support `[−L, L]`. The Paley–Wiener bound
`‖ĝ(s)‖ ≤ e^{|Re s| L} ∫ ‖g‖` enters as a named hypothesis.
-/

namespace RankinSelbergDelta.Analysis.PaleyWiener

open MeasureTheory Set Filter Topology

lemma hasDerivAt_neg_inv_sq {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun t : ℝ => -(1 / t ^ 2)) (2 / t ^ 3) t := by
  have h := ((hasDerivAt_pow 2 t).inv (pow_ne_zero 2 ht)).neg
  convert h using 1 <;> first
    | (funext u; simp [one_div])
    | ((try simp only [id]); field_simp; (try ring))

lemma tendsto_neg_inv_sq : Tendsto (fun t : ℝ => -(1 / t ^ 2)) atTop (𝓝 0) := by
  have h : Tendsto (fun t : ℝ => 1 / t ^ 2) atTop (𝓝 0) := by
    have := tendsto_inv_atTop_zero.comp
      (tendsto_pow_atTop (n := 2) (by norm_num) : Tendsto (fun x : ℝ => x ^ 2) atTop atTop)
    refine this.congr fun t => ?_
    simp [Function.comp, one_div]
  simpa using h.neg

lemma integrableOn_Ioi_two_div_cube {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => 2 / t ^ 3) (Ioi b) :=
  integrableOn_Ioi_deriv_of_nonneg (hasDerivAt_neg_inv_sq hb.ne').continuousAt.continuousWithinAt
    (fun t ht => hasDerivAt_neg_inv_sq (lt_trans hb ht).ne')
    (fun t ht => by have := lt_trans hb ht; positivity) tendsto_neg_inv_sq

/-- `∫_{b}^{∞} 2/t³ dt = 1/b²` for `b > 0`. -/
lemma integral_Ioi_two_div_cube {b : ℝ} (hb : 0 < b) :
    ∫ t in Ioi b, 2 / t ^ 3 = 1 / b ^ 2 := by
  rw [integral_Ioi_of_hasDerivAt_of_tendsto
    (hasDerivAt_neg_inv_sq hb.ne').continuousAt.continuousWithinAt
    (fun t ht => hasDerivAt_neg_inv_sq (lt_trans hb ht).ne') (integrableOn_Ioi_two_div_cube hb)
    tendsto_neg_inv_sq]
  ring

lemma hasDerivAt_neg_one_add_log_div {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => -((1 + Real.log t) / t)) (Real.log t / t ^ 2) t := by
  have h1 : HasDerivAt (fun t : ℝ => 1 + Real.log t) t⁻¹ t := (Real.hasDerivAt_log ht.ne').const_add 1
  have h := (h1.div (hasDerivAt_id t) ht.ne').neg
  convert h using 1 <;> first
    | (funext u; simp [id])
    | ((try simp only [id]); field_simp; (try ring))

lemma tendsto_neg_one_add_log_div : Tendsto (fun t : ℝ => -((1 + Real.log t) / t)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => Real.log t / t) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h2 : Tendsto (fun t : ℝ => 1 / t) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have := (h2.add h1).neg
  rw [add_zero, neg_zero] at this
  refine this.congr fun t => ?_
  ring

/-- `∫_{H}^{∞} log t / t² dt = (1 + log H)/H` for `H ≥ 1`, with the integrand integrable. -/
lemma integral_Ioi_log_div_sq {H : ℝ} (hH : 1 ≤ H) :
    IntegrableOn (fun t : ℝ => Real.log t / t ^ 2) (Ioi H) ∧
    ∫ t in Ioi H, Real.log t / t ^ 2 = (1 + Real.log H) / H := by
  have hH0 : 0 < H := by linarith
  have hnn : ∀ t ∈ Ioi H, 0 ≤ Real.log t / t ^ 2 := fun t ht =>
    div_nonneg (Real.log_nonneg (by linarith [mem_Ioi.mp ht])) (by positivity)
  have hint := integrableOn_Ioi_deriv_of_nonneg
    (hasDerivAt_neg_one_add_log_div hH0).continuousAt.continuousWithinAt
    (fun t ht => hasDerivAt_neg_one_add_log_div (lt_trans hH0 ht)) hnn tendsto_neg_one_add_log_div
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto
    (hasDerivAt_neg_one_add_log_div hH0).continuousAt.continuousWithinAt
    (fun t ht => hasDerivAt_neg_one_add_log_div (lt_trans hH0 ht)) hint
    tendsto_neg_one_add_log_div]
  ring

/-- **Abel summation for the zero tail.** -/
theorem sum_div_im_sq_le (S : Finset ℂ) (m : ℂ → ℕ) {H K : ℝ} (hH : 1 ≤ H) (hK : 0 ≤ K)
    (hS : ∀ ρ ∈ S, H < |ρ.im|)
    (hN : ∀ t : ℝ, H ≤ t → ((S.filter (fun ρ => |ρ.im| ≤ t)).sum (fun ρ => (m ρ : ℝ)))
      ≤ K * t * Real.log t) :
    S.sum (fun ρ => (m ρ : ℝ) / ρ.im ^ 2) ≤ 2 * K * (1 + Real.log H) / H := by
  classical
  have hH0 : 0 < H := by linarith
  -- each term as an integral over `Ioi H` of an indicator
  have hterm : ∀ ρ ∈ S, (m ρ : ℝ) / ρ.im ^ 2
      = ∫ t in Ioi H, (Ioi |ρ.im|).indicator (fun t => (m ρ : ℝ) * (2 / t ^ 3)) t := by
    intro ρ hρ
    have hb : 0 < |ρ.im| := lt_trans hH0 (hS ρ hρ)
    rw [setIntegral_indicator measurableSet_Ioi,
      show Ioi H ∩ Ioi |ρ.im| = Ioi |ρ.im| from
        Set.inter_eq_right.mpr (Ioi_subset_Ioi (hS ρ hρ).le),
      integral_const_mul, integral_Ioi_two_div_cube hb, sq_abs]
    ring
  -- integrability of each indicator term
  have hint : ∀ ρ ∈ S, IntegrableOn
      ((Ioi |ρ.im|).indicator (fun t => (m ρ : ℝ) * (2 / t ^ 3))) (Ioi H) := fun ρ _ =>
    ((integrableOn_Ioi_two_div_cube hH0).const_mul (m ρ : ℝ)).indicator measurableSet_Ioi
  rw [Finset.sum_congr rfl hterm, ← integral_finset_sum _ hint]
  -- the pointwise bound of the summed indicator by `K t log t · 2/t³`
  have hbound : ∀ t ∈ Ioi H,
      (∑ ρ ∈ S, (Ioi |ρ.im|).indicator (fun t => (m ρ : ℝ) * (2 / t ^ 3)) t)
        ≤ 2 * K * (Real.log t / t ^ 2) := by
    intro t ht
    have ht : H < t := ht
    have ht0 : 0 < t := lt_trans hH0 ht
    have hsum : (∑ ρ ∈ S, (Ioi |ρ.im|).indicator (fun t => (m ρ : ℝ) * (2 / t ^ 3)) t)
        = ((S.filter (fun ρ => |ρ.im| < t)).sum (fun ρ => (m ρ : ℝ))) * (2 / t ^ 3) := by
      rw [Finset.sum_mul, Finset.sum_filter]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      by_cases h : |ρ.im| < t
      · rw [if_pos h, Set.indicator_of_mem (mem_Ioi.mpr h)]
      · rw [if_neg h, Set.indicator_of_notMem (by simpa using h)]
    rw [hsum]
    have hle : ((S.filter (fun ρ => |ρ.im| < t)).sum (fun ρ => (m ρ : ℝ)))
        ≤ ((S.filter (fun ρ => |ρ.im| ≤ t)).sum (fun ρ => (m ρ : ℝ))) :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.monotone_filter_right _ (by intro ρ _ h; exact le_of_lt h)) (fun _ _ _ => by positivity)
    have h2 := (hle.trans (hN t ht.le))
    calc ((S.filter (fun ρ => |ρ.im| < t)).sum (fun ρ => (m ρ : ℝ))) * (2 / t ^ 3)
        ≤ (K * t * Real.log t) * (2 / t ^ 3) := by gcongr
      _ = 2 * K * (Real.log t / t ^ 2) := by field_simp; (try ring)
  obtain ⟨hint2, hval⟩ := integral_Ioi_log_div_sq hH
  calc (∫ t in Ioi H, ∑ ρ ∈ S, (Ioi |ρ.im|).indicator (fun t => (m ρ : ℝ) * (2 / t ^ 3)) t)
      ≤ ∫ t in Ioi H, 2 * K * (Real.log t / t ^ 2) :=
        setIntegral_mono_on (integrable_finset_sum _ hint) (hint2.const_mul _) measurableSet_Ioi
          hbound
    _ = 2 * K * (1 + Real.log H) / H := by
        rw [integral_const_mul, hval]; ring

/-- **The tail of a zero sum.** -/
theorem norm_tail_sum_le (S : Finset ℂ) (m : ℂ → ℕ) (φ : ℂ → ℂ) {H K C : ℝ} (hH : 1 ≤ H)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hS : ∀ ρ ∈ S, H < |ρ.im|)
    (hN : ∀ t : ℝ, H ≤ t → ((S.filter (fun ρ => |ρ.im| ≤ t)).sum (fun ρ => (m ρ : ℝ)))
      ≤ K * t * Real.log t)
    (hφ : ∀ ρ ∈ S, ‖φ ρ‖ * ρ.im ^ 2 ≤ C) :
    ‖S.sum (fun ρ => (m ρ : ℂ) * φ ρ)‖ ≤ C * (2 * K * (1 + Real.log H) / H) := by
  have hH0 : 0 < H := by linarith
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∀ ρ ∈ S, ‖(m ρ : ℂ) * φ ρ‖ ≤ C * ((m ρ : ℝ) / ρ.im ^ 2) := by
    intro ρ hρ
    have hb : 0 < ρ.im ^ 2 := by
      have := lt_trans hH0 (hS ρ hρ)
      have : ρ.im ≠ 0 := fun h => by rw [h, abs_zero] at this; linarith
      positivity
    rw [norm_mul, Complex.norm_natCast]
    have : ‖φ ρ‖ ≤ C / ρ.im ^ 2 := by rw [le_div_iff₀ hb]; exact hφ ρ hρ
    calc (m ρ : ℝ) * ‖φ ρ‖ ≤ (m ρ : ℝ) * (C / ρ.im ^ 2) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = C * ((m ρ : ℝ) / ρ.im ^ 2) := by ring
  calc ∑ ρ ∈ S, ‖(m ρ : ℂ) * φ ρ‖ ≤ ∑ ρ ∈ S, C * ((m ρ : ℝ) / ρ.im ^ 2) := Finset.sum_le_sum h1
    _ = C * ∑ ρ ∈ S, (m ρ : ℝ) / ρ.im ^ 2 := by rw [Finset.mul_sum]
    _ ≤ C * (2 * K * (1 + Real.log H) / H) :=
        mul_le_mul_of_nonneg_left (sum_div_im_sq_le S m hH hK hS hN) hC

/-- **The reach of a support-`L` Weil form.** With the sup bound
`‖ĝ(s)‖ ≤ e^{|Re s| L} M` (`norm_ghat_le`, a hypothesis here) and the second-derivative decay
`‖ĝ(s)‖ (Im s)² ≤ e^{|Re s| L} M₂` (the same bound for `g''`), the self-dual transform
`ĥ(ρ) = ĝ(ρ) conj(ĝ(1 − conj ρ))` of a zero `ρ` with `|Re ρ| ≤ a` and `|1 − Re ρ| ≤ a` satisfies
`‖ĥ(ρ)‖ (Im ρ)² ≤ e^{2aL} M M₂`; hence the zeros of height `> H` contribute at most
`e^{2aL} M M₂ · 2K (1 + log H)/H` to the zero sum. -/
theorem tail_weilForm_le (S : Finset ℂ) (m : ℂ → ℕ) (ghat : ℂ → ℂ) {H K L a M M₂ : ℝ}
    (hH : 1 ≤ H) (hK : 0 ≤ K) (hL : 0 ≤ L) (ha : 0 ≤ a) (hM : 0 ≤ M) (hM₂ : 0 ≤ M₂)
    (hS : ∀ ρ ∈ S, H < |ρ.im|) (hre : ∀ ρ ∈ S, |ρ.re| ≤ a ∧ |1 - ρ.re| ≤ a)
    (hN : ∀ t : ℝ, H ≤ t → ((S.filter (fun ρ => |ρ.im| ≤ t)).sum (fun ρ => (m ρ : ℝ)))
      ≤ K * t * Real.log t)
    (hPW : ∀ s : ℂ, ‖ghat s‖ ≤ Real.exp (|s.re| * L) * M)
    (hPW₂ : ∀ s : ℂ, ‖ghat s‖ * s.im ^ 2 ≤ Real.exp (|s.re| * L) * M₂) :
    ‖S.sum (fun ρ => (m ρ : ℂ) * (ghat ρ * (starRingEnd ℂ) (ghat (1 - (starRingEnd ℂ) ρ))))‖
      ≤ (Real.exp (2 * a * L) * (M * M₂)) * (2 * K * (1 + Real.log H) / H) := by
  refine norm_tail_sum_le S m _ hH hK (by positivity) hS hN fun ρ hρ => ?_
  obtain ⟨hr1, hr2⟩ := hre ρ hρ
  have hLa : Real.exp (|ρ.re| * L) ≤ Real.exp (a * L) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hr1 hL)
  have hre' : (1 - (starRingEnd ℂ) ρ).re = 1 - ρ.re := by simp
  have him' : (1 - (starRingEnd ℂ) ρ).im = ρ.im := by simp
  have hLb : Real.exp (|(1 - (starRingEnd ℂ) ρ).re| * L) ≤ Real.exp (a * L) := by
    rw [hre']; exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hr2 hL)
  have h1 := hPW₂ ρ
  have h2 := hPW (1 - (starRingEnd ℂ) ρ)
  rw [norm_mul, Complex.norm_conj]
  calc ‖ghat ρ‖ * ‖ghat (1 - (starRingEnd ℂ) ρ)‖ * ρ.im ^ 2
      = (‖ghat ρ‖ * ρ.im ^ 2) * ‖ghat (1 - (starRingEnd ℂ) ρ)‖ := by ring
    _ ≤ (Real.exp (|ρ.re| * L) * M₂) * (Real.exp (|(1 - (starRingEnd ℂ) ρ).re| * L) * M) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ ≤ (Real.exp (a * L) * M₂) * (Real.exp (a * L) * M) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hLa hM₂) (mul_le_mul_of_nonneg_right hLb hM)
          (by positivity) (by positivity)
    _ = Real.exp (2 * a * L) * (M * M₂) := by
        rw [show 2 * a * L = a * L + a * L by ring, Real.exp_add]; ring

end RankinSelbergDelta.Analysis.PaleyWiener
