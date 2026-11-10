import RankinSelbergDelta.CuspForm.LSeries

/-!
# The Mellin transform of the mean square

Given the mean-square identity of `MeanSquare.lean`, the Mellin transform of
`y ↦ Σ_n |a(n)|² e^{−4πny}` is `(4π)^{−w} Γ(w) D(w)` for `Re w > k + 1` (`rsMellin_eq`).
-/

namespace RankinSelbergDelta.RankinSelberg

open Complex UpperHalfPlane ModularForm CongruenceSubgroup ModularFormClass
open Function Filter Asymptotics Topology Set Real MeasureTheory RankinSelbergDelta.CuspForm

noncomputable section

variable {F : Type*} [FunLike F ℍ ℂ] {k : ℤ}
  [cf : CuspFormClass F (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ(1)) k]

/-- The Rankin–Selberg Dirichlet series `D(w) = Σ_{n} |a(n)|² n^{-w}`. -/
def rsD (f : F) (w : ℂ) : ℂ := ∑' n : ℕ, (‖(qExpansion 1 f).coeff n‖ ^ 2 : ℂ) / (n : ℂ) ^ w

private lemma strictWidthInfty_rs :
    (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ(1)).strictWidthInfty = 1 :=
  Subgroup.strictWidthInfty_eq_one_of_T_mem (mem_Gamma_one ModularGroup.T)

include cf in
/-- The summability input for `hasSum_mellin`: `Σ_n ‖a(n)‖² (4πn)^{-σ}` converges for `σ > k+1`. -/
theorem summable_rs_mellin (f : F) {w : ℂ} (hw : (k : ℝ) + 1 < w.re) :
    Summable (fun n : ℕ => ‖(‖(qExpansion 1 f).coeff n‖ ^ 2 : ℂ)‖ / (4 * Real.pi * (n : ℝ)) ^ w.re) := by
  have hbd : (fun n : ℕ => (qExpansion 1 f).coeff n) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ ((k : ℝ) / 2) := by
    have := CuspFormClass.qExpansion_isBigO (k := k) f
    rwa [strictWidthInfty_rs] at this
  have hsq : (fun n : ℕ => ‖(qExpansion 1 f).coeff n‖ ^ 2) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (k : ℝ) := by
    have h2 := (hbd.norm_left.mul hbd.norm_left)
    refine h2.congr' (by filter_upwards with n; rw [sq]) ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [← Real.rpow_add hnpos]; congr 1; ring
  refine summable_of_isBigO_nat
    (g := fun n : ℕ => (n : ℝ) ^ ((k : ℝ) - w.re)) ?_ ?_
  · rw [Real.summable_nat_rpow]; linarith
  have e1 : (fun n : ℕ => ‖(‖(qExpansion 1 f).coeff n‖ ^ 2 : ℂ)‖ / (4 * Real.pi * (n : ℝ)) ^ w.re)
      =ᶠ[atTop] fun n : ℕ => ((4 * Real.pi) ^ (-w.re) * ‖(qExpansion 1 f).coeff n‖ ^ 2)
          * (n : ℝ) ^ (-w.re) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
      Real.mul_rpow (by positivity) hnpos.le, Real.rpow_neg (by positivity),
      Real.rpow_neg hnpos.le, div_eq_mul_inv, mul_inv]
    ring
  have hA : (fun n : ℕ => (4 * Real.pi) ^ (-w.re) * ‖(qExpansion 1 f).coeff n‖ ^ 2)
      =O[atTop] fun n : ℕ => (n : ℝ) ^ (k : ℝ) := hsq.const_mul_left _
  have hB := hA.mul (isBigO_refl (fun n : ℕ => (n : ℝ) ^ (-w.re)) atTop)
  refine hB.congr' e1.symm ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [← Real.rpow_add hnpos, sub_eq_add_neg]

include cf in
/-- **The Mellin transform of the mean-square is the Rankin–Selberg Dirichlet series.**
    If `G` is the `x`-average `G(t) = ∫₀¹ |f(x+it)|² dx` (supplied as the `HasSum` form `hG`, i.e.
    `G(t) = Σ_n |a(n)|² e^{-4π n t}`), then for `Re w > k+1`,
    `mellin G w = (4π)^{-w} Γ(w) D(w)`. -/
theorem rsMellin_eq (f : F) (hk : 0 < k) {w : ℂ} (hw : (k : ℝ) + 1 < w.re) (G : ℝ → ℂ)
    (hG : ∀ t ∈ Set.Ioi (0 : ℝ),
      HasSum (fun n : ℕ => (‖(qExpansion 1 f).coeff n‖ ^ 2 : ℂ)
          * (Real.exp (-(4 * Real.pi * (n : ℝ)) * t) : ℂ)) (G t)) :
    mellin G w = ((4 * Real.pi : ℝ) : ℂ) ^ (-w) * Complex.Gamma w * rsD f w := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hs0 : 0 < w.re := by linarith
  have hp : ∀ n : ℕ, (‖(qExpansion 1 f).coeff n‖ ^ 2 : ℂ) = 0 ∨ 0 < 4 * Real.pi * (n : ℝ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · left; rw [hn, qExpansion_coeff_zero_cusp f]; simp
    · right
      have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      positivity
  have hM := hasSum_mellin hp hs0 hG (summable_rs_mellin f hw)
  rw [← hM.tsum_eq, rsD, ← tsum_mul_left]
  refine tsum_congr (fun n => ?_)
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; rw [qExpansion_coeff_zero_cusp f]; simp
  · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hπ0 : (0 : ℝ) ≤ 4 * Real.pi := by positivity
    have h4π : ((4 * Real.pi : ℝ) : ℂ) ≠ 0 := by
      rw [Ne, Complex.ofReal_eq_zero]; positivity
    have hnℂ : ((n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have h4πw : ((4 * Real.pi : ℝ) : ℂ) ^ w ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]; push_neg; intro h; exact absurd h h4π
    have hnw : ((n : ℕ) : ℂ) ^ w ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]; push_neg; intro h; exact absurd h hnℂ
    rw [show ((4 * Real.pi * (n : ℝ) : ℝ) : ℂ) = ((4 * Real.pi : ℝ) : ℂ) * ((n : ℝ) : ℂ) from
          Complex.ofReal_mul _ _,
        Complex.mul_cpow_ofReal_nonneg hπ0 hnpos.le, Complex.ofReal_natCast, Complex.cpow_neg]
    field_simp

end

end RankinSelbergDelta.RankinSelberg
