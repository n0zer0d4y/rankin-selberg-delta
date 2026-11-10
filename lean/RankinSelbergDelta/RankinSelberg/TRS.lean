import Mathlib

/-!
# An abstract de la Vallée Poussin nonvanishing theorem

For `G : ℂ → ℂ` and real `y`: if `‖G(1+x)³ G(1+x+iy)⁴ G(1+x+2iy)‖ ≥ 1` for all `x > 0`,
`G(1 + x) = O(1/x)` as `x → 0⁺`, `G` is differentiable at `1 + iy` and continuous at `1 + 2iy`,
then `G(1 + iy) ≠ 0` (`trs_ne_zero`). This abstracts Mathlib's argument for ζ and Dirichlet
L-functions.
-/
namespace RankinSelbergDelta.RankinSelberg

open Complex Asymptotics Filter Topology

/-- A zero of `G` at `1 + iy` (with `G` differentiable there) makes the horizontal slice `O(x)`. -/
lemma dlVP_zero_isBigO {G : ℂ → ℂ} {y : ℝ} (hG : DifferentiableAt ℂ G (1 + I * y))
    (h0 : G (1 + I * y) = 0) :
    (fun x : ℝ ↦ G (1 + x + I * y)) =O[𝓝[>] 0] fun x : ℝ ↦ (x : ℂ) := by
  simp_rw [add_comm (1 : ℂ), add_assoc]
  have h := hG.hasDerivAt
  rw [← zero_add (1 + I * y)] at h
  simpa only [zero_add, h0, sub_zero]
    using (Complex.isBigO_comp_ofReal_nhds
      (h.comp_add_const 0 _).differentiableAt.isBigO_sub) |>.mono nhdsWithin_le_nhds

/-- `G` continuous at `1 + 2iy` makes the horizontal slice there `O(1)`. -/
lemma dlVP_bounded_isBigO {G : ℂ → ℂ} {y : ℝ} (hG : ContinuousAt G (1 + 2 * I * y)) :
    (fun x : ℝ ↦ G (1 + x + 2 * I * y)) =O[𝓝[>] 0] fun _ ↦ (1 : ℂ) := by
  refine IsBigO.mono ?_ nhdsWithin_le_nhds
  simp_rw [add_comm (1 : ℂ), add_assoc]
  have h := hG
  rw [← zero_add (1 + 2 * I * y)] at h
  exact h.comp (f := fun x : ℝ ↦ x + (1 + 2 * I * y)) (x := 0) (by fun_prop) |>.tendsto.isBigO_one ℂ

/-- **Abstract de la Vallée Poussin nonvanishing.** With the 3-4-1 product bound `H1`,
    a simple pole `H2`, and regularity `H3`/`H4` off the pole, `G` does not vanish at `1 + iy`. -/
theorem trs_ne_zero {G : ℂ → ℂ} {y : ℝ}
    (H1 : ∀ x : ℝ, 0 < x →
      1 ≤ ‖G (1 + x) ^ 3 * G (1 + x + I * y) ^ 4 * G (1 + x + 2 * I * y)‖)
    (H2 : (fun x : ℝ ↦ G (1 + x)) =O[𝓝[>] 0] fun x : ℝ ↦ (1 : ℂ) / x)
    (H3 : DifferentiableAt ℂ G (1 + I * y))
    (H4 : ContinuousAt G (1 + 2 * I * y)) :
    G (1 + I * y) ≠ 0 := by
  intro Hz
  have help (x : ℝ) : ((1 / x) ^ 3 * x ^ 4 * 1 : ℂ) = x := by
    rcases eq_or_ne x 0 with rfl | h
    · rw [ofReal_zero, zero_pow (by norm_num), mul_zero, mul_one]
    · rw [one_div, inv_pow, pow_succ _ 3, ← mul_assoc,
        inv_mul_cancel₀ <| pow_ne_zero 3 (ofReal_ne_zero.mpr h), one_mul, mul_one]
  have H₀ : (fun _ : ℝ ↦ (1 : ℝ)) =O[𝓝[>] 0]
      fun x ↦ G (1 + x) ^ 3 * G (1 + x + I * y) ^ 4 * G (1 + x + 2 * I * y) :=
    IsBigO.of_bound' <| eventually_nhdsWithin_of_forall
      fun x hx ↦ (norm_one (α := ℝ)).symm ▸ (H1 x hx)
  have H := H2.pow 3 |>.mul <| (dlVP_zero_isBigO H3 Hz).pow 4 |>.mul <|
    dlVP_bounded_isBigO H4
  simp only [← mul_assoc, help] at H
  replace H := (H₀.trans H).norm_right
  simp only [norm_real] at H
  exact isLittleO_irrefl (.of_forall (fun _ ↦ one_ne_zero)) <|
    H.of_norm_right.trans_isLittleO <| isLittleO_id_one.mono nhdsWithin_le_nhds

/-- Witness: the hypotheses `H1`-`H4` of `trs_ne_zero` are jointly satisfiable (not vacuous).
    `G ≡ 1` with `y = 1`: `H1` is `1 ≤ ‖1‖ = 1`; `H3`/`H4` hold for a constant; and `H2` holds
    because a constant is `O(1/x)` as `x → 0⁺` (since `x⁻¹ → ∞`). -/
theorem trs_ne_zero_hyps_satisfiable :
    ∃ (G : ℂ → ℂ) (y : ℝ),
      (∀ x : ℝ, 0 < x →
        1 ≤ ‖G (1 + x) ^ 3 * G (1 + x + I * y) ^ 4 * G (1 + x + 2 * I * y)‖) ∧
      ((fun x : ℝ ↦ G (1 + x)) =O[𝓝[>] 0] fun x : ℝ ↦ (1 : ℂ) / x) ∧
      DifferentiableAt ℂ G (1 + I * y) ∧ ContinuousAt G (1 + 2 * I * y) := by
  refine ⟨fun _ ↦ 1, 1, ?_, ?_, differentiableAt_const _, continuousAt_const⟩
  · intro x _; simp
  · rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [tendsto_inv_nhdsGT_zero.eventually_ge_atTop (1 : ℝ), self_mem_nhdsWithin]
      with x hx hx0
    have hx0' : (0 : ℝ) < x := Set.mem_Ioi.mp hx0
    simp only [norm_one, one_mul, one_div, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hx0']
    exact hx

end RankinSelbergDelta.RankinSelberg
