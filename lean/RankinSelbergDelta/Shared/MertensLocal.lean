import Mathlib

/-!
# The local 3-4-1 positivity

`3 + 4 cos u + cos 2u = 2 (1 + cos u)² ≥ 0`, and its consequence for a nonnegative measure
`μ = Σ_j w_j δ_{φ_j}`: `Σ_j w_j (3 + 4 cos(φ_j − θ) + cos 2(φ_j − θ)) ≥ 0` for every shift `θ`
(`mertens341_nonneg`), together with the same statement for any nonnegative cosine polynomial.
-/
namespace RankinSelbergDelta.Shared

open scoped BigOperators

/-- The Mertens 3-4-1 identity: `3 + 4 cos u + cos 2u = 2 (1 + cos u)^2`. -/
theorem mertens341_identity (u : ℝ) :
    3 + 4 * Real.cos u + Real.cos (2 * u) = 2 * (1 + Real.cos u) ^ 2 := by
  rw [Real.cos_two_mul]; ring

/-- Hence the 3-4-1 weight is nonnegative for every real angle. -/
theorem mertens341_nonneg (u : ℝ) : 0 ≤ 3 + 4 * Real.cos u + Real.cos (2 * u) := by
  rw [mertens341_identity]; positivity

/-- **Local Mertens positivity.** Paired against a nonnegative spectral measure
    `sum_j w_j delta_{phi_j}` (`w_j >= 0`), the 3-4-1 combination is nonnegative at every shift
    `theta`. -/
theorem mertens341_measure_nonneg {m : ℕ} (w φ : Fin m → ℝ) (hw : ∀ j, 0 ≤ w j) (θ : ℝ) :
    0 ≤ ∑ j, w j * (3 + 4 * Real.cos (φ j - θ) + Real.cos (2 * (φ j - θ))) := by
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (hw j) (mertens341_nonneg _)

/-- Witness: the measure positivity is non-trivial — a genuine two-atom nonnegative measure at a
    generic shift gives a strictly usable nonnegative value (not vacuous). -/
theorem mertens341_measure_nonneg_hyps_satisfiable :
    ∃ (m : ℕ) (w φ : Fin m → ℝ), 0 < m ∧ (∀ j, 0 ≤ w j) ∧
      0 ≤ ∑ j, w j * (3 + 4 * Real.cos (φ j - 0) + Real.cos (2 * (φ j - 0))) := by
  refine ⟨2, ![1, 2], ![0, 1], by norm_num, ?_, ?_⟩
  · intro j; fin_cases j <;> norm_num
  · exact mertens341_measure_nonneg ![1, 2] ![0, 1] (by intro j; fin_cases j <;> norm_num) 0

/-- **** The 3-4-1 is one instance of a general principle: for ANY
    pointwise-nonnegative weight `P` and any nonnegative spectral measure `∑_j w_j δ_{φ_j}`
    (`w_j ≥ 0`), the pairing at every shift `θ` is nonnegative. `mertens341_measure_nonneg` is the
    case `P u = 3 + 4 cos u + cos 2u`; the admissible weights are exactly the nonnegative cosine
    polynomials, and this lemma pins the only structure the argument uses: `P ≥ 0` and `w ≥ 0`. -/
theorem measure_pairing_nonneg_of_nonneg {m : ℕ} (P : ℝ → ℝ) (hP : ∀ u, 0 ≤ P u)
    (w φ : Fin m → ℝ) (hw : ∀ j, 0 ≤ w j) (θ : ℝ) :
    0 ≤ ∑ j, w j * P (φ j - θ) := by
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (hw j) (hP _)

/-- `mertens341_measure_nonneg` as an instance of the general kernel (the 3-4-1 is one admissible
    weight), confirming the generalization subsumes it. -/
theorem mertens341_measure_nonneg' {m : ℕ} (w φ : Fin m → ℝ) (hw : ∀ j, 0 ≤ w j) (θ : ℝ) :
    0 ≤ ∑ j, w j * (3 + 4 * Real.cos (φ j - θ) + Real.cos (2 * (φ j - θ))) :=
  measure_pairing_nonneg_of_nonneg (fun u => 3 + 4 * Real.cos u + Real.cos (2 * u))
    mertens341_nonneg w φ hw θ

/-- **Fejér–Riesz nonnegativity.** Every squared-modulus trigonometric polynomial
    `‖∑_k z_k e^{i k u}‖^2` is a pointwise-nonnegative weight, hence admissible in
    `measure_pairing_nonneg_of_nonneg`. By the Fejér–Riesz theorem every nonnegative cosine
    polynomial has this form, so covers them all; the 3-4-1 weight `2(1+cos u)^2` is the
    instance `z = (1/√2, √2, 1/√2)`. -/
theorem fejer_riesz_weight_nonneg {N : ℕ} (z : Fin N → ℂ) (u : ℝ) :
    0 ≤ ‖∑ k : Fin N, z k * Complex.exp (((k : ℕ) : ℂ) * u * Complex.I)‖ ^ 2 := by
  positivity

/-- The Fejér–Riesz weight paired against a nonnegative spectral measure is nonnegative at every
    shift — the general positivity for the full class of nonnegative cosine polynomials. -/
theorem fejer_riesz_measure_nonneg {m N : ℕ} (z : Fin N → ℂ) (w φ : Fin m → ℝ)
    (hw : ∀ j, 0 ≤ w j) (θ : ℝ) :
    0 ≤ ∑ j, w j * ‖∑ k : Fin N, z k * Complex.exp (((k : ℕ) : ℂ) * ((φ j - θ : ℝ) : ℂ) * Complex.I)‖ ^ 2 := by
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (hw j) (by positivity)

/-- Witness: the Fejér–Riesz pairing is non-trivial — a genuine one-term polynomial and a two-atom
    nonnegative measure give a usable nonnegative value (not vacuous). -/
theorem fejer_riesz_measure_nonneg_hyps_satisfiable :
    ∃ (m N : ℕ) (z : Fin N → ℂ) (w φ : Fin m → ℝ), 0 < m ∧ 0 < N ∧ (∀ j, 0 ≤ w j) ∧
      0 ≤ ∑ j, w j * ‖∑ k : Fin N, z k * Complex.exp (((k : ℕ) : ℂ) * ((φ j - (0:ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 := by
  refine ⟨2, 1, ![1], ![1, 2], ![0, 1], by norm_num, by norm_num, ?_, ?_⟩
  · intro j; fin_cases j <;> norm_num
  · exact fejer_riesz_measure_nonneg ![1] ![1, 2] ![0, 1] (by intro j; fin_cases j <;> norm_num) 0

end RankinSelbergDelta.Shared
