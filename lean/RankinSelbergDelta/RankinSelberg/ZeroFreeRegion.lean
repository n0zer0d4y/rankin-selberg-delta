import Mathlib

/-!
# The de la Vallée Poussin optimisation

Given the 3-4-1 inequality `3/(σ − 1) − 4/(σ − β) + A·L ≥ 0` for all `σ ∈ (1, 2]` at a zero
`β + iγ`, with `L = log |γ| ≥ 1`, evaluating at `σ = 1 + 4(1 − β)` gives
`β ≤ 1 − 1/(20 A L)` (`zero_free_of_logDeriv_341`).
-/

namespace RankinSelbergDelta.RankinSelberg

/-- **The de la Vallée Poussin zero-free-region core.** If at a putative zero `β + iγ`
(`3/4 < β < 1`, `L = log|γ| ≥ 1`) the combined 3-4-1 inequality
`0 ≤ 3/(σ−1) − 4/(σ−β) + A·L` holds for every `σ ∈ (1, 2]`, then `β ≤ 1 − 1/(20 A L)`:
the zero is pushed into the region `Re s ≤ 1 − c/log|γ|`, `c = 1/(20 A)`. -/
theorem zero_free_of_dlVP_bound {β A L : ℝ} (hβlo : 3 / 4 < β) (hβ1 : β < 1)
    (hA : 0 < A) (hL : 1 ≤ L)
    (H : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → 0 ≤ 3 / (σ - 1) - 4 / (σ - β) + A * L) :
    β ≤ 1 - 1 / (20 * A * L) := by
  set δ : ℝ := 1 - β with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hδ4 : δ < 1 / 4 := by rw [hδ]; linarith
  -- evaluate the hypothesis at σ = 1 + 4δ ∈ (1, 2]
  have hσ1 : (1 : ℝ) < 1 + 4 * δ := by linarith
  have hσ2 : 1 + 4 * δ ≤ 2 := by linarith
  have key := H (1 + 4 * δ) hσ1 hσ2
  have e1 : (1 + 4 * δ) - 1 = 4 * δ := by ring
  have e2 : (1 + 4 * δ) - β = 5 * δ := by rw [hδ]; ring
  rw [e1, e2] at key
  -- 3/(4δ) − 4/(5δ) = −1/(20δ)
  have hcollapse : 3 / (4 * δ) - 4 / (5 * δ) = -(1 / (20 * δ)) := by
    field_simp
    ring
  rw [hcollapse] at key
  -- key : 0 ≤ −1/(20δ) + A·L  ⇒  1/(20δ) ≤ A·L  ⇒  1 ≤ 20 A L δ  ⇒  1/(20 A L) ≤ δ
  have h1 : 1 / (20 * δ) ≤ A * L := by linarith
  have h20δ : (0 : ℝ) < 20 * δ := by linarith
  have hmul : (1 : ℝ) ≤ A * L * (20 * δ) := by
    rw [div_le_iff₀ h20δ] at h1; linarith
  have hALpos : (0 : ℝ) < 20 * A * L := by positivity
  have hfinal : 1 / (20 * A * L) ≤ δ := by
    rw [div_le_iff₀ hALpos]; nlinarith [hmul]
  rw [hδ] at hfinal
  linarith

/-- **The de la Vallée Poussin zero-free region from the 3-4-1 and the log-derivative bounds.**
Writing `P σ = −(G'/G)(σ)`, `Z σ = −Re (G'/G)(σ+iγ)`, `W σ = −Re (G'/G)(σ+2iγ)`, the Euler-product
3-4-1 positivity gives `0 ≤ 3 P σ + 4 Z σ + W σ`; the simple pole gives `P σ ≤ 1/(σ−1) + C`; a zero
at `β + iγ` gives `Z σ ≤ −1/(σ−β) + C·log|γ|` (the zero's partial-fraction term); and the growth
bound gives `W σ ≤ C·log|γ|`. These combine to the hypothesis of `zero_free_of_dlVP_bound`, yielding
`β ≤ 1 − 1/(160 C log|γ|)` — the zero-free region. The analytic inputs (`hpole` from the continuation,
`hzero`/`hW` from Hadamard partial fractions + the complex-Stirling growth bound) are the remaining
discharges. -/
theorem zero_free_of_logDeriv_341 {β γ C : ℝ} (hβlo : 3 / 4 < β) (hβ1 : β < 1) (hC : 0 < C)
    (hL : 1 ≤ Real.log |γ|) (P Z W : ℝ → ℝ)
    (h341 : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → 0 ≤ 3 * P σ + 4 * Z σ + W σ)
    (hpole : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → P σ ≤ 1 / (σ - 1) + C)
    (hzero : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → Z σ ≤ -(1 / (σ - β)) + C * Real.log |γ|)
    (hW : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → W σ ≤ C * Real.log |γ|) :
    β ≤ 1 - 1 / (20 * (8 * C) * Real.log |γ|) := by
  have hM : C ≤ C * Real.log |γ| := le_mul_of_one_le_right hC.le hL
  refine zero_free_of_dlVP_bound hβlo hβ1 (by positivity) hL (fun σ hσ1 hσ2 => ?_)
  have h3 := h341 σ hσ1 hσ2
  have hp := hpole σ hσ1 hσ2
  have hz := hzero σ hσ1 hσ2
  have hw := hW σ hσ1 hσ2
  rw [show (8 * C) * Real.log |γ| = 8 * (C * Real.log |γ|) from by ring,
      show (3 : ℝ) / (σ - 1) = 3 * (1 / (σ - 1)) from by ring,
      show (4 : ℝ) / (σ - β) = 4 * (1 / (σ - β)) from by ring]
  linarith [h3, hp, hz, hw, hM]

/-- The Mertens 3-4-1 positivity `3 + 4cos θ + cos 2θ = 2(1+cos θ)² ≥ 0` (self-contained copy;
the Euler-product positivity at the heart of de la Vallée Poussin). -/
theorem mertens341_nonneg (u : ℝ) : 0 ≤ 3 + 4 * Real.cos u + Real.cos (2 * u) := by
  have hid : 3 + 4 * Real.cos u + Real.cos (2 * u) = 2 * (1 + Real.cos u) ^ 2 := by
    rw [Real.cos_two_mul]; ring
  rw [hid]; positivity

/-- **The 3-4-1 inequality for a nonnegative von Mangoldt log-derivative** (discharges `h341`).
For `Λ ≥ 0` with the log-derivative series `Σ Λ(n)/n^σ` absolutely convergent, the Euler-product
positivity `3 + 4cos θ + cos 2θ ≥ 0` gives
`0 ≤ 3·Σ Λ/n^σ + 4·Σ Λ cos(t·log n)/n^σ + Σ Λ cos(2t·log n)/n^σ` — exactly `3 P + 4 Z + W` with
`P/Z/W = −Re(L'/L)` at `σ, σ+it, σ+2it`. The arithmetic core of the de la Vallée Poussin argument. -/
theorem three_four_one_vonMangoldt {Λ : ℕ → ℝ} (hΛ : ∀ n, 0 ≤ Λ n) (σ t : ℝ)
    (hs : Summable fun n : ℕ => Λ n / (n : ℝ) ^ σ) :
    0 ≤ 3 * (∑' n, Λ n / (n : ℝ) ^ σ)
      + 4 * (∑' n, Λ n / (n : ℝ) ^ σ * Real.cos (t * Real.log n))
      + (∑' n, Λ n / (n : ℝ) ^ σ * Real.cos (2 * t * Real.log n)) := by
  have hbase_nonneg : ∀ n : ℕ, 0 ≤ Λ n / (n : ℝ) ^ σ := fun n =>
    div_nonneg (hΛ n) (by positivity)
  -- each cos-weighted series is summable, by comparison with the base series (|cos| ≤ 1)
  have hcos : ∀ u : ℝ, Summable fun n : ℕ => Λ n / (n : ℝ) ^ σ * Real.cos (u * Real.log n) := by
    intro u
    refine Summable.of_norm_bounded hs (fun n => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hbase_nonneg n)]
    exact mul_le_of_le_one_right (hbase_nonneg n) (Real.abs_cos_le_one _)
  -- the three series sum (via HasSum) to the combined nonnegative summand base·(3+4cosθ+cos2θ)
  have hsum := ((hs.hasSum.mul_left 3).add ((hcos t).hasSum.mul_left 4)).add (hcos (2 * t)).hasSum
  rw [← hsum.tsum_eq]
  refine tsum_nonneg (fun n => ?_)
  rw [show (2 : ℝ) * t * Real.log n = 2 * (t * Real.log n) from by ring]
  nlinarith [mul_nonneg (hbase_nonneg n) (mertens341_nonneg (t * Real.log n))]

