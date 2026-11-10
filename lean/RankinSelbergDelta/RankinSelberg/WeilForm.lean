import Mathlib

/-!
# The self-dual Weil form: the test-function side

With the transform `ĝ(s) = ∫ g(x) e^{sx} dx`, the reflection `g♯(y) = conj(g(−y)) e^{−y}` satisfies
`ĝ♯(s) = conj(ĝ(1 − conj s))`, and `h = g ⋆ g♯` has `ĥ(s) = ĝ(s) · conj(ĝ(1 − conj s))`. On the
critical line `ĥ(1/2 + iγ) = ‖ĝ(1/2 + iγ)‖² ≥ 0`. Support: `supp g ⊆ [−L, L]` gives
`supp h ⊆ [−2L, 2L]`.
-/

namespace RankinSelbergDelta.RankinSelberg.WeilForm

open MeasureTheory Complex
open scoped ComplexConjugate

/-- The two-sided Laplace transform (the same as `RankinSelbergDelta.RankinSelberg.ghat`). -/
noncomputable def ghat (g : ℝ → ℂ) (s : ℂ) : ℂ := ∫ x : ℝ, g x * Complex.exp (s * x)

/-- The self-dual reflection `g♯(y) = conj(g(−y)) e^{−y}`. -/
noncomputable def gsharp (g : ℝ → ℂ) (y : ℝ) : ℂ := conj (g (-y)) * Complex.exp (-(y : ℂ))

/-- The self-dual test function `h = g ⋆ g♯` (Mathlib's convolution for the multiplication map). -/
noncomputable def selfDual (g : ℝ → ℂ) : ℝ → ℂ :=
  convolution g (gsharp g) (ContinuousLinearMap.mul ℝ ℂ) volume

/-- `ĝ♯(s) = conj(ĝ(1 − conj s))`. -/
lemma ghat_gsharp (g : ℝ → ℂ) (s : ℂ) : ghat (gsharp g) s = conj (ghat g (1 - conj s)) := by
  unfold ghat gsharp
  rw [← integral_conj,
    ← MeasureTheory.integral_neg_eq_self (fun x : ℝ => conj (g x * Complex.exp ((1 - conj s) * x)))]
  congr 1
  funext y
  rw [map_mul, ← Complex.exp_conj, mul_assoc, ← Complex.exp_add]
  congr 2
  simp only [map_mul, map_sub, map_one, Complex.conj_conj, Complex.conj_ofReal]
  push_cast
  ring

lemma continuous_gsharp (g : ℝ → ℂ) (hc : Continuous g) : Continuous (gsharp g) := by
  unfold gsharp
  exact (Complex.continuous_conj.comp (hc.comp continuous_neg)).mul (by fun_prop)

lemma hasCompactSupport_gsharp (g : ℝ → ℂ) (hs : HasCompactSupport g) :
    HasCompactSupport (gsharp g) := by
  unfold gsharp
  have h1 : HasCompactSupport (fun y : ℝ => g (-y)) := hs.comp_homeomorph (Homeomorph.neg ℝ)
  have h2 : HasCompactSupport (fun y : ℝ => conj (g (-y))) :=
    h1.comp_left (map_zero (starRingEnd ℂ))
  exact h2.mul_right

lemma continuous_selfDual (g : ℝ → ℂ) (hc : Continuous g) (hs : HasCompactSupport g) :
    Continuous (selfDual g) :=
  HasCompactSupport.continuous_convolution_right _ (hasCompactSupport_gsharp g hs)
    (hc.integrable_of_hasCompactSupport hs).locallyIntegrable (continuous_gsharp g hc)

lemma hasCompactSupport_selfDual (g : ℝ → ℂ) (hs : HasCompactSupport g) :
    HasCompactSupport (selfDual g) :=
  HasCompactSupport.convolution _ hs (hasCompactSupport_gsharp g hs)

/-- `ĥ(s) = ĝ(s) · ĝ♯(s)` for `h = g ⋆ g♯`, `g` continuous with compact support. -/
lemma ghat_selfDual (g : ℝ → ℂ) (hc : Continuous g) (hs : HasCompactSupport g) (s : ℂ) :
    ghat (selfDual g) s = ghat g s * ghat (gsharp g) s := by
  have hpt : ∀ u : ℝ, selfDual g u * Complex.exp (s * u)
      = convolution (fun x : ℝ => g x * Complex.exp (s * x))
          (fun x : ℝ => gsharp g x * Complex.exp (s * x)) (ContinuousLinearMap.mul ℝ ℂ) volume u := by
    intro u
    unfold selfDual
    simp only [convolution_def, ContinuousLinearMap.mul_apply']
    rw [← integral_mul_const]
    congr 1
    funext t
    rw [show Complex.exp (s * u) = Complex.exp (s * t) * Complex.exp (s * ((u - t : ℝ) : ℂ)) by
      rw [← Complex.exp_add]; congr 1; push_cast; ring]
    ring
  have hg1 : Integrable (fun x : ℝ => g x * Complex.exp (s * x)) :=
    (hc.mul (by fun_prop)).integrable_of_hasCompactSupport hs.mul_right
  have hg2 : Integrable (fun x : ℝ => gsharp g x * Complex.exp (s * x)) :=
    ((continuous_gsharp g hc).mul (by fun_prop)).integrable_of_hasCompactSupport
      (hasCompactSupport_gsharp g hs).mul_right
  unfold ghat
  simp_rw [hpt]
  rw [integral_convolution (ContinuousLinearMap.mul ℝ ℂ) hg1 hg2, ContinuousLinearMap.mul_apply']

/-- **`ĥ(s) = ĝ(s) · conj(ĝ(1 − conj s))`.** -/
theorem ghat_selfDual_eq (g : ℝ → ℂ) (hc : Continuous g) (hs : HasCompactSupport g) (s : ℂ) :
    ghat (selfDual g) s = ghat g s * conj (ghat g (1 - conj s)) := by
  rw [ghat_selfDual g hc hs, ghat_gsharp]

/-- On the critical line, `ĥ(1/2 + iγ) = ‖ĝ(1/2 + iγ)‖²`. -/
theorem ghat_selfDual_line (g : ℝ → ℂ) (hc : Continuous g) (hs : HasCompactSupport g) (γ : ℝ) :
    ghat (selfDual g) ((1 / 2 : ℂ) + γ * Complex.I)
      = ((‖ghat g ((1 / 2 : ℂ) + γ * Complex.I)‖ ^ 2 : ℝ) : ℂ) := by
  rw [ghat_selfDual_eq g hc hs]
  have e : (1 : ℂ) - conj ((1 / 2 : ℂ) + γ * Complex.I) = (1 / 2 : ℂ) + γ * Complex.I := by
    apply Complex.ext <;> simp <;> norm_num
  rw [e, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- **The zero sum of the self-dual form over zeros on the line is a nonnegative real.** For a
divisor `D ≥ 0` with finite support concentrated on `Re u = 1/2`,
`∑ᶠ u, D u · ĥ(u) = ∑ᶠ u, D u · ‖ĝ(u)‖² ≥ 0`. -/
theorem finsum_divisor_ghat_selfDual_nonneg (g : ℝ → ℂ) (hc : Continuous g)
    (hs : HasCompactSupport g) (D : ℂ → ℤ) (hD : ∀ u, 0 ≤ D u)
    (hfin : (Function.support D).Finite) (hline : ∀ u, D u ≠ 0 → u.re = 1 / 2) :
    (∑ᶠ u, (D u : ℂ) * ghat (selfDual g) u)
      = ((∑ᶠ u, (D u : ℝ) * ‖ghat g u‖ ^ 2 : ℝ) : ℂ) ∧
    0 ≤ ∑ᶠ u, (D u : ℝ) * ‖ghat g u‖ ^ 2 := by
  classical
  refine ⟨?_, finsum_nonneg fun u => mul_nonneg (by exact_mod_cast hD u) (by positivity)⟩
  set S : Finset ℂ := hfin.toFinset with hS
  have hsub1 : Function.support (fun u => (D u : ℂ) * ghat (selfDual g) u) ⊆ (S : Set ℂ) := by
    intro u hu
    rw [Function.mem_support] at hu
    have : D u ≠ 0 := fun h => hu (by rw [h]; simp)
    rw [hS, Set.Finite.coe_toFinset]
    exact this
  have hsub2 : Function.support (fun u => (D u : ℝ) * ‖ghat g u‖ ^ 2) ⊆ (S : Set ℂ) := by
    intro u hu
    rw [Function.mem_support] at hu
    have : D u ≠ 0 := fun h => hu (by rw [h]; simp)
    rw [hS, Set.Finite.coe_toFinset]
    exact this
  rw [finsum_eq_sum_of_support_subset _ hsub1, finsum_eq_sum_of_support_subset _ hsub2,
    Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  by_cases h0 : D u = 0
  · simp [h0]
  · have hre := hline u h0
    have e : u = (1 / 2 : ℂ) + u.im * Complex.I := by
      apply Complex.ext <;> simp [hre]
    rw [e, ghat_selfDual_line g hc hs, ← e]
    push_cast
    ring

end RankinSelbergDelta.RankinSelberg.WeilForm
