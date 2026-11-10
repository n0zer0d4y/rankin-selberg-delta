import Mathlib

/-!
# Lemmas for the archimedean term of the Weil form

The derivative of a function with `f(conj z) = conj(f z)` satisfies the same reflection
(`deriv_conj_of_conj`), so its logarithmic derivative does too; and a kernel bounded below by `−A₀`
on `|t| < t₀` and nonnegative beyond integrates against a bounded weight to at least
`−2 t₀ A₀ W` (`integral_kernel_ge`).
-/

namespace RankinSelbergDelta.RankinSelberg.ArchimedeanBound

open MeasureTheory Set Filter Topology
open scoped ComplexConjugate

/-- **Schwarz reflection for the derivative.** -/
theorem deriv_conj_of_conj {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hc : ∀ z, f (conj z) = conj (f z)) (z : ℂ) :
    deriv f (conj z) = conj (deriv f z) := by
  -- `f = conj ∘ f ∘ conj`; differentiate the right-hand side over `ℝ` at `conj z`
  have hfz : HasDerivAt f (deriv f z) z := (hf z).hasDerivAt
  have hF : HasFDerivAt f (ContinuousLinearMap.toSpanSingleton ℂ (deriv f z)) z :=
    hasDerivAt_iff_hasFDerivAt.mp hfz
  have hFR := hF.restrictScalars ℝ
  have h1 : HasFDerivAt (f ∘ (Complex.conjCLE : ℂ → ℂ))
      ((ContinuousLinearMap.toSpanSingleton ℂ (deriv f z)).restrictScalars ℝ |>.comp
        (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap) (conj z) := by
    have hc' : HasFDerivAt (Complex.conjCLE : ℂ → ℂ)
        (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap (conj z) :=
      (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).hasFDerivAt
    have hz : (Complex.conjCLE : ℂ → ℂ) (conj z) = z := by simp
    have hFR' : HasFDerivAt f ((ContinuousLinearMap.toSpanSingleton ℂ (deriv f z)).restrictScalars ℝ)
        ((Complex.conjCLE : ℂ → ℂ) (conj z)) := by rw [hz]; exact hFR
    exact hFR'.comp (conj z) hc'
  have h2 : HasFDerivAt ((Complex.conjCLE : ℂ → ℂ) ∘ f ∘ (Complex.conjCLE : ℂ → ℂ))
      ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.comp
        ((ContinuousLinearMap.toSpanSingleton ℂ (deriv f z)).restrictScalars ℝ |>.comp
          (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap)) (conj z) :=
    (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).hasFDerivAt.comp (conj z) h1
  -- the composite is `f`, and its ℝ-derivative is multiplication by `conj (deriv f z)`
  have hfun : (Complex.conjCLE : ℂ → ℂ) ∘ f ∘ (Complex.conjCLE : ℂ → ℂ) = f := by
    funext w
    simp only [Function.comp, Complex.conjCLE_apply]
    rw [hc, Complex.conj_conj]
  rw [hfun] at h2
  have hlin : (ContinuousLinearMap.toSpanSingleton ℂ (conj (deriv f z))).restrictScalars ℝ
      = (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.comp
        ((ContinuousLinearMap.toSpanSingleton ℂ (deriv f z)).restrictScalars ℝ |>.comp
          (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap) := by
    ext w
    simp [ContinuousLinearMap.toSpanSingleton_apply, Complex.conjCLE_apply]
  have h3 : HasFDerivAt f (ContinuousLinearMap.toSpanSingleton ℂ (conj (deriv f z))) (conj z) :=
    hasFDerivAt_of_restrictScalars ℝ h2 hlin
  exact (hasDerivAt_iff_hasFDerivAt.mpr h3).deriv

/-- Schwarz reflection for the logarithmic derivative. -/
theorem logDeriv_conj_of_conj {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hc : ∀ z, f (conj z) = conj (f z)) (z : ℂ) :
    logDeriv f (conj z) = conj (logDeriv f z) := by
  rw [logDeriv_apply, logDeriv_apply, deriv_conj_of_conj hf hc, hc, map_div₀]

/-- **The kernel lower bound.** -/
theorem integral_kernel_ge {A w : ℝ → ℝ} {t₀ A₀ W : ℝ} (ht₀ : 0 ≤ t₀) (hA₀ : 0 ≤ A₀) (hW : 0 ≤ W)
    (hint : Integrable (fun t => A t * w t)) (hw0 : ∀ t, 0 ≤ w t) (hwW : ∀ t, w t ≤ W)
    (hpos : ∀ t, t₀ ≤ |t| → 0 ≤ A t) (hneg : ∀ t, |t| < t₀ → -A₀ ≤ A t) :
    -(2 * t₀ * A₀ * W) ≤ ∫ t, A t * w t := by
  have hvol : volume (Ioo (-t₀) t₀) ≠ ⊤ := by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  have hind : Integrable ((Ioo (-t₀) t₀).indicator (fun _ : ℝ => -(A₀ * W))) := by
    refine IntegrableOn.integrable_indicator ?_ measurableSet_Ioo
    first
      | exact integrableOn_const_iff.mpr (Or.inr (lt_top_iff_ne_top.mpr hvol))
      | exact integrableOn_const (hs := hvol)
      | exact integrableOn_const hvol
  have hle : (Ioo (-t₀) t₀).indicator (fun _ : ℝ => -(A₀ * W)) ≤ fun t => A t * w t := by
    intro t
    by_cases ht : t ∈ Ioo (-t₀) t₀
    · rw [Set.indicator_of_mem ht]
      have habs : |t| < t₀ := by rw [abs_lt]; exact ⟨ht.1, ht.2⟩
      have h1 := hneg t habs
      have h2 := hw0 t
      have h3 := hwW t
      nlinarith
    · rw [Set.indicator_of_notMem ht]
      have habs : t₀ ≤ |t| := by
        rw [mem_Ioo, not_and_or] at ht
        rw [le_abs]
        rcases ht with h | h
        · right; linarith
        · left; linarith
      exact mul_nonneg (hpos t habs) (hw0 t)
  have := integral_mono hind hint hle
  rw [integral_indicator measurableSet_Ioo, setIntegral_const, measureReal_def, Real.volume_Ioo,
    ENNReal.toReal_ofReal (by linarith)] at this
  calc -(2 * t₀ * A₀ * W) = (t₀ - -t₀) • -(A₀ * W) := by simp; ring
    _ ≤ ∫ t, A t * w t := this

end RankinSelbergDelta.RankinSelberg.ArchimedeanBound
