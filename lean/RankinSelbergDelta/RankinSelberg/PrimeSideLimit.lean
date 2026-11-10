import RankinSelbergDelta.RankinSelberg.ExplicitFormulaRect

/-!
# The prime side of the explicit formula

The right edge of the contour and the prime side of the explicit formula as a limit:
`−∑_{n ≥ 2} Λ_G(n) · 2π g(log n)`, by Laplace inversion and dominated convergence.
-/

open MeasureTheory Filter
open scoped NNReal MatrixGroups Pointwise

noncomputable section


/-! ### The right edge of the explicit formula

The `Λ_G` series of `−G'/G` on `Re s = σ > 1` is pulled through the integral along
a vertical segment, under a bounded weight `h`. -/

namespace RankinSelbergDelta.RankinSelberg

open Complex UpperHalfPlane MeasureTheory Set Filter RankinSelbergDelta.Eisenstein
open scoped Real Topology Modular

variable {F : Type*} [FunLike F ℍ ℂ] (k : ℤ)
  [cf : CuspFormClass F (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma 1)) k]

/-- **Interchange of a `tsum` and an interval integral** under a summable constant majorant. -/
theorem intervalIntegral_tsum_of_bound {F : ℕ → ℝ → ℂ} {M : ℕ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ∀ n, Continuous (F n)) (hM : Summable M) (hbound : ∀ n t, ‖F n t‖ ≤ M n) :
    ∫ t in a..b, ∑' n, F n t = ∑' n, ∫ t in a..b, F n t := by
  have hM0 : ∀ n, 0 ≤ M n := fun n => (norm_nonneg _).trans (hbound n 0)
  simp_rw [intervalIntegral.integral_of_le hab]
  apply integral_tsum
  · intro n
    exact (hcont n).aestronglyMeasurable
  · -- `∑' n, ∫⁻ ‖F n t‖ₑ ≤ ∑' n, ofReal (M n) * ofReal (b − a) < ∞`
    have hle : ∀ n, ∫⁻ t, ‖F n t‖ₑ ∂(volume.restrict (Ioc a b))
        ≤ ENNReal.ofReal (M n) * ENNReal.ofReal (b - a) := by
      intro n
      calc ∫⁻ t, ‖F n t‖ₑ ∂(volume.restrict (Ioc a b))
          ≤ ∫⁻ _, ENNReal.ofReal (M n) ∂(volume.restrict (Ioc a b)) := by
            apply lintegral_mono
            intro t
            show ‖F n t‖ₑ ≤ ENNReal.ofReal (M n)
            rw [← ofReal_norm_eq_enorm]
            exact ENNReal.ofReal_le_ofReal (hbound n t)
        _ = ENNReal.ofReal (M n) * ENNReal.ofReal (b - a) := by
            rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
    rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg hM0 hM]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top


include cf in
/-- **The right edge.** For `σ > 1`, `h` continuous with `‖h(σ + it)‖ ≤ B`, and `a ≤ b`:
`∫_a^b (G'/G)(σ + it) h(σ + it) dt = −∑_n ∫_a^b Λ_G(n) e^{−(σ+it) log n} h(σ + it) dt`. -/
theorem integral_logDeriv_Gfull_right_edge (f : F) (hk : 0 < k)
    (hf : IsHeckeEigenCoeffs (rsCoeff f) k) {σ : ℝ} (hσ : 1 < σ) (h : ℂ → ℂ) (hh : Continuous h)
    {B : ℝ} (hB : ∀ t : ℝ, ‖h ((σ : ℂ) + t * Complex.I)‖ ≤ B) {a b : ℝ} (hab : a ≤ b) :
    ∫ t in a..b, logDeriv (Gfull k f) ((σ : ℂ) + t * Complex.I) * h ((σ : ℂ) + t * Complex.I)
      = -∑' n, ∫ t in a..b, vmTerm (rsVonMangoldt (rsCoeff f) k) ((σ : ℂ) + t * Complex.I) n
          * h ((σ : ℂ) + t * Complex.I) := by
  set Λ := rsVonMangoldt (rsCoeff f) k with hΛdef
  have hΛ : ∀ n, 0 ≤ Λ n := rsVonMangoldt_nonneg _ _
  set ε : ℝ := σ - 1 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hmaj : Summable fun n => (2 / ε) * ‖dlvpTerm Λ ((1 + ε / 2 : ℝ) : ℂ) n‖ * B :=
    ((summable_norm_iff.mpr (summable_dlvpTerm_rs k f hk hf (s := ((1 + ε / 2 : ℝ) : ℂ))
      (by simp only [Complex.ofReal_re]; linarith))).mul_left _).mul_right _
  have hre : ∀ t : ℝ, ((σ : ℂ) + t * Complex.I).re = σ := by intro t; simp
  have hpt : ∀ t : ℝ, logDeriv (Gfull k f) ((σ : ℂ) + t * Complex.I) * h ((σ : ℂ) + t * Complex.I)
      = ∑' n, -(vmTerm Λ ((σ : ℂ) + t * Complex.I) n * h ((σ : ℂ) + t * Complex.I)) := by
    intro t
    rw [logDeriv_Gfull_eq_neg_tsum k f hk hf (by rw [hre]; exact hσ), neg_mul, ← tsum_mul_right,
      ← tsum_neg]
  simp_rw [hpt]
  rw [intervalIntegral_tsum_of_bound hab ?_ hmaj ?_, ← tsum_neg]
  · congr 1
    funext n
    exact intervalIntegral.integral_neg
  · intro n
    by_cases hn : 2 ≤ n
    · simp only [vmTerm, if_pos hn]
      fun_prop
    · simp only [vmTerm, if_neg hn, zero_mul, neg_zero]
      exact continuous_const
  · intro n t
    rw [norm_neg, norm_mul]
    exact mul_le_mul (norm_vmTerm_le_majorant Λ hΛ hεpos (by rw [hre]; linarith) n) (hB t)
      (norm_nonneg _) (by positivity)

end RankinSelbergDelta.RankinSelberg

/-! ### The prime side of the explicit formula as a limit

With `ĝ(s) = ∫ g(x) e^{sx} dx`, `lim_{T→∞} ∫_{−T}^{T} (G'/G)(σ+it) ĝ(σ+it) dt
= −∑_{n≥2} Λ_G(n) · 2π g(log n)`: the right-edge interchange, Laplace inversion at
`y = log n` (namespace `RankinSelbergDelta.LaplaceInv`) and Tannery's
theorem (`tendsto_tsum_of_dominated_convergence`) with the majorant of the right-edge interchange times `∫|ĝ|`. -/

namespace RankinSelbergDelta.LaplaceInv

open MeasureTheory Real
open scoped FourierTransform

/-- **Laplace inversion on the line `Re s = σ`.** -/
theorem laplace_inversion_line (g : ℝ → ℂ) (σ y : ℝ)
    (hg : Integrable (fun x : ℝ => g x * Complex.exp (σ * x)))
    (hF : Integrable (𝓕 (fun x : ℝ => g x * Complex.exp (σ * x))))
    (hc : ContinuousAt g y) :
    ∫ t : ℝ, Complex.exp (-(((σ : ℂ) + t * Complex.I) * y))
        * (∫ x : ℝ, g x * Complex.exp (((σ : ℂ) + t * Complex.I) * x))
      = 2 * Real.pi * g y := by
  set gσ : ℝ → ℂ := fun x => g x * Complex.exp (σ * x) with hgσ
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  -- the inner integral is the Fourier transform of `gσ` at `−t/(2π)`
  have hinner : ∀ t : ℝ, (∫ x : ℝ, g x * Complex.exp (((σ : ℂ) + t * Complex.I) * x))
      = 𝓕 gσ (-t / (2 * Real.pi)) := by
    intro t
    rw [Real.fourier_real_eq_integral_exp_smul]
    congr 1
    funext x
    simp only [hgσ, smul_eq_mul]
    rw [mul_comm (Complex.exp _) (g x * _), mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    field_simp
  simp_rw [hinner]
  -- substitute `w = −t/(2π)`
  have hsub : (∫ t : ℝ, Complex.exp (-(((σ : ℂ) + t * Complex.I) * y)) * 𝓕 gσ (-t / (2 * Real.pi)))
      = ∫ t : ℝ, (fun w : ℝ => Complex.exp (-((σ : ℂ) * y))
          * (Complex.exp (((2 * Real.pi * w * y : ℝ) : ℂ) * Complex.I) * 𝓕 gσ w))
          ((-1 / (2 * Real.pi)) * t) := by
    congr 1
    funext t
    simp only []
    rw [show (-1 / (2 * Real.pi)) * t = -t / (2 * Real.pi) by ring, ← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    field_simp
    ring
  rw [hsub, MeasureTheory.Measure.integral_comp_mul_left (fun w : ℝ => Complex.exp (-((σ : ℂ) * y))
    * (Complex.exp (((2 * Real.pi * w * y : ℝ) : ℂ) * Complex.I) * 𝓕 gσ w)) (-1 / (2 * Real.pi))]
  beta_reduce
  rw [integral_const_mul]
  -- Fourier inversion
  have hcσ : ContinuousAt gσ y := hc.mul (Continuous.continuousAt (by fun_prop))
  have hinv : (∫ w : ℝ, Complex.exp (((2 * Real.pi * w * y : ℝ) : ℂ) * Complex.I) * 𝓕 gσ w)
      = gσ y := by
    have h1 := MeasureTheory.Integrable.fourierInv_fourier_eq hg hF hcσ
    rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul] at h1
    rw [← h1]
    congr 1
    funext w
    simp only [smul_eq_mul]
    congr 2
    push_cast
    ring
  rw [hinv]
  have habs : |(-1 / (2 * Real.pi))⁻¹| = 2 * Real.pi := by
    rw [inv_div, abs_div, abs_neg, abs_one, abs_of_pos Real.two_pi_pos, div_one]
  rw [habs, Complex.real_smul]
  simp only [hgσ]
  rw [mul_comm (g y), ← mul_assoc (Complex.exp _), ← Complex.exp_add]
  push_cast
  rw [show -((σ : ℂ) * y) + σ * y = 0 by ring, Complex.exp_zero, one_mul]


end RankinSelbergDelta.LaplaceInv

namespace RankinSelbergDelta.RankinSelberg

open Complex UpperHalfPlane MeasureTheory Set Filter RankinSelbergDelta.Eisenstein
open scoped Real Topology Modular FourierTransform

variable {F : Type*} [FunLike F ℍ ℂ] (k : ℤ)
  [cf : CuspFormClass F (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma 1)) k]

/-- The two-sided Laplace transform (Mellin transform in `e^x`) of a test function. -/
noncomputable def ghat (g : ℝ → ℂ) (s : ℂ) : ℂ := ∫ x : ℝ, g x * Complex.exp (s * x)

lemma norm_ghat_line_le (g : ℝ → ℂ) (σ t : ℝ) :
    ‖ghat g ((σ : ℂ) + t * Complex.I)‖ ≤ ∫ x : ℝ, ‖g x * Complex.exp (σ * x)‖ := by
  unfold ghat
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext x
  rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp]
  congr 2
  simp [Complex.mul_re]

/-- `ĝ(σ + it) = 𝓕 g_σ (−t/(2π))`. -/
lemma ghat_line_eq_fourier (g : ℝ → ℂ) (σ t : ℝ) :
    ghat g ((σ : ℂ) + t * Complex.I)
      = 𝓕 (fun x : ℝ => g x * Complex.exp (σ * x)) (-t / (2 * Real.pi)) := by
  unfold ghat
  rw [Real.fourier_real_eq_integral_exp_smul]
  congr 1
  funext x
  simp only [smul_eq_mul]
  rw [mul_comm (Complex.exp _) (g x * _), mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  field_simp

lemma integrable_ghat_line (g : ℝ → ℂ) (σ : ℝ)
    (hF : Integrable (𝓕 (fun x : ℝ => g x * Complex.exp (σ * x)))) :
    Integrable (fun t : ℝ => ghat g ((σ : ℂ) + t * Complex.I)) := by
  have hR : (-1 / (2 * Real.pi) : ℝ) ≠ 0 := by
    have := Real.pi_pos
    exact div_ne_zero (by norm_num) (by positivity)
  have h := hF.comp_mul_left' hR
  refine h.congr (Filter.Eventually.of_forall fun t => ?_)
  show 𝓕 (fun x : ℝ => g x * Complex.exp (σ * x)) (-1 / (2 * Real.pi) * t)
    = ghat g ((σ : ℂ) + t * Complex.I)
  rw [ghat_line_eq_fourier]
  congr 1
  ring

include cf in
/-- **The prime side of the explicit formula.** For `σ > 1`, a continuous test function `g` with
`g_σ = g e^{σx}` integrable, `𝓕 g_σ` integrable, and `ĝ` continuous:
`∫_{−T}^{T} (G'/G)(σ+it) ĝ(σ+it) dt → −∑_{n ≥ 2} Λ_G(n) · 2π g(log n)` as `T → ∞`. -/
theorem prime_side_Gfull (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k) {σ : ℝ}
    (hσ : 1 < σ) (g : ℝ → ℂ) (hgc : Continuous g) (hghc : Continuous (ghat g))
    (hg : Integrable (fun x : ℝ => g x * Complex.exp (σ * x)))
    (hF : Integrable (𝓕 (fun x : ℝ => g x * Complex.exp (σ * x)))) :
    Tendsto (fun T : ℝ => ∫ t in (-T)..T,
        logDeriv (Gfull k f) ((σ : ℂ) + t * Complex.I) * ghat g ((σ : ℂ) + t * Complex.I)) atTop
      (𝓝 (-∑' n, if 2 ≤ n then (rsVonMangoldt (rsCoeff f) k n : ℂ) * (2 * Real.pi * g (Real.log n))
        else 0)) := by
  set Λ := rsVonMangoldt (rsCoeff f) k with hΛdef
  have hΛ : ∀ n, 0 ≤ Λ n := rsVonMangoldt_nonneg _ _
  set ε : ℝ := σ - 1 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  set M : ℕ → ℝ := fun n => (2 / ε) * ‖dlvpTerm Λ ((1 + ε / 2 : ℝ) : ℂ) n‖ with hM
  have hMsum : Summable M :=
    (summable_norm_iff.mpr (summable_dlvpTerm_rs k f hk hf (s := ((1 + ε / 2 : ℝ) : ℂ))
      (by simp only [Complex.ofReal_re]; linarith))).mul_left _
  have hre : ∀ t : ℝ, ((σ : ℂ) + t * Complex.I).re = σ := by intro t; simp
  have hvm : ∀ (n : ℕ) (t : ℝ), ‖vmTerm Λ ((σ : ℂ) + t * Complex.I) n‖ ≤ M n := fun n t =>
    norm_vmTerm_le_majorant Λ hΛ hεpos (by rw [hre]; linarith) n
  set B : ℝ := ∫ x : ℝ, ‖g x * Complex.exp (σ * x)‖ with hB
  have hBle : ∀ t : ℝ, ‖ghat g ((σ : ℂ) + t * Complex.I)‖ ≤ B := norm_ghat_line_le g σ
  have hghat : Integrable (fun t : ℝ => ghat g ((σ : ℂ) + t * Complex.I)) :=
    integrable_ghat_line g σ hF
  set C : ℝ := ∫ t : ℝ, ‖ghat g ((σ : ℂ) + t * Complex.I)‖ with hC
  have hpt : ∀ T : ℝ, 0 ≤ T → (∫ t in (-T)..T,
      logDeriv (Gfull k f) ((σ : ℂ) + t * Complex.I) * ghat g ((σ : ℂ) + t * Complex.I))
      = -∑' n, ∫ t in (-T)..T, vmTerm Λ ((σ : ℂ) + t * Complex.I) n
          * ghat g ((σ : ℂ) + t * Complex.I) := fun T hT =>
    integral_logDeriv_Gfull_right_edge k f hk hf hσ (ghat g) hghc hBle (by linarith)
  have hvmc : ∀ n, Continuous fun t : ℝ => vmTerm Λ ((σ : ℂ) + t * Complex.I) n := by
    intro n
    by_cases hn : 2 ≤ n
    · simp only [vmTerm, if_pos hn]; fun_prop
    · simp only [vmTerm, if_neg hn]; exact continuous_const
  have hint : ∀ n, Integrable fun t : ℝ =>
      vmTerm Λ ((σ : ℂ) + t * Complex.I) n * ghat g ((σ : ℂ) + t * Complex.I) := by
    intro n
    refine (hghat.norm.const_mul (M n)).mono'
      ((hvmc n).aestronglyMeasurable.mul hghat.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hvm n t) (norm_nonneg _)
  have hval : ∀ n, (∫ t : ℝ, vmTerm Λ ((σ : ℂ) + t * Complex.I) n
      * ghat g ((σ : ℂ) + t * Complex.I))
      = if 2 ≤ n then (Λ n : ℂ) * (2 * Real.pi * g (Real.log n)) else 0 := by
    intro n
    by_cases hn : 2 ≤ n
    · simp only [vmTerm, if_pos hn]
      simp_rw [mul_assoc]
      rw [integral_const_mul]
      congr 1
      unfold ghat
      exact (RankinSelbergDelta.LaplaceInv.laplace_inversion_line g σ (Real.log n) hg hF
        hgc.continuousAt).trans (by ring)
    · simp [vmTerm, hn]
  have hab : ∀ n, Tendsto (fun T : ℝ => ∫ t in (-T)..T, vmTerm Λ ((σ : ℂ) + t * Complex.I) n
      * ghat g ((σ : ℂ) + t * Complex.I)) atTop
      (𝓝 (if 2 ≤ n then (Λ n : ℂ) * (2 * Real.pi * g (Real.log n)) else 0)) := by
    intro n
    rw [← hval n]
    exact intervalIntegral_tendsto_integral (hint n) tendsto_neg_atTop_atBot tendsto_id
  have hbound : ∀ᶠ T : ℝ in atTop, ∀ n, ‖∫ t in (-T)..T, vmTerm Λ ((σ : ℂ) + t * Complex.I) n
      * ghat g ((σ : ℂ) + t * Complex.I)‖ ≤ M n * C := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT n
    have hTT : -T ≤ T := by linarith
    refine (intervalIntegral.norm_integral_le_integral_norm hTT).trans ?_
    have h1 : ∀ t : ℝ, ‖vmTerm Λ ((σ : ℂ) + t * Complex.I) n * ghat g ((σ : ℂ) + t * Complex.I)‖
        ≤ M n * ‖ghat g ((σ : ℂ) + t * Complex.I)‖ := fun (t : ℝ) => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hvm n t) (norm_nonneg _)
    refine (intervalIntegral.integral_mono_on hTT (hint n).norm.intervalIntegrable
      (hghat.norm.const_mul (M n)).intervalIntegrable (fun t _ => h1 t)).trans ?_
    rw [intervalIntegral.integral_const_mul, hC]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [intervalIntegral.integral_of_le hTT]
    exact setIntegral_le_integral hghat.norm (Filter.Eventually.of_forall fun t => norm_nonneg _)
  have hmain := tendsto_tsum_of_dominated_convergence (f := fun T n => ∫ t in (-T)..T,
      vmTerm Λ ((σ : ℂ) + t * Complex.I) n * ghat g ((σ : ℂ) + t * Complex.I))
    (hMsum.mul_right C) hab hbound
  refine (hmain.neg).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  exact (hpt T hT).symm

end RankinSelbergDelta.RankinSelberg
