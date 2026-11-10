import Mathlib

/-!
# The modular discriminant `Δ = E₄³ − E₆²`

`Δ` as a level-one cusp form of weight 12, built from Mathlib's normalised Eisenstein series: its
constant `q`-coefficient is `1 − 1 = 0`, so it vanishes at the cusp, and its first coefficient is
`3·240 − 2·(−504) = 1728`, so `Δ ≠ 0` (`Δ_ne_zero`). It witnesses the hypotheses of
`RankinSelbergDelta.RankinSelberg.rsD_simplePole` (`rsD_simplePole_hyps_satisfiable`).
-/

open ModularForm EisensteinSeries CongruenceSubgroup UpperHalfPlane Complex Filter Topology
open scoped ModularForm Real

namespace RankinSelbergDelta.CuspForm

/-- The weight-4 normalized Eisenstein series `E4` (level one). -/
noncomputable def E4 : ModularForm (Γ(1) : Subgroup (GL (Fin 2) ℝ)) 4 :=
  E (by norm_num : (3 : ℕ) ≤ 4)

/-- The weight-6 normalized Eisenstein series `E6` (level one). -/
noncomputable def E6 : ModularForm (Γ(1) : Subgroup (GL (Fin 2) ℝ)) 6 :=
  E (by norm_num : (3 : ℕ) ≤ 6)

/-- `E4^3`, weight 12. -/
noncomputable def E4cubed : ModularForm (Γ(1) : Subgroup (GL (Fin 2) ℝ)) 12 :=
  (E4.mul E4).mul E4

/-- `E6^2`, weight 12. -/
noncomputable def E6sq : ModularForm (Γ(1) : Subgroup (GL (Fin 2) ℝ)) 12 :=
  E6.mul E6

/-- The modular discriminant (unnormalized), `Δ = E4^3 − E6^2`, as a weight-12 modular form of
level one. -/
noncomputable def ΔModular : ModularForm (Γ(1) : Subgroup (GL (Fin 2) ℝ)) 12 :=
  E4cubed - E6sq

/-- `1` is a strict period of the level-one group. -/
lemma one_mem_strictPeriods_levelOne :
    (1 : ℝ) ∈ (Γ(1) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

/-! ### The `q`-expansion of `E_k` as a `HasSum` over `ℕ` -/

/-- `σ_j(n) ≤ n^(j+1)`. -/
lemma sigma_le_pow (j n : ℕ) : (ArithmeticFunction.sigma j n : ℝ) ≤ (n : ℝ) ^ (j + 1) := by
  rw [ArithmeticFunction.sigma_apply]
  push_cast
  calc (∑ d ∈ n.divisors, (d : ℝ) ^ j) ≤ ∑ d ∈ n.divisors, (n : ℝ) ^ j := by
        refine Finset.sum_le_sum fun d hd => ?_
        exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.divisor_le hd) j
    _ = (n.divisors.card : ℝ) * (n : ℝ) ^ j := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (n : ℝ) * (n : ℝ) ^ j := by
        gcongr
        exact_mod_cast Nat.card_divisors_le_self n
    _ = (n : ℝ) ^ (j + 1) := by ring

/-- The `q`-coefficients of `E_k`: `c 0 = 1`, `c m = −(2k/B_k) σ_{k−1}(m)` for `m ≥ 1`. -/
noncomputable def eisCoeff (k : ℕ) (m : ℕ) : ℂ :=
  if m = 0 then 1 else -(2 * (k : ℂ) / ((bernoulli k : ℚ) : ℂ)) * (ArithmeticFunction.sigma (k - 1) m : ℂ)

lemma eisCoeff_zero (k : ℕ) : eisCoeff k 0 = 1 := by simp [eisCoeff]

lemma eisCoeff_one (k : ℕ) : eisCoeff k 1 = -(2 * (k : ℂ) / ((bernoulli k : ℚ) : ℂ)) := by
  simp [eisCoeff, ArithmeticFunction.sigma_apply]

/-- The tail of the Eisenstein `q`-series is summable. -/
lemma summable_sigma_mul_qpow {k : ℕ} (hk : 1 ≤ k) (τ : ℍ) :
    Summable fun n : ℕ => (ArithmeticFunction.sigma (k - 1) (n + 1) : ℂ) * cexp (2 * π * Complex.I * τ) ^ (n + 1) := by
  have h1 : Summable fun c : ℕ => (c : ℂ) ^ k * cexp (2 * π * Complex.I * τ) ^ c := by
    have := summable_pow_mul_cexp k 1 τ
    simpa using this
  have h2 : Summable fun n : ℕ => ((n + 1 : ℕ) : ℂ) ^ k * cexp (2 * π * Complex.I * τ) ^ (n + 1) :=
    (summable_nat_add_iff 1).mpr h1
  refine Summable.of_norm_bounded h2.norm fun n => ?_
  rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_natCast, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have := sigma_le_pow (k - 1) (n + 1)
  rwa [Nat.sub_add_cancel hk] at this

/-- **The `q`-expansion of `E_k` as a `HasSum`**: `E_k(τ) = Σ_m c_m 𝕢(τ)^m`. -/
lemma hasSum_E_qExpansion {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) (τ : ℍ) :
    HasSum (fun m : ℕ => eisCoeff k m • Function.Periodic.qParam 1 τ ^ m) (E hk τ) := by
  have hq : Function.Periodic.qParam 1 (τ : ℂ) = cexp (2 * π * Complex.I * τ) := by
    simp [Function.Periodic.qParam]
  have hE := q_expansion_bernoulli hk hk2 τ
  have hsum := summable_sigma_mul_qpow (by omega : 1 ≤ k) τ
  have htail : HasSum (fun n : ℕ => eisCoeff k (n + 1) • Function.Periodic.qParam 1 τ ^ (n + 1))
      (E hk τ - ∑ i ∈ Finset.range 1, eisCoeff k i • Function.Periodic.qParam 1 τ ^ i) := by
    have h := hsum.hasSum.mul_left (-(2 * (k : ℂ) / ((bernoulli k : ℚ) : ℂ)))
    have hval : -(2 * (k : ℂ) / ((bernoulli k : ℚ) : ℂ))
        * ∑' n : ℕ, (ArithmeticFunction.sigma (k - 1) (n + 1) : ℂ) * cexp (2 * π * Complex.I * τ) ^ (n + 1)
        = E hk τ - ∑ i ∈ Finset.range 1, eisCoeff k i • Function.Periodic.qParam 1 τ ^ i := by
      rw [Finset.sum_range_one, eisCoeff_zero, pow_zero, smul_eq_mul, mul_one, hE]
      simp only [zpow_natCast]
      rw [tsum_pnat_eq_tsum_succ
        (f := fun n : ℕ => (ArithmeticFunction.sigma (k - 1) n : ℂ) * cexp (2 * π * Complex.I * τ) ^ n)]
      ring
    rw [hval] at h
    have heq : (fun n : ℕ => eisCoeff k (n + 1) • Function.Periodic.qParam 1 τ ^ (n + 1))
        = fun n : ℕ => -(2 * (k : ℂ) / ((bernoulli k : ℚ) : ℂ))
          * ((ArithmeticFunction.sigma (k - 1) (n + 1) : ℂ) * cexp (2 * π * Complex.I * τ) ^ (n + 1)) := by
      funext n
      simp only [eisCoeff, Nat.succ_ne_zero, if_false, hq, smul_eq_mul]
      ring
    rw [heq]
    exact h
  exact (hasSum_nat_add_iff' 1).mp htail

/-! ### The coefficients of `E4`, `E6`, and `Δ` -/

lemma coeff_E4 (m : ℕ) : (ModularFormClass.qExpansion 1 E4).coeff m = eisCoeff 4 m :=
  (qExpansion_coeff_unique one_pos one_mem_strictPeriods_levelOne
    (hasSum_E_qExpansion (by norm_num : (3 : ℕ) ≤ 4) (by decide) ) m).symm

lemma coeff_E6 (m : ℕ) : (ModularFormClass.qExpansion 1 E6).coeff m = eisCoeff 6 m :=
  (qExpansion_coeff_unique one_pos one_mem_strictPeriods_levelOne
    (hasSum_E_qExpansion (by norm_num : (3 : ℕ) ≤ 6) (by decide) ) m).symm

lemma bernoulli'_six : bernoulli' 6 = 1 / 42 := by
  have h5 : bernoulli' 5 = 0 := bernoulli'_odd_eq_zero (by decide) (by norm_num)
  have c2 : Nat.choose 6 2 = 15 := by decide
  have c3 : Nat.choose 6 3 = 20 := by decide
  have c4 : Nat.choose 6 4 = 15 := by decide
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, h5, c2, c3, c4]

lemma bernoulli_four : bernoulli 4 = -1 / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four]

lemma bernoulli_six : bernoulli 6 = 1 / 42 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_six]

lemma coeff_E4_zero : (ModularFormClass.qExpansion 1 E4).coeff 0 = 1 := by rw [coeff_E4, eisCoeff_zero]
lemma coeff_E6_zero : (ModularFormClass.qExpansion 1 E6).coeff 0 = 1 := by rw [coeff_E6, eisCoeff_zero]

lemma coeff_E4_one : (ModularFormClass.qExpansion 1 E4).coeff 1 = 240 := by
  rw [coeff_E4, eisCoeff_one, bernoulli_four]
  push_cast
  norm_num

lemma coeff_E6_one : (ModularFormClass.qExpansion 1 E6).coeff 1 = -504 := by
  rw [coeff_E6, eisCoeff_one, bernoulli_six]
  push_cast
  norm_num

/-- `coeff 1` of a product of power series. -/
lemma coeff_one_mul (φ ψ : PowerSeries ℂ) :
    (φ * ψ).coeff 1 = φ.coeff 0 * ψ.coeff 1 + φ.coeff 1 * ψ.coeff 0 := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

lemma coeff_zero_mul' (φ ψ : PowerSeries ℂ) : (φ * ψ).coeff 0 = φ.coeff 0 * ψ.coeff 0 := by
  rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton]

lemma qExpansion_ΔModular :
    ModularFormClass.qExpansion 1 ΔModular = ModularFormClass.qExpansion 1 E4 * ModularFormClass.qExpansion 1 E4 * ModularFormClass.qExpansion 1 E4
      - ModularFormClass.qExpansion 1 E6 * ModularFormClass.qExpansion 1 E6 := by
  have h := (qExpansionAddHom (h := 1) one_pos one_mem_strictPeriods_levelOne 12).map_sub
    E4cubed E6sq
  have h3 : ModularFormClass.qExpansion 1 E4cubed = ModularFormClass.qExpansion 1 E4 * ModularFormClass.qExpansion 1 E4 * ModularFormClass.qExpansion 1 E4 := by
    unfold E4cubed
    rw [ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_levelOne,
      ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_levelOne]
  have h2 : ModularFormClass.qExpansion 1 E6sq = ModularFormClass.qExpansion 1 E6 * ModularFormClass.qExpansion 1 E6 := by
    unfold E6sq
    rw [ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_levelOne]
  rw [← h3, ← h2]
  exact h

lemma coeff_ΔModular_zero : (ModularFormClass.qExpansion 1 ΔModular).coeff 0 = 0 := by
  rw [qExpansion_ΔModular, map_sub, coeff_zero_mul', coeff_zero_mul', coeff_zero_mul',
    coeff_E4_zero, coeff_E6_zero]
  ring

lemma coeff_ΔModular_one : (ModularFormClass.qExpansion 1 ΔModular).coeff 1 = 1728 := by
  rw [qExpansion_ΔModular, map_sub, coeff_one_mul, coeff_one_mul, coeff_zero_mul', coeff_one_mul,
    coeff_E4_zero, coeff_E6_zero, coeff_E4_one, coeff_E6_one]
  norm_num

/-! ### Cusp vanishing and nonvanishing -/

lemma valueAtInfty_ΔModular : valueAtInfty (⇑ΔModular) = 0 := by
  rw [← ModularFormClass.qExpansion_coeff_zero (f := ΔModular) (k := 12) one_pos
    one_mem_strictPeriods_levelOne, coeff_ΔModular_zero]

lemma isZeroAtImInfty_ΔModular : IsZeroAtImInfty (⇑ΔModular) := by
  have h := ModularFormClass.exp_decay_sub_atImInfty (f := ΔModular) (k := 12) one_pos
    one_mem_strictPeriods_levelOne
  rw [valueAtInfty_ΔModular] at h
  simp only [sub_zero] at h
  have hexp : Tendsto (fun τ : ℍ => Real.exp (-2 * π * τ.im / 1)) atImInfty (𝓝 0) := by
    refine Real.tendsto_exp_atBot.comp ?_
    have h1 : Tendsto (fun τ : ℍ => τ.im) atImInfty atTop := tendsto_comap
    have h2 : Tendsto (fun τ : ℍ => (2 * π) * τ.im) atImInfty atTop :=
      h1.const_mul_atTop (by positivity)
    have h3 := tendsto_neg_atTop_atBot.comp h2
    refine h3.congr fun τ => ?_
    simp only [Function.comp_def]
    ring
  exact h.trans_tendsto hexp

/-- `Δ` as a cusp form: it vanishes at every cusp because its constant `q`-coefficient is
`1 − 1 = 0`. -/
noncomputable def Δ : CuspForm (Γ(1) : Subgroup (GL (Fin 2) ℝ)) 12 where
  toSlashInvariantForm := ΔModular.toSlashInvariantForm
  holo' := ΔModular.holo'
  zero_at_cusps' := by
    intro c hc
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    simp only [SlashInvariantForm.toFun_eq_coe, ModularForm.toSlashInvariantForm_coe]
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    have hmem : ((γ : GL (Fin 2) ℝ)) ∈ (Γ(1) : Subgroup (GL (Fin 2) ℝ)) :=
      Subgroup.mem_map.mpr ⟨γ, mem_Gamma_one γ, rfl⟩
    rw [SL_slash, SlashInvariantForm.slash_action_eqn ΔModular _ hmem]
    exact isZeroAtImInfty_ΔModular

lemma coe_Δ : (⇑Δ : ℍ → ℂ) = ⇑ΔModular := rfl

/-- `Δ` is not the zero cusp form: its `q¹`-coefficient is `1728 ≠ 0`. -/
theorem Δ_ne_zero : (⇑Δ : ℍ → ℂ) ≠ 0 := by
  intro h
  rw [coe_Δ] at h
  have h0 : ΔModular = 0 := DFunLike.coe_injective (by simpa using h)
  have h1 := coeff_ΔModular_one
  rw [h0, ModularForm.coe_zero, qExpansion_zero] at h1
  simp at h1

/-- Witness that the hypotheses of `rsD_simplePole` are satisfiable: `Δ` is a concrete nonzero
level-one weight-12 cusp form. -/
theorem rsD_simplePole_hyps_satisfiable :
    ∃ (f : CuspForm (Γ(1) : Subgroup (GL (Fin 2) ℝ)) 12), (0 : ℤ) < 12 ∧ (⇑f : ℍ → ℂ) ≠ 0 :=
  ⟨Δ, by norm_num, Δ_ne_zero⟩

end RankinSelbergDelta.CuspForm
