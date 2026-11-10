import Mathlib
import RankinSelbergDelta.CuspForm.DeltaHeckeEigenform
import RankinSelbergDelta.RankinSelberg.EdgeNonvanishing

/-!
# `L(Δ, 1 + it) ≠ 0`

The normalised discriminant `fΔ = Δ/1728` has `q`-coefficients `τ(n)`. Its coefficients satisfy the
Hecke relations (`isHeckeEigenCoeffs_rsCoeff_fΔ`) and are real (`hreal_fΔ`), so
`RankinSelbergDelta.RankinSelberg.Lfunction_ne_zero_on_one_line` applies:
`L(Δ, 1 + it) ≠ 0` for every real `t ≠ 0` (`Lfunction_ne_zero_Delta`).
-/

open RankinSelbergDelta.RankinSelberg Complex
open scoped CongruenceSubgroup

namespace RankinSelbergDelta.Hecke

noncomputable section

/-- The normalized discriminant `Δ/1728` as a level-one weight-12 cusp form (`a(1) = 1`). -/
noncomputable def fΔ : CuspForm (Γ(1) : Subgroup (GL (Fin 2) ℝ)) 12 :=
  (1 / 1728 : ℂ) • RankinSelbergDelta.CuspForm.Δ

/-- The `q`-coefficients of `fΔ` are the normalized `Δ` coefficients `aΔ`. -/
lemma rsCoeff_fΔ : rsCoeff fΔ = aΔ := by
  funext n
  have h : ModularFormClass.qExpansion 1 fΔ
      = (1 / 1728 : ℂ) • ModularFormClass.qExpansion 1 RankinSelbergDelta.CuspForm.Δ := by
    show ModularFormClass.qExpansion 1 ((1 / 1728 : ℂ) • RankinSelbergDelta.CuspForm.Δ) = _
    exact qExpansion_smul one_pos RankinSelbergDelta.CuspForm.one_mem_strictPeriods_levelOne _ _
  rw [rsCoeff, h, aΔ_eq_coeff_Δ]
  simp [smul_eq_mul]

/-- `fΔ` satisfies the Hecke-eigenform relations (three fields proved). -/
lemma isHeckeEigenCoeffs_rsCoeff_fΔ : IsHeckeEigenCoeffs (rsCoeff fΔ) 12 := by
  rw [rsCoeff_fΔ]; exact isHeckeEigenCoeffs_aΔ'

/-- `fΔ` has real `q`-coefficients. -/
lemma hreal_fΔ : ∀ n, (starRingEnd ℂ) (rsCoeff fΔ n) = rsCoeff fΔ n := by
  intro n; rw [rsCoeff_fΔ]; exact conj_coeff_ΔnormM n

/-- **`L(Δ, 1 + it) ≠ 0`**: for the concrete normalized real Hecke eigenform `Δ`, the completed
`L`-function is nonzero at `1 + it` for every real `t ≠ 0`. -/
theorem Lfunction_ne_zero_Delta {t : ℝ} (ht : t ≠ 0) :
    Lfun 12 fΔ (by norm_num) (1 + Complex.I * t) ≠ 0 :=
  Lfunction_ne_zero_on_one_line 12 fΔ (by norm_num) isHeckeEigenCoeffs_rsCoeff_fΔ hreal_fΔ ht

/-- Witness that the hypotheses of `Lfunction_ne_zero_Delta` can all hold: the structural
hypotheses (`IsHeckeEigenCoeffs`, `hreal`) are discharged for the concrete `fΔ` by
`isHeckeEigenCoeffs_rsCoeff_fΔ` and `hreal_fΔ` (both proved), and the remaining hypothesis `t ≠ 0`
is satisfiable (`t = 1`). So the theorem is non-vacuous. -/
theorem Lfunction_ne_zero_Delta_hyps_satisfiable :
    RankinSelbergDelta.RankinSelberg.IsHeckeEigenCoeffs (RankinSelbergDelta.RankinSelberg.rsCoeff fΔ) 12
      ∧ (∀ n, (starRingEnd ℂ) (RankinSelbergDelta.RankinSelberg.rsCoeff fΔ n)
          = RankinSelbergDelta.RankinSelberg.rsCoeff fΔ n)
      ∧ ∃ t : ℝ, t ≠ 0 :=
  ⟨isHeckeEigenCoeffs_rsCoeff_fΔ, hreal_fΔ, 1, one_ne_zero⟩

end

end RankinSelbergDelta.Hecke
