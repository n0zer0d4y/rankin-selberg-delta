/-
  Axiom check: every theorem cited in a claims.md (main theorems, their specialisations to Δ, and the
  witnesses) should depend only on `propext`, `Classical.choice` and `Quot.sound`
  (no `sorryAx`, no `Lean.ofReduceBool`). Run from `lean/`:  lake env lean AxiomCheck.lean
-/
import RankinSelbergDelta

open RankinSelbergDelta

-- Paper 1: the Rankin–Selberg pole and L(f, 1 + it) ≠ 0
#print axioms RankinSelberg.rsD_simplePole
#print axioms RankinSelberg.rsD_continuation
#print axioms CuspForm.Δ_ne_zero
#print axioms CuspForm.rsD_simplePole_hyps_satisfiable
#print axioms Hecke.heckeT_Delta_eq_smul
#print axioms Hecke.isHeckeEigenCoeffs_rsCoeff_fΔ
#print axioms Hecke.hreal_fΔ
#print axioms RankinSelberg.rs_square_ne_zero
#print axioms RankinSelberg.Lfunction_ne_zero_on_one_line
#print axioms Hecke.Lfunction_ne_zero_Delta
#print axioms Hecke.Lfunction_ne_zero_Delta_hyps_satisfiable
#print axioms Delta.fΔ_ne_zero
#print axioms Delta.rankinSelberg_pole_Delta

-- Paper 2: the zero-free region
#print axioms RankinSelberg.zero_free_of_logDeriv_341
#print axioms RankinSelberg.rs_zero_free_region
#print axioms Delta.zero_free_region_Delta

-- Paper 3: the explicit formula
#print axioms RankinSelberg.differentiable_rsHent
#print axioms RankinSelberg.rsHent_eq
#print axioms RankinSelberg.exists_wcount_zeros_rsHent_le_mul_log
#print axioms RankinSelberg.explicitFormula_Gfull_tsum
#print axioms RankinSelberg.explicitFormula_Gfull_tsum_of_smooth
#print axioms RankinSelberg.explicitFormula_Gfull_tsum_hyps_satisfiable
#print axioms Delta.explicit_formula_Delta
#print axioms Delta.explicit_formula_Delta_hyps_satisfiable

-- Supporting: Hurwitz's theorem in zero-locus form
#print axioms Shared.hurwitz_zero_locus
