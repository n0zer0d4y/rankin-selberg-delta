import Mathlib
import RankinSelbergDelta.CuspForm.Discriminant
import RankinSelbergDelta.RankinSelberg.HeckeEuler

/-!
# Hecke operators on level-one forms

The Hecke operator `T_p` on weight-`k` level-one forms, defined through the `p + 1` coset
representatives of determinant `p` and the `GL(2, ℝ)` slash action: the coset matrices, their
determinants, the definition of `T_p`, and its action on `q`-expansions.
-/

open Matrix Complex UpperHalfPlane CongruenceSubgroup
open scoped ModularForm MatrixGroups

namespace RankinSelbergDelta.Hecke

/-- A real `2x2` matrix of nonzero determinant, as an element of `GL(2,R)`. -/
noncomputable def mkGL (M : Matrix (Fin 2) (Fin 2) ℝ) (h : M.det ≠ 0) : GL (Fin 2) ℝ :=
  ((Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr h)).unit

@[simp] lemma mkGL_coe (M : Matrix (Fin 2) (Fin 2) ℝ) (h : M.det ≠ 0) :
    (mkGL M h : Matrix (Fin 2) (Fin 2) ℝ) = M := by
  simp [mkGL]

@[simp] lemma mkGL_apply (M : Matrix (Fin 2) (Fin 2) ℝ) (h : M.det ≠ 0) (i j : Fin 2) :
    (mkGL M h) i j = M i j := by
  change (mkGL M h : Matrix (Fin 2) (Fin 2) ℝ) i j = M i j
  rw [mkGL_coe]

/-- The coset representative `[[1, j], [0, p]]` (determinant `p`). -/
noncomputable def heckeCoset (p j : ℕ) (hp : (p : ℝ) ≠ 0) : GL (Fin 2) ℝ :=
  mkGL !![1, (j : ℝ); 0, (p : ℝ)] (by
    rw [Matrix.det_fin_two_of]; simpa using hp)

/-- The coset representative `[[p, 0], [0, 1]]` (determinant `p`). -/
noncomputable def heckeCosetInf (p : ℕ) (hp : (p : ℝ) ≠ 0) : GL (Fin 2) ℝ :=
  mkGL !![(p : ℝ), 0; 0, 1] (by
    rw [Matrix.det_fin_two_of]; simpa using hp)

lemma det_heckeCoset (p j : ℕ) (hp : (p : ℝ) ≠ 0) :
    (heckeCoset p j hp).det.val = (p : ℝ) := by
  simp [heckeCoset, Matrix.GeneralLinearGroup.val_det_apply, mkGL_coe, Matrix.det_fin_two_of]

lemma det_heckeCosetInf (p : ℕ) (hp : (p : ℝ) ≠ 0) :
    (heckeCosetInf p hp).det.val = (p : ℝ) := by
  simp [heckeCosetInf, Matrix.GeneralLinearGroup.val_det_apply, mkGL_coe, Matrix.det_fin_two_of]

/-- The weight-`k` Hecke operator `T_p` on functions `ℍ → ℂ`, as the slash-sum over the
`p + 1` determinant-`p` coset representatives. -/
noncomputable def heckeT (p : ℕ) (k : ℤ) (hp : (p : ℝ) ≠ 0) (f : ℍ → ℂ) : ℍ → ℂ :=
  fun z => (∑ j ∈ Finset.range p, (f ∣[k] heckeCoset p j hp) z) + (f ∣[k] heckeCosetInf p hp) z

/-! ### The normalized discriminant (`a(1) = 1`) and its base coefficients.

`IsHeckeEigenCoeffs` requires the leading coefficient `a(1) = 1`. The unnormalized
`Δ = E₄³ − E₆²` has `q¹`-coefficient `1728`, so the normalized form is `Δ / 1728`. We work at
the `ModularForm` level (where `coeff_ΔModular_zero/one` and `qExpansion_smul` apply directly);
the `CuspForm` packaging is done at assembly. -/

/-- The normalized discriminant `Δ / 1728` as a weight-12 level-one modular form (`a(1) = 1`). -/
noncomputable def ΔnormM := (1 / 1728 : ℂ) • RankinSelbergDelta.CuspForm.ΔModular

/-- The `q`-coefficients of the normalized discriminant: `(1/1728)` times those of `Δ`. -/
lemma coeff_ΔnormM (n : ℕ) :
    (ModularFormClass.qExpansion 1 ΔnormM).coeff n
      = (1 / 1728 : ℂ) * (ModularFormClass.qExpansion 1 RankinSelbergDelta.CuspForm.ΔModular).coeff n := by
  have h : ModularFormClass.qExpansion 1 ΔnormM
      = (1 / 1728 : ℂ) • ModularFormClass.qExpansion 1 RankinSelbergDelta.CuspForm.ΔModular := by
    show ModularFormClass.qExpansion 1 ((1 / 1728 : ℂ) • RankinSelbergDelta.CuspForm.ΔModular) = _
    exact qExpansion_smul one_pos RankinSelbergDelta.CuspForm.one_mem_strictPeriods_levelOne _ _
  rw [h]
  simp [smul_eq_mul]

/-- The normalized discriminant is a cusp form: constant `q`-coefficient `0`. -/
lemma coeff_ΔnormM_zero : (ModularFormClass.qExpansion 1 ΔnormM).coeff 0 = 0 := by
  rw [coeff_ΔnormM, RankinSelbergDelta.CuspForm.coeff_ΔModular_zero]; ring

/-- The normalized discriminant has leading coefficient `a(1) = 1` (`τ(1) = 1`). -/
lemma coeff_ΔnormM_one : (ModularFormClass.qExpansion 1 ΔnormM).coeff 1 = 1 := by
  rw [coeff_ΔnormM, RankinSelbergDelta.CuspForm.coeff_ΔModular_one]; norm_num

/-! ### The root-of-unity sum (the arithmetic core of the Hecke q-expansion).

`Σ_{j<p} ζ^j = p` when `p ∣ n`, else `0`, where `ζ = e^{2πi n / p}` -- this is what makes the
`Σ_{j<p} f((z+j)/p)` term of `T_p` collapse to `p · Σ_m a(pm) q^m`. Self-contained (no modular
forms), from `geom_sum`. -/

private lemma two_pi_I_ne_zero' : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
  mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero

/-- `ζ := e^{2πi n/p}` satisfies `ζ^p = 1`. -/
lemma rootOfUnity_pow (p n : ℕ) (hp : 0 < p) :
    (Complex.exp (2 * ↑Real.pi * Complex.I * ↑n / ↑p)) ^ p = 1 := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [← Complex.exp_nat_mul]
  rw [show (↑p * (2 * ↑Real.pi * Complex.I * ↑n / ↑p)) = (↑n : ℂ) * (2 * ↑Real.pi * Complex.I) by
    field_simp]
  rw [Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow]

/-- **The root-of-unity sum**: `Σ_{j<p} (e^{2πi n/p})^j = p` if `p ∣ n`, else `0`. -/
lemma sum_rootOfUnity (p n : ℕ) (hp : 0 < p) :
    ∑ j ∈ Finset.range p, (Complex.exp (2 * ↑Real.pi * Complex.I * ↑n / ↑p)) ^ j
      = if p ∣ n then (p : ℂ) else 0 := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  set ζ := Complex.exp (2 * ↑Real.pi * Complex.I * ↑n / ↑p) with hζ
  by_cases hpn : p ∣ n
  · have hζ1 : ζ = 1 := by
      obtain ⟨m, rfl⟩ := hpn
      rw [hζ, show (2 * ↑Real.pi * Complex.I * ↑(p * m) / ↑p : ℂ)
          = (↑m : ℂ) * (2 * ↑Real.pi * Complex.I) by
        push_cast; field_simp, Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow]
    simp [hζ1, hpn]
  · have hζne : ζ ≠ 1 := by
      intro h
      apply hpn
      obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp (hζ ▸ h)
      -- hk : 2πI·n/p = k·(2πI);  cancel 2πI and clear p  ⇒  n = k·p
      rw [div_eq_iff hp'] at hk
      have hn : (n : ℂ) = (k : ℂ) * p :=
        mul_left_cancel₀ two_pi_I_ne_zero' (by linear_combination hk)
      have hdvd : (p : ℤ) ∣ (n : ℤ) := ⟨k, by exact_mod_cast (by rw [hn]; ring : (n : ℂ) = p * k)⟩
      exact_mod_cast hdvd
    rw [geom_sum_eq hζne, rootOfUnity_pow p n hp, sub_self, zero_div, if_neg hpn]

/-! ### Explicit slash values of the coset representatives.

`f ∣[k] [[p,0],[0,1]] = p^{k-1} f(p·τ)` and `f ∣[k] [[1,j],[0,p]] = p^{-1} f((τ+j)/p)`, from
`ModularForm.slash_apply` (`σ = id` for `det > 0`, `denom`/`num` computed on the explicit
matrices). -/

open ModularForm in
/-- Slash value on the `∞`-coset: `f ∣[k] [[p,0],[0,1]] (τ) = p^{k-1} · f(([[p,0],[0,1]]) • τ)`. -/
lemma heckeCosetInf_slash_apply (p : ℕ) (k : ℤ) (hp0 : 0 < p) (hne : (p : ℝ) ≠ 0)
    (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] heckeCosetInf p hne) τ
      = ((p : ℝ) : ℂ) ^ (k - 1) * f (heckeCosetInf p hne • τ) := by
  have hdet : (0 : ℝ) < (heckeCosetInf p hne).det.val := by
    rw [det_heckeCosetInf]; exact_mod_cast hp0
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
  rw [slash_apply, show UpperHalfPlane.σ (heckeCosetInf p hne) = RingHom.id ℂ from by rw [UpperHalfPlane.σ, if_pos hdet]]
  have hden : denom (heckeCosetInf p hne) (τ : ℂ) = 1 := by
    simp [denom, heckeCosetInf, mkGL_coe, Matrix.cons_val_one, Matrix.cons_val_zero,
      Matrix.head_cons]
  rw [RingHom.id_apply, hden, _root_.one_zpow, mul_one, det_heckeCosetInf, abs_of_pos hppos]
  push_cast
  ring

open ModularForm in
/-- Slash value on the `j`-coset: `f ∣[k] [[1,j],[0,p]] (τ) = p^{-1} · f(([[1,j],[0,p]]) • τ)`. -/
lemma heckeCoset_slash_apply (p j : ℕ) (k : ℤ) (hp0 : 0 < p) (hne : (p : ℝ) ≠ 0)
    (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] heckeCoset p j hne) τ
      = ((p : ℝ) : ℂ) ^ (-1 : ℤ) * f (heckeCoset p j hne • τ) := by
  have hdet : (0 : ℝ) < (heckeCoset p j hne).det.val := by
    rw [det_heckeCoset]; exact_mod_cast hp0
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
  have hcne : ((p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hne
  rw [slash_apply, show UpperHalfPlane.σ (heckeCoset p j hne) = RingHom.id ℂ from by rw [UpperHalfPlane.σ, if_pos hdet]]
  have hden : denom (heckeCoset p j hne) (τ : ℂ) = ((p : ℝ) : ℂ) := by
    simp [denom, heckeCoset, mkGL_coe, Matrix.cons_val_one, Matrix.cons_val_zero,
      Matrix.head_cons]
  have hpow : ((p : ℝ) : ℂ) ^ (k - 1) * ((p : ℝ) : ℂ) ^ (-k) = ((p : ℝ) : ℂ) ^ (-1 : ℤ) := by
    rw [← zpow_add₀ hcne]; congr 1; ring
  rw [RingHom.id_apply, hden, det_heckeCoset, abs_of_pos hppos, mul_assoc, hpow, mul_comm]

/-! ### The explicit form of `T_p` as a sum of translates/scalings. -/

/-- `(T_p f)(z) = Σ_{j<p} p^{-1} f((z+j)/p) + p^{k-1} f(pz)` (values as `ℍ`-points via the
coset Möbius action), directly from the slash values. -/
lemma heckeT_eq (p : ℕ) (k : ℤ) (hp0 : 0 < p) (hne : (p : ℝ) ≠ 0) (f : ℍ → ℂ) (z : ℍ) :
    heckeT p k hne f z
      = (∑ j ∈ Finset.range p, ((p : ℝ) : ℂ) ^ (-1 : ℤ) * f (heckeCoset p j hne • z))
        + ((p : ℝ) : ℂ) ^ (k - 1) * f (heckeCosetInf p hne • z) := by
  simp only [heckeT]
  rw [heckeCosetInf_slash_apply p k hp0 hne f z]
  congr 1
  exact Finset.sum_congr rfl (fun j _ => heckeCoset_slash_apply p j k hp0 hne f z)

/-! ### The Möbius action of the cosets on `ℍ`. -/

/-- `heckeCoset p j • τ = (τ + j) / p` in `ℂ`. -/
lemma coe_heckeCoset_smul (p j : ℕ) (hp0 : 0 < p) (hp : (p : ℝ) ≠ 0) (τ : ℍ) :
    (↑(heckeCoset p j hp • τ) : ℂ) = ((τ : ℂ) + (j : ℂ)) / (p : ℂ) := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (by rw [det_heckeCoset]; exact_mod_cast hp0)]
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, heckeCoset, mkGL_coe, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  push_cast
  ring

/-- `heckeCosetInf p • τ = p · τ` in `ℂ`. -/
lemma coe_heckeCosetInf_smul (p : ℕ) (hp0 : 0 < p) (hp : (p : ℝ) ≠ 0) (τ : ℍ) :
    (↑(heckeCosetInf p hp • τ) : ℂ) = (p : ℂ) * (τ : ℂ) := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (by rw [det_heckeCosetInf]; exact_mod_cast hp0)]
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, heckeCosetInf, mkGL_coe, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  push_cast
  ring

/-- The `q`-parameter at `heckeCosetInf • τ` is `(𝕢 1 τ)^p` (the `f(pτ)` term contributes
`q^{pm}`). -/
lemma qParam_heckeCosetInf_smul (p : ℕ) (hp0 : 0 < p) (hp : (p : ℝ) ≠ 0) (τ : ℍ) :
    Function.Periodic.qParam 1 (↑(heckeCosetInf p hp • τ))
      = (Function.Periodic.qParam 1 (τ : ℂ)) ^ p := by
  simp only [Function.Periodic.qParam, div_one, coe_heckeCosetInf_smul p hp0 hp τ]
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

/-- The `q`-parameter at `heckeCoset p j • τ` splits as a `p`-th root times a `p`-th root of
unity (the Fourier phase that `sum_rootOfUnity` collapses). -/
lemma qParam_heckeCoset_smul (p j : ℕ) (hp0 : 0 < p) (hp : (p : ℝ) ≠ 0) (τ : ℍ) :
    Function.Periodic.qParam 1 (↑(heckeCoset p j hp • τ))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) / p)
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) / p) := by
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one,
    coe_heckeCoset_smul p j hp0 hp τ]
  rw [← Complex.exp_add]
  congr 1
  ring

/-! ### The `heckeCosetInf` term of the `T_p` `q`-expansion. -/

/-- The `heckeCosetInf` (i.e. `f(pτ)`) term: `f(pτ) = Σ_n [p∣n] a(n/p) · q^n`, read off
`a(m) q^{pm}` by reindexing `n = pm`. This is the `p^{k-1}·a(n/p)` half of the `T_p` coefficient
formula `b(n) = a(pn) + [p∣n] p^{k-1} a(n/p)`. -/
lemma hasSum_heckeCosetInf_term {F : Type*} [FunLike F ℍ ℂ] {k : ℤ}
    [ModularFormClass F (Γ(1) : Subgroup (GL (Fin 2) ℝ)) k]
    (p : ℕ) (hp0 : 0 < p) (hp : (p : ℝ) ≠ 0) (f : F) (τ : ℍ) :
    HasSum (fun n => (if p ∣ n then (ModularFormClass.qExpansion 1 f).coeff (n / p) else 0)
                      • (Function.Periodic.qParam 1 (τ : ℂ)) ^ n)
           ((f : ℍ → ℂ) (heckeCosetInf p hp • τ)) := by
  have hbase := ModularFormClass.hasSum_qExpansion (k := k) f one_pos
    RankinSelbergDelta.CuspForm.one_mem_strictPeriods_levelOne (heckeCosetInf p hp • τ)
  have hb2 : HasSum (fun m => (ModularFormClass.qExpansion 1 f).coeff m
      • (Function.Periodic.qParam 1 (τ : ℂ)) ^ (p * m))
      ((f : ℍ → ℂ) (heckeCosetInf p hp • τ)) := by
    convert hbase using 2 with m
    rw [qParam_heckeCosetInf_smul p hp0 hp τ, pow_mul]
  have hinj : Function.Injective (fun m : ℕ => p * m) := mul_right_injective₀ hp0.ne'
  have hz : ∀ n ∉ Set.range (fun m : ℕ => p * m),
      (if p ∣ n then (ModularFormClass.qExpansion 1 f).coeff (n / p) else 0)
        • (Function.Periodic.qParam 1 (τ : ℂ)) ^ n = (0 : ℂ) := by
    intro n hn
    rw [if_neg (fun hdvd => hn ⟨n / p, Nat.mul_div_cancel' hdvd⟩), zero_smul]
  refine (Function.Injective.hasSum_iff hinj hz).mp ?_
  convert hb2 using 2 with m
  simp only [Function.comp_apply, if_pos (Dvd.intro m rfl), Nat.mul_div_cancel_left m hp0]

/-- The `heckeCoset` (translates) term: `Σ_{j<p} f((τ+j)/p) = Σ_n p·a(pn)·q^n`. The Fourier phase
`Σ_j exp(2πijm/p) = p·[p∣m]` (`sum_rootOfUnity`) keeps only the `p`-multiples `m = pn`, and the
`p`-th root `exp(2πiτ/p)^{pn} = q^n`. This is the `a(pn)` half of the `T_p` coefficient formula
(the outer `p^{-1}` of `T_p` cancels the `p` here). -/
lemma hasSum_heckeCoset_sum {F : Type*} [FunLike F ℍ ℂ] {k : ℤ}
    [ModularFormClass F (Γ(1) : Subgroup (GL (Fin 2) ℝ)) k]
    (p : ℕ) (hp0 : 0 < p) (hp : (p : ℝ) ≠ 0) (f : F) (τ : ℍ) :
    HasSum (fun n => ((p : ℂ) * (ModularFormClass.qExpansion 1 f).coeff (p * n))
                      • (Function.Periodic.qParam 1 (τ : ℂ)) ^ n)
           (∑ j ∈ Finset.range p, (f : ℍ → ℂ) (heckeCoset p j hp • τ)) := by
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
  set ρ : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) / p) with hρ
  have hρp : ρ ^ p = Function.Periodic.qParam 1 (τ : ℂ) := by
    rw [hρ, ← Complex.exp_nat_mul, Function.Periodic.qParam]
    simp only [Complex.ofReal_one, div_one]
    congr 1
    field_simp
  -- (1) the finite sum of per-coset q-expansions
  have hsum := hasSum_sum (fun j (_ : j ∈ Finset.range p) =>
    ModularFormClass.hasSum_qExpansion (k := k) f one_pos
      RankinSelbergDelta.CuspForm.one_mem_strictPeriods_levelOne (heckeCoset p j hp • τ))
  -- (2) collapse the inner finite sum over j, per m
  have hinner : ∀ m, (∑ j ∈ Finset.range p,
        (ModularFormClass.qExpansion 1 f).coeff m
          • Function.Periodic.qParam 1 (↑(heckeCoset p j hp • τ)) ^ m)
      = (if p ∣ m then (p : ℂ) else 0) * ((ModularFormClass.qExpansion 1 f).coeff m * ρ ^ m) := by
    intro m
    have hj : ∀ j ∈ Finset.range p,
        (ModularFormClass.qExpansion 1 f).coeff m
          • Function.Periodic.qParam 1 (↑(heckeCoset p j hp • τ)) ^ m
        = (ModularFormClass.qExpansion 1 f).coeff m * ρ ^ m
          * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) / p)) ^ j := by
      intro j _
      rw [qParam_heckeCoset_smul p j hp0 hp τ, mul_pow, smul_eq_mul, ← hρ,
        show (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) / p)) ^ m
            = (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) / p)) ^ j by
          rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]; congr 1; push_cast; ring]
      ring
    rw [Finset.sum_congr rfl hj, ← Finset.mul_sum, sum_rootOfUnity p m hp0]
    exact mul_comm _ _
  -- (3) rewrite hsum's summand, then reindex m = p*n
  simp only [hinner] at hsum
  have hinj : Function.Injective (fun n : ℕ => p * n) := mul_right_injective₀ hp0.ne'
  have hHsupp : ∀ m ∉ Set.range (fun n : ℕ => p * n),
      (if p ∣ m then (p : ℂ) else 0)
          * ((ModularFormClass.qExpansion 1 f).coeff m * ρ ^ m) = (0 : ℂ) := by
    intro m hm
    rw [if_neg (fun hdvd => hm ⟨m / p, Nat.mul_div_cancel' hdvd⟩), zero_mul]
  have hcomp := (Function.Injective.hasSum_iff hinj hHsupp).mpr hsum
  convert hcomp using 2 with n
  simp only [Function.comp_apply, if_pos (dvd_mul_right p n), smul_eq_mul, pow_mul, hρp]
  ring

/-- **The `T_p` `q`-expansion coefficient formula (HasSum form)**: for a level-one cusp form `f`,
`(T_p f)(τ) = Σ_n (a(pn) + [p∣n] p^{k-1} a(n/p)) q^n`, assembled from the coset and `∞`-coset
halves via `heckeT_eq`. No cusp-form packaging is needed yet; the coefficient read-off
(`qExpansion_coeff_unique` against `heckeTCuspForm`) is the only step that needs the merge. -/
theorem hasSum_heckeT_qExpansion {F : Type*} [FunLike F ℍ ℂ] {k : ℤ}
    [ModularFormClass F (Γ(1) : Subgroup (GL (Fin 2) ℝ)) k]
    (p : ℕ) (hp0 : 0 < p) (hp : (p : ℝ) ≠ 0) (f : F) (τ : ℍ) :
    HasSum (fun n => ((ModularFormClass.qExpansion 1 f).coeff (p * n)
            + (if p ∣ n then ((p : ℝ) : ℂ) ^ (k - 1)
                * (ModularFormClass.qExpansion 1 f).coeff (n / p) else 0))
          • (Function.Periodic.qParam 1 (τ : ℂ)) ^ n)
          (heckeT p k hp (f : ℍ → ℂ) τ) := by
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hc : HasSum (fun n => (ModularFormClass.qExpansion 1 f).coeff (p * n)
              • (Function.Periodic.qParam 1 (τ : ℂ)) ^ n)
            (((p : ℝ) : ℂ) ^ (-1 : ℤ)
              * ∑ j ∈ Finset.range p, (f : ℍ → ℂ) (heckeCoset p j hp • τ)) := by
    have h := (hasSum_heckeCoset_sum p hp0 hp f τ).mul_left (((p : ℝ) : ℂ) ^ (-1 : ℤ))
    convert h using 2 with n
    rw [smul_eq_mul, smul_eq_mul, Complex.ofReal_natCast, _root_.zpow_neg_one]
    field_simp
  have hi : HasSum (fun n => (if p ∣ n then ((p : ℝ) : ℂ) ^ (k - 1)
                * (ModularFormClass.qExpansion 1 f).coeff (n / p) else 0)
              • (Function.Periodic.qParam 1 (τ : ℂ)) ^ n)
            (((p : ℝ) : ℂ) ^ (k - 1) * (f : ℍ → ℂ) (heckeCosetInf p hp • τ)) := by
    have h := (hasSum_heckeCosetInf_term p hp0 hp f τ).mul_left (((p : ℝ) : ℂ) ^ (k - 1))
    convert h using 2 with n
    rw [smul_eq_mul, smul_eq_mul]
    split_ifs <;> ring
  rw [heckeT_eq p k hp0 hp (f : ℍ → ℂ) τ, ← Finset.mul_sum]
  have hsum := hc.add hi
  simp only [← add_smul] at hsum
  exact hsum

/-! ### `Δ` has real `q`-coefficients (`hreal`), via `E₄`, `E₆` real. -/

/-- A power series over `ℂ` has real coefficients. -/
def HasRealCoeffs (φ : PowerSeries ℂ) : Prop :=
  ∀ n, (starRingEnd ℂ) (φ.coeff n) = φ.coeff n

lemma HasRealCoeffs.mul {φ ψ : PowerSeries ℂ} (hφ : HasRealCoeffs φ) (hψ : HasRealCoeffs ψ) :
    HasRealCoeffs (φ * ψ) := by
  intro n
  rw [PowerSeries.coeff_mul, map_sum]
  exact Finset.sum_congr rfl fun x _ => by rw [map_mul, hφ, hψ]

lemma HasRealCoeffs.sub {φ ψ : PowerSeries ℂ} (hφ : HasRealCoeffs φ) (hψ : HasRealCoeffs ψ) :
    HasRealCoeffs (φ - ψ) := by
  intro n
  rw [map_sub, map_sub, hφ, hψ]

/-- `eisCoeff` is real (it is built from `1`, naturals, rationals). -/
lemma conj_eisCoeff (k m : ℕ) :
    (starRingEnd ℂ) (RankinSelbergDelta.CuspForm.eisCoeff k m) = RankinSelbergDelta.CuspForm.eisCoeff k m := by
  unfold RankinSelbergDelta.CuspForm.eisCoeff
  split_ifs
  · simp
  · simp [Complex.ext_iff, Complex.div_re, Complex.div_im]

lemma hasRealCoeffs_E4 : HasRealCoeffs (ModularFormClass.qExpansion 1 RankinSelbergDelta.CuspForm.E4) := by
  intro n; rw [RankinSelbergDelta.CuspForm.coeff_E4, conj_eisCoeff]

lemma hasRealCoeffs_E6 : HasRealCoeffs (ModularFormClass.qExpansion 1 RankinSelbergDelta.CuspForm.E6) := by
  intro n; rw [RankinSelbergDelta.CuspForm.coeff_E6, conj_eisCoeff]

/-- `Δ` has real `q`-coefficients. -/
lemma hasRealCoeffs_ΔModular :
    HasRealCoeffs (ModularFormClass.qExpansion 1 RankinSelbergDelta.CuspForm.ΔModular) := by
  rw [RankinSelbergDelta.CuspForm.qExpansion_ΔModular]
  exact ((hasRealCoeffs_E4.mul hasRealCoeffs_E4).mul hasRealCoeffs_E4).sub
    (hasRealCoeffs_E6.mul hasRealCoeffs_E6)

/-- **`hreal` for the normalized discriminant**: every `q`-coefficient of `Δ/1728` is real. -/
lemma conj_coeff_ΔnormM (n : ℕ) :
    (starRingEnd ℂ) ((ModularFormClass.qExpansion 1 ΔnormM).coeff n)
      = (ModularFormClass.qExpansion 1 ΔnormM).coeff n := by
  rw [coeff_ΔnormM, map_mul,
    show (starRingEnd ℂ) (1 / 1728 : ℂ) = 1 / 1728 by rw [map_div₀, map_one, map_ofNat]]
  congr 1
  exact hasRealCoeffs_ΔModular n

/-! ### The normalized `Δ` coefficient sequence `aΔ` and its base coefficients.

`aΔ` is the `q`-expansion coefficient sequence of `Δ/1728` (the normalized Ramanujan-`τ`, `aΔ 1 = 1`).
`IsHeckeEigenCoeffs aΔ 12` is proved COMPLETE (all four fields) as `isHeckeEigenCoeffs_aΔ'` in
`CuspForm/DeltaHeckeEigenform.lean`, and `Lfunction_ne_zero_Delta` (`CuspForm/NormalizedDelta.lean`)
uses it. -/

/-- The normalized `Δ` coefficient sequence `a(n) = (q`-expansion of `Δ/1728`)`.coeff n`. -/
noncomputable def aΔ (n : ℕ) : ℂ := (ModularFormClass.qExpansion 1 ΔnormM).coeff n

@[simp] lemma aΔ_zero : aΔ 0 = 0 := coeff_ΔnormM_zero
@[simp] lemma aΔ_one : aΔ 1 = 1 := coeff_ΔnormM_one

-- `IsHeckeEigenCoeffs aΔ 12` is proved COMPLETE as `isHeckeEigenCoeffs_aΔ'` in
-- `RankinSelbergDelta/CuspForm/DeltaHeckeEigenform.lean` (all four fields; `mul_coprime` via the single-prime
-- induction `isHeckeEigenCoeffs_of_relation`).

end RankinSelbergDelta.Hecke
