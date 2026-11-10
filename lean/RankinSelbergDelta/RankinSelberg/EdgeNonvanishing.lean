import RankinSelbergDelta.RankinSelberg.EulerProduct

/-!
# `L(f, 1 + it) ≠ 0`

For a level-one Hecke eigenform `f` with real coefficients and real `t ≠ 0`,
`L(f, 1 + it) ≠ 0` (`Lfunction_ne_zero_on_one_line`). For `σ > 1` the product
`ζ(σ) L(σ+it)² L(σ−it)² G(σ+2it) G(σ)² G(σ−2it)` is the exponential of a series with
nonnegative terms, so its modulus is at least 1; a zero of `L` at `1 + it` would make it tend to 0.
-/

open MeasureTheory Filter
open scoped NNReal MatrixGroups Pointwise

noncomputable section


/-! ## A bridge lemma: `Λ = (2π)^{-s} Γ(s) L` stated on `completedLSeries` -/

namespace RankinSelbergDelta.CuspForm

open Complex UpperHalfPlane ModularForm SlashInvariantForm CongruenceSubgroup ModularFormClass

variable {F : Type*} [FunLike F ℍ ℂ] {k : ℤ}
  [cf : CuspFormClass F (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma 1)) k]

include cf in
theorem completedLSeries_eq_dirichlet' (f : F) (hk : 0 < k) {s : ℂ}
    (hs : (k : ℝ) / 2 + 1 < s.re) :
    completedLSeries f hk s
      = ((2 * Real.pi : ℝ) : ℂ) ^ (-s) * Complex.Gamma s
          * LSeries (fun n ↦ (ModularFormClass.qExpansion 1 f).coeff n) s :=
  completedLSeries_eq_dirichlet f hk hs

end RankinSelbergDelta.CuspForm

/-! ## `L(f, 1 + it) ≠ 0` for `t ≠ 0` (isobaric positivity on the real axis) -/

namespace RankinSelbergDelta.RankinSelberg

open Complex UpperHalfPlane MeasureTheory Set Filter Topology Asymptotics
open scoped ENNReal Modular NNReal

noncomputable section

/-! ### power sums, the Euler factor of `L(f, s)`, the isobaric term identity -/

/-- The power-sum sequence `T_0 = 2, T_1 = x, T_{j+2} = x T_{j+1} − T_j`: `T_j(α + β) = α^j + β^j`
when `αβ = 1`. -/
def powSum (x : ℂ) : ℕ → ℂ
  | 0 => 2
  | 1 => x
  | (j + 2) => x * powSum x (j + 1) - powSum x j

@[simp] lemma powSum_zero (x : ℂ) : powSum x 0 = 2 := rfl
@[simp] lemma powSum_one (x : ℂ) : powSum x 1 = x := rfl
lemma powSum_add_two (x : ℂ) (j : ℕ) : powSum x (j + 2) = x * powSum x (j + 1) - powSum x j := rfl

/-- `α^j + β^j = powSum (α + β) j` when `αβ = 1`. -/
lemma pow_add_pow_eq_powSum {α β : ℂ} (hαβ : α * β = 1) (j : ℕ) :
    α ^ j + β ^ j = powSum (α + β) j := by
  induction j using Nat.twoStepInduction with
  | zero => norm_num
  | one => simp
  | more j ih1 ih2 =>
    rw [powSum_add_two, ← ih1, ← ih2]
    linear_combination (-(α ^ j + β ^ j)) * hαβ

lemma conj_powSum (x : ℂ) (j : ℕ) :
    (starRingEnd ℂ) (powSum x j) = powSum ((starRingEnd ℂ) x) j := by
  induction j using Nat.twoStepInduction with
  | zero => simp only [powSum_zero]; exact map_ofNat (starRingEnd ℂ) 2
  | one => simp
  | more j ih1 ih2 => rw [powSum_add_two, powSum_add_two, map_sub, map_mul, ih1, ih2]

/-- A power sum of a real argument is real: `powSum x j = ((powSum x j).re : ℂ)`. -/
lemma powSum_ofReal_re {x : ℂ} (hx : (starRingEnd ℂ) x = x) (j : ℕ) :
    (((powSum x j).re : ℝ) : ℂ) = powSum x j := by
  rw [← Complex.conj_eq_iff_re, conj_powSum, hx]

/-- The Euler factor of `L(f, s)` at `p`: `(1 − ã Y + Y²)⁻¹`, `Y = p^{-s}`. -/
def eulerFac (x Y : ℂ) : ℂ := (1 - x * Y + Y ^ 2)⁻¹

/-- The generating function of the Hecke sequence: `(Σ_e h_e(x) Y^e)(1 − xY + Y²) = 1`. -/
lemma heckeSeq_genfun (x Y : ℂ) (hu : Summable fun e => heckeSeq x e * Y ^ e) :
    (∑' e, heckeSeq x e * Y ^ e) * (1 - x * Y + Y ^ 2) = 1 := by
  have h0 := hu.hasSum
  have hj : ∀ j, HasSum (fun e => shiftSeq (heckeSeq x) j e * Y ^ e)
      (Y ^ j * ∑' e, heckeSeq x e * Y ^ e) := fun j => hasSum_shiftSeq h0 j
  set v : ℕ → ℂ := fun e => heckeSeq x e - x * shiftSeq (heckeSeq x) 1 e + shiftSeq (heckeSeq x) 2 e
    with hv
  have hvsum : HasSum (fun e => v e * Y ^ e)
      ((∑' e, heckeSeq x e * Y ^ e) - x * (Y ^ 1 * ∑' e, heckeSeq x e * Y ^ e)
        + Y ^ 2 * ∑' e, heckeSeq x e * Y ^ e) := by
    have := (h0.sub ((hj 1).mul_left x)).add (hj 2)
    have heq : (fun e => v e * Y ^ e)
        = fun e => heckeSeq x e * Y ^ e - x * (shiftSeq (heckeSeq x) 1 e * Y ^ e)
          + shiftSeq (heckeSeq x) 2 e * Y ^ e := by
      funext e
      simp only [hv]
      ring
    rw [heq]
    exact this
  have hvz : ∀ e, 2 ≤ e → v e = 0 := by
    intro e he
    obtain ⟨m, rfl⟩ : ∃ m, e = m + 2 := ⟨e - 2, by omega⟩
    simp only [hv, shiftSeq, show 1 ≤ m + 2 by omega, show 2 ≤ m + 2 by omega, if_true,
      show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega, heckeSeq_add_two]
    ring
  have hfin : HasSum (fun e => v e * Y ^ e) (∑ e ∈ Finset.range 2, v e * Y ^ e) :=
    hasSum_sum_of_ne_finset_zero fun e he => by
      rw [Finset.mem_range, not_lt] at he
      rw [hvz e he, zero_mul]
  have key := hvsum.unique hfin
  have hv0 : v 0 = 1 := by simp [hv, shiftSeq]
  have hv1 : v 1 = 0 := by simp [hv, shiftSeq]
  rw [Finset.sum_range_succ, Finset.sum_range_one, hv0, hv1] at key
  linear_combination key

/-- The two-log series of a prime: `Σ_j T_{j+1}(α+β) Y^{j+1}/(j+1) = −log(1−αY) − log(1−βY)`. -/
lemma hasSum_powSum_log {α β Y : ℂ} (hαβ : α * β = 1) (h1 : ‖α * Y‖ < 1) (h2 : ‖β * Y‖ < 1) :
    HasSum (fun j : ℕ => powSum (α + β) (j + 1) * Y ^ (j + 1) / ((j : ℂ) + 1))
      (-(Complex.log (1 - α * Y) + Complex.log (1 - β * Y))) := by
  have e : (fun j : ℕ => powSum (α + β) (j + 1) * Y ^ (j + 1) / ((j : ℂ) + 1))
      = fun j : ℕ => (α * Y) ^ (j + 1) / ((j : ℂ) + 1) + (β * Y) ^ (j + 1) / ((j : ℂ) + 1) := by
    funext j
    rw [← pow_add_pow_eq_powSum hαβ, mul_pow, mul_pow]
    ring
  rw [e]
  have := (hasSum_taylor_neg_log h1).add (hasSum_taylor_neg_log h2)
  convert this using 1
  ring

/-- `exp(−log(1−αY) − log(1−βY)) = eulerFac (α+β) Y` when `αβ = 1`. -/
lemma exp_neg_two_log_eq_eulerFac {α β Y : ℂ} (hαβ : α * β = 1) (h1 : ‖α * Y‖ < 1)
    (h2 : ‖β * Y‖ < 1) :
    Complex.exp (-(Complex.log (1 - α * Y) + Complex.log (1 - β * Y))) = eulerFac (α + β) Y := by
  rw [Complex.exp_neg, Complex.exp_add, Complex.exp_log (one_sub_ne_zero_of_norm_lt_one h1),
    Complex.exp_log (one_sub_ne_zero_of_norm_lt_one h2), eulerFac]
  congr 1
  linear_combination (Y ^ 2) * hαβ

/-- The local factor of `L(f, s)` as a power series: `Σ_e h_e(x) Y^e = eulerFac x Y`. -/
lemma tsum_heckeSeq_eq_eulerFac (x Y : ℂ) (hu : Summable fun e => heckeSeq x e * Y ^ e)
    (hne : 1 - x * Y + Y ^ 2 ≠ 0) :
    (∑' e, heckeSeq x e * Y ^ e) = eulerFac x Y := by
  rw [eulerFac]
  exact eq_inv_of_mul_eq_one_left (heckeSeq_genfun x Y hu)

/-- **The isobaric term identity**: with `E E' = 1` and `2c = E + E'`,
`(1 + 2Pc)² R/(j+1) = R/(j+1) + 2·P R E/(j+1) + 2·P R E'/(j+1) + P² R E²/(j+1) + 2·P² R/(j+1)
+ P² R E'²/(j+1)`. -/
lemma iso_term_identity (P R E E' c : ℂ) (hEE : E * E' = 1) (hc : 2 * c = E + E') (j : ℕ) :
    (1 + 2 * P * c) ^ 2 / ((j : ℂ) + 1) * R
      = R / ((j : ℂ) + 1) + 2 * (P * (R * E) / ((j : ℂ) + 1)) + 2 * (P * (R * E') / ((j : ℂ) + 1))
        + P ^ 2 / ((j : ℂ) + 1) * (R * E ^ 2) + 2 * (P ^ 2 / ((j : ℂ) + 1) * R)
        + P ^ 2 / ((j : ℂ) + 1) * (R * E' ^ 2) := by
  linear_combination (R / ((j : ℂ) + 1) * (2 * P + P ^ 2 * (2 * c + E + E'))) * hc
    + (R / ((j : ℂ) + 1) * 2 * P ^ 2) * hEE

/-- `(1 + 2Pc)² ≤ 2 + 8P²` for `|c| ≤ 1`. -/
lemma iso_weight_le (P c : ℝ) (hc : c ^ 2 ≤ 1) : (1 + 2 * P * c) ^ 2 ≤ 2 + 8 * P ^ 2 := by
  nlinarith [sq_nonneg (1 - 2 * P * c), sq_nonneg P, mul_nonneg (sq_nonneg P) (sub_nonneg.mpr hc)]


variable {F : Type*} [FunLike F ℍ ℂ] (k : ℤ)
  [cf : CuspFormClass F (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma 1)) k]
/-! ### the per-prime isobaric series, its positivity, its decomposition into six
logarithms, and its exponential -/

/-- The isobaric weight at `p^(j+1)`: `(1 + 2 P_{j+1} cos((j+1)θ))² /(j+1) · Y₀^(j+1)`. -/
def isoTerm (P : ℕ → ℝ) (θ Y₀ : ℝ) (j : ℕ) : ℝ :=
  (1 + 2 * P (j + 1) * Real.cos (((j : ℝ) + 1) * θ)) ^ 2 / ((j : ℝ) + 1) * Y₀ ^ (j + 1)

lemma isoTerm_nonneg (P : ℕ → ℝ) (θ : ℝ) {Y₀ : ℝ} (hY : 0 ≤ Y₀) (j : ℕ) :
    0 ≤ isoTerm P θ Y₀ j := by
  unfold isoTerm; positivity

/-- `isoTerm ≤ 2 Y₀^(j+1) + 8 · P_{j+1}²/(j+1) · Y₀^(j+1)`. -/
lemma isoTerm_le (P : ℕ → ℝ) (θ : ℝ) {Y₀ : ℝ} (hY : 0 ≤ Y₀) (j : ℕ) :
    isoTerm P θ Y₀ j ≤ 2 * Y₀ ^ (j + 1) + 8 * (P (j + 1) ^ 2 / ((j : ℝ) + 1) * Y₀ ^ (j + 1)) := by
  unfold isoTerm
  have hc : Real.cos (((j : ℝ) + 1) * θ) ^ 2 ≤ 1 := Real.cos_sq_le_one _
  have hw := iso_weight_le (P (j + 1)) _ hc
  have hpos : 0 ≤ Y₀ ^ (j + 1) / ((j : ℝ) + 1) := by positivity
  have hj1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by
    have : (0 : ℝ) ≤ j := by positivity
    linarith
  have hle : Y₀ ^ (j + 1) / ((j : ℝ) + 1) ≤ Y₀ ^ (j + 1) :=
    div_le_self (by positivity) hj1
  calc (1 + 2 * P (j + 1) * Real.cos (((j : ℝ) + 1) * θ)) ^ 2 / ((j : ℝ) + 1) * Y₀ ^ (j + 1)
      = (1 + 2 * P (j + 1) * Real.cos (((j : ℝ) + 1) * θ)) ^ 2 * (Y₀ ^ (j + 1) / ((j : ℝ) + 1)) := by
        ring
    _ ≤ (2 + 8 * P (j + 1) ^ 2) * (Y₀ ^ (j + 1) / ((j : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right hw hpos
    _ = 2 * (Y₀ ^ (j + 1) / ((j : ℝ) + 1)) + 8 * (P (j + 1) ^ 2 / ((j : ℝ) + 1) * Y₀ ^ (j + 1)) := by
        ring
    _ ≤ 2 * Y₀ ^ (j + 1) + 8 * (P (j + 1) ^ 2 / ((j : ℝ) + 1) * Y₀ ^ (j + 1)) := by
        linarith

/-- The real power sums of a real-coefficient form: `P_j = (powSum ã_p j).re`. -/
def rsPow (f : F) (p : ℕ) (j : ℕ) : ℝ := (powSum (heckeNorm (rsCoeff f) k p) j).re

/-- The normalised eigenvalue is real when the coefficients are. -/
lemma conj_heckeNorm (f : F) (hreal : ∀ n, (starRingEnd ℂ) (rsCoeff f n) = rsCoeff f n) (p : ℕ) :
    (starRingEnd ℂ) (heckeNorm (rsCoeff f) k p) = heckeNorm (rsCoeff f) k p := by
  have hq : (p : ℂ) ^ (((k : ℂ) - 1) / 2) = (((p : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by positivity)]
    congr 1
    push_cast
    ring
  rw [heckeNorm, map_div₀, hreal, hq, Complex.conj_ofReal]

lemma rsPow_eq (f : F) (hreal : ∀ n, (starRingEnd ℂ) (rsCoeff f n) = rsCoeff f n) (p : ℕ) (j : ℕ) :
    ((rsPow k f p j : ℝ) : ℂ) = powSum (heckeNorm (rsCoeff f) k p) j :=
  powSum_ofReal_re (conj_heckeNorm k f hreal p) j

lemma rsPow_eq_pow_add_pow (f : F) (hreal : ∀ n, (starRingEnd ℂ) (rsCoeff f n) = rsCoeff f n)
    (p : ℕ) (j : ℕ) :
    ((rsPow k f p j : ℝ) : ℂ) = satakeα (rsCoeff f) k p ^ j + satakeβ (rsCoeff f) k p ^ j := by
  rw [rsPow_eq k f hreal, ← satake_add, ← pow_add_pow_eq_powSum (satake_mul _ _ _)]

/-- `‖α^j + β^j‖² = P_j²` for a real-coefficient form. -/
lemma normSq_satake_pow_eq (f : F) (hreal : ∀ n, (starRingEnd ℂ) (rsCoeff f n) = rsCoeff f n)
    (p : ℕ) (j : ℕ) :
    ‖satakeα (rsCoeff f) k p ^ j + satakeβ (rsCoeff f) k p ^ j‖ ^ 2 = rsPow k f p j ^ 2 := by
  rw [← rsPow_eq_pow_add_pow k f hreal, Complex.norm_real, Real.norm_eq_abs, sq_abs]

include cf in
/-- `‖α Y‖ < 1` and `‖β Y‖ < 1` for `Y = p^{-s}`, `Re s > 1`. -/
lemma satake_mul_cpow_norm_lt (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k) {p : ℕ}
    (hp : p.Prime) {s : ℂ} (hs : 1 < s.re) :
    ‖satakeα (rsCoeff f) k p * (p : ℂ) ^ (-s)‖ < 1 ∧ ‖satakeβ (rsCoeff f) k p * (p : ℂ) ^ (-s)‖ < 1 := by
  obtain ⟨hα, hβ, hY⟩ := satake_norm_lt k f hk hf hp hs
  have hY0 : 0 ≤ ‖(p : ℂ) ^ (-s)‖ := norm_nonneg _
  have key : ∀ a : ℝ, 0 ≤ a → a ^ 2 * ‖(p : ℂ) ^ (-s)‖ < 1 → a * ‖(p : ℂ) ^ (-s)‖ < 1 := by
    intro a ha h
    by_contra hcon
    push_neg at hcon
    have h1 : 1 ≤ (a * ‖(p : ℂ) ^ (-s)‖) ^ 2 := one_le_pow₀ hcon
    have h2 : (a * ‖(p : ℂ) ^ (-s)‖) ^ 2 = a ^ 2 * ‖(p : ℂ) ^ (-s)‖ * ‖(p : ℂ) ^ (-s)‖ := by ring
    have h3 : a ^ 2 * ‖(p : ℂ) ^ (-s)‖ * ‖(p : ℂ) ^ (-s)‖ < 1 * 1 :=
      mul_lt_mul'' h hY (by positivity) hY0
    linarith
  rw [norm_mul, norm_mul]
  exact ⟨key _ (norm_nonneg _) hα, key _ (norm_nonneg _) hβ⟩

include cf in
/-- **The per-prime decomposition**: for `σ > 1` and `θ = t log p`, the isobaric series at `p`
sums to the six logarithms `−log(1−p^{-σ}) + 2 λ_p(σ+it) + 2 λ_p(σ−it) + ℓ_p(σ+2it) + 2 ℓ_p(σ)
+ ℓ_p(σ−2it)`. -/
lemma hasSum_isoTerm (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k)
    (hreal : ∀ n, (starRingEnd ℂ) (rsCoeff f n) = rsCoeff f n) {p : ℕ} (hp : p.Prime) (t : ℝ)
    {σ : ℝ} (hσ : 1 < σ) :
    HasSum (fun j => ((isoTerm (rsPow k f p) (t * Real.log p) ((p : ℝ) ^ (-σ)) j : ℝ) : ℂ))
      (-Complex.log (1 - (p : ℂ) ^ (-(σ : ℂ)))
        + 2 * (-(Complex.log (1 - satakeα (rsCoeff f) k p * (p : ℂ) ^ (-((σ : ℂ) + Complex.I * t)))
            + Complex.log (1 - satakeβ (rsCoeff f) k p * (p : ℂ) ^ (-((σ : ℂ) + Complex.I * t)))))
        + 2 * (-(Complex.log (1 - satakeα (rsCoeff f) k p * (p : ℂ) ^ (-((σ : ℂ) - Complex.I * t)))
            + Complex.log (1 - satakeβ (rsCoeff f) k p * (p : ℂ) ^ (-((σ : ℂ) - Complex.I * t)))))
        + rsLocal k f p ((σ : ℂ) + 2 * Complex.I * t) + 2 * rsLocal k f p σ
        + rsLocal k f p ((σ : ℂ) - 2 * Complex.I * t)) := by
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hs0 : 1 < ((σ : ℂ)).re := by simpa using hσ
  have hs1 : 1 < ((σ : ℂ) + Complex.I * t).re := by simp; exact hσ
  have hs1' : 1 < ((σ : ℂ) - Complex.I * t).re := by simp; exact hσ
  have hs2 : 1 < ((σ : ℂ) + 2 * Complex.I * t).re := by simp; exact hσ
  have hs2' : 1 < ((σ : ℂ) - 2 * Complex.I * t).re := by simp; exact hσ
  set α := satakeα (rsCoeff f) k p with hα
  set β := satakeβ (rsCoeff f) k p with hβ
  have hcpow : (p : ℂ) ^ (-(σ : ℂ)) = (((p : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hpR.le, Complex.ofReal_neg, Complex.ofReal_natCast]
  -- the six series
  have h0 := hasSum_taylor_neg_log (satake_norm_lt k f hk hf hp hs0).2.2
  obtain ⟨hα1, hβ1⟩ := satake_mul_cpow_norm_lt k f hk hf hp hs1
  obtain ⟨hα1', hβ1'⟩ := satake_mul_cpow_norm_lt k f hk hf hp hs1'
  have h1 := hasSum_powSum_log (satake_mul (rsCoeff f) k p) hα1 hβ1
  have h1' := hasSum_powSum_log (satake_mul (rsCoeff f) k p) hα1' hβ1'
  rw [satake_add] at h1 h1'
  obtain ⟨a2, b2, c2, d2⟩ := rho_norm_lt k f hk hf hp hs2
  obtain ⟨a2', b2', c2', d2'⟩ := rho_norm_lt k f hk hf hp hs2'
  obtain ⟨a0, b0, c0, d0⟩ := rho_norm_lt k f hk hf hp hs0
  have h2 : HasSum (rsLogTerm α β ((p : ℂ) ^ (-((σ : ℂ) + 2 * Complex.I * t))))
      (rsLocal k f p ((σ : ℂ) + 2 * Complex.I * t)) :=
    (hasSum_rsLogTerm a2 b2 c2 d2).summable.hasSum
  have h2' : HasSum (rsLogTerm α β ((p : ℂ) ^ (-((σ : ℂ) - 2 * Complex.I * t))))
      (rsLocal k f p ((σ : ℂ) - 2 * Complex.I * t)) :=
    (hasSum_rsLogTerm a2' b2' c2' d2').summable.hasSum
  have h5 : HasSum (rsLogTerm α β ((p : ℂ) ^ (-(σ : ℂ)))) (rsLocal k f p σ) :=
    (hasSum_rsLogTerm a0 b0 c0 d0).summable.hasSum
  have H := (((((h0.add (h1.mul_left 2)).add (h1'.mul_left 2)).add h2).add (h5.mul_left 2)).add h2')
  refine (funext fun j => ?_ : (fun j => ((isoTerm (rsPow k f p) (t * Real.log p) ((p : ℝ) ^ (-σ)) j : ℝ) : ℂ)) = _) ▸ H
  -- the termwise identity
  set θ : ℝ := t * Real.log p with hθ
  set E : ℂ := Complex.exp (-(((j : ℂ) + 1) * (Complex.I * θ))) with hE
  set E' : ℂ := Complex.exp (((j : ℂ) + 1) * (Complex.I * θ)) with hE'
  set R : ℂ := ((p : ℂ) ^ (-(σ : ℂ))) ^ (j + 1) with hR
  have hEE : E * E' = 1 := by
    rw [hE, hE', ← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    ring
  have hc : 2 * ((Real.cos (((j : ℝ) + 1) * θ) : ℝ) : ℂ) = E + E' := by
    rw [Complex.ofReal_cos, Complex.cos, hE, hE']
    have e1 : ((((j : ℝ) + 1) * θ : ℝ) : ℂ) * Complex.I = ((j : ℂ) + 1) * (Complex.I * θ) := by
      push_cast; ring
    have e2 : -((((j : ℝ) + 1) * θ : ℝ) : ℂ) * Complex.I = -(((j : ℂ) + 1) * (Complex.I * θ)) := by
      push_cast; ring
    rw [e1, e2]
    ring
  have hpow : ∀ w : ℂ, ((p : ℂ) ^ (-w)) ^ (j + 1)
      = Complex.exp (-(((j : ℂ) + 1) * (w * (Real.log p : ℂ)))) := by
    intro w
    rw [natCast_cpow_neg_eq_exp hp1, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hY1 : ((p : ℂ) ^ (-((σ : ℂ) + Complex.I * t))) ^ (j + 1) = R * E := by
    rw [hpow, hR, hpow, hE, ← Complex.exp_add, hθ]
    congr 1
    push_cast
    ring
  have hY1' : ((p : ℂ) ^ (-((σ : ℂ) - Complex.I * t))) ^ (j + 1) = R * E' := by
    rw [hpow, hR, hpow, hE', ← Complex.exp_add, hθ]
    congr 1
    push_cast
    ring
  have hY2 : ((p : ℂ) ^ (-((σ : ℂ) + 2 * Complex.I * t))) ^ (j + 1) = R * E ^ 2 := by
    rw [hpow, hR, hpow, hE, ← Complex.exp_nat_mul, ← Complex.exp_add, hθ]
    congr 1
    push_cast
    ring
  have hY2' : ((p : ℂ) ^ (-((σ : ℂ) - 2 * Complex.I * t))) ^ (j + 1) = R * E' ^ 2 := by
    rw [hpow, hR, hpow, hE', ← Complex.exp_nat_mul, ← Complex.exp_add, hθ]
    congr 1
    push_cast
    ring
  have hP : ((rsPow k f p (j + 1) : ℝ) : ℂ) = powSum (heckeNorm (rsCoeff f) k p) (j + 1) :=
    rsPow_eq k f hreal p (j + 1)
  have hPsq : ((‖α ^ (j + 1) + β ^ (j + 1)‖ ^ 2 : ℝ) : ℂ) = ((rsPow k f p (j + 1) : ℝ) : ℂ) ^ 2 := by
    rw [hα, hβ, normSq_satake_pow_eq k f hreal p (j + 1)]
    push_cast
    ring
  have hlhs : ((isoTerm (rsPow k f p) θ ((p : ℝ) ^ (-σ)) j : ℝ) : ℂ)
      = (1 + 2 * ((rsPow k f p (j + 1) : ℝ) : ℂ) * ((Real.cos (((j : ℝ) + 1) * θ) : ℝ) : ℂ)) ^ 2
          / ((j : ℂ) + 1) * R := by
    rw [isoTerm, hR, hcpow]
    push_cast
    ring
  rw [hlhs, iso_term_identity _ R E E' _ hEE hc j, ← hY1, ← hY1', ← hY2, ← hY2']
  simp only [rsLogTerm]
  rw [hPsq, ← hP, hR]

include cf in
/-- The real isobaric series at `p` is summable, nonnegative, and bounded by
`4 p^{-σ} + 8 rsLocalR`. -/
lemma isoLocal_summable_le (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k)
    (hreal : ∀ n, (starRingEnd ℂ) (rsCoeff f n) = rsCoeff f n) {p : ℕ} (hp : p.Prime) (t : ℝ)
    {σ : ℝ} (hσ : 1 < σ) :
    Summable (isoTerm (rsPow k f p) (t * Real.log p) ((p : ℝ) ^ (-σ)))
      ∧ ∑' j, isoTerm (rsPow k f p) (t * Real.log p) ((p : ℝ) ^ (-σ)) j
          ≤ 4 * (p : ℝ) ^ (-σ) + 8 * rsLocalR k f p σ := by
  set Y₀ : ℝ := (p : ℝ) ^ (-σ) with hY₀
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hY0 : 0 < Y₀ := by rw [hY₀]; positivity
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hYhalf : Y₀ ≤ 1 / 2 := by
    rw [hY₀, Real.rpow_neg hpR.le]
    calc ((p : ℝ) ^ σ)⁻¹ ≤ ((p : ℝ) ^ (1 : ℝ))⁻¹ :=
          inv_anti₀ (by positivity) (Real.rpow_le_rpow_of_exponent_le (by linarith) hσ.le)
      _ ≤ 1 / 2 := by rw [Real.rpow_one, one_div]; exact inv_anti₀ (by norm_num) hp2
  have hY1 : Y₀ < 1 := by linarith
  have hs0 : 1 < ((σ : ℂ)).re := by simpa using hσ
  -- the dominating series
  have hgeom : Summable fun j : ℕ => Y₀ ^ (j + 1) :=
    (summable_geometric_of_lt_one hY0.le hY1).comp_injective (add_left_injective 1)
  have hgeom_sum : ∑' j : ℕ, Y₀ ^ (j + 1) ≤ 2 * Y₀ := by
    have : ∑' j : ℕ, Y₀ ^ (j + 1) = Y₀ * (1 - Y₀)⁻¹ := by
      rw [← tsum_geometric_of_lt_one hY0.le hY1, ← tsum_mul_left]
      exact tsum_congr fun j => by rw [pow_succ']
    rw [this]
    have h1 : 1 / 2 ≤ 1 - Y₀ := by linarith
    calc Y₀ * (1 - Y₀)⁻¹ ≤ Y₀ * (1 / 2)⁻¹ :=
          mul_le_mul_of_nonneg_left (inv_anti₀ (by norm_num) h1) hY0.le
      _ = 2 * Y₀ := by ring
  obtain ⟨a0, b0, c0, d0⟩ := rho_norm_lt k f hk hf hp hs0
  have hlogR : Summable (rsLogR (satakeα (rsCoeff f) k p) (satakeβ (rsCoeff f) k p) Y₀) := by
    have h := (hasSum_rsLogTerm a0 b0 c0 d0).summable.norm
    refine h.congr fun j => ?_
    rw [norm_rsLogTerm, Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re, Complex.ofReal_re]
  have hterm : ∀ j, isoTerm (rsPow k f p) (t * Real.log p) Y₀ j
      ≤ 2 * Y₀ ^ (j + 1) + 8 * rsLogR (satakeα (rsCoeff f) k p) (satakeβ (rsCoeff f) k p) Y₀ j := by
    intro j
    refine (isoTerm_le _ _ hY0.le j).trans (le_of_eq ?_)
    rw [rsLogR, normSq_satake_pow_eq k f hreal p (j + 1)]
  have hdom : Summable fun j => 2 * Y₀ ^ (j + 1)
      + 8 * rsLogR (satakeα (rsCoeff f) k p) (satakeβ (rsCoeff f) k p) Y₀ j :=
    (hgeom.mul_left 2).add (hlogR.mul_left 8)
  have hsum : Summable (isoTerm (rsPow k f p) (t * Real.log p) Y₀) :=
    Summable.of_nonneg_of_le (fun j => isoTerm_nonneg _ _ hY0.le j) hterm hdom
  refine ⟨hsum, ?_⟩
  calc ∑' j, isoTerm (rsPow k f p) (t * Real.log p) Y₀ j
      ≤ ∑' j, (2 * Y₀ ^ (j + 1)
          + 8 * rsLogR (satakeα (rsCoeff f) k p) (satakeβ (rsCoeff f) k p) Y₀ j) :=
        hsum.tsum_le_tsum hterm hdom
    _ = 2 * ∑' j, Y₀ ^ (j + 1) + 8 * rsLocalR k f p σ := by
        rw [(hgeom.mul_left 2).tsum_add (hlogR.mul_left 8), tsum_mul_left, tsum_mul_left]
        rfl
    _ ≤ 2 * (2 * Y₀) + 8 * rsLocalR k f p σ := by
        have := mul_le_mul_of_nonneg_left hgeom_sum (by norm_num : (0 : ℝ) ≤ 2)
        linarith
    _ = 4 * Y₀ + 8 * rsLocalR k f p σ := by ring

include cf in
/-- **The exponential of the per-prime isobaric series**:
`exp ℓ_p^η(σ) = (1 − p^{-σ})⁻¹ · E_p(σ+it)² · E_p(σ−it)² · exp ℓ_p(σ+2it) · (exp ℓ_p(σ))² · exp ℓ_p(σ−2it)`. -/
lemma exp_isoLocal_eq (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k)
    (hreal : ∀ n, (starRingEnd ℂ) (rsCoeff f n) = rsCoeff f n) {p : ℕ} (hp : p.Prime) (t : ℝ)
    {σ : ℝ} (hσ : 1 < σ) :
    Complex.exp (((∑' j, isoTerm (rsPow k f p) (t * Real.log p) ((p : ℝ) ^ (-σ)) j : ℝ) : ℂ))
      = (1 - (p : ℂ) ^ (-(σ : ℂ)))⁻¹
        * (eulerFac (heckeNorm (rsCoeff f) k p) ((p : ℂ) ^ (-((σ : ℂ) + Complex.I * t)))
          * eulerFac (heckeNorm (rsCoeff f) k p) ((p : ℂ) ^ (-((σ : ℂ) + Complex.I * t))))
        * (eulerFac (heckeNorm (rsCoeff f) k p) ((p : ℂ) ^ (-((σ : ℂ) - Complex.I * t)))
          * eulerFac (heckeNorm (rsCoeff f) k p) ((p : ℂ) ^ (-((σ : ℂ) - Complex.I * t))))
        * Complex.exp (rsLocal k f p ((σ : ℂ) + 2 * Complex.I * t))
        * (Complex.exp (rsLocal k f p σ) * Complex.exp (rsLocal k f p σ))
        * Complex.exp (rsLocal k f p ((σ : ℂ) - 2 * Complex.I * t)) := by
  have hs0 : 1 < ((σ : ℂ)).re := by simpa using hσ
  have hs1 : 1 < ((σ : ℂ) + Complex.I * t).re := by simp; exact hσ
  have hs1' : 1 < ((σ : ℂ) - Complex.I * t).re := by simp; exact hσ
  have hH := hasSum_isoTerm k f hk hf hreal hp t hσ
  have hsum := (isoLocal_summable_le k f hk hf hreal hp t hσ).1
  have hreal_sum : HasSum (fun j => ((isoTerm (rsPow k f p) (t * Real.log p) ((p : ℝ) ^ (-σ)) j : ℝ) : ℂ))
      (((∑' j, isoTerm (rsPow k f p) (t * Real.log p) ((p : ℝ) ^ (-σ)) j : ℝ) : ℂ)) :=
    (Complex.hasSum_ofReal).mpr hsum.hasSum
  rw [hreal_sum.unique hH]
  obtain ⟨hα1, hβ1⟩ := satake_mul_cpow_norm_lt k f hk hf hp hs1
  obtain ⟨hα1', hβ1'⟩ := satake_mul_cpow_norm_lt k f hk hf hp hs1'
  have hY : ‖(p : ℂ) ^ (-(σ : ℂ))‖ < 1 := (satake_norm_lt k f hk hf hp hs0).2.2
  have e2 : ∀ z : ℂ, Complex.exp (2 * z) = Complex.exp z * Complex.exp z := fun z => by
    rw [two_mul, Complex.exp_add]
  rw [Complex.exp_add, Complex.exp_add, Complex.exp_add, Complex.exp_add, Complex.exp_add, e2, e2,
    e2, Complex.exp_neg, Complex.exp_log (one_sub_ne_zero_of_norm_lt_one hY),
    exp_neg_two_log_eq_eulerFac (satake_mul _ _ _) hα1 hβ1,
    exp_neg_two_log_eq_eulerFac (satake_mul _ _ _) hα1' hβ1', satake_add]

/-! ### the Euler product of `L(f, s)`, the global isobaric identity, and the
positivity inequality `1 ≤ ‖ζ(σ) L(σ+it)² L(σ−it)² G(σ+2it) G(σ)² G(σ−2it)‖` for `σ > 1` -/

/-- The Dirichlet series of `f` in the analytic normalisation,
`L(f, w) = Σ_n a_n n^{-(w + (k-1)/2)}` (absolutely convergent for `Re w > 1` by Rankin's bound). -/
def rsL (f : F) (w : ℂ) : ℂ := ∑' n : ℕ, rsCoeff f n * (n : ℂ) ^ (-(w + ((k : ℂ) - 1) / 2))

include cf in
/-- **Absolute convergence for `Re w > 1`**, from Rankin's mean-square bound and
`b ≤ (b² + 1)/2` with `b = ‖a_n‖ n^{-(k-1)/2}`. -/
lemma summable_norm_rsLterm (f : F) (hk : 0 < k) {w : ℂ} (hw : 1 < w.re) :
    Summable fun n : ℕ => ‖rsCoeff f n * (n : ℂ) ^ (-(w + ((k : ℂ) - 1) / 2))‖ := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hR : Summable fun n : ℕ => ‖rsCoeff f n‖ ^ 2 / (n : ℝ) ^ (w.re + k - 1) :=
    summable_rsDirichlet' k f hk (by linarith)
  have hZ : Summable fun n : ℕ => (n : ℝ) ^ (-w.re) := Real.summable_nat_rpow.mpr (by linarith)
  have hdom : Summable fun n : ℕ =>
      (‖rsCoeff f n‖ ^ 2 / (n : ℝ) ^ (w.re + k - 1) + (n : ℝ) ^ (-w.re)) / 2 :=
    (hR.add hZ).div_const 2
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hdom
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : rsCoeff f 0 = 0 := RankinSelbergDelta.CuspForm.qExpansion_coeff_zero_cusp f
    rw [h0, zero_mul, norm_zero]
    positivity
  · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hre : (-(w + ((k : ℂ) - 1) / 2)).re = -(w.re + ((k : ℝ) - 1) / 2) := by
      have : ((((k : ℂ) - 1) / 2)).re = ((k : ℝ) - 1) / 2 := by simp [Complex.div_re]
      rw [Complex.neg_re, Complex.add_re, this]
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hn, hre]
    set b : ℝ := ‖rsCoeff f n‖ * (n : ℝ) ^ (-(((k : ℝ) - 1) / 2)) with hb
    have hsplit : ‖rsCoeff f n‖ * (n : ℝ) ^ (-(w.re + ((k : ℝ) - 1) / 2)) = b * (n : ℝ) ^ (-w.re) := by
      rw [hb, show -(w.re + ((k : ℝ) - 1) / 2) = -(((k : ℝ) - 1) / 2) + -w.re by ring,
        Real.rpow_add hnR]
      ring
    have e1 : ((n : ℝ) ^ (-(((k : ℝ) - 1) / 2))) ^ 2 = (n : ℝ) ^ (-((k : ℝ) - 1)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hnR.le]
      congr 1
      push_cast
      ring
    have e2 : (n : ℝ) ^ (-((k : ℝ) - 1)) * (n : ℝ) ^ (-w.re) = ((n : ℝ) ^ (w.re + k - 1))⁻¹ := by
      rw [← Real.rpow_add hnR, ← Real.rpow_neg hnR.le]
      congr 1
      ring
    have hb2 : b ^ 2 * (n : ℝ) ^ (-w.re) = ‖rsCoeff f n‖ ^ 2 / (n : ℝ) ^ (w.re + k - 1) := by
      rw [hb, mul_pow, e1, mul_assoc, e2, div_eq_mul_inv]
    have hb1 : b ≤ (b ^ 2 + 1) / 2 := by nlinarith [sq_nonneg (b - 1)]
    have hn0 : 0 ≤ (n : ℝ) ^ (-w.re) := by positivity
    calc ‖rsCoeff f n‖ * (n : ℝ) ^ (-(w.re + ((k : ℝ) - 1) / 2)) = b * (n : ℝ) ^ (-w.re) := hsplit
      _ ≤ (b ^ 2 + 1) / 2 * (n : ℝ) ^ (-w.re) := mul_le_mul_of_nonneg_right hb1 hn0
      _ = (b ^ 2 * (n : ℝ) ^ (-w.re) + (n : ℝ) ^ (-w.re)) / 2 := by ring
      _ = _ := by rw [hb2]

include cf in
/-- `a(p^e) (p^e)^{-(w + (k-1)/2)} = h_e(ã) (p^{-w})^e`. -/
lemma lterm_prime_pow (f : F) (hf : IsHeckeEigenCoeffs (rsCoeff f) k) {p : ℕ} (hp : p.Prime)
    (w : ℂ) (e : ℕ) :
    rsCoeff f (p ^ e) * ((p ^ e : ℕ) : ℂ) ^ (-(w + ((k : ℂ) - 1) / 2))
      = heckeSeq (heckeNorm (rsCoeff f) k p) e * ((p : ℂ) ^ (-w)) ^ e := by
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hpe1 : 1 ≤ p ^ e := Nat.one_le_pow _ _ hp.pos
  have hq : ((p : ℂ) ^ (((k : ℂ) - 1) / 2)) ^ e * ((p ^ e : ℕ) : ℂ) ^ (-(w + ((k : ℂ) - 1) / 2))
      = ((p : ℂ) ^ (-w)) ^ e := by
    rw [natCast_cpow_eq_exp hpe1, natCast_cpow_eq_exp hp1 (((k : ℂ) - 1) / 2),
      natCast_cpow_neg_eq_exp hp1, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add,
      Nat.cast_pow, Real.log_pow]
    congr 1
    push_cast
    ring
  rw [hecke_coeff_pow hf hp e, mul_right_comm, hq]
  ring

include cf in
/-- Summability of the local series `Σ_e h_e(ã) (p^{-w})^e` at `Re w > 1`. -/
lemma summable_heckeSeq_cpow (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k) {p : ℕ}
    (hp : p.Prime) {w : ℂ} (hw : 1 < w.re) :
    Summable fun e => heckeSeq (heckeNorm (rsCoeff f) k p) e * ((p : ℂ) ^ (-w)) ^ e := by
  refine Summable.of_norm ?_
  have hY : ‖(p : ℂ) ^ (-w)‖ = (p : ℝ) ^ (-w.re) := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hY0 : 0 ≤ (p : ℝ) ^ (-w.re) := by positivity
  have hY1 : (p : ℝ) ^ (-w.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
  have hsq : Summable fun e : ℕ =>
      ‖heckeSeq (heckeNorm (rsCoeff f) k p) e‖ ^ 2 * ((p : ℝ) ^ (-w.re)) ^ e :=
    summable_heckeSeq_sq k f hk hf hp hw
  have hgeo : Summable fun e : ℕ => ((p : ℝ) ^ (-w.re)) ^ e := summable_geometric_of_lt_one hY0 hY1
  refine Summable.of_nonneg_of_le (fun e => norm_nonneg _) (fun e => ?_) ((hsq.add hgeo).div_const 2)
  rw [norm_mul, norm_pow, hY]
  nlinarith [sq_nonneg (‖heckeSeq (heckeNorm (rsCoeff f) k p) e‖ - 1), pow_nonneg hY0 e,
    mul_nonneg (sq_nonneg (‖heckeSeq (heckeNorm (rsCoeff f) k p) e‖ - 1)) (pow_nonneg hY0 e)]

/-- The coefficient `a_n n^{-(w + (k-1)/2)}` of `L(f, w)` as a multiplicative arithmetic function. -/
def lcoefAF (f : F) (hf : IsHeckeEigenCoeffs (rsCoeff f) k) (w : ℂ) : ArithmeticFunction ℂ :=
  ArithmeticFunction.pmul ⟨rsCoeff f, hf.zero⟩ (cpowAF (w + ((k : ℂ) - 1) / 2))

include cf in
/-- **The Euler product of `L(f, w)`** for `Re w > 1`: `L(f, w) = ∏_p (1 − ã_p p^{-w} + p^{-2w})⁻¹`. -/
theorem hasProd_rsL (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k) {w : ℂ}
    (hw : 1 < w.re) :
    HasProd (fun p : Nat.Primes => eulerFac (heckeNorm (rsCoeff f) k p) ((p : ℂ) ^ (-w)))
      (rsL k f w) := by
  have hmulA : (lcoefAF k f hf w).IsMultiplicative := by
    refine ArithmeticFunction.IsMultiplicative.pmul ⟨?_, ?_⟩ (isMultiplicative_cpowAF _)
    · simp only [ArithmeticFunction.coe_mk, hf.one]
    · intro m n hmn
      simp only [ArithmeticFunction.coe_mk]
      exact hf.mul_coprime m n hmn
  have hval : ∀ n : ℕ, lcoefAF k f hf w n = rsCoeff f n * (n : ℂ) ^ (-(w + ((k : ℂ) - 1) / 2)) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [lcoefAF, cpowAF, rsCoeff, RankinSelbergDelta.CuspForm.qExpansion_coeff_zero_cusp f]
    · simp only [lcoefAF, ArithmeticFunction.pmul_apply, cpowAF, ArithmeticFunction.coe_mk, if_neg hn]
  have hgsum : Summable fun n => ‖lcoefAF k f hf w n‖ := by
    refine (summable_norm_rsLterm k f hk hw).congr fun n => ?_
    rw [hval]
  have hEP := hmulA.eulerProduct_hasProd hgsum
  have htot : (∑' n, lcoefAF k f hf w n) = rsL k f w := by
    rw [rsL]
    exact tsum_congr hval
  rw [htot] at hEP
  convert hEP using 1
  funext p
  have hsum := summable_heckeSeq_cpow k f hk hf p.2 hw
  obtain ⟨hα, hβ⟩ := satake_mul_cpow_norm_lt k f hk hf p.2 hw
  have hne : 1 - heckeNorm (rsCoeff f) k p * (p : ℂ) ^ (-w) + ((p : ℂ) ^ (-w)) ^ 2 ≠ 0 := by
    have hfac : 1 - heckeNorm (rsCoeff f) k p * (p : ℂ) ^ (-w) + ((p : ℂ) ^ (-w)) ^ 2
        = (1 - satakeα (rsCoeff f) k p * (p : ℂ) ^ (-w))
          * (1 - satakeβ (rsCoeff f) k p * (p : ℂ) ^ (-w)) := by
      rw [← satake_add]
      linear_combination (-(((p : ℂ) ^ (-w)) ^ 2)) * satake_mul (rsCoeff f) k p
    rw [hfac]
    exact mul_ne_zero (one_sub_ne_zero_of_norm_lt_one hα) (one_sub_ne_zero_of_norm_lt_one hβ)
  rw [← tsum_heckeSeq_eq_eulerFac _ _ hsum hne]
  exact tsum_congr fun e => by rw [hval, lterm_prime_pow k f hf p.2 w e]

include cf in
/-- `∏_p exp ℓ_p(s) = G(s)` for `Re s > 1`. -/
lemma hasProd_exp_rsLocal (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k) {s : ℂ}
    (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => Complex.exp (rsLocal k f p s)) (Gfull k f s) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h2s : 1 < (2 * s).re := by
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat]; linarith
  have hζ := riemannZeta_eulerProduct_hasProd h2s
  have hD := hasProd_rsD k f hk hf (w := s + k - 1)
    (by simp only [Complex.sub_re, Complex.add_re, Complex.intCast_re, Complex.one_re]; linarith)
  rw [Gfull_eq k f hk hs]
  convert hζ.mul hD using 1
  funext p
  exact exp_rsLocal_eq k f hk hf p.2 hs

include cf in
/-- **The global isobaric identity**: for `σ > 1`,
`exp(Σ_p ℓ_p^η(σ)) = ζ(σ) L(σ+it)² L(σ−it)² G(σ+2it) G(σ)² G(σ−2it)`. -/
theorem isoProduct_eq (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k)
    (hreal : ∀ n, (starRingEnd ℂ) (rsCoeff f n) = rsCoeff f n) (t : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    ((Real.exp (∑' p : Nat.Primes,
        ∑' j, isoTerm (rsPow k f p) (t * Real.log p) (((p : ℕ) : ℝ) ^ (-σ)) j) : ℝ) : ℂ)
      = riemannZeta σ
        * (rsL k f ((σ : ℂ) + Complex.I * t) * rsL k f ((σ : ℂ) + Complex.I * t))
        * (rsL k f ((σ : ℂ) - Complex.I * t) * rsL k f ((σ : ℂ) - Complex.I * t))
        * Gfull k f ((σ : ℂ) + 2 * Complex.I * t) * (Gfull k f σ * Gfull k f σ)
        * Gfull k f ((σ : ℂ) - 2 * Complex.I * t) := by
  have hs0 : 1 < ((σ : ℂ)).re := by simpa using hσ
  have hs1 : 1 < ((σ : ℂ) + Complex.I * t).re := by simp; exact hσ
  have hs1' : 1 < ((σ : ℂ) - Complex.I * t).re := by simp; exact hσ
  have hs2 : 1 < ((σ : ℂ) + 2 * Complex.I * t).re := by simp; exact hσ
  have hs2' : 1 < ((σ : ℂ) - 2 * Complex.I * t).re := by simp; exact hσ
  -- summability over the primes
  have hbound : Summable fun p : Nat.Primes => 4 * ((p : ℕ) : ℝ) ^ (-σ) + 8 * rsLocalR k f p σ :=
    ((Nat.Primes.summable_rpow.mpr (by linarith : -σ < -1)).mul_left 4).add
      ((summable_rsLocalR k f hk hf hσ).mul_left 8)
  have hS : Summable fun p : Nat.Primes =>
      ∑' j, isoTerm (rsPow k f p) (t * Real.log p) (((p : ℕ) : ℝ) ^ (-σ)) j := by
    refine Summable.of_nonneg_of_le (fun p => tsum_nonneg fun j => isoTerm_nonneg _ _ (by positivity) j)
      (fun p => (isoLocal_summable_le k f hk hf hreal p.2 t hσ).2) hbound
  -- the product of the exponentials, in `ℂ`
  have hP := (hS.hasSum.rexp).map Complex.ofRealHom Complex.continuous_ofReal
  -- the six Euler products
  have hA := riemannZeta_eulerProduct_hasProd hs0
  have hB := hasProd_rsL k f hk hf hs1
  have hB' := hasProd_rsL k f hk hf hs1'
  have hC := hasProd_exp_rsLocal k f hk hf hs2
  have hD := hasProd_exp_rsLocal k f hk hf hs0
  have hC' := hasProd_exp_rsLocal k f hk hf hs2'
  have htot := (((((hA.mul (hB.mul hB)).mul (hB'.mul hB')).mul hC).mul (hD.mul hD)).mul hC')
  refine HasProd.unique ?_ htot
  convert hP using 1
  funext p
  simp only [Function.comp_apply, Complex.ofRealHom_eq_coe]
  rw [Complex.ofReal_exp, exp_isoLocal_eq k f hk hf hreal p.2 t hσ]

include cf in
/-- **The positivity inequality**: for `σ > 1`,
`1 ≤ ‖ζ(σ) L(σ+it)² L(σ−it)² G(σ+2it) G(σ)² G(σ−2it)‖`. -/
theorem one_le_norm_isoProduct (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k)
    (hreal : ∀ n, (starRingEnd ℂ) (rsCoeff f n) = rsCoeff f n) (t : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    1 ≤ ‖riemannZeta σ
        * (rsL k f ((σ : ℂ) + Complex.I * t) * rsL k f ((σ : ℂ) + Complex.I * t))
        * (rsL k f ((σ : ℂ) - Complex.I * t) * rsL k f ((σ : ℂ) - Complex.I * t))
        * Gfull k f ((σ : ℂ) + 2 * Complex.I * t) * (Gfull k f σ * Gfull k f σ)
        * Gfull k f ((σ : ℂ) - 2 * Complex.I * t)‖ := by
  rw [← isoProduct_eq k f hk hf hreal t hσ, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_nonneg _)]
  exact Real.one_le_exp (tsum_nonneg fun p => tsum_nonneg fun j => isoTerm_nonneg _ _ (by positivity) j)

/-! ### the entire L-function `L(f, ·)`, its agreement with the Dirichlet series on
`Re w > 1`, the conjugation symmetry, and `L(f, 1 + it) ≠ 0` for `t ≠ 0` -/

/-- **The L-function of `f` in the analytic normalisation**, as an entire function:
`L(f, w) = Λ(w') (2π)^{w'} / Γ(w')` with `w' = w + (k−1)/2`, where `Λ` is the completed
L-function of `f` (Mathlib's `StrongFEPair` through `RankinSelbergDelta.CuspForm.fePair`). -/
def Lfun (f : F) (hk : 0 < k) (w : ℂ) : ℂ :=
  RankinSelbergDelta.CuspForm.completedLSeries f hk (w + ((k : ℂ) - 1) / 2)
    * ((2 * Real.pi : ℝ) : ℂ) ^ (w + ((k : ℂ) - 1) / 2)
    * (Complex.Gamma (w + ((k : ℂ) - 1) / 2))⁻¹

/-- `L(f, ·)` is entire. -/
theorem differentiable_Lfun (f : F) (hk : 0 < k) : Differentiable ℂ (Lfun k f hk) := by
  have h2π : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hΛ : Differentiable ℂ fun w : ℂ =>
      RankinSelbergDelta.CuspForm.completedLSeries f hk (w + ((k : ℂ) - 1) / 2) :=
    (RankinSelbergDelta.CuspForm.differentiable_completedLSeries f hk).comp (differentiable_id.add_const _)
  have hpow : Differentiable ℂ fun w : ℂ => ((2 * Real.pi : ℝ) : ℂ) ^ (w + ((k : ℂ) - 1) / 2) :=
    fun w => (differentiableAt_id.add_const _).const_cpow (Or.inl h2π)
  have hΓ : Differentiable ℂ fun w : ℂ => (Complex.Gamma (w + ((k : ℂ) - 1) / 2))⁻¹ :=
    Complex.differentiable_one_div_Gamma.comp (differentiable_id.add_const _)
  exact (hΛ.mul hpow).mul hΓ

/-- The term of `rsL` is the `LSeries` term of `n ↦ a_n n^{-(k-1)/2}`. -/
lemma rsLterm_eq_term (f : F) (w : ℂ) (n : ℕ) :
    rsCoeff f n * (n : ℂ) ^ (-(w + ((k : ℂ) - 1) / 2))
      = LSeries.term (fun n => rsCoeff f n * (n : ℂ) ^ (-(((k : ℂ) - 1) / 2))) w n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_zero, rsCoeff, RankinSelbergDelta.CuspForm.qExpansion_coeff_zero_cusp f]
  · have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [LSeries.term_of_ne_zero hn, show -(w + ((k : ℂ) - 1) / 2) = -(((k : ℂ) - 1) / 2) + -w by ring,
      Complex.cpow_add _ _ hn0, Complex.cpow_neg (n : ℂ) w]
    ring

lemma rsL_eq_LSeries (f : F) (w : ℂ) :
    rsL k f w = LSeries (fun n => rsCoeff f n * (n : ℂ) ^ (-(((k : ℂ) - 1) / 2))) w := by
  unfold rsL LSeries
  exact tsum_congr fun n => rsLterm_eq_term k f w n

include cf in
lemma LSeriesSummable_rsL (f : F) (hk : 0 < k) {w : ℂ} (hw : 1 < w.re) :
    LSeriesSummable (fun n => rsCoeff f n * (n : ℂ) ^ (-(((k : ℂ) - 1) / 2))) w := by
  refine Summable.of_norm ((summable_norm_rsLterm k f hk hw).congr fun n => ?_)
  rw [rsLterm_eq_term]

include cf in
lemma abscissaOfAbsConv_rsL_le (f : F) (hk : 0 < k) :
    LSeries.abscissaOfAbsConv (fun n => rsCoeff f n * (n : ℂ) ^ (-(((k : ℂ) - 1) / 2))) ≤ (1 : ℝ) :=
  LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
    LSeriesSummable_rsL k f hk (w := (y : ℂ)) (by simpa using hy)

include cf in
/-- `rsL` is holomorphic on `Re w > 1`. -/
lemma differentiableOn_rsL (f : F) (hk : 0 < k) :
    DifferentiableOn ℂ (rsL k f) {w : ℂ | 1 < w.re} := by
  have heq : rsL k f = LSeries (fun n => rsCoeff f n * (n : ℂ) ^ (-(((k : ℂ) - 1) / 2))) :=
    funext fun w => rsL_eq_LSeries k f w
  rw [heq]
  refine (LSeries_differentiableOn _).mono fun w hw => ?_
  simp only [Set.mem_setOf_eq] at hw ⊢
  exact lt_of_le_of_lt (abscissaOfAbsConv_rsL_le k f hk) (by exact_mod_cast hw)

include cf in
/-- `L(f, w) = rsL w` for `Re w > 3/2`, from the `Λ(s) = (2π)^{-s} Γ(s) Σ a_n n^{-s}`. -/
lemma Lfun_eq_rsL_of_lt (f : F) (hk : 0 < k) {w : ℂ} (hw : 3 / 2 < w.re) :
    Lfun k f hk w = rsL k f w := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hre : (w + ((k : ℂ) - 1) / 2).re = w.re + ((k : ℝ) - 1) / 2 := by
    have : ((((k : ℂ) - 1) / 2)).re = ((k : ℝ) - 1) / 2 := by simp [Complex.div_re]
    rw [Complex.add_re, this]
  have hs : (k : ℝ) / 2 + 1 < (w + ((k : ℂ) - 1) / 2).re := by rw [hre]; linarith
  have hΓ : Complex.Gamma (w + ((k : ℂ) - 1) / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by rw [hre]; linarith)
  have h2π : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have h1 : ((2 * Real.pi : ℝ) : ℂ) ^ (-(w + ((k : ℂ) - 1) / 2))
      * ((2 * Real.pi : ℝ) : ℂ) ^ (w + ((k : ℂ) - 1) / 2) = 1 := by
    rw [← Complex.cpow_add _ _ h2π, neg_add_cancel, Complex.cpow_zero]
  have h2 : Complex.Gamma (w + ((k : ℂ) - 1) / 2) * (Complex.Gamma (w + ((k : ℂ) - 1) / 2))⁻¹ = 1 :=
    mul_inv_cancel₀ hΓ
  have hL : LSeries (fun n => (ModularFormClass.qExpansion 1 f).coeff n) (w + ((k : ℂ) - 1) / 2)
      = rsL k f w := by
    rw [rsL, LSeries]
    refine tsum_congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term_zero, rsCoeff, RankinSelbergDelta.CuspForm.qExpansion_coeff_zero_cusp f]
    · rw [LSeries.term_of_ne_zero hn, Complex.cpow_neg, div_eq_mul_inv]
      rfl
  rw [Lfun, RankinSelbergDelta.CuspForm.completedLSeries_eq_dirichlet' f hk hs]
  linear_combination (LSeries (fun n => (ModularFormClass.qExpansion 1 f).coeff n)
      (w + ((k : ℂ) - 1) / 2) * (Complex.Gamma (w + ((k : ℂ) - 1) / 2)
        * (Complex.Gamma (w + ((k : ℂ) - 1) / 2))⁻¹)) * h1
    + LSeries (fun n => (ModularFormClass.qExpansion 1 f).coeff n) (w + ((k : ℂ) - 1) / 2) * h2 + hL

include cf in
/-- **`L(f, w) = rsL w` on `Re w > 1`** (identity theorem on the half-plane). -/
theorem Lfun_eq_rsL (f : F) (hk : 0 < k) {w : ℂ} (hw : 1 < w.re) : Lfun k f hk w = rsL k f w := by
  set U : Set ℂ := {w | 1 < w.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : Convex ℝ U := convex_halfSpace_re_gt 1
  have hfa : AnalyticOnNhd ℂ (Lfun k f hk) U :=
    DifferentiableOn.analyticOnNhd (differentiable_Lfun k f hk).differentiableOn hUo
  have hga : AnalyticOnNhd ℂ (rsL k f) U :=
    DifferentiableOn.analyticOnNhd (differentiableOn_rsL k f hk) hUo
  have hz₀ : (2 : ℂ) ∈ U := by simp [hU]
  have hV : IsOpen {w : ℂ | 3 / 2 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2V : (2 : ℂ) ∈ {w : ℂ | 3 / 2 < w.re} := by simp; norm_num
  have hfg : Lfun k f hk =ᶠ[𝓝 (2 : ℂ)] rsL k f :=
    Filter.eventually_of_mem (hV.mem_nhds h2V) fun w hw => Lfun_eq_rsL_of_lt k f hk hw
  exact hfa.eqOn_of_preconnected_of_eventuallyEq hga hUc.isPreconnected hz₀ hfg hw

include cf in
/-- **Conjugation symmetry** of the Dirichlet series for a real-coefficient form:
`rsL (conj w) = conj (rsL w)` on `Re w > 1`. -/
lemma rsL_conj (f : F) (hk : 0 < k) (hreal : ∀ n, (starRingEnd ℂ) (rsCoeff f n) = rsCoeff f n)
    {w : ℂ} (hw : 1 < w.re) :
    rsL k f ((starRingEnd ℂ) w) = (starRingEnd ℂ) (rsL k f w) := by
  have hsum : Summable fun n : ℕ => rsCoeff f n * (n : ℂ) ^ (-(w + ((k : ℂ) - 1) / 2)) :=
    Summable.of_norm (summable_norm_rsLterm k f hk hw)
  have hH := hsum.hasSum.map (starRingEnd ℂ) Complex.continuous_conj
  unfold rsL
  rw [← hH.tsum_eq]
  refine tsum_congr fun n => ?_
  simp only [Function.comp_apply]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [rsCoeff, RankinSelbergDelta.CuspForm.qExpansion_coeff_zero_cusp f]
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hc : (starRingEnd ℂ) (w + ((k : ℂ) - 1) / 2) = (starRingEnd ℂ) w + ((k : ℂ) - 1) / 2 := by
      rw [map_add, map_div₀, map_sub, map_intCast, map_one, map_ofNat]
    rw [map_mul, hreal, natCast_cpow_eq_exp hn1, natCast_cpow_eq_exp hn1, ← Complex.exp_conj, map_mul,
      Complex.conj_ofReal, map_neg, hc]

/-- `conj (σ + it) = σ − it`. -/
lemma conj_ofReal_add_I_mul (σ t : ℝ) :
    (starRingEnd ℂ) ((σ : ℂ) + Complex.I * t) = (σ : ℂ) - Complex.I * t := by
  apply Complex.ext <;> simp

include cf in
/-- **Nonvanishing on `Re w = 1` (t ≠ 0)**: for a level-1 weight-`k` Hecke eigenform `f` with real coefficients
and every real `t ≠ 0`, `L(f, 1 + it) ≠ 0`.

The proof is the isobaric positivity argument on the real axis: for `σ > 1` the exponential of
the nonnegative series `Σ_p Σ_j (1 + 2 P_j(p) cos(jt log p))² p^{-jσ}/j` equals
`ζ(σ) L(σ+it)² L(σ−it)² G(σ+2it) G(σ)² G(σ−2it)` (with `G` the Rankin–Selberg square), so this
product has modulus `≥ 1`. If `L(1+it) = 0` the product is `O(σ − 1)` as `σ → 1⁺`
(`ζ, G = O(1/(σ−1))`, `L(σ±it) = O(σ−1)`, `G(1±2it)` finite because `t ≠ 0`), a contradiction. -/
theorem Lfunction_ne_zero_on_one_line (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k)
    (hreal : ∀ n, (starRingEnd ℂ) (rsCoeff f n) = rsCoeff f n) {t : ℝ} (ht : t ≠ 0) :
    Lfun k f hk (1 + Complex.I * t) ≠ 0 := by
  intro Hz
  -- ζ and G near the pole
  have hζ : (fun x : ℝ => riemannZeta (((1 + x : ℝ) : ℂ))) =O[𝓝[>] 0] fun x : ℝ => (1 : ℂ) / x := by
    refine (dlVP_pole_isBigO riemannZeta_residue_one).congr' ?_ EventuallyEq.rfl
    filter_upwards with x
    push_cast
    rfl
  have hG : (fun x : ℝ => Gfull k f (((1 + x : ℝ) : ℂ))) =O[𝓝[>] 0] fun x : ℝ => (1 : ℂ) / x := by
    refine (Gfull_isBigO k f hk).congr' ?_ EventuallyEq.rfl
    filter_upwards with x
    push_cast
    rfl
  -- L near its zero
  have hL0 : (fun w : ℂ => Lfun k f hk w - Lfun k f hk (1 + Complex.I * t))
      =O[𝓝 (1 + Complex.I * t)] fun w => w - (1 + Complex.I * t) :=
    (differentiable_Lfun k f hk _).isBigO_sub
  have hmap : Tendsto (fun x : ℝ => (1 + Complex.I * t) + (x : ℂ)) (𝓝[>] 0)
      (𝓝 (1 + Complex.I * t)) := by
    have : Tendsto (fun x : ℝ => (1 + Complex.I * t) + (x : ℂ)) (𝓝 0)
        (𝓝 ((1 + Complex.I * t) + ((0 : ℝ) : ℂ))) :=
      (continuous_const.add Complex.continuous_ofReal).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have hL : (fun x : ℝ => Lfun k f hk ((1 + Complex.I * t) + x)) =O[𝓝[>] 0] fun x : ℝ => (x : ℂ) := by
    have := hL0.comp_tendsto hmap
    simpa [Hz, Function.comp_def] using this
  have hL1 : (fun x : ℝ => rsL k f (((1 + x : ℝ) : ℂ) + Complex.I * t)) =O[𝓝[>] 0]
      fun x : ℝ => (x : ℂ) := by
    refine hL.congr' ?_ EventuallyEq.rfl
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hre : 1 < ((1 + Complex.I * t) + (x : ℂ)).re := by simp; exact hx
    rw [Lfun_eq_rsL k f hk hre]
    congr 1
    push_cast
    ring
  have hL1' : (fun x : ℝ => rsL k f (((1 + x : ℝ) : ℂ) - Complex.I * t)) =O[𝓝[>] 0]
      fun x : ℝ => (x : ℂ) := by
    refine IsBigO.of_norm_left ?_
    refine hL1.norm_left.congr' ?_ EventuallyEq.rfl
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hre : 1 < ((((1 + x : ℝ) : ℂ)) + Complex.I * t).re := by simp; exact hx
    rw [← conj_ofReal_add_I_mul, rsL_conj k f hk hreal hre, Complex.norm_conj]
  -- G at the shifted points
  have hC : (fun x : ℝ => Gfull k f (((1 + x : ℝ) : ℂ) + 2 * Complex.I * t)) =O[𝓝[>] 0]
      fun _ : ℝ => (1 : ℂ) := by
    have hcont := continuousAt_Gfull_line2 k f hk ht
    have hmap2 : Tendsto (fun x : ℝ => (((1 + x : ℝ) : ℂ) + 2 * Complex.I * t)) (𝓝[>] 0)
        (𝓝 (1 + 2 * Complex.I * t)) := by
      have : Tendsto (fun x : ℝ => (((1 + x : ℝ) : ℂ) + 2 * Complex.I * t)) (𝓝 0)
          (𝓝 ((((1 + (0 : ℝ) : ℝ) : ℂ)) + 2 * Complex.I * t)) := by
        refine Continuous.tendsto ?_ 0
        fun_prop
      simpa using this.mono_left nhdsWithin_le_nhds
    exact (hcont.tendsto.comp hmap2).isBigO_one ℂ
  have hC' : (fun x : ℝ => Gfull k f (((1 + x : ℝ) : ℂ) - 2 * Complex.I * t)) =O[𝓝[>] 0]
      fun _ : ℝ => (1 : ℂ) := by
    have hcont := continuousAt_Gfull_line2 k f hk (neg_ne_zero.mpr ht)
    rw [show (1 + 2 * Complex.I * ((-t : ℝ) : ℂ)) = 1 - 2 * Complex.I * t by push_cast; ring] at hcont
    have hmap2 : Tendsto (fun x : ℝ => (((1 + x : ℝ) : ℂ) - 2 * Complex.I * t)) (𝓝[>] 0)
        (𝓝 (1 - 2 * Complex.I * t)) := by
      have : Tendsto (fun x : ℝ => (((1 + x : ℝ) : ℂ) - 2 * Complex.I * t)) (𝓝 0)
          (𝓝 ((((1 + (0 : ℝ) : ℝ) : ℂ)) - 2 * Complex.I * t)) := by
        refine Continuous.tendsto ?_ 0
        fun_prop
      simpa using this.mono_left nhdsWithin_le_nhds
    exact (hcont.tendsto.comp hmap2).isBigO_one ℂ
  -- the positivity inequality, `1 ≤ ‖F x‖` for `x > 0`
  have H1 : ∀ x : ℝ, 0 < x → 1 ≤ ‖riemannZeta (((1 + x : ℝ) : ℂ))
      * (rsL k f (((1 + x : ℝ) : ℂ) + Complex.I * t) * rsL k f (((1 + x : ℝ) : ℂ) + Complex.I * t))
      * (rsL k f (((1 + x : ℝ) : ℂ) - Complex.I * t) * rsL k f (((1 + x : ℝ) : ℂ) - Complex.I * t))
      * Gfull k f (((1 + x : ℝ) : ℂ) + 2 * Complex.I * t)
      * (Gfull k f (((1 + x : ℝ) : ℂ)) * Gfull k f (((1 + x : ℝ) : ℂ)))
      * Gfull k f (((1 + x : ℝ) : ℂ) - 2 * Complex.I * t)‖ :=
    fun x hx => one_le_norm_isoProduct k f hk hf hreal t (σ := 1 + x) (by linarith)
  have H₀ : (fun _ : ℝ => (1 : ℝ)) =O[𝓝[>] 0] fun x : ℝ => riemannZeta (((1 + x : ℝ) : ℂ))
      * (rsL k f (((1 + x : ℝ) : ℂ) + Complex.I * t) * rsL k f (((1 + x : ℝ) : ℂ) + Complex.I * t))
      * (rsL k f (((1 + x : ℝ) : ℂ) - Complex.I * t) * rsL k f (((1 + x : ℝ) : ℂ) - Complex.I * t))
      * Gfull k f (((1 + x : ℝ) : ℂ) + 2 * Complex.I * t)
      * (Gfull k f (((1 + x : ℝ) : ℂ)) * Gfull k f (((1 + x : ℝ) : ℂ)))
      * Gfull k f (((1 + x : ℝ) : ℂ) - 2 * Complex.I * t) :=
    IsBigO.of_bound' <| eventually_nhdsWithin_of_forall
      fun x hx => (norm_one (α := ℝ)).symm ▸ (H1 x hx)
  -- the product is `O(x)`
  have H := (((((hζ.mul (hL1.mul hL1)).mul (hL1'.mul hL1')).mul hC).mul (hG.mul hG)).mul hC')
  have help : ∀ x : ℝ, ((1 : ℂ) / x * ((x : ℂ) * x) * ((x : ℂ) * x) * 1
      * ((1 : ℂ) / x * ((1 : ℂ) / x)) * 1 : ℂ) = x := by
    intro x
    rcases eq_or_ne x 0 with rfl | h
    · simp
    · have hx : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h
      field_simp
  have Hx : (fun x : ℝ => (1 : ℂ) / x * ((x : ℂ) * x) * ((x : ℂ) * x) * 1
      * ((1 : ℂ) / x * ((1 : ℂ) / x)) * 1) =O[𝓝[>] 0] fun x : ℝ => (x : ℂ) :=
    IsBigO.of_bound 1 (Filter.Eventually.of_forall fun x => by rw [help x, one_mul])
  replace H := (H₀.trans (H.trans Hx)).norm_right
  simp only [Complex.norm_real] at H
  exact isLittleO_irrefl (.of_forall (fun _ ↦ one_ne_zero)) <|
    H.of_norm_right.trans_isLittleO <| isLittleO_id_one.mono nhdsWithin_le_nhds


end

end RankinSelbergDelta.RankinSelberg
