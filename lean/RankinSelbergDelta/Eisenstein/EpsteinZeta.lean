import RankinSelbergDelta.Eisenstein.EpsteinTheta

/-!
# The Epstein zeta function and the real-analytic Eisenstein series

`Z_z(s) = Σ' |mz + n|^{−2s} (Im z)^s` and `E(z, s) = Z_z(s) / (2 ζ(2s))`. Through the
`WeakFEPair` built from the theta function, `π^{−s} Γ(s) Z_z(s)` is meromorphic with a simple pole
at `s = 1` of residue 1. Hence `Z_z` has a simple pole at `s = 1` with residue `π`, and `E` with
residue `3/π`.
-/

namespace RankinSelbergDelta.Eisenstein

open Complex UpperHalfPlane Filter Topology Set Real

noncomputable section

/-- The completed Epstein theta FE-pair's `Λ`, meromorphic on `ℂ` with a simple pole at `s = 1`. -/
def epsteinΛ (z : ℍ) : ℂ → ℂ := (epsteinFEPair z).Λ

/-- `epsteinΛ` is differentiable away from `s = 0` and `s = 1`. -/
theorem differentiableAt_epsteinΛ (z : ℍ) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (epsteinΛ z) s :=
  (epsteinFEPair z).differentiableAt_Λ (Or.inl hs0) (Or.inl (by simpa using hs1))

/-- The simple pole of `epsteinΛ` at `s = 1`: residue `1` (`= ε • g₀`). -/
theorem epsteinΛ_residue_one (z : ℍ) :
    Tendsto (fun s : ℂ => (s - 1) • epsteinΛ z s) (𝓝[≠] 1) (𝓝 1) := by
  have h := (epsteinFEPair z).Λ_residue_k
  simpa [epsteinΛ, epsteinFEPair] using h

/-- The Epstein zeta function `Z_z(s) = π^s / Γ(s) · Λ(s)` (so `Λ(s) = π^{-s} Γ(s) Z_z(s)`). -/
def epsteinZeta (z : ℍ) (s : ℂ) : ℂ := (π : ℂ) ^ s / Complex.Gamma s * epsteinΛ z s

/-- The Epstein zeta has a simple pole at `s = 1` with residue `π`. -/
theorem epsteinZeta_residue_one (z : ℍ) :
    Tendsto (fun s : ℂ => (s - 1) * epsteinZeta z s) (𝓝[≠] 1) (𝓝 (π : ℂ)) := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hL : Tendsto (fun s : ℂ => (s - 1) * epsteinΛ z s) (𝓝[≠] 1) (𝓝 1) := by
    simpa [smul_eq_mul] using epsteinΛ_residue_one z
  have hc : Tendsto (fun s : ℂ => (π : ℂ) ^ s / Complex.Gamma s) (𝓝[≠] 1) (𝓝 (π : ℂ)) := by
    have hcont : ContinuousAt (fun s : ℂ => (π : ℂ) ^ s / Complex.Gamma s) 1 :=
      (continuousAt_const_cpow hπ).div Complex.differentiableAt_Gamma_one.continuousAt
        (by rw [Complex.Gamma_one]; exact one_ne_zero)
    have h : Tendsto (fun s : ℂ => (π : ℂ) ^ s / Complex.Gamma s) (𝓝[≠] 1)
        (𝓝 ((π : ℂ) ^ (1 : ℂ) / Complex.Gamma 1)) := hcont.continuousWithinAt.tendsto
    simpa [Complex.cpow_one, Complex.Gamma_one] using h
  have heq : (fun s : ℂ => (s - 1) * epsteinZeta z s)
      = fun s => ((π : ℂ) ^ s / Complex.Gamma s) * ((s - 1) * epsteinΛ z s) := by
    funext s; rw [epsteinZeta]; ring
  rw [heq]
  simpa using hc.mul hL

/-- The Epstein-zeta Dirichlet summand `Q_z(p)^{-σ}` is summable over `p ≠ (0,0)` for `σ > 1`
    (2-D convergence), by comparison with the lattice sum `‖p‖^{-2σ}` via the positive-definite
    bound `Q_z(p) ≥ c·(m²+n²) ≥ c·‖p‖²`. -/
lemma summable_Qform_neg_rpow (z : ℍ) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun p : {p : ℤ × ℤ // p ≠ 0} => (Qform z (p : ℤ × ℤ).1 (p : ℤ × ℤ).2) ^ (-σ) := by
  obtain ⟨c, hc, hcle⟩ := Qform_lower_bound z
  have hlat : Summable fun x : Fin 2 → ℤ => ‖x‖ ^ (-(2 * σ)) :=
    EisensteinSeries.summable_one_div_norm_rpow (by linarith)
  have hlat2 : Summable fun p : ℤ × ℤ => ‖(finTwoArrowEquiv ℤ).symm p‖ ^ (-(2 * σ)) :=
    ((finTwoArrowEquiv ℤ).symm.summable_iff
      (f := fun x : Fin 2 → ℤ => ‖x‖ ^ (-(2 * σ)))).mpr hlat
  have hcmp : Summable fun p : {p : ℤ × ℤ // p ≠ 0} =>
      c ^ (-σ) * ‖(finTwoArrowEquiv ℤ).symm (p : ℤ × ℤ)‖ ^ (-(2 * σ)) :=
    (hlat2.subtype _).mul_left _
  refine Summable.of_nonneg_of_le (fun p => Real.rpow_nonneg (Qform_nonneg z _ _) _)
    (fun p => ?_) hcmp
  obtain ⟨⟨m, n⟩, hp⟩ := p
  have hne : ¬ (m = 0 ∧ n = 0) := by rintro ⟨rfl, rfl⟩; exact hp rfl
  have hv : ‖(finTwoArrowEquiv ℤ).symm (m, n)‖ = ((max m.natAbs n.natAbs : ℕ) : ℝ) := by
    rw [show (finTwoArrowEquiv ℤ).symm (m, n) = ![m, n] from rfl,
      EisensteinSeries.norm_eq_max_natAbs]
    simp
  have hnorm_sq : ‖(finTwoArrowEquiv ℤ).symm (m, n)‖ ^ 2 ≤ (m : ℝ) ^ 2 + (n : ℝ) ^ 2 := by
    rw [hv]
    have hm : ((m.natAbs : ℝ)) ^ 2 = (m : ℝ) ^ 2 := by rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
    have hn : ((n.natAbs : ℝ)) ^ 2 = (n : ℝ) ^ 2 := by rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
    rcases le_total m.natAbs n.natAbs with h | h
    · rw [max_eq_right h, hn]; nlinarith [sq_nonneg (m : ℝ)]
    · rw [max_eq_left h, hm]; nlinarith [sq_nonneg (n : ℝ)]
  have hnv_pos : (0 : ℝ) < ‖(finTwoArrowEquiv ℤ).symm (m, n)‖ := by
    rw [hv, Nat.cast_pos]
    rcases not_and_or.mp hne with h | h
    · exact lt_of_lt_of_le (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr h)) (le_max_left _ _)
    · exact lt_of_lt_of_le (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr h)) (le_max_right _ _)
  have hcv : c * ‖(finTwoArrowEquiv ℤ).symm (m, n)‖ ^ 2 ≤ Qform z m n :=
    le_trans (mul_le_mul_of_nonneg_left hnorm_sq hc.le) (hcle m n)
  have hcvpos : (0 : ℝ) < c * ‖(finTwoArrowEquiv ℤ).symm (m, n)‖ ^ 2 :=
    mul_pos hc (pow_pos hnv_pos 2)
  calc Qform z m n ^ (-σ)
      ≤ (c * ‖(finTwoArrowEquiv ℤ).symm (m, n)‖ ^ 2) ^ (-σ) :=
        Real.rpow_le_rpow_of_nonpos hcvpos hcv (by linarith)
    _ = c ^ (-σ) * ‖(finTwoArrowEquiv ℤ).symm (m, n)‖ ^ (-(2 * σ)) := by
        rw [Real.mul_rpow hc.le (by positivity),
          ← Real.rpow_natCast ‖(finTwoArrowEquiv ℤ).symm (m, n)‖ 2,
          ← Real.rpow_mul (norm_nonneg _)]
        ring_nf

/-- **The Epstein zeta as a lattice Dirichlet series.** For `Re s > 1`,
    `Z_z(s) = Σ'_{(m,n) ≠ 0} Q_z(m,n)^{-s}`. This identifies the FE-pair's `Λ` (through
    `π^s/Γ(s)`) with the absolutely convergent lattice sum, via `WeakFEPair.hasMellin`
    (`Λ s = mellin(θ_z − 1) s`) and `hasSum_mellin_pi_mul`. The input files 3–4 (coset
    decomposition, unfolding) consume this form. -/
theorem epsteinZeta_eq_tsum (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    epsteinZeta z s
      = ∑' p : {p : ℤ × ℤ // p ≠ 0}, (Qform z (p : ℤ × ℤ).1 (p : ℤ × ℤ).2 : ℂ) ^ (-s) := by
  have hs0 : 0 < s.re := by linarith
  have hΓ : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs0
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  -- positivity of Q on the subtype
  have hQpos : ∀ p : {p : ℤ × ℤ // p ≠ 0}, 0 < Qform z (p : ℤ × ℤ).1 (p : ℤ × ℤ).2 := by
    intro p
    obtain ⟨c, hc, hcle⟩ := Qform_lower_bound z
    have hmn : (0 : ℝ) < ((p : ℤ × ℤ).1 : ℝ) ^ 2 + ((p : ℤ × ℤ).2 : ℝ) ^ 2 := by
      by_contra h
      push_neg at h
      have h1 : ((p : ℤ × ℤ).1 : ℝ) = 0 ∧ ((p : ℤ × ℤ).2 : ℝ) = 0 := by
        constructor <;> nlinarith [sq_nonneg ((p : ℤ × ℤ).1 : ℝ), sq_nonneg ((p : ℤ × ℤ).2 : ℝ)]
      exact p.2 (Prod.ext (by exact_mod_cast h1.1) (by exact_mod_cast h1.2))
    calc (0 : ℝ) < c * (((p : ℤ × ℤ).1 : ℝ) ^ 2 + ((p : ℤ × ℤ).2 : ℝ) ^ 2) := by positivity
      _ ≤ _ := hcle _ _
  -- the Mellin = Dirichlet series HasSum
  have hHasSum := hasSum_mellin_pi_mul
    (a := fun _ : {p : ℤ × ℤ // p ≠ 0} => (1 : ℂ))
    (q := fun p => Qform z (p : ℤ × ℤ).1 (p : ℤ × ℤ).2)
    (F := fun t => thetaQ z t - 1) (s := s)
    (fun p => Or.inr (hQpos p)) hs0 ?_ ?_
  · -- from HasSum, extract Λ and conclude
    have hmel : mellin (fun t => thetaQ z t - 1) s = epsteinΛ z s := by
      have := ((epsteinFEPair z).hasMellin (s := s) (by simpa using hs)).2
      simpa [epsteinΛ, epsteinFEPair] using this
    rw [hmel] at hHasSum
    have htsum := hHasSum.tsum_eq
    rw [epsteinZeta, ← htsum, ← tsum_mul_left]
    refine tsum_congr fun p => ?_
    have hqpos := hQpos p
    have hQne : ((Qform z (p : ℤ × ℤ).1 (p : ℤ × ℤ).2 : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hqpos.ne'
    have hπs : (Real.pi : ℂ) ^ s ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]; push_neg; intro h; exact absurd h hπ
    have hQs : ((Qform z (p : ℤ × ℤ).1 (p : ℤ × ℤ).2 : ℝ) : ℂ) ^ s ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]; push_neg; intro h; exact absurd h hQne
    rw [Complex.cpow_neg (Real.pi : ℂ) s, Complex.cpow_neg _ s]
    field_simp
  · -- hF : the theta sum minus the (0,0) term
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    classical
    set f : ℤ × ℤ → ℂ := fun p => (Real.exp (-Real.pi * t * Qform z p.1 p.2) : ℂ) with hf
    have hHS : HasSum f (thetaQ z t) := (summable_thetaQ z ht0).hasSum
    have hf00 : f (0, 0) = 1 := by simp [hf, Qform_zero]
    have hcompl : HasSum (fun i : {x : ℤ × ℤ // x ∉ ({(0, 0)} : Finset (ℤ × ℤ))} => f i)
        (thetaQ z t - 1) := by
      rw [Finset.hasSum_compl_iff, Finset.sum_singleton, hf00]
      simpa using hHS
    have h01 : ∀ x : ℤ × ℤ, x ≠ 0 ↔ x ∉ ({(0, 0)} : Finset (ℤ × ℤ)) := fun x => by
      rw [Finset.mem_singleton]; exact Iff.rfl
    have hsub := ((Equiv.subtypeEquivRight h01).hasSum_iff
      (f := fun i : {x : ℤ × ℤ // x ∉ ({(0, 0)} : Finset (ℤ × ℤ))} => f i)).mpr hcompl
    have heq : (fun i : {x : ℤ × ℤ // x ≠ 0} =>
        (1 : ℂ) * (Real.exp (-Real.pi * Qform z (i : ℤ × ℤ).1 (i : ℤ × ℤ).2 * t) : ℂ))
        = fun i : {x : ℤ × ℤ // x ≠ 0} =>
          f ((Equiv.subtypeEquivRight h01 i :
            {x : ℤ × ℤ // x ∉ ({(0, 0)} : Finset (ℤ × ℤ))}) : ℤ × ℤ) := by
      funext i
      simp only [Equiv.subtypeEquivRight_apply, hf, one_mul]
      rw [show (-Real.pi * t * Qform z (i : ℤ × ℤ).1 (i : ℤ × ℤ).2)
            = -Real.pi * Qform z (i : ℤ × ℤ).1 (i : ℤ × ℤ).2 * t from by ring]
    show HasSum (fun i : {x : ℤ × ℤ // x ≠ 0} =>
        (1 : ℂ) * (Real.exp (-Real.pi * Qform z (i : ℤ × ℤ).1 (i : ℤ × ℤ).2 * t) : ℂ))
        (thetaQ z t - 1)
    rw [heq]
    exact hsub
  · -- h_sum : summability
    refine (summable_Qform_neg_rpow z hs).congr fun p => ?_
    rw [norm_one, Real.rpow_neg (Qform_nonneg z _ _), one_div]

/-- The real-analytic Eisenstein series `E(z,s) = Z_z(s) / (2 ζ(2s))`. -/
def eisensteinE (z : ℍ) (s : ℂ) : ℂ := epsteinZeta z s / (2 * riemannZeta (2 * s))

/-- `E(z,s)` has a simple pole at `s = 1` with residue `3/π` (`= π / (2 ζ(2))`, `ζ(2) = π²/6`). -/
theorem eisensteinE_residue_one (z : ℍ) :
    Tendsto (fun s : ℂ => (s - 1) * eisensteinE z s) (𝓝[≠] 1) (𝓝 (3 / π : ℂ)) := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hZ := epsteinZeta_residue_one z
  have hζcont : ContinuousAt (fun s : ℂ => riemannZeta (2 * s)) 1 := by
    have : ContinuousAt riemannZeta (2 * 1) := (differentiableAt_riemannZeta (by norm_num)).continuousAt
    exact this.comp (by fun_prop)
  have hne : (2 : ℂ) * riemannZeta 2 ≠ 0 := by
    rw [riemannZeta_two]
    exact mul_ne_zero two_ne_zero (div_ne_zero (pow_ne_zero 2 hπ) (by norm_num))
  have hden : Tendsto (fun s : ℂ => 1 / (2 * riemannZeta (2 * s))) (𝓝[≠] 1)
      (𝓝 (1 / (2 * riemannZeta 2))) := by
    have hcont : ContinuousAt (fun s : ℂ => 1 / (2 * riemannZeta (2 * s))) 1 :=
      continuousAt_const.div (continuousAt_const.mul hζcont) (by simpa using hne)
    simpa only [mul_one] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have heq : (fun s : ℂ => (s - 1) * eisensteinE z s)
      = fun s => ((s - 1) * epsteinZeta z s) * (1 / (2 * riemannZeta (2 * s))) := by
    funext s; rw [eisensteinE]; ring
  have hval : (3 / π : ℂ) = (π : ℂ) * (1 / (2 * riemannZeta 2)) := by
    rw [riemannZeta_two]; field_simp; ring
  rw [heq, hval]
  exact hZ.mul hden

end

end RankinSelbergDelta.Eisenstein
