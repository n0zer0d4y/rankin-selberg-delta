import RankinSelbergDelta.RankinSelberg.ExplicitFormulaSmooth

/-!
# The sum over zeros of `G`

`summable_zeroSum_Gfull`: the sum of `ĝ` over the zeros of `(s − 1) G(s)` in the critical strip
converges absolutely; and `explicitFormula_Gfull_tsum`, the explicit formula as an identity of
series over all zeros, with its smooth corollaries.
-/

open MeasureTheory Filter
open scoped NNReal MatrixGroups Pointwise

noncomputable section

/-! ## The unconditional zero sum

The generic part below uses `RankinSelbergDelta.ZeroCount`, `RankinSelbergDelta.ArgPrinciple`,
`RankinSelbergDelta.Analysis.PaleyWiener.sum_div_im_sq_le`, `eq_zero_of_divisor_ne_zero`. Mathlib names
relied on: `summable_of_sum_le`, `Summable.of_norm`, `tendsto_tsum_of_dominated_convergence`,
`tsum_eq_finsum`, `tendsto_nhds_unique`, `MeromorphicOn.divisor_apply`,
`MeromorphicOn.AnalyticOnNhd.divisor_nonneg`, `Function.locallyFinsuppWithin.finiteSupport`,
`Function.locallyFinsuppWithin.supportWithinDomain`, `Complex.mem_reProdIm`, `Set.uIcc_of_le`,
`Complex.norm_natCast`, `Int.toNat_of_nonneg`, `Finset.sum_filter_add_sum_filter_not`,
`Finset.sum_le_sum_of_subset_of_nonneg`, `finsum_mem_eq_finite_toFinset_sum`. -/

namespace RankinSelbergDelta.RankinSelberg.ZeroSum

open RankinSelbergDelta.ZeroCount RankinSelbergDelta.ArgPrinciple RankinSelbergDelta.Analysis.PaleyWiener
open MeasureTheory Filter Topology

/-- The closed vertical strip `1 - σ ≤ Re u ≤ σ`. -/
def strip (σ : ℝ) : Set ℂ := {u : ℂ | 1 - σ ≤ u.re ∧ u.re ≤ σ}

lemma mem_strip {σ : ℝ} {u : ℂ} : u ∈ strip σ ↔ 1 - σ ≤ u.re ∧ u.re ≤ σ := Iff.rfl

/-- Membership in the rectangle `[1 - σ, σ] × [-t, t]`. -/
lemma mem_closedRect_strip_iff {σ t : ℝ} (hσ : 1 - σ ≤ σ) (ht : 0 ≤ t) (u : ℂ) :
    u ∈ closedRect ⟨1 - σ, -t⟩ ⟨σ, t⟩ ↔ (1 - σ ≤ u.re ∧ u.re ≤ σ) ∧ |u.im| ≤ t := by
  rw [closedRect, Complex.mem_reProdIm]
  show u.re ∈ Set.uIcc (1 - σ) σ ∧ u.im ∈ Set.uIcc (-t) t ↔ _
  rw [Set.uIcc_of_le hσ, Set.uIcc_of_le (by linarith : -t ≤ t), Set.mem_Icc, Set.mem_Icc, abs_le]

/-- The divisor of an entire function on a set is nonnegative. -/
lemma divisor_nonneg_of_entire (h : ℂ → ℂ) (hh : ∀ z, AnalyticAt ℂ h z) (U : Set ℂ) (u : ℂ) :
    0 ≤ MeromorphicOn.divisor h U u := by
  have hfa : AnalyticOnNhd ℂ h U := fun s _ => hh s
  have := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfa u
  simpa using this

/-- A nonzero divisor value lies in the domain. -/
lemma mem_of_divisor_ne_zero {h : ℂ → ℂ} {U : Set ℂ} {u : ℂ}
    (hu : MeromorphicOn.divisor h U u ≠ 0) : u ∈ U :=
  (MeromorphicOn.divisor h U).supportWithinDomain (Function.mem_support.mpr hu)

/-- **Absolute summability of the zero sum.** For `h` entire with the band count
`wcount h (band (-1) σ₀ T) ≤ K T log T` (`T ≥ 2`, `σ₀ ≥ 2`), `1 < σ < 2`, and a weight with
`‖φ s‖ (Im s)² ≤ B` on the strip for `|Im s| ≥ 1`, the family `u ↦ ‖D(u) φ(u)‖` is summable,
`D` the divisor of `h` on the strip. -/
theorem summable_norm_divisor_mul (h : ℂ → ℂ) (hh : ∀ z, AnalyticAt ℂ h z) {σ σ₀ K : ℝ}
    (hσ1 : 1 < σ) (hσ2 : σ < 2) (hσ₀ : 2 ≤ σ₀)
    (hcount : ∀ T : ℝ, 2 ≤ T → (zerosIn h (band (-1) σ₀ T)).Finite ∧
      wcount h (band (-1) σ₀ T) ≤ K * T * Real.log T)
    (φ : ℂ → ℂ)
    (hdec : ∃ B : ℝ, ∀ s : ℂ, 1 - σ ≤ s.re → s.re ≤ σ → 1 ≤ |s.im| → ‖φ s‖ * s.im ^ 2 ≤ B) :
    Summable (fun u : ℂ => ‖((MeromorphicOn.divisor h (strip σ)) u : ℂ) * φ u‖) := by
  classical
  set U : Set ℂ := strip σ with hU
  set D := MeromorphicOn.divisor h U with hD
  have hfa : AnalyticOnNhd ℂ h U := fun s _ => hh s
  have hD0 : ∀ u, 0 ≤ D u := fun u => divisor_nonneg_of_entire h hh U u
  have hre : ∀ u, D u ≠ 0 → 1 - σ ≤ u.re ∧ u.re ≤ σ := fun u hu => mem_of_divisor_ne_zero hu
  -- the rectangle of height `2`
  set K₂ : Set ℂ := closedRect ⟨1 - σ, -2⟩ ⟨σ, 2⟩ with hK₂
  set D₂ := MeromorphicOn.divisor h K₂ with hD₂
  have hfa₂ : AnalyticOnNhd ℂ h K₂ := fun s _ => hh s
  have hD₂fin : (Function.support D₂).Finite := D₂.finiteSupport (isCompact_closedRect _ _)
  set S₂ : Finset ℂ := hD₂fin.toFinset with hS₂
  have hmemK₂ : ∀ u, u ∈ K₂ ↔ (1 - σ ≤ u.re ∧ u.re ≤ σ) ∧ |u.im| ≤ 2 := fun u =>
    mem_closedRect_strip_iff (by linarith) (by norm_num) u
  have hagree : ∀ u ∈ K₂, D u = D₂ u := by
    intro u hu
    have huU : u ∈ U := ((hmemK₂ u).mp hu).1
    rw [hD, hD₂, MeromorphicOn.divisor_apply hfa.meromorphicOn huU,
      MeromorphicOn.divisor_apply hfa₂.meromorphicOn hu]
  obtain ⟨B, hB⟩ := hdec
  have hB0 : 0 ≤ B := by
    have h1 := hB Complex.I (by simp; linarith) (by simp; linarith) (by simp)
    have h2 : 0 ≤ ‖φ Complex.I‖ * (Complex.I).im ^ 2 := by positivity
    linarith
  set Clow : ℝ := ∑ u ∈ S₂, ‖(D u : ℂ) * φ u‖ with hClow
  set K' : ℝ := max K 0 with hK'
  set m : ℂ → ℕ := fun u => (D u).toNat with hm
  have hmD : ∀ u, ((m u : ℕ) : ℂ) = (D u : ℂ) := fun u => by
    simp only [hm]
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (hD0 u)]
  refine summable_of_sum_le (fun u => norm_nonneg _)
    (c := Clow + B * (2 * K' * (1 + Real.log 2) / 2)) fun s => ?_
  -- drop the terms outside the support of `D`
  set s₁ : Finset ℂ := s.filter (fun u => D u ≠ 0) with hs₁
  have hs1 : ∑ u ∈ s, ‖(D u : ℂ) * φ u‖ = ∑ u ∈ s₁, ‖(D u : ℂ) * φ u‖ := by
    rw [hs₁, Finset.sum_filter]
    refine Finset.sum_congr rfl fun u _ => ?_
    split_ifs with hu
    · rfl
    · rw [not_not.mp hu]; simp
  rw [hs1, ← Finset.sum_filter_add_sum_filter_not s₁ (fun u => |u.im| ≤ 2)]
  -- the low part is dominated by the fixed finite sum over `S₂`
  have hlow : ∑ u ∈ s₁.filter (fun u => |u.im| ≤ 2), ‖(D u : ℂ) * φ u‖ ≤ Clow := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => norm_nonneg _
    intro u hu
    rw [Finset.mem_filter, hs₁, Finset.mem_filter] at hu
    obtain ⟨⟨_, hDu⟩, him⟩ := hu
    have huK : u ∈ K₂ := (hmemK₂ u).mpr ⟨hre u hDu, him⟩
    rw [hS₂, Set.Finite.mem_toFinset, Function.mem_support, ← hagree u huK]
    exact hDu
  -- the high part by Abel summation
  set S' : Finset ℂ := s₁.filter (fun u => ¬ |u.im| ≤ 2) with hS'
  have hS'H : ∀ ρ ∈ S', 2 < |ρ.im| := by
    intro ρ hρ
    rw [hS', Finset.mem_filter] at hρ
    exact lt_of_not_ge hρ.2
  have hS'D : ∀ ρ ∈ S', D ρ ≠ 0 := by
    intro ρ hρ
    rw [hS', Finset.mem_filter, hs₁, Finset.mem_filter] at hρ
    exact hρ.1.2
  have hN : ∀ t : ℝ, 2 ≤ t → ((S'.filter (fun ρ => |ρ.im| ≤ t)).sum (fun ρ => (m ρ : ℝ)))
      ≤ K' * t * Real.log t := by
    intro t ht
    obtain ⟨hfinB, hwc⟩ := hcount t ht
    have hlogt : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
    have hsub : ∀ ρ ∈ S'.filter (fun ρ => |ρ.im| ≤ t),
        ρ ∈ zerosIn h (band (-1) σ₀ t) := by
      intro ρ hρ
      rw [Finset.mem_filter] at hρ
      obtain ⟨hρS', hρt⟩ := hρ
      have hρH := hS'H ρ hρS'
      have hDρ := hS'D ρ hρS'
      obtain ⟨h1, h2⟩ := hre ρ hDρ
      refine ⟨⟨by linarith, by linarith, by linarith, hρt⟩, ?_⟩
      exact eq_zero_of_divisor_ne_zero hfa (mem_of_divisor_ne_zero hDρ) hDρ
    have hmult : ∀ ρ ∈ S'.filter (fun ρ => |ρ.im| ≤ t),
        (m ρ : ℝ) = (mult h ρ : ℝ) := by
      intro ρ hρ
      rw [Finset.mem_filter] at hρ
      have hDρ := hS'D ρ hρ.1
      have := mult_eq_divisor hfa (mem_of_divisor_ne_zero hDρ)
      rw [← hD] at this
      have h2 : ((m ρ : ℕ) : ℤ) = D ρ := by simp only [hm]; exact Int.toNat_of_nonneg (hD0 ρ)
      have h3 : ((m ρ : ℕ) : ℤ) = (mult h ρ : ℤ) := by rw [h2, this]
      exact_mod_cast h3
    calc ((S'.filter (fun ρ => |ρ.im| ≤ t)).sum (fun ρ => (m ρ : ℝ)))
        = (S'.filter (fun ρ => |ρ.im| ≤ t)).sum (fun ρ => (mult h ρ : ℝ)) :=
          Finset.sum_congr rfl hmult
      _ ≤ wcount h (band (-1) σ₀ t) := by
          rw [wcount, finsum_mem_eq_finite_toFinset_sum _ hfinB]
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => Nat.cast_nonneg _
          intro ρ hρ
          rw [Set.Finite.mem_toFinset]
          exact hsub ρ hρ
      _ ≤ K * t * Real.log t := hwc
      _ ≤ K' * t * Real.log t := by
          have : 0 ≤ t * Real.log t := mul_nonneg (by linarith) hlogt
          nlinarith [le_max_left K 0]
  have hhigh : ∑ u ∈ S', ‖(D u : ℂ) * φ u‖ ≤ B * (2 * K' * (1 + Real.log 2) / 2) := by
    have h1 : ∀ ρ ∈ S', ‖(D ρ : ℂ) * φ ρ‖ ≤ B * ((m ρ : ℝ) / ρ.im ^ 2) := by
      intro ρ hρ
      have hρH := hS'H ρ hρ
      have hb : 0 < ρ.im ^ 2 := by
        have : ρ.im ≠ 0 := fun h0 => by rw [h0, abs_zero] at hρH; linarith
        positivity
      obtain ⟨hr1, hr2⟩ := hre ρ (hS'D ρ hρ)
      have hφ : ‖φ ρ‖ ≤ B / ρ.im ^ 2 := by
        rw [le_div_iff₀ hb]; exact hB ρ hr1 hr2 (by linarith)
      rw [← hmD, norm_mul, Complex.norm_natCast]
      calc (m ρ : ℝ) * ‖φ ρ‖ ≤ (m ρ : ℝ) * (B / ρ.im ^ 2) :=
            mul_le_mul_of_nonneg_left hφ (by positivity)
        _ = B * ((m ρ : ℝ) / ρ.im ^ 2) := by ring
    calc ∑ ρ ∈ S', ‖(D ρ : ℂ) * φ ρ‖ ≤ ∑ ρ ∈ S', B * ((m ρ : ℝ) / ρ.im ^ 2) :=
          Finset.sum_le_sum h1
      _ = B * ∑ ρ ∈ S', (m ρ : ℝ) / ρ.im ^ 2 := by rw [Finset.mul_sum]
      _ ≤ B * (2 * K' * (1 + Real.log 2) / 2) :=
          mul_le_mul_of_nonneg_left
            (sum_div_im_sq_le S' m (by norm_num) (le_max_right _ _) hS'H hN) hB0
  linarith [hlow, hhigh]

/-- The zero sum is summable (as a series in `ℂ`). -/
theorem summable_divisor_mul (h : ℂ → ℂ) (hh : ∀ z, AnalyticAt ℂ h z) {σ σ₀ K : ℝ}
    (hσ1 : 1 < σ) (hσ2 : σ < 2) (hσ₀ : 2 ≤ σ₀)
    (hcount : ∀ T : ℝ, 2 ≤ T → (zerosIn h (band (-1) σ₀ T)).Finite ∧
      wcount h (band (-1) σ₀ T) ≤ K * T * Real.log T)
    (φ : ℂ → ℂ)
    (hdec : ∃ B : ℝ, ∀ s : ℂ, 1 - σ ≤ s.re → s.re ≤ σ → 1 ≤ |s.im| → ‖φ s‖ * s.im ^ 2 ≤ B) :
    Summable (fun u : ℂ => ((MeromorphicOn.divisor h (strip σ)) u : ℂ) * φ u) :=
  (summable_norm_divisor_mul h hh hσ1 hσ2 hσ₀ hcount φ hdec).of_norm

/-- **The rectangle sums converge to the full zero sum.** If `u ↦ D(u) φ(u)` is absolutely
summable and the sums over the rectangles `[1 - σ, σ] × [-T_j, T_j]` with `T_j ≥ j` converge to
`L`, then `∑' u, D(u) φ(u) = L` (Tannery's theorem). -/
theorem tsum_divisor_mul_eq_of_tendsto_rect (h : ℂ → ℂ) (hh : ∀ z, AnalyticAt ℂ h z) {σ : ℝ}
    (hσ1 : 1 < σ) (φ : ℂ → ℂ)
    (hsum : Summable (fun u : ℂ => ‖((MeromorphicOn.divisor h (strip σ)) u : ℂ) * φ u‖))
    (T : ℕ → ℝ) (hT : ∀ j : ℕ, (j : ℝ) ≤ T j) {L : ℂ}
    (hlim : Tendsto (fun j : ℕ => ∑ᶠ u, ((MeromorphicOn.divisor h
        (closedRect ⟨1 - σ, -(T j)⟩ ⟨σ, T j⟩)) u : ℂ) * φ u) atTop (𝓝 L)) :
    ∑' u, ((MeromorphicOn.divisor h (strip σ)) u : ℂ) * φ u = L := by
  classical
  set U : Set ℂ := strip σ with hU
  set D := MeromorphicOn.divisor h U with hD
  have hfaU : AnalyticOnNhd ℂ h U := fun s _ => hh s
  set f : ℕ → ℂ → ℂ := fun j u => if |u.im| ≤ T j then (D u : ℂ) * φ u else 0 with hf
  have hpt : ∀ u, Tendsto (fun j => f j u) atTop (𝓝 ((D u : ℂ) * φ u)) := by
    intro u
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈|u.im|⌉₊] with j hj
    have hle : |u.im| ≤ T j := (Nat.le_ceil _).trans ((Nat.cast_le.mpr hj).trans (hT j))
    simp only [hf, if_pos hle]
  have hbd : ∀ᶠ j in atTop, ∀ u, ‖f j u‖ ≤ ‖(D u : ℂ) * φ u‖ := by
    refine Eventually.of_forall fun j u => ?_
    simp only [hf]
    split_ifs
    · exact le_rfl
    · rw [norm_zero]; exact norm_nonneg _
  have hconv : Tendsto (fun j => ∑' u, f j u) atTop (𝓝 (∑' u, (D u : ℂ) * φ u)) :=
    tendsto_tsum_of_dominated_convergence hsum hpt hbd
  have heq : ∀ j, (∑' u, f j u)
      = ∑ᶠ u, ((MeromorphicOn.divisor h (closedRect ⟨1 - σ, -(T j)⟩ ⟨σ, T j⟩)) u : ℂ) * φ u := by
    intro j
    set Kj : Set ℂ := closedRect ⟨1 - σ, -(T j)⟩ ⟨σ, T j⟩ with hKj
    set Dj := MeromorphicOn.divisor h Kj with hDj
    have hfa : AnalyticOnNhd ℂ h Kj := fun s _ => hh s
    have hT0 : 0 ≤ T j := (Nat.cast_nonneg j).trans (hT j)
    have hmemK : ∀ u, u ∈ Kj ↔ (1 - σ ≤ u.re ∧ u.re ≤ σ) ∧ |u.im| ≤ T j := fun u =>
      mem_closedRect_strip_iff (by linarith) hT0 u
    have hptwise : ∀ u, f j u = (Dj u : ℂ) * φ u := by
      intro u
      simp only [hf]
      by_cases hu : u ∈ Kj
      · obtain ⟨huU, him⟩ := (hmemK u).mp hu
        rw [if_pos him, hD, hDj, MeromorphicOn.divisor_apply hfaU.meromorphicOn huU,
          MeromorphicOn.divisor_apply hfa.meromorphicOn hu]
      · have hDju : Dj u = 0 := by
          by_contra hne
          exact hu (mem_of_divisor_ne_zero hne)
        rw [hDju, Int.cast_zero, zero_mul]
        split_ifs with him
        · have hDu : D u = 0 := by
            by_contra hne
            exact hu ((hmemK u).mpr ⟨mem_of_divisor_ne_zero hne, him⟩)
          rw [hDu, Int.cast_zero, zero_mul]
        · rfl
    rw [show f j = fun u => (Dj u : ℂ) * φ u from funext hptwise]
    refine tsum_eq_finsum ?_
    refine (Dj.finiteSupport (isCompact_closedRect _ _)).subset fun u hu => ?_
    rw [Function.mem_support] at hu ⊢
    intro h0
    apply hu
    rw [h0]
    simp
  rw [show (fun j => ∑' u, f j u) = fun j => ∑ᶠ u, ((MeromorphicOn.divisor h
      (closedRect ⟨1 - σ, -(T j)⟩ ⟨σ, T j⟩)) u : ℂ) * φ u from funext heq] at hconv
  exact tendsto_nhds_unique hconv hlim

end RankinSelbergDelta.RankinSelberg.ZeroSum

namespace RankinSelbergDelta.RankinSelberg

open UpperHalfPlane MeasureTheory Filter Topology RankinSelbergDelta.ArgPrinciple
open scoped FourierTransform ContDiff

variable {F : Type*} [FunLike F ℍ ℂ] (k : ℤ)
  [cf : CuspFormClass F (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma 1)) k]

/-- **The zero sum converges absolutely.** Under the decay hypothesis `hdec` of
`explicitFormula_Gfull`, the zero sum `u ↦ m_u ĝ(u)` over the divisor of the entire `(s − 1)G` on
the strip `1 − σ ≤ Re u ≤ σ` is absolutely summable. -/
theorem summable_norm_zeroSum_Gfull (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k)
    {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ < 2) (g : ℝ → ℂ)
    (hdec : ∃ B : ℝ, ∀ s : ℂ, 1 - σ ≤ s.re → s.re ≤ σ → 1 ≤ |s.im| → ‖ghat g s‖ * s.im ^ 2 ≤ B) :
    Summable (fun u : ℂ =>
      ‖((MeromorphicOn.divisor (rsHent k f) (ZeroSum.strip σ)) u : ℂ) * ghat g u‖) := by
  obtain ⟨σ₀, hσ₀, K, hK⟩ := exists_wcount_zeros_rsHent_le_mul_log k f hk hf
  exact ZeroSum.summable_norm_divisor_mul (rsHent k f) (analyticAt_rsHent k f hk) hσ1 hσ2 hσ₀ hK
    (ghat g) hdec

/-- **Summability of the zero sum.** The zero sum is summable. -/
theorem summable_zeroSum_Gfull (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k)
    {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ < 2) (g : ℝ → ℂ)
    (hdec : ∃ B : ℝ, ∀ s : ℂ, 1 - σ ≤ s.re → s.re ≤ σ → 1 ≤ |s.im| → ‖ghat g s‖ * s.im ^ 2 ≤ B) :
    Summable (fun u : ℂ =>
      ((MeromorphicOn.divisor (rsHent k f) (ZeroSum.strip σ)) u : ℂ) * ghat g u) :=
  (summable_norm_zeroSum_Gfull k f hk hf hσ1 hσ2 g hdec).of_norm

/-- **The explicit formula as a series over ALL zeros.** Under the
hypotheses of `explicitFormula_Gfull`, `∑' u, m_u ĝ(u)` (over the divisor of the entire `(s − 1)G`
on the strip `1 − σ ≤ Re u ≤ σ`) equals
`ĝ(1) − ∑_n Λ_G(n) g(log n) − ∑_n Λ_G(n) g(−log n)/n − (1/2π) ∫ (archimedean kernel)`. -/
theorem explicitFormula_Gfull_tsum (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k)
    {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ < 2) (g : ℝ → ℂ) (hgc : Continuous g)
    (hga : ∀ s : ℂ, AnalyticAt ℂ (ghat g) s)
    (hg : Integrable (fun x : ℝ => g x * Complex.exp (σ * x)))
    (hF : Integrable (𝓕 (fun x : ℝ => g x * Complex.exp (σ * x))))
    (hg' : Integrable (fun x : ℝ => g (-x) * Complex.exp (-(x : ℂ)) * Complex.exp (σ * x)))
    (hF' : Integrable (𝓕 (fun x : ℝ => g (-x) * Complex.exp (-(x : ℂ)) * Complex.exp (σ * x))))
    (hdec : ∃ B : ℝ, ∀ s : ℂ, 1 - σ ≤ s.re → s.re ≤ σ → 1 ≤ |s.im| → ‖ghat g s‖ * s.im ^ 2 ≤ B)
    (hArch : Integrable (fun t : ℝ =>
      (logDeriv (rsPre k) ((σ : ℂ) - t * Complex.I)
          + logDeriv (rsPre k) (((1 - σ : ℝ) : ℂ) + t * Complex.I))
        * ghat g (((1 - σ : ℝ) : ℂ) + t * Complex.I))) :
    ∑' u, ((MeromorphicOn.divisor (rsHent k f) (ZeroSum.strip σ)) u : ℂ) * ghat g u
      = ghat g 1
        - ∑' n, (if 2 ≤ n then (rsVonMangoldt (rsCoeff f) k n : ℂ) * g (Real.log n) else 0)
        - ∑' n, (if 2 ≤ n then (rsVonMangoldt (rsCoeff f) k n : ℂ) * (g (-(Real.log n)) / n)
            else 0)
        - (1 / (2 * Real.pi)) * ∫ t : ℝ, (logDeriv (rsPre k) ((σ : ℂ) - t * Complex.I)
            + logDeriv (rsPre k) (((1 - σ : ℝ) : ℂ) + t * Complex.I))
            * ghat g (((1 - σ : ℝ) : ℂ) + t * Complex.I) := by
  obtain ⟨T, hT, hlim⟩ := explicitFormula_Gfull k f hk hf hσ1 hσ2 g hgc hga hg hF hg' hF' hdec hArch
  exact ZeroSum.tsum_divisor_mul_eq_of_tendsto_rect (rsHent k f) (analyticAt_rsHent k f hk) hσ1
    (ghat g) (summable_norm_zeroSum_Gfull k f hk hf hσ1 hσ2 g hdec) T (fun j => (hT j).1) hlim

/-- **For `g ∈ C_c^∞`:** the zero sum is summable. -/
theorem summable_zeroSum_Gfull_of_smooth (f : F) (hk : 0 < k)
    (hf : IsHeckeEigenCoeffs (rsCoeff f) k) {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ < 2) (g : ℝ → ℂ)
    (hg : ContDiff ℝ ∞ g) (hgs : HasCompactSupport g) :
    Summable (fun u : ℂ =>
      ((MeromorphicOn.divisor (rsHent k f) (ZeroSum.strip σ)) u : ℂ) * ghat g u) :=
  summable_zeroSum_Gfull k f hk hf hσ1 hσ2 g (exists_norm_ghat_mul_im_sq_le hg hgs hσ1 hσ2)

/-- **For `g ∈ C_c^∞`: the explicit formula as a series over all zeros**, with only
smoothness and compact support assumed on the test function. -/
theorem explicitFormula_Gfull_tsum_of_smooth (f : F) (hk : 0 < k)
    (hf : IsHeckeEigenCoeffs (rsCoeff f) k) {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ < 2) (g : ℝ → ℂ)
    (hg : ContDiff ℝ ∞ g) (hgs : HasCompactSupport g) :
    ∑' u, ((MeromorphicOn.divisor (rsHent k f) (ZeroSum.strip σ)) u : ℂ) * ghat g u
      = ghat g 1
        - ∑' n, (if 2 ≤ n then (rsVonMangoldt (rsCoeff f) k n : ℂ) * g (Real.log n) else 0)
        - ∑' n, (if 2 ≤ n then (rsVonMangoldt (rsCoeff f) k n : ℂ) * (g (-(Real.log n)) / n)
            else 0)
        - (1 / (2 * Real.pi)) * ∫ t : ℝ, (logDeriv (rsPre k) ((σ : ℂ) - t * Complex.I)
            + logDeriv (rsPre k) (((1 - σ : ℝ) : ℂ) + t * Complex.I))
            * ghat g (((1 - σ : ℝ) : ℂ) + t * Complex.I) := by
  have hgc : Continuous g := hg.continuous
  have hneg_s : HasCompactSupport (fun x : ℝ => g (-x)) :=
    hgs.comp_homeomorph (Homeomorph.neg ℝ)
  have hneg_c : ContDiff ℝ ∞ (fun x : ℝ => g (-x)) := hg.comp contDiff_neg
  have hexp_c : ContDiff ℝ ∞ (fun x : ℝ => Complex.exp (-(x : ℂ))) :=
    Complex.contDiff_exp.comp Complex.ofRealCLM.contDiff.neg
  have hrev_c : ContDiff ℝ ∞ (fun x : ℝ => g (-x) * Complex.exp (-(x : ℂ))) := hneg_c.mul hexp_c
  have hrev_s : HasCompactSupport (fun x : ℝ => g (-x) * Complex.exp (-(x : ℂ))) :=
    hneg_s.mul_right
  refine explicitFormula_Gfull_tsum k f hk hf hσ1 hσ2 g hgc (analyticAt_ghat hgc hgs)
    (integrable_mul_cexp hgc hgs σ)
    (integrable_fourierIntegral_of_smooth (hg.mul (contDiff_cexp_mul σ)) hgs.mul_right)
    ((hrev_c.continuous.mul (continuous_cexp_mul σ)).integrable_of_hasCompactSupport
      hrev_s.mul_right)
    (integrable_fourierIntegral_of_smooth (hrev_c.mul (contDiff_cexp_mul σ)) hrev_s.mul_right)
    (exists_norm_ghat_mul_im_sq_le hg hgs hσ1 hσ2)
    (integrable_arch_kernel k hk hσ1 hσ2 g (continuous_ghat hgc hgs) fun N => ?_)
  obtain ⟨B, hB⟩ := exists_norm_ghat_mul_one_add_abs_im_pow_le hg hgs N
  refine ⟨B, fun t => ?_⟩
  have hre : (((1 - σ : ℝ) : ℂ) + t * Complex.I).re = 1 - σ := by simp
  have him : (((1 - σ : ℝ) : ℂ) + t * Complex.I).im = t := by simp
  have := hB (((1 - σ : ℝ) : ℂ) + t * Complex.I)
    (by rw [hre]; exact abs_le.mpr ⟨by linarith, by linarith⟩)
  rw [him] at this
  exact this

/-- Non-vacuity witness for the new hypotheses of `explicitFormula_Gfull_tsum_of_smooth` and
`summable_zeroSum_Gfull_of_smooth`: `σ = 3/2` and a `ContDiffBump` with `g 0 = 1`. -/
theorem explicitFormula_Gfull_tsum_hyps_satisfiable :
    ∃ (σ : ℝ) (g : ℝ → ℂ), 1 < σ ∧ σ < 2 ∧ ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ g 0 = 1 :=
  explicitFormula_Gfull_of_smooth_hyps_satisfiable

end RankinSelbergDelta.RankinSelberg
