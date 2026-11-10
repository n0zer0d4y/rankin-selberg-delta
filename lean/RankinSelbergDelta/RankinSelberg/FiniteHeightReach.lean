import RankinSelbergDelta.RankinSelberg.ZeroCountMultiplicity
import RankinSelbergDelta.Analysis.PaleyWienerReach

/-!
# The height reached by a compactly supported Weil form

For a test function supported in `[−L, L]`, the zero sum of the Weil form of `G` is determined up
to a tail that depends only on the zeros above a height `e^{O(L)}`
(`exists_wcount_zeros_rsHent_le_mul_log`, `weilForm_Gfull_reach`).
-/

open MeasureTheory Filter
open scoped NNReal MatrixGroups Pointwise

noncomputable section

namespace RankinSelbergDelta.RankinSelberg

open Complex UpperHalfPlane MeasureTheory Set Filter RankinSelbergDelta.Eisenstein RankinSelbergDelta.ArgPrinciple
open scoped Real Topology Modular FourierTransform ComplexConjugate

variable {F : Type*} [FunLike F ℍ ℂ] (k : ℤ)
  [cf : CuspFormClass F (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma 1)) k]

/-- A nonzero divisor value of an analytic function is a zero. -/
lemma eq_zero_of_divisor_ne_zero {f : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U) {u : ℂ}
    (hu : u ∈ U) (hD : MeromorphicOn.divisor f U u ≠ 0) : f u = 0 := by
  rw [MeromorphicOn.divisor_apply hf.meromorphicOn hu, (hf u hu).meromorphicOrderAt_eq] at hD
  by_contra h
  apply hD
  rw [analyticOrderAt_eq_zero.mpr (Or.inr h)]
  rfl

include cf in
/-- **`N(T) = O(T log T)` WITH MULTIPLICITY for the entire `(s − 1)G`**, on the band
`−1 ≤ Re s ≤ σ₀`, `1 ≤ |Im s| ≤ T`; the band's zero set is finite. -/
theorem exists_wcount_zeros_rsHent_le_mul_log (f : F) (hk : 0 < k)
    (hf : IsHeckeEigenCoeffs (rsCoeff f) k) :
    ∃ σ₀ : ℝ, 2 ≤ σ₀ ∧ ∃ K : ℝ, ∀ T : ℝ, 2 ≤ T →
      (RankinSelbergDelta.ZeroCount.zerosIn (rsHent k f) (RankinSelbergDelta.ZeroCount.band (-1) σ₀ T)).Finite ∧
      RankinSelbergDelta.ZeroCount.wcount (rsHent k f) (RankinSelbergDelta.ZeroCount.band (-1) σ₀ T)
        ≤ K * T * Real.log T := by
  obtain ⟨σ₀, hσ₀, hlow⟩ := exists_norm_Gfull_ge k f hk hf
  set R : ℝ := 2 * (σ₀ - (-1)) + 1 with hR
  obtain ⟨C, N, hC, hgrow⟩ := exists_norm_Gfull_le_halfStrip k f hk (⌈σ₀⌉₊ + 3)
  set B₀ : ℝ := 3 * σ₀ + 4 with hB₀
  have hB₀1 : 1 ≤ B₀ := by rw [hB₀]; linarith
  refine ⟨σ₀, hσ₀, ?_⟩
  refine RankinSelbergDelta.ZeroCount.exists_wcount_band_le_mul_log (a := -1) (σ₀ := σ₀) (C := C * B₀)
    (c := 3 / 8) (N := N + 1) (by linarith) (by positivity) (by norm_num)
    (fun z _ => analyticAt_rsHent k f hk z) ?_ ?_
  · intro z hz1 hz2 hzim
    have hz0 : z ≠ 0 := by
      intro h; rw [h, Complex.zero_im, abs_zero] at hzim; linarith
    have hz1' : z ≠ 1 := by
      intro h; rw [h, Complex.one_im, abs_zero] at hzim; linarith
    rw [rsHent_eq k f hk hz0 hz1', norm_mul]
    have hG := hgrow z (by
      have := Nat.le_ceil σ₀
      push_cast
      linarith) hzim
    have hs1 : ‖z - 1‖ ≤ B₀ * (1 + |z.im|) := by
      have h1 := Complex.norm_le_abs_re_add_abs_im (z - 1)
      rw [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero] at h1
      have h2 : |z.re - 1| ≤ B₀ := by
        rw [abs_le, hB₀]; constructor <;> linarith
      nlinarith [abs_nonneg z.im]
    calc ‖z - 1‖ * ‖Gfull k f z‖ ≤ (B₀ * (1 + |z.im|)) * (C * (1 + |z.im|) ^ N) :=
          mul_le_mul hs1 hG (norm_nonneg _) (by positivity)
      _ = C * B₀ * (1 + |z.im|) ^ (N + 1) := by ring
  · intro t
    have hpt : RankinSelbergDelta.ZeroCount.pt σ₀ t = (σ₀ : ℂ) + Complex.I * t := by
      apply Complex.ext <;> simp [RankinSelbergDelta.ZeroCount.pt]
    rw [hpt]
    have hz0 : (σ₀ : ℂ) + Complex.I * t ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hz1 : (σ₀ : ℂ) + Complex.I * t ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    rw [rsHent_eq k f hk hz0 hz1, norm_mul]
    have h1 : 1 ≤ ‖(σ₀ : ℂ) + Complex.I * t - 1‖ := by
      have := Complex.abs_re_le_norm ((σ₀ : ℂ) + Complex.I * t - 1)
      have hre : ((σ₀ : ℂ) + Complex.I * t - 1).re = σ₀ - 1 := by simp
      rw [hre, abs_of_pos (by linarith)] at this
      linarith
    have h2 := hlow t
    calc (3 / 8 : ℝ) = 1 * (3 / 8) := (one_mul _).symm
      _ ≤ ‖(σ₀ : ℂ) + Complex.I * t - 1‖ * ‖Gfull k f ((σ₀ : ℂ) + Complex.I * t)‖ :=
          mul_le_mul h1 h2 (by norm_num) (norm_nonneg _)

include cf in
/-- **The finite-height reach of compact-support Weil positivity for `G`**.
With the Paley–Wiener bound `‖ĝ(s)‖ ≤ e^{|Re s| L} M` (`norm_ghat_le`, a hypothesis here)
and its second-derivative form `‖ĝ(s)‖ (Im s)² ≤ e^{|Re s| L} M₂`: there is `K ≥ 0` (depending on
`f`) such that, whenever every zero of the continuation of height `≤ H` lies on `Re s = 1/2`
(`H ≥ 2`), the arithmetic side of the self-dual Weil form has real part
`≥ −e^{2σL} M M₂ · 2K (1 + log H)/H`. Zeros of height `> H` are invisible to a support-`L` test
function up to this error, which is small only when `e^{2σL} ≪ H / log H`: compact support
resolves zeros only up to height `e^{O(L)}`. -/
theorem weilForm_Gfull_reach (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k) {σ : ℝ}
    (hσ1 : 1 < σ) (hσ2 : σ < 2) {L M M₂ : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M) (hM₂ : 0 ≤ M₂) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (g : ℝ → ℂ) (hc : Continuous g) (hs : HasCompactSupport g)
      (hga : ∀ s : ℂ, AnalyticAt ℂ (ghat (WeilForm.selfDual g)) s)
      (hg : Integrable (fun x : ℝ => WeilForm.selfDual g x * Complex.exp (σ * x)))
      (hF : Integrable (𝓕 (fun x : ℝ => WeilForm.selfDual g x * Complex.exp (σ * x))))
      (hg' : Integrable (fun x : ℝ => WeilForm.selfDual g (-x) * Complex.exp (-(x : ℂ))
        * Complex.exp (σ * x)))
      (hF' : Integrable (𝓕 (fun x : ℝ => WeilForm.selfDual g (-x) * Complex.exp (-(x : ℂ))
        * Complex.exp (σ * x))))
      (hdec : ∃ B : ℝ, ∀ s : ℂ, 1 - σ ≤ s.re → s.re ≤ σ → 1 ≤ |s.im| →
        ‖ghat (WeilForm.selfDual g) s‖ * s.im ^ 2 ≤ B)
      (hArch : Integrable (fun t : ℝ =>
        (logDeriv (rsPre k) ((σ : ℂ) - t * Complex.I)
            + logDeriv (rsPre k) (((1 - σ : ℝ) : ℂ) + t * Complex.I))
          * ghat (WeilForm.selfDual g) (((1 - σ : ℝ) : ℂ) + t * Complex.I)))
      (hPW : ∀ s : ℂ, ‖ghat g s‖ ≤ Real.exp (|s.re| * L) * M)
      (hPW₂ : ∀ s : ℂ, ‖ghat g s‖ * s.im ^ 2 ≤ Real.exp (|s.re| * L) * M₂)
      (H : ℝ) (hH : 2 ≤ H)
      (hlineH : ∀ z w u : ℂ, (MeromorphicOn.divisor (rsHent k f) (closedRect z w)) u ≠ 0 →
        |u.im| ≤ H → u.re = 1 / 2),
      -(Real.exp (2 * σ * L) * (M * M₂)) * (2 * K * (1 + Real.log H) / H)
        ≤ (ghat g 1 * conj (ghat g 0)
          - ∑' n, (if 2 ≤ n then (rsVonMangoldt (rsCoeff f) k n : ℂ) * WeilForm.selfDual g (Real.log n)
              else 0)
          - ∑' n, (if 2 ≤ n then (rsVonMangoldt (rsCoeff f) k n : ℂ)
              * (WeilForm.selfDual g (-(Real.log n)) / n) else 0)
          - (1 / (2 * Real.pi)) * ∫ t : ℝ, (logDeriv (rsPre k) ((σ : ℂ) - t * Complex.I)
              + logDeriv (rsPre k) (((1 - σ : ℝ) : ℂ) + t * Complex.I))
              * ghat (WeilForm.selfDual g) (((1 - σ : ℝ) : ℂ) + t * Complex.I)).re := by
  classical
  obtain ⟨σ₀, hσ₀, K₀, hK₀⟩ := exists_wcount_zeros_rsHent_le_mul_log k f hk hf
  refine ⟨max K₀ 0, le_max_right _ _, ?_⟩
  intro g hc hs hga hg hF hg' hF' hdec hArch hPW hPW₂ H hH hlineH
  have hH1 : 1 ≤ H := by linarith
  have hhc : Continuous (WeilForm.selfDual g) := WeilForm.continuous_selfDual g hc hs
  obtain ⟨T, hT, hlim⟩ := explicitFormula_Gfull k f hk hf hσ1 hσ2 (WeilForm.selfDual g) hhc hga
    hg hF hg' hF' hdec hArch
  have hpt : ∀ u : ℂ, ghat (WeilForm.selfDual g) u = ghat g u * conj (ghat g (1 - conj u)) :=
    fun u => WeilForm.ghat_selfDual_eq g hc hs u
  have h1 : ghat (WeilForm.selfDual g) 1 = ghat g 1 * conj (ghat g 0) := by
    rw [hpt]; simp
  rw [h1] at hlim
  -- the real part of every finsum is at least `−ε`
  have hreal : ∀ j : ℕ,
      -(Real.exp (2 * σ * L) * (M * M₂)) * (2 * max K₀ 0 * (1 + Real.log H) / H) ≤
      (∑ᶠ u, ((MeromorphicOn.divisor (rsHent k f) (closedRect ⟨1 - σ, -(T j)⟩ ⟨σ, T j⟩)) u : ℂ)
        * ghat (WeilForm.selfDual g) u).re := by
    intro j
    set Kj : Set ℂ := closedRect ⟨1 - σ, -(T j)⟩ ⟨σ, T j⟩ with hKj
    set D := MeromorphicOn.divisor (rsHent k f) Kj with hD
    have hfa : AnalyticOnNhd ℂ (rsHent k f) Kj := fun s _ => analyticAt_rsHent k f hk s
    have hD0 : ∀ u, 0 ≤ D u := fun u => by
      have := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfa u
      simpa using this
    have hDfin : (Function.support D).Finite :=
      (MeromorphicOn.divisor (rsHent k f) Kj).finiteSupport (isCompact_closedRect _ _)
    set S : Finset ℂ := hDfin.toFinset with hS
    have hmemS : ∀ u, u ∈ S ↔ D u ≠ 0 := fun u => by
      rw [hS, Set.Finite.mem_toFinset, Function.mem_support]
    have hre_rect : ∀ u, D u ≠ 0 → 1 - σ ≤ u.re ∧ u.re ≤ σ := by
      intro u hu
      have huK : u ∈ Kj := D.supportWithinDomain (Function.mem_support.mpr hu)
      rw [hKj, closedRect, Complex.mem_reProdIm, Set.uIcc_of_le (by show 1 - σ ≤ σ; linarith)] at huK
      exact ⟨huK.1.1, huK.1.2⟩
    -- the finsum as a finite sum over `S`
    have hsum : (∑ᶠ u, (D u : ℂ) * ghat (WeilForm.selfDual g) u)
        = ∑ u ∈ S, (D u : ℂ) * ghat (WeilForm.selfDual g) u := by
      refine finsum_eq_sum_of_support_subset _ fun u hu => ?_
      rw [Function.mem_support] at hu
      rw [hS, Set.Finite.coe_toFinset]
      intro h0; apply hu; rw [h0]; simp
    rw [hsum, ← Finset.sum_filter_add_sum_filter_not S (fun u => |u.im| ≤ H)]
    -- the on-line part is a nonnegative real
    set D' : ℂ → ℤ := fun u => if |u.im| ≤ H then D u else 0 with hD'
    have hD'0 : ∀ u, 0 ≤ D' u := fun u => by
      simp only [hD']; split_ifs
      · exact hD0 u
      · exact le_rfl
    have hD'fin : (Function.support D').Finite := by
      refine hDfin.subset fun u hu => ?_
      rw [Function.mem_support] at hu ⊢
      simp only [hD'] at hu
      split_ifs at hu with h
      · exact hu
      · exact absurd rfl hu
    have hD'line : ∀ u, D' u ≠ 0 → u.re = 1 / 2 := by
      intro u hu
      simp only [hD'] at hu
      split_ifs at hu with h
      · exact hlineH _ _ u hu h
      · exact absurd rfl hu
    obtain ⟨heq, hnn⟩ := WeilForm.finsum_divisor_ghat_selfDual_nonneg g hc hs D' hD'0 hD'fin hD'line
    have hsupp' : Function.support (fun u => (D' u : ℂ) * ghat (WeilForm.selfDual g) u)
        ⊆ (S : Set ℂ) := by
      intro u hu
      rw [Function.mem_support] at hu
      have hDu : D u ≠ 0 := by
        intro h0
        apply hu
        have hD'u : D' u = 0 := by simp only [hD']; split_ifs <;> simp [h0]
        rw [hD'u]; simp
      rw [hS, Set.Finite.coe_toFinset]
      exact hDu
    have hon' : ∀ u ∈ S, (if |u.im| ≤ H then (D u : ℂ) * ghat (WeilForm.selfDual g) u else 0)
        = (D' u : ℂ) * ghat (WeilForm.selfDual g) u := by
      intro u _
      simp only [hD']; split_ifs <;> simp
    have hon : (∑ u ∈ S.filter (fun u => |u.im| ≤ H), (D u : ℂ) * ghat (WeilForm.selfDual g) u)
        = ((∑ᶠ u, (D' u : ℝ) * ‖ghat g u‖ ^ 2 : ℝ) : ℂ) := by
      rw [Finset.sum_filter, Finset.sum_congr rfl hon', ← finsum_eq_sum_of_support_subset _ hsupp']
      exact heq
    -- the tail
    set S' : Finset ℂ := S.filter (fun u => ¬ |u.im| ≤ H) with hS'
    set m : ℂ → ℕ := fun u => (D u).toNat with hm
    have hmD : ∀ u, ((m u : ℕ) : ℂ) = (D u : ℂ) := fun u => by
      simp only [hm]
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (hD0 u)]
    have htail_eq : (∑ u ∈ S', (D u : ℂ) * ghat (WeilForm.selfDual g) u)
        = ∑ u ∈ S', (m u : ℂ) * (ghat g u * conj (ghat g (1 - conj u))) := by
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [hmD, hpt]
    have hS'H : ∀ ρ ∈ S', H < |ρ.im| := by
      intro ρ hρ
      rw [hS', Finset.mem_filter] at hρ
      exact lt_of_not_ge hρ.2
    have hS're : ∀ ρ ∈ S', |ρ.re| ≤ σ ∧ |1 - ρ.re| ≤ σ := by
      intro ρ hρ
      rw [hS', Finset.mem_filter, hmemS] at hρ
      obtain ⟨h1, h2⟩ := hre_rect ρ hρ.1
      constructor <;> rw [abs_le] <;> constructor <;> linarith
    have hN : ∀ t : ℝ, H ≤ t → ((S'.filter (fun ρ => |ρ.im| ≤ t)).sum (fun ρ => (m ρ : ℝ)))
        ≤ max K₀ 0 * t * Real.log t := by
      intro t ht
      have ht2 : 2 ≤ t := by linarith
      obtain ⟨hfinB, hwc⟩ := hK₀ t ht2
      have hlogt : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
      -- every element of the filtered set is a zero of `rsHent` in the band
      have hsub : ∀ ρ ∈ S'.filter (fun ρ => |ρ.im| ≤ t),
          ρ ∈ RankinSelbergDelta.ZeroCount.zerosIn (rsHent k f) (RankinSelbergDelta.ZeroCount.band (-1) σ₀ t) := by
        intro ρ hρ
        rw [Finset.mem_filter] at hρ
        obtain ⟨hρS', hρt⟩ := hρ
        have hρH := hS'H ρ hρS'
        rw [hS', Finset.mem_filter, hmemS] at hρS'
        obtain ⟨h1, h2⟩ := hre_rect ρ hρS'.1
        refine ⟨⟨by linarith, by linarith, by linarith, hρt⟩, ?_⟩
        have huK : ρ ∈ Kj := D.supportWithinDomain (Function.mem_support.mpr hρS'.1)
        exact eq_zero_of_divisor_ne_zero hfa huK hρS'.1
      have hmult : ∀ ρ ∈ S'.filter (fun ρ => |ρ.im| ≤ t),
          (m ρ : ℝ) = (RankinSelbergDelta.ZeroCount.mult (rsHent k f) ρ : ℝ) := by
        intro ρ hρ
        rw [Finset.mem_filter, hS', Finset.mem_filter, hmemS] at hρ
        have huK : ρ ∈ Kj := D.supportWithinDomain (Function.mem_support.mpr hρ.1.1)
        have := RankinSelbergDelta.ZeroCount.mult_eq_divisor hfa huK
        rw [← hD] at this
        have h2 : ((m ρ : ℕ) : ℤ) = D ρ := by simp only [hm]; exact Int.toNat_of_nonneg (hD0 ρ)
        have h3 : ((m ρ : ℕ) : ℤ) = (RankinSelbergDelta.ZeroCount.mult (rsHent k f) ρ : ℤ) := by
          rw [h2, this]
        exact_mod_cast h3
      calc ((S'.filter (fun ρ => |ρ.im| ≤ t)).sum (fun ρ => (m ρ : ℝ)))
          = (S'.filter (fun ρ => |ρ.im| ≤ t)).sum
              (fun ρ => (RankinSelbergDelta.ZeroCount.mult (rsHent k f) ρ : ℝ)) :=
            Finset.sum_congr rfl hmult
        _ ≤ RankinSelbergDelta.ZeroCount.wcount (rsHent k f) (RankinSelbergDelta.ZeroCount.band (-1) σ₀ t) := by
            rw [RankinSelbergDelta.ZeroCount.wcount, finsum_mem_eq_finite_toFinset_sum _ hfinB]
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => Nat.cast_nonneg _
            intro ρ hρ
            rw [Set.Finite.mem_toFinset]
            exact hsub ρ hρ
        _ ≤ K₀ * t * Real.log t := hwc
        _ ≤ max K₀ 0 * t * Real.log t := by
            have : 0 ≤ t * Real.log t := mul_nonneg (by linarith) hlogt
            nlinarith [le_max_left K₀ 0]
    have htail := RankinSelbergDelta.Analysis.PaleyWiener.tail_weilForm_le S' m (ghat g) hH1
      (le_max_right _ _) hL (by linarith) hM hM₂ hS'H hS're hN hPW hPW₂
    rw [← htail_eq] at htail
    -- assemble
    rw [hon, Complex.add_re, Complex.ofReal_re]
    have hre_tail := Complex.abs_re_le_norm (∑ u ∈ S', (D u : ℂ) * ghat (WeilForm.selfDual g) u)
    rw [abs_le] at hre_tail
    calc -(Real.exp (2 * σ * L) * (M * M₂)) * (2 * max K₀ 0 * (1 + Real.log H) / H)
        = -((Real.exp (2 * σ * L) * (M * M₂)) * (2 * max K₀ 0 * (1 + Real.log H) / H)) := by ring
      _ ≤ -‖∑ u ∈ S', (D u : ℂ) * ghat (WeilForm.selfDual g) u‖ := neg_le_neg htail
      _ ≤ (∑ u ∈ S', (D u : ℂ) * ghat (WeilForm.selfDual g) u).re := hre_tail.1
      _ ≤ (∑ᶠ u, (D' u : ℝ) * ‖ghat g u‖ ^ 2)
          + (∑ u ∈ S', (D u : ℂ) * ghat (WeilForm.selfDual g) u).re := by
          have hnn' : 0 ≤ ∑ᶠ u, (D' u : ℝ) * ‖ghat g u‖ ^ 2 := hnn
          linarith
  -- pass to the limit
  have hlim' := (Complex.continuous_re.tendsto _).comp hlim
  refine ge_of_tendsto' hlim' fun j => ?_
  simp only [Function.comp]
  exact hreal j

end RankinSelbergDelta.RankinSelberg
