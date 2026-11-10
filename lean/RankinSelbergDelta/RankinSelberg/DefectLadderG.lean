import RankinSelbergDelta.RankinSelberg.ArchimedeanCriticalLine
import RankinSelbergDelta.RankinSelberg.DefectLadder

/-!
# The near-line lower bound for the Weil form of `G`

`weilForm_Gfull_ladder`: if `G` has no zero with `|Re ρ − 1/2| > ε`, the arithmetic side of the
self-dual Weil form of `G` is at least `−e^{2εL} K (M² + M M₂)`.
-/

open MeasureTheory Filter
open scoped NNReal MatrixGroups Pointwise

noncomputable section

namespace RankinSelbergDelta.RankinSelberg

open Complex UpperHalfPlane MeasureTheory Set Filter RankinSelbergDelta.Eisenstein RankinSelbergDelta.ArgPrinciple
open scoped Real Topology Modular FourierTransform ComplexConjugate

variable {F : Type*} [FunLike F ℍ ℂ] (k : ℤ)
  [cf : CuspFormClass F (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma 1)) k]

include cf in
/-- **The exponential-defect ladder for `G`.**
If every zero of `rsHent = (s − 1)·G` in the rectangles of the explicit formula satisfies
`|Re ρ − 1/2| ≤ ε` (the zero-free strips `Re s > 1/2 + ε` and `Re s < 1/2 − ε`; the second is the
functional-equation reflection of the first), then with the CENTERED Paley–Wiener bounds
`‖ĝ(s)‖ ≤ e^{|Re s − 1/2| L} M` and `‖ĝ(s)‖ (Im s)² ≤ e^{|Re s − 1/2| L} M₂` (`norm_ghat_le` applied to `g(x) e^{x/2}` and to its second derivative), the arithmetic side of the
self-dual Weil form of `G` has real part `≥ −e^{2εL} K (M² + M M₂)`, with `K` depending only on
`(k, f, σ)`: `K = N₂ + 2 max(K₀, 0)` where `N₂` is the number (with multiplicity) of zeros of
`rsHent` in `[1 − σ, σ] × [−2, 2]` and `K₀` the constant of `exists_wcount_zeros_rsHent_le_mul_log`.
The on-line zeros contribute a nonnegative real (`WeilForm.finsum_divisor_ghat_selfDual_nonneg`),
the off-line zeros of height `≤ 2` at most `e^{2εL} M² N₂`, and the off-line zeros of height `> 2`
at most `e^{2εL} M M₂ · 2K₀(1 + log 2)/2` by Abel summation (`sum_div_im_sq_le`). `ε = 1/2` is the
Euler-product strip; `ε = 0` is the Riemann hypothesis for `G`. -/
theorem weilForm_Gfull_ladder (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k) {σ : ℝ}
    (hσ1 : 1 < σ) (hσ2 : σ < 2) {ε L M M₂ : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M) (hM₂ : 0 ≤ M₂) :
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
      (hPW : ∀ s : ℂ, ‖ghat g s‖ ≤ Real.exp (|s.re - 1 / 2| * L) * M)
      (hPW₂ : ∀ s : ℂ, ‖ghat g s‖ * s.im ^ 2 ≤ Real.exp (|s.re - 1 / 2| * L) * M₂)
      (hstrip : ∀ z w u : ℂ, (MeromorphicOn.divisor (rsHent k f) (closedRect z w)) u ≠ 0 →
        |u.re - 1 / 2| ≤ ε),
      -(Real.exp (2 * ε * L) * K * (M * M + M * M₂))
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
  -- the zeros of height `≤ 2`, with multiplicity: a fixed finite number `N₂`
  set R₂ : Set ℂ := closedRect ⟨1 - σ, -2⟩ ⟨σ, 2⟩ with hR₂
  set DR := MeromorphicOn.divisor (rsHent k f) R₂ with hDR
  have hfaR : AnalyticOnNhd ℂ (rsHent k f) R₂ := fun s _ => analyticAt_rsHent k f hk s
  have hDRfin : (Function.support DR).Finite :=
    (MeromorphicOn.divisor (rsHent k f) R₂).finiteSupport (isCompact_closedRect _ _)
  have hDR0 : ∀ u, 0 ≤ DR u := fun u => by
    have := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfaR u
    simpa using this
  set N₂ : ℝ := ∑ u ∈ hDRfin.toFinset, (DR u : ℝ) with hN₂
  have hN₂0 : 0 ≤ N₂ := Finset.sum_nonneg fun u _ => by exact_mod_cast hDR0 u
  refine ⟨N₂ + 2 * max K₀ 0, by positivity, ?_⟩
  intro g hc hs hga hg hF hg' hF' hdec hArch hPW hPW₂ hstrip
  have hhc : Continuous (WeilForm.selfDual g) := WeilForm.continuous_selfDual g hc hs
  obtain ⟨T, hT, hlim⟩ := explicitFormula_Gfull k f hk hf hσ1 hσ2 (WeilForm.selfDual g) hhc hga
    hg hF hg' hF' hdec hArch
  have hpt : ∀ u : ℂ, ghat (WeilForm.selfDual g) u = ghat g u * conj (ghat g (1 - conj u)) :=
    fun u => WeilForm.ghat_selfDual_eq g hc hs u
  have h1 : ghat (WeilForm.selfDual g) 1 = ghat g 1 * conj (ghat g 0) := by
    rw [hpt]; simp
  rw [h1] at hlim
  have hreal : ∀ j : ℕ,
      -(Real.exp (2 * ε * L) * (N₂ + 2 * max K₀ 0) * (M * M + M * M₂)) ≤
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
    -- multiplicities
    set m : ℂ → ℕ := fun u => (D u).toNat with hm
    have hmD : ∀ u, ((m u : ℕ) : ℂ) = (D u : ℂ) := fun u => by
      simp only [hm]
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (hD0 u)]
    have hmDr : ∀ u, ((m u : ℕ) : ℝ) = (D u : ℝ) := fun u => by
      simp only [hm]
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (hD0 u)]
    have hterm : ∀ u, (D u : ℂ) * ghat (WeilForm.selfDual g) u
        = (m u : ℂ) * DefectLadder.sdTerm (ghat g) u := by
      intro u; rw [hmD, hpt, DefectLadder.sdTerm]
    -- the on-line part is a nonnegative real
    set D' : ℂ → ℤ := fun u => if u.re = 1 / 2 then D u else 0 with hD'
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
      · exact h
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
    have hon' : ∀ u ∈ S, (if u.re = 1 / 2 then (m u : ℂ) * DefectLadder.sdTerm (ghat g) u else 0)
        = (D' u : ℂ) * ghat (WeilForm.selfDual g) u := by
      intro u _
      simp only [hD']; split_ifs
      · rw [hterm]
      · simp
    have hon : (∑ ρ ∈ S.filter (fun ρ => ρ.re = 1 / 2), (m ρ : ℂ) * DefectLadder.sdTerm (ghat g) ρ)
        = ((∑ᶠ u, (D' u : ℝ) * ‖ghat g u‖ ^ 2 : ℝ) : ℂ) := by
      rw [Finset.sum_filter, Finset.sum_congr rfl hon', ← finsum_eq_sum_of_support_subset _ hsupp']
      exact heq
    have honS : 0 ≤ (∑ ρ ∈ S.filter (fun ρ => ρ.re = 1 / 2),
        (m ρ : ℂ) * DefectLadder.sdTerm (ghat g) ρ).re := by
      rw [hon, Complex.ofReal_re]; exact hnn
    have hstripS : ∀ ρ ∈ S, |ρ.re - 1 / 2| ≤ ε := fun ρ hρ => hstrip _ _ ρ ((hmemS ρ).mp hρ)
    have hmain := DefectLadder.re_sum_ge S m (ghat g) hL hM hM₂ hPW hPW₂ hstripS honS
    -- the bounded off-line part: at most `N₂`
    set T₀ := (S.filter (fun ρ => ¬ ρ.re = 1 / 2)).filter (fun ρ => ¬ 2 < |ρ.im|) with hT₀
    have hmemR₂ : ∀ ρ, D ρ ≠ 0 → |ρ.im| ≤ 2 → ρ ∈ R₂ := by
      intro ρ hρD hρim
      obtain ⟨h1, h2⟩ := hre_rect ρ hρD
      rw [hR₂, closedRect, Complex.mem_reProdIm, Set.uIcc_of_le (by show 1 - σ ≤ σ; linarith),
        Set.uIcc_of_le (by norm_num : (-2 : ℝ) ≤ 2)]
      exact ⟨⟨h1, h2⟩, abs_le.mp hρim⟩
    have hDDR : ∀ ρ, D ρ ≠ 0 → |ρ.im| ≤ 2 → D ρ = DR ρ := by
      intro ρ hρD hρim
      have huK : ρ ∈ Kj := D.supportWithinDomain (Function.mem_support.mpr hρD)
      have e1 := RankinSelbergDelta.ZeroCount.mult_eq_divisor hfa huK
      have e2 := RankinSelbergDelta.ZeroCount.mult_eq_divisor hfaR (hmemR₂ ρ hρD hρim)
      rw [← hD] at e1
      rw [← hDR] at e2
      rw [← e1, ← e2]
    have hN₂le : (∑ ρ ∈ T₀, (m ρ : ℝ)) ≤ N₂ := by
      have hsub : T₀ ⊆ hDRfin.toFinset := by
        intro ρ hρ
        rw [hT₀, Finset.mem_filter, Finset.mem_filter, hmemS] at hρ
        obtain ⟨⟨hρD, _⟩, hρim⟩ := hρ
        push_neg at hρim
        rw [Set.Finite.mem_toFinset, Function.mem_support, ← hDDR ρ hρD hρim]
        exact hρD
      have hmDR : ∀ ρ ∈ T₀, (m ρ : ℝ) = (DR ρ : ℝ) := by
        intro ρ hρ
        rw [hT₀, Finset.mem_filter, Finset.mem_filter, hmemS] at hρ
        obtain ⟨⟨hρD, _⟩, hρim⟩ := hρ
        push_neg at hρim
        rw [hmDr, hDDR ρ hρD hρim]
      calc (∑ ρ ∈ T₀, (m ρ : ℝ)) = ∑ ρ ∈ T₀, (DR ρ : ℝ) := Finset.sum_congr rfl hmDR
        _ ≤ ∑ u ∈ hDRfin.toFinset, (DR u : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun u _ _ => by exact_mod_cast hDR0 u)
    -- the tail: Abel summation with the zero count
    set T₁ := (S.filter (fun ρ => ¬ ρ.re = 1 / 2)).filter (fun ρ => 2 < |ρ.im|) with hT₁
    have hT₁H : ∀ ρ ∈ T₁, (2 : ℝ) < |ρ.im| := fun ρ hρ => (Finset.mem_filter.mp hρ).2
    have hN : ∀ t : ℝ, 2 ≤ t → ((T₁.filter (fun ρ => |ρ.im| ≤ t)).sum (fun ρ => (m ρ : ℝ)))
        ≤ max K₀ 0 * t * Real.log t := by
      intro t ht
      obtain ⟨hfinB, hwc⟩ := hK₀ t ht
      have hlogt : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
      have hsub : ∀ ρ ∈ T₁.filter (fun ρ => |ρ.im| ≤ t),
          ρ ∈ RankinSelbergDelta.ZeroCount.zerosIn (rsHent k f) (RankinSelbergDelta.ZeroCount.band (-1) σ₀ t) := by
        intro ρ hρ
        rw [Finset.mem_filter] at hρ
        obtain ⟨hρT, hρt⟩ := hρ
        have hρH := hT₁H ρ hρT
        rw [hT₁, Finset.mem_filter, Finset.mem_filter, hmemS] at hρT
        obtain ⟨h1, h2⟩ := hre_rect ρ hρT.1.1
        refine ⟨⟨by linarith, by linarith, by linarith, hρt⟩, ?_⟩
        have huK : ρ ∈ Kj := D.supportWithinDomain (Function.mem_support.mpr hρT.1.1)
        exact eq_zero_of_divisor_ne_zero hfa huK hρT.1.1
      have hmult : ∀ ρ ∈ T₁.filter (fun ρ => |ρ.im| ≤ t),
          (m ρ : ℝ) = (RankinSelbergDelta.ZeroCount.mult (rsHent k f) ρ : ℝ) := by
        intro ρ hρ
        rw [Finset.mem_filter, hT₁, Finset.mem_filter, Finset.mem_filter, hmemS] at hρ
        have huK : ρ ∈ Kj := D.supportWithinDomain (Function.mem_support.mpr hρ.1.1.1)
        have := RankinSelbergDelta.ZeroCount.mult_eq_divisor hfa huK
        rw [← hD] at this
        have h2 : ((m ρ : ℕ) : ℤ) = D ρ := by simp only [hm]; exact Int.toNat_of_nonneg (hD0 ρ)
        have h3 : ((m ρ : ℕ) : ℤ) = (RankinSelbergDelta.ZeroCount.mult (rsHent k f) ρ : ℤ) := by
          rw [h2, this]
        exact_mod_cast h3
      calc ((T₁.filter (fun ρ => |ρ.im| ≤ t)).sum (fun ρ => (m ρ : ℝ)))
          = (T₁.filter (fun ρ => |ρ.im| ≤ t)).sum
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
    have hA := RankinSelbergDelta.Analysis.PaleyWiener.sum_div_im_sq_le T₁ m (H := 2) (by norm_num)
      (le_max_right K₀ 0) hT₁H hN
    have hlog2 : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hAle : (∑ ρ ∈ T₁, (m ρ : ℝ) / ρ.im ^ 2) ≤ 2 * max K₀ 0 := by
      calc (∑ ρ ∈ T₁, (m ρ : ℝ) / ρ.im ^ 2) ≤ 2 * max K₀ 0 * (1 + Real.log 2) / 2 := hA
        _ ≤ 2 * max K₀ 0 := by nlinarith [le_max_right K₀ 0]
    -- assemble
    rw [hsum, Finset.sum_congr rfl (fun u _ => hterm u)]
    have hexp : 0 ≤ Real.exp (2 * ε * L) := (Real.exp_pos _).le
    have hMM : 0 ≤ M * M := by positivity
    have hMM₂ : 0 ≤ M * M₂ := by positivity
    have hcomb : (M * M) * (∑ ρ ∈ T₀, (m ρ : ℝ)) + (M * M₂) * (∑ ρ ∈ T₁, (m ρ : ℝ) / ρ.im ^ 2)
        ≤ (N₂ + 2 * max K₀ 0) * (M * M + M * M₂) := by
      have hK' : 0 ≤ 2 * max K₀ 0 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hN₂le hMM, mul_le_mul_of_nonneg_left hAle hMM₂,
        mul_nonneg hN₂0 hMM₂, mul_nonneg hK' hMM]
    have hcomb' := mul_le_mul_of_nonneg_left hcomb hexp
    calc -(Real.exp (2 * ε * L) * (N₂ + 2 * max K₀ 0) * (M * M + M * M₂))
        = -(Real.exp (2 * ε * L) * ((N₂ + 2 * max K₀ 0) * (M * M + M * M₂))) := by ring
      _ ≤ -(Real.exp (2 * ε * L)
            * ((M * M) * ∑ ρ ∈ T₀, (m ρ : ℝ) + (M * M₂) * ∑ ρ ∈ T₁, (m ρ : ℝ) / ρ.im ^ 2)) :=
          neg_le_neg hcomb'
      _ ≤ _ := hmain
  -- pass to the limit
  have hlim' := (Complex.continuous_re.tendsto _).comp hlim
  refine ge_of_tendsto' hlim' fun j => ?_
  simp only [Function.comp]
  exact hreal j

end RankinSelbergDelta.RankinSelberg
