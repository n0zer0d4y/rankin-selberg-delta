import RankinSelbergDelta.RankinSelberg.WeilFormG

/-!
# Counting zeros with multiplicity

The order `ordZ f u` of an analytic function at a point, and the count of zeros with multiplicity
in a disc, in the namespace `RankinSelbergDelta.ZeroCount`.
-/

open MeasureTheory Filter
open scoped NNReal MatrixGroups Pointwise

noncomputable section

namespace RankinSelbergDelta.ZeroCount

open Complex Metric MeasureTheory Filter Topology


/-! ### The zero count with multiplicity

`ordZ f u` is the order of `f` at `u` as an
integer (the value of every divisor containing `u`), `mult f u = (ordZ f u).toNat` its
nonnegative version, and `wcount f S = ∑ᶠ u ∈ zerosIn f S, mult f u`. Jensen's inequality already
weights zeros by the divisor, so the counting results for distinct zeros hold unchanged with
`wcount` in place of `ncard`. -/

/-- The order of `f` at `u`, as an integer: the value of `MeromorphicOn.divisor f U u` for every
`U ∋ u` (`MeromorphicOn.divisor_apply`). -/
noncomputable def ordZ (f : ℂ → ℂ) (u : ℂ) : ℤ := (meromorphicOrderAt f u).untop₀

lemma divisor_eq_ordZ {f : ℂ → ℂ} {U : Set ℂ} (hf : MeromorphicOn f U) {u : ℂ} (hu : u ∈ U) :
    MeromorphicOn.divisor f U u = ordZ f u := MeromorphicOn.divisor_apply hf hu

/-- The multiplicity of `u` as a zero of `f` (a natural number). -/
noncomputable def mult (f : ℂ → ℂ) (u : ℂ) : ℕ := (ordZ f u).toNat

lemma mult_eq_divisor {f : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U) {u : ℂ} (hu : u ∈ U) :
    (mult f u : ℤ) = MeromorphicOn.divisor f U u := by
  rw [mult, divisor_eq_ordZ hf.meromorphicOn hu]
  have h0 : 0 ≤ MeromorphicOn.divisor f U u := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf u
  rw [divisor_eq_ordZ hf.meromorphicOn hu] at h0
  exact Int.toNat_of_nonneg h0

/-- The weighted zero count of `f` on `S`. -/
noncomputable def wcount (f : ℂ → ℂ) (S : Set ℂ) : ℝ := ∑ᶠ u ∈ zerosIn f S, (mult f u : ℝ)

lemma wsum_nonneg (w : ℂ → ℝ) (hw : ∀ u, 0 ≤ w u) (S : Set ℂ) : 0 ≤ ∑ᶠ u ∈ S, w u :=
  finsum_nonneg fun u => finsum_nonneg fun _ => hw u

lemma wsum_mono {A B : Set ℂ} (hB : B.Finite) (hAB : A ⊆ B) (w : ℂ → ℝ) (hw : ∀ u, 0 ≤ w u) :
    ∑ᶠ u ∈ A, w u ≤ ∑ᶠ u ∈ B, w u := by
  rw [finsum_mem_eq_finite_toFinset_sum _ (hB.subset hAB), finsum_mem_eq_finite_toFinset_sum _ hB]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun u _ _ => hw u
  intro u hu
  rw [Set.Finite.mem_toFinset] at hu ⊢
  exact hAB hu

lemma wsum_union_le {A B : Set ℂ} (hA : A.Finite) (hB : B.Finite) (w : ℂ → ℝ)
    (hw : ∀ u, 0 ≤ w u) : ∑ᶠ u ∈ A ∪ B, w u ≤ ∑ᶠ u ∈ A, w u + ∑ᶠ u ∈ B, w u := by
  have h := finsum_mem_union_inter (f := w) hA hB
  have h0 := wsum_nonneg w hw (A ∩ B)
  linarith

lemma wsum_biUnion_le {ι : Type*} (s : Finset ι) (t : ι → Set ℂ) (ht : ∀ i ∈ s, (t i).Finite)
    (w : ℂ → ℝ) (hw : ∀ u, 0 ≤ w u) :
    ∑ᶠ u ∈ (⋃ i ∈ s, t i), w u ≤ ∑ i ∈ s, ∑ᶠ u ∈ t i, w u := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    have hfin : (⋃ i ∈ s, t i).Finite :=
      s.finite_toSet.biUnion fun i hi => ht i (Finset.mem_insert_of_mem hi)
    refine (wsum_union_le (ht a (Finset.mem_insert_self a s)) hfin w hw).trans ?_
    exact add_le_add le_rfl (ih fun i hi => ht i (Finset.mem_insert_of_mem hi))

lemma mult_nonneg_real (f : ℂ → ℂ) (u : ℂ) : (0 : ℝ) ≤ (mult f u : ℝ) := Nat.cast_nonneg _

/-- **Jensen's zero count with multiplicity.** -/
theorem jensen_wcount_disc {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hc : f c ≠ 0) :
    wcount f (closedBall c (R / 2)) * Real.log 2
      ≤ Real.circleAverage (fun z => Real.log ‖f z‖) c R - Real.log ‖f c‖ := by
  have habs : |R| = R := abs_of_pos hR
  have hf' : AnalyticOnNhd ℂ f (closedBall c |R|) := by rw [habs]; exact hf
  have hmero : MeromorphicOn f (closedBall c |R|) := hf'.meromorphicOn
  have hcmem : c ∈ closedBall c R := mem_closedBall_self hR.le
  have hcmem' : c ∈ closedBall c |R| := by rw [habs]; exact hcmem
  set D := MeromorphicOn.divisor f (closedBall c |R|) with hD
  have hJ := MeromorphicOn.circleAverage_log_norm hR.ne' hmero
  have hDc : D c = 0 := by
    rw [hD, MeromorphicOn.divisor_apply hmero hcmem', (hf' c hcmem').meromorphicOrderAt_eq,
      analyticOrderAt_eq_zero.mpr (Or.inr hc)]
    rfl
  have htc : meromorphicTrailingCoeffAt f c = f c :=
    (hf' c hcmem').meromorphicTrailingCoeffAt_of_ne_zero hc
  rw [hDc, htc] at hJ
  simp only [Int.cast_zero, zero_mul, add_zero] at hJ
  have hkey : Real.circleAverage (fun z => Real.log ‖f z‖) c R - Real.log ‖f c‖
      = ∑ᶠ u, (D u : ℝ) * Real.log (R * ‖c - u‖⁻¹) := by
    rw [show (fun z => Real.log ‖f z‖) = (Real.log ‖f ·‖) from rfl, hJ]; ring
  rw [hkey]
  have hfin : D.support.Finite := D.finiteSupport (isCompact_closedBall c |R|)
  have hsupp : (fun u => (D u : ℝ) * Real.log (R * ‖c - u‖⁻¹)).support ⊆ hfin.toFinset := by
    intro u hu
    rw [Set.Finite.coe_toFinset]
    intro h0
    apply hu
    simp only [Function.mem_support, ne_eq, Decidable.not_not] at h0 ⊢
    rw [h0]; simp
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  have hDnn : ∀ u, (0 : ℤ) ≤ D u := fun u => MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf' u
  have hzero_sub : zerosIn f (closedBall c (R / 2)) ⊆ D.support := by
    intro u hu
    have hu' : u ∈ closedBall c |R| := by
      rw [habs]
      exact closedBall_subset_closedBall (by linarith) hu.1
    have h1 : 1 ≤ D u := one_le_divisor_of_zero hf' hu' hu.2
      (analyticOrderAt_ne_top_of_ne_zero_center (by rw [habs]; exact hR.le) hf' hc hu')
    rw [Function.mem_support]
    omega
  have hZfin : (zerosIn f (closedBall c (R / 2))).Finite := hfin.subset hzero_sub
  have hZsub : hZfin.toFinset ⊆ hfin.toFinset := by
    intro u hu
    rw [Set.Finite.mem_toFinset] at hu ⊢
    exact hzero_sub hu
  have hterm_nn : ∀ u ∈ hfin.toFinset, 0 ≤ (D u : ℝ) * Real.log (R * ‖c - u‖⁻¹) := by
    intro u hu
    rw [Set.Finite.mem_toFinset] at hu
    have hu' : u ∈ closedBall c |R| := D.supportWithinDomain hu
    rw [habs, mem_closedBall, dist_comm, dist_eq_norm] at hu'
    refine mul_nonneg (by exact_mod_cast hDnn u) ?_
    by_cases h0 : ‖c - u‖ = 0
    · rw [h0]; simp
    · have hpos : 0 < ‖c - u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      apply Real.log_nonneg
      rw [← div_eq_mul_inv, le_div_iff₀ hpos, one_mul]
      exact hu'
  -- every term at a zero in the small disc is at least `mult · log 2`
  have hterm_ge : ∀ u ∈ hZfin.toFinset,
      (mult f u : ℝ) * Real.log 2 ≤ (D u : ℝ) * Real.log (R * ‖c - u‖⁻¹) := by
    intro u hu
    rw [Set.Finite.mem_toFinset] at hu
    have hu' : u ∈ closedBall c |R| := by
      rw [habs]; exact closedBall_subset_closedBall (by linarith) hu.1
    have hDu : (mult f u : ℤ) = D u := mult_eq_divisor hf' hu'
    have hDu' : (mult f u : ℝ) = (D u : ℝ) := by exact_mod_cast hDu
    have hne : u ≠ c := by
      intro h; rw [h] at hu; exact hc hu.2
    have hpos : 0 < ‖c - u‖ := by
      rw [norm_pos_iff, sub_ne_zero]; exact hne.symm
    have hle : ‖c - u‖ ≤ R / 2 := by
      have := hu.1; rwa [mem_closedBall, dist_comm, dist_eq_norm] at this
    have h2 : (2 : ℝ) ≤ R * ‖c - u‖⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hpos]; linarith
    have hlog : Real.log 2 ≤ Real.log (R * ‖c - u‖⁻¹) :=
      Real.log_le_log (by norm_num) h2
    rw [hDu']
    exact mul_le_mul_of_nonneg_left hlog (by exact_mod_cast hDnn u)
  calc wcount f (closedBall c (R / 2)) * Real.log 2
      = ∑ u ∈ hZfin.toFinset, (mult f u : ℝ) * Real.log 2 := by
        rw [wcount, finsum_mem_eq_finite_toFinset_sum _ hZfin, Finset.sum_mul]
    _ ≤ ∑ u ∈ hZfin.toFinset, (D u : ℝ) * Real.log (R * ‖c - u‖⁻¹) :=
        Finset.sum_le_sum hterm_ge
    _ ≤ ∑ u ∈ hfin.toFinset, (D u : ℝ) * Real.log (R * ‖c - u‖⁻¹) :=
        Finset.sum_le_sum_of_subset_of_nonneg hZsub (fun u hu _ => hterm_nn u hu)

/-- **The per-disc bound with multiplicity.** -/
theorem disc_wcount_le {f : ℂ → ℂ} {σ₀ R C c : ℝ} {N : ℕ} (hR : 0 < R) (hC : 0 < C) (hc : 0 < c)
    (hf : ∀ z : ℂ, 1 ≤ |z.im| → AnalyticAt ℂ f z)
    (hgrow : ∀ z : ℂ, σ₀ - R ≤ z.re → z.re ≤ σ₀ + R → 1 ≤ |z.im| → ‖f z‖ ≤ C * (1 + |z.im|) ^ N)
    (hlow : ∀ t : ℝ, c ≤ ‖f (pt σ₀ t)‖) (t : ℝ) (ht : R + 1 ≤ |t|) :
    wcount f (closedBall (pt σ₀ t) (R / 2)) * Real.log 2
      ≤ Real.log (max C 1) + N * Real.log (1 + |t| + R) - Real.log c := by
  have hball : AnalyticOnNhd ℂ f (closedBall (pt σ₀ t) R) := by
    intro z hz
    have := mem_closedBall_pt_bounds hz
    exact hf z (by linarith [this.2.2.1])
  have hcen : f (pt σ₀ t) ≠ 0 := by
    intro h; have := hlow t; rw [h, norm_zero] at this; linarith
  have hJ := jensen_wcount_disc hR hball hcen
  refine le_trans hJ ?_
  have habs : |R| = R := abs_of_pos hR
  have hCA : Real.circleAverage (fun z => Real.log ‖f z‖) (pt σ₀ t) R
      ≤ Real.log (max C 1) + N * Real.log (1 + |t| + R) := by
    have hsph : MeromorphicOn f (sphere (pt σ₀ t) |R|) := by
      rw [habs]
      exact (hball.mono sphere_subset_closedBall).meromorphicOn
    refine Real.circleAverage_mono_on_of_le_circle
      (circleIntegrable_log_norm_meromorphicOn hsph) fun z hz => ?_
    rw [habs] at hz
    have hzb := mem_closedBall_pt_bounds (sphere_subset_closedBall hz)
    have hzim : 1 ≤ |z.im| := by linarith [hzb.2.2.1]
    have hg := hgrow z hzb.1 hzb.2.1 hzim
    have hC1 : 1 ≤ max C 1 := le_max_right _ _
    have hpos1 : 0 < 1 + |t| + R := by positivity
    have hbound : ‖f z‖ ≤ max C 1 * (1 + |t| + R) ^ N := by
      calc ‖f z‖ ≤ C * (1 + |z.im|) ^ N := hg
        _ ≤ max C 1 * (1 + |t| + R) ^ N := by
          apply mul_le_mul (le_max_left _ _) _ (by positivity) (by linarith)
          exact pow_le_pow_left₀ (by positivity) (by linarith [hzb.2.2.2]) N
    have hge1 : 1 ≤ max C 1 * (1 + |t| + R) ^ N := by
      calc (1 : ℝ) = 1 * 1 := (one_mul _).symm
        _ ≤ max C 1 * (1 + |t| + R) ^ N :=
          mul_le_mul hC1 (one_le_pow₀ (by linarith)) zero_le_one (by linarith)
    have hlogeq : Real.log (max C 1 * (1 + |t| + R) ^ N)
        = Real.log (max C 1) + N * Real.log (1 + |t| + R) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    rw [← hlogeq]
    by_cases h0 : ‖f z‖ = 0
    · rw [h0, Real.log_zero]; exact Real.log_nonneg hge1
    · exact Real.log_le_log (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)) hbound
  have hlc : Real.log c ≤ Real.log ‖f (pt σ₀ t)‖ := Real.log_le_log hc (hlow t)
  linarith

/-- **The Riemann–von Mangoldt upper bound WITH MULTIPLICITY** (and the finiteness of the band's
zero set). -/
theorem exists_wcount_band_le_mul_log {f : ℂ → ℂ} {a σ₀ C c : ℝ} {N : ℕ} (ha : a ≤ σ₀) (hC : 0 < C)
    (hc : 0 < c) (hf : ∀ z : ℂ, 1 ≤ |z.im| → AnalyticAt ℂ f z)
    (hgrow : ∀ z : ℂ, σ₀ - (2 * (σ₀ - a) + 1) ≤ z.re → z.re ≤ σ₀ + (2 * (σ₀ - a) + 1) →
      1 ≤ |z.im| → ‖f z‖ ≤ C * (1 + |z.im|) ^ N)
    (hlow : ∀ t : ℝ, c ≤ ‖f (pt σ₀ t)‖) :
    ∃ K : ℝ, ∀ T : ℝ, 2 ≤ T →
      (zerosIn f (band a σ₀ T)).Finite ∧ wcount f (band a σ₀ T) ≤ K * T * Real.log T := by
  set R : ℝ := 2 * (σ₀ - a) + 1 with hRdef
  have hR : 0 < R := by rw [hRdef]; linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcen : ∀ t, f (pt σ₀ t) ≠ 0 := fun t h => by
    have := hlow t; rw [h, norm_zero] at this; linarith
  set w : ℂ → ℝ := fun u => (mult f u : ℝ) with hw
  have hw0 : ∀ u, 0 ≤ w u := fun u => Nat.cast_nonneg _
  set Kp : Set ℂ := {z | a ≤ z.re ∧ z.re ≤ σ₀ ∧ 1 ≤ z.im ∧ z.im ≤ R + 1} with hKp
  set Km : Set ℂ := {z | a ≤ z.re ∧ z.re ≤ σ₀ ∧ -(R + 1) ≤ z.im ∧ z.im ≤ -1} with hKm
  have hfU : AnalyticOnNhd ℂ f (upStrip (σ₀ - R) (σ₀ + R)) := fun z hz =>
    hf z (by rw [abs_of_pos (by linarith [hz.2.2])]; exact hz.2.2)
  have hfD : AnalyticOnNhd ℂ f (downStrip (σ₀ - R) (σ₀ + R)) := fun z hz =>
    hf z (by rw [abs_of_neg (by linarith [hz.2.2])]; linarith [hz.2.2])
  have hnzU : ∃ z ∈ upStrip (σ₀ - R) (σ₀ + R), f z ≠ 0 :=
    ⟨pt σ₀ (R + 2), ⟨by simp; linarith, by simp; linarith, by simp; linarith⟩, hcen _⟩
  have hnzD : ∃ z ∈ downStrip (σ₀ - R) (σ₀ + R), f z ≠ 0 :=
    ⟨pt σ₀ (-(R + 2)), ⟨by simp; linarith, by simp; linarith, by simp; linarith⟩, hcen _⟩
  have hKpfin : (zerosIn f Kp).Finite :=
    zerosIn_finite (isCompact_rectIcc _ _ _ _)
      (hfU.mono fun z hz => ⟨by linarith [hz.1], by linarith [hz.2.1], hz.2.2.1⟩)
      (fun u hu => analyticOrderAt_ne_top_of_convex (convex_upStrip _ _) hfU hnzU
        ⟨by linarith [hu.1], by linarith [hu.2.1], hu.2.2.1⟩)
  have hKmfin : (zerosIn f Km).Finite :=
    zerosIn_finite (isCompact_rectIcc _ _ _ _)
      (hfD.mono fun z hz => ⟨by linarith [hz.1], by linarith [hz.2.1], hz.2.2.2⟩)
      (fun u hu => analyticOrderAt_ne_top_of_convex (convex_downStrip _ _) hfD hnzD
        ⟨by linarith [hu.1], by linarith [hu.2.1], hu.2.2.2⟩)
  set tj : ℕ → ℝ := fun j => R + 1 + j + 1 / 2 with htj
  have htjpos : ∀ j : ℕ, 0 < tj j := fun j => by simp only [htj]; positivity
  have hdisc : ∀ (j : ℕ) (s : ℝ), |s| = 1 →
      wcount f (closedBall (pt σ₀ (s * tj j)) (R / 2)) * Real.log 2
        ≤ Real.log (max C 1) + N * Real.log (1 + tj j + R) - Real.log c := by
    intro j s hs
    have habs : |s * tj j| = tj j := by rw [abs_mul, hs, one_mul, abs_of_pos (htjpos j)]
    have := disc_wcount_le hR hC hc hf hgrow hlow (s * tj j)
      (by rw [habs]; simp only [htj]; linarith)
    rwa [habs] at this
  have hdfin : ∀ (j : ℕ) (s : ℝ), |s| = 1 →
      (zerosIn f (closedBall (pt σ₀ (s * tj j)) (R / 2))).Finite := by
    intro j s hs
    have habs : |s * tj j| = tj j := by rw [abs_mul, hs, one_mul, abs_of_pos (htjpos j)]
    have hb : AnalyticOnNhd ℂ f (closedBall (pt σ₀ (s * tj j)) (R / 2)) := by
      intro z hz
      have h1 := mem_closedBall_pt_bounds hz
      rw [habs] at h1
      exact hf z (by simp only [htj] at h1; linarith [h1.2.2.1])
    exact zerosIn_finite (isCompact_closedBall _ _) hb
      (fun u hu => analyticOrderAt_ne_top_of_ne_zero_center (by positivity) hb (hcen _) hu)
  set D : ℝ := Real.log (max C 1) + N * Real.log (2 * R + 3) + |Real.log c| with hD
  have hD0 : 0 ≤ D := by
    have h1 : 0 ≤ Real.log (max C 1) := Real.log_nonneg (le_max_right _ _)
    have h2 : 0 ≤ Real.log (2 * R + 3) := Real.log_nonneg (by linarith)
    have h3 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have h4 := abs_nonneg (Real.log c)
    rw [hD]; nlinarith
  set C₀ : ℝ := wcount f Kp + wcount f Km with hC₀
  have hC₀0 : 0 ≤ C₀ := by
    rw [hC₀]
    exact add_nonneg (wsum_nonneg w hw0 _) (wsum_nonneg w hw0 _)
  refine ⟨C₀ / (2 * Real.log 2) + 4 * (D / Real.log 2 + N) / Real.log 2, fun T hT => ?_⟩
  set L := Real.log T with hL
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hT
  set K : ℕ := ⌊T⌋₊ + 1 with hK
  have hKle : (K : ℝ) ≤ 2 * T := by
    rw [hK]; push_cast
    have := Nat.floor_le (by linarith : (0 : ℝ) ≤ T); linarith
  have hdiscL : ∀ j ∈ Finset.range K, ∀ s : ℝ, |s| = 1 →
      wcount f (closedBall (pt σ₀ (s * tj j)) (R / 2)) ≤ (D + N * L) / Real.log 2 := by
    intro j hj s hs
    have hjT : (j : ℝ) ≤ T := by
      rw [Finset.mem_range, hK, Nat.lt_add_one_iff] at hj
      exact le_trans (by exact_mod_cast hj) (Nat.floor_le (by linarith))
    have hlog : Real.log (1 + tj j + R) ≤ Real.log (2 * R + 3) + L := by
      rw [hL, ← Real.log_mul (by linarith) (by linarith)]
      apply Real.log_le_log (by simp only [htj]; positivity)
      simp only [htj]; nlinarith
    have h1 := hdisc j s hs
    have h2 : Real.log (max C 1) + N * Real.log (1 + tj j + R) - Real.log c ≤ D + N * L := by
      rw [hD]
      have := neg_abs_le (Real.log c)
      have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      nlinarith
    rw [le_div_iff₀ hl2]; linarith
  -- the cover
  have hcov : zerosIn f (band a σ₀ T) ⊆
      ((zerosIn f Kp ∪ zerosIn f Km)
        ∪ ⋃ j ∈ Finset.range K, zerosIn f (closedBall (pt σ₀ (1 * tj j)) (R / 2)))
        ∪ ⋃ j ∈ Finset.range K, zerosIn f (closedBall (pt σ₀ ((-1) * tj j)) (R / 2)) := by
    intro z hz
    obtain ⟨⟨h1, h2, h3, h4⟩, hz0⟩ := hz
    rcases le_or_gt 0 z.im with hy | hy
    · rw [abs_of_nonneg hy] at h3 h4
      rcases le_or_gt z.im (R + 1) with hlow' | hhigh
      · exact Or.inl (Or.inl (Or.inl ⟨⟨h1, h2, h3, hlow'⟩, hz0⟩))
      · refine Or.inl (Or.inr ?_)
        rw [Set.mem_iUnion₂]
        refine ⟨⌊1 * z.im - (R + 1)⌋₊, ?_, ?_, hz0⟩
        · rw [Finset.mem_range, hK, Nat.lt_add_one_iff]
          exact Nat.floor_mono (by linarith)
        · have := mem_closedBall_centre ha hRdef ⟨h1, h2⟩ (s := 1) (by simp) (by linarith)
          simpa only [htj] using this
    · rw [abs_of_neg hy] at h3 h4
      rcases le_or_gt (-z.im) (R + 1) with hlow' | hhigh
      · exact Or.inl (Or.inl (Or.inr ⟨⟨h1, h2, by linarith, by linarith⟩, hz0⟩))
      · refine Or.inr ?_
        rw [Set.mem_iUnion₂]
        refine ⟨⌊(-1) * z.im - (R + 1)⌋₊, ?_, ?_, hz0⟩
        · rw [Finset.mem_range, hK, Nat.lt_add_one_iff]
          exact Nat.floor_mono (by linarith)
        · have := mem_closedBall_centre ha hRdef ⟨h1, h2⟩ (s := -1) (by simp) (by linarith)
          simpa only [htj] using this
  have hfinU : (⋃ j ∈ Finset.range K, zerosIn f (closedBall (pt σ₀ (1 * tj j)) (R / 2))).Finite :=
    (Finset.range K).finite_toSet.biUnion fun j _ => hdfin j 1 (by simp)
  have hfinD : (⋃ j ∈ Finset.range K, zerosIn f (closedBall (pt σ₀ ((-1) * tj j)) (R / 2))).Finite :=
    (Finset.range K).finite_toSet.biUnion fun j _ => hdfin j (-1) (by simp)
  have hfin : (((zerosIn f Kp ∪ zerosIn f Km)
        ∪ ⋃ j ∈ Finset.range K, zerosIn f (closedBall (pt σ₀ (1 * tj j)) (R / 2)))
        ∪ ⋃ j ∈ Finset.range K, zerosIn f (closedBall (pt σ₀ ((-1) * tj j)) (R / 2))).Finite :=
    ((hKpfin.union hKmfin).union hfinU).union hfinD
  -- the union bound
  have hcast : wcount f (band a σ₀ T) ≤ C₀
      + (∑ j ∈ Finset.range K, wcount f (closedBall (pt σ₀ (1 * tj j)) (R / 2)))
      + ∑ j ∈ Finset.range K, wcount f (closedBall (pt σ₀ ((-1) * tj j)) (R / 2)) := by
    unfold wcount
    refine (wsum_mono hfin hcov w hw0).trans ?_
    refine (wsum_union_le ((hKpfin.union hKmfin).union hfinU) hfinD w hw0).trans ?_
    refine add_le_add ((wsum_union_le (hKpfin.union hKmfin) hfinU w hw0).trans ?_) ?_
    · refine add_le_add (wsum_union_le hKpfin hKmfin w hw0) ?_
      exact wsum_biUnion_le _ _ (fun j _ => hdfin j 1 (by simp)) w hw0
    · exact wsum_biUnion_le _ _ (fun j _ => hdfin j (-1) (by simp)) w hw0
  have hb0 : 0 ≤ (D + N * L) / Real.log 2 := by
    apply div_nonneg _ hl2.le
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith
  have hsum1 : (∑ j ∈ Finset.range K, wcount f (closedBall (pt σ₀ (1 * tj j)) (R / 2)))
        ≤ K * ((D + N * L) / Real.log 2) := by
    have := Finset.sum_le_card_nsmul (Finset.range K)
      (fun j => wcount f (closedBall (pt σ₀ (1 * tj j)) (R / 2)))
      ((D + N * L) / Real.log 2) (fun j hj => hdiscL j hj 1 (by simp))
    simpa [nsmul_eq_mul] using this
  have hsum2 : (∑ j ∈ Finset.range K, wcount f (closedBall (pt σ₀ ((-1) * tj j)) (R / 2)))
        ≤ K * ((D + N * L) / Real.log 2) := by
    have := Finset.sum_le_card_nsmul (Finset.range K)
      (fun j => wcount f (closedBall (pt σ₀ ((-1) * tj j)) (R / 2)))
      ((D + N * L) / Real.log 2) (fun j hj => hdiscL j hj (-1) (by simp))
    simpa [nsmul_eq_mul] using this
  have hKb := mul_le_mul_of_nonneg_right hKle hb0
  have hmain : wcount f (band a σ₀ T) ≤ C₀ + 2 * (2 * T) * ((D + N * L) / Real.log 2) := by
    linarith
  have hTL : 2 * Real.log 2 ≤ T * L := by nlinarith
  refine ⟨hfin.subset hcov, ?_⟩
  calc wcount f (band a σ₀ T)
      ≤ C₀ + 2 * (2 * T) * ((D + N * L) / Real.log 2) := hmain
    _ ≤ C₀ * (T * L / (2 * Real.log 2))
        + 4 * T * ((D * (L / Real.log 2) + N * L) / Real.log 2) := by
        have h1 : C₀ ≤ C₀ * (T * L / (2 * Real.log 2)) :=
          le_mul_of_one_le_right hC₀0 (by rw [le_div_iff₀ (by positivity)]; linarith)
        have h2 : D ≤ D * (L / Real.log 2) :=
          le_mul_of_one_le_right hD0 (by rw [le_div_iff₀ hl2]; linarith)
        have h3 : 2 * (2 * T) * ((D + N * L) / Real.log 2)
            ≤ 4 * T * ((D * (L / Real.log 2) + N * L) / Real.log 2) := by
          rw [show 2 * (2 * T) = 4 * T by ring]
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          apply div_le_div_of_nonneg_right _ hl2.le
          linarith
        linarith
    _ = (C₀ / (2 * Real.log 2) + 4 * (D / Real.log 2 + N) / Real.log 2) * T * L := by
        field_simp

end RankinSelbergDelta.ZeroCount
