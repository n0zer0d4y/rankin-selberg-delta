import RankinSelbergDelta.RankinSelberg.LogDerivBounds

/-!
# The zero count `N_G(T) = O(T log T)` and the prime side

The Riemann–von Mangoldt upper bound for the number of zeros of `G` up to height `T`, from
Jensen's formula; and the prime side of the explicit formula.
-/

open MeasureTheory Filter
open scoped NNReal MatrixGroups Pointwise

noncomputable section


/-! ### the Riemann–von Mangoldt upper bound `N_G(T) = O(T log T)`. The generic part below is Jensen's zero
count on discs centred on `Re z = σ₀` at unit-spaced heights, the circle average bounded by polynomial
growth, the centre bounded below, wrapped in its own namespace; it is then instantiated for
`Gfull k f` with `exists_norm_Gfull_ge` (the centre line `Re s = σ₀ ≥ 2`, `‖G‖ ≥ 3/8`),
`exists_norm_Gfull_le_halfStrip` (growth on `Re s ≥ −A`, `|Im s| ≥ 1`) and `differentiableAt_Gfull`. -/

namespace RankinSelbergDelta.ZeroCount

open Complex Metric MeasureTheory Filter Topology

open Complex Metric MeasureTheory Filter Topology

/-- The zeros of `f` lying in `S`. -/
def zerosIn (f : ℂ → ℂ) (S : Set ℂ) : Set ℂ := {z | z ∈ S ∧ f z = 0}

lemma zerosIn_mono (f : ℂ → ℂ) {S T : Set ℂ} (h : S ⊆ T) : zerosIn f S ⊆ zerosIn f T :=
  fun _ hz => ⟨h hz.1, hz.2⟩

/-- An analytic function on a closed disc that is nonzero at the centre is nowhere locally zero
on the disc. -/
lemma analyticOrderAt_ne_top_of_ne_zero_center {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hc : f c ≠ 0) {u : ℂ} (hu : u ∈ closedBall c R) :
    analyticOrderAt f u ≠ ⊤ := by
  intro htop
  rw [analyticOrderAt_eq_top] at htop
  have := hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_closedBall c R).isPreconnected
    hu htop (mem_closedBall_self hR)
  exact hc this

/-- At a zero of an analytic, not locally zero function, the divisor is at least `1`. -/
lemma one_le_divisor_of_zero {f : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U) {u : ℂ}
    (hu : u ∈ U) (hfu : f u = 0) (hne : analyticOrderAt f u ≠ ⊤) :
    1 ≤ MeromorphicOn.divisor f U u := by
  rw [MeromorphicOn.divisor_apply hf.meromorphicOn hu, (hf u hu).meromorphicOrderAt_eq]
  have h0 : analyticOrderAt f u ≠ 0 := analyticOrderAt_ne_zero.mpr ⟨hf u hu, hfu⟩
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
  rw [← hn] at h0 ⊢
  rw [ENat.map_coe, WithTop.untop₀_coe]
  have : n ≠ 0 := by
    intro h; apply h0; rw [h]; rfl
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr this

/-- **Jensen zero count on a disc.** -/
theorem jensen_count_disc {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hc : f c ≠ 0) :
    ((zerosIn f (closedBall c (R / 2))).ncard : ℝ) * Real.log 2
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
  -- the circle average minus the centre value is the divisor sum
  have hkey : Real.circleAverage (fun z => Real.log ‖f z‖) c R - Real.log ‖f c‖
      = ∑ᶠ u, (D u : ℝ) * Real.log (R * ‖c - u‖⁻¹) := by
    rw [show (fun z => Real.log ‖f z‖) = (Real.log ‖f ·‖) from rfl, hJ]; ring
  rw [hkey]
  -- finite support
  have hfin : D.support.Finite := D.finiteSupport (isCompact_closedBall c |R|)
  have hsupp : (fun u => (D u : ℝ) * Real.log (R * ‖c - u‖⁻¹)).support ⊆ hfin.toFinset := by
    intro u hu
    rw [Set.Finite.coe_toFinset]
    intro h0
    apply hu
    simp only [Function.mem_support, ne_eq, Decidable.not_not] at h0 ⊢
    rw [h0]; simp
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  -- the zero set is a subset of the support
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
  -- every term is nonnegative
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
  -- every term at a zero in the small disc is at least `log 2`
  have hterm_ge : ∀ u ∈ hZfin.toFinset, Real.log 2 ≤ (D u : ℝ) * Real.log (R * ‖c - u‖⁻¹) := by
    intro u hu
    rw [Set.Finite.mem_toFinset] at hu
    have h1 : (1 : ℝ) ≤ D u := by
      have hu' : u ∈ closedBall c |R| := by
        rw [habs]; exact closedBall_subset_closedBall (by linarith) hu.1
      exact_mod_cast one_le_divisor_of_zero hf' hu' hu.2
        (analyticOrderAt_ne_top_of_ne_zero_center (by rw [habs]; exact hR.le) hf' hc hu')
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
    have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    calc Real.log 2 = 1 * Real.log 2 := (one_mul _).symm
      _ ≤ (D u : ℝ) * Real.log (R * ‖c - u‖⁻¹) :=
          mul_le_mul h1 hlog hlog0 (by linarith)
  calc ((zerosIn f (closedBall c (R / 2))).ncard : ℝ) * Real.log 2
      = ∑ u ∈ hZfin.toFinset, Real.log 2 := by
        rw [Finset.sum_const, nsmul_eq_mul, Set.ncard_eq_toFinset_card _ hZfin]
    _ ≤ ∑ u ∈ hZfin.toFinset, (D u : ℝ) * Real.log (R * ‖c - u‖⁻¹) :=
        Finset.sum_le_sum hterm_ge
    _ ≤ ∑ u ∈ hfin.toFinset, (D u : ℝ) * Real.log (R * ‖c - u‖⁻¹) :=
        Finset.sum_le_sum_of_subset_of_nonneg hZsub (fun u hu _ => hterm_nn u hu)

/-- The point `x + t i`. -/
def pt (x t : ℝ) : ℂ := ⟨x, t⟩

@[simp] lemma pt_re (x t : ℝ) : (pt x t).re = x := rfl
@[simp] lemma pt_im (x t : ℝ) : (pt x t).im = t := rfl

lemma circleMap_pt (x t R θ : ℝ) :
    circleMap (pt x t) R θ = pt (x + R * Real.cos θ) (t + R * Real.sin θ) := by
  apply Complex.ext
  · simp [circleMap, pt, Complex.exp_ofReal_mul_I_re]
  · simp [circleMap, pt, Complex.exp_ofReal_mul_I_im]

/-- The closed vertical strip `α ≤ Re z ≤ β`. -/
def strip (α β : ℝ) : Set ℂ := {z | α ≤ z.re ∧ z.re ≤ β}

lemma isLinearMap_re : IsLinearMap ℝ (fun z : ℂ => z.re) :=
  ⟨fun x y => Complex.add_re x y, fun c z => by simp⟩

lemma convex_strip (α β : ℝ) : Convex ℝ (strip α β) :=
  (convex_halfSpace_ge isLinearMap_re α).inter (convex_halfSpace_le isLinearMap_re β)

lemma analyticOrderAt_ne_top_of_convex {f : ℂ → ℂ} {S : Set ℂ} (hS : Convex ℝ S)
    (hf : AnalyticOnNhd ℂ f S) (hz : ∃ z ∈ S, f z ≠ 0) {u : ℂ} (hu : u ∈ S) :
    analyticOrderAt f u ≠ ⊤ := by
  intro htop
  rw [analyticOrderAt_eq_top] at htop
  obtain ⟨z, hzS, hz⟩ := hz
  exact hz (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hS.isPreconnected hu htop hzS)

/-- Zeros of an analytic, nowhere locally zero function on a compact set are finite. -/
lemma zerosIn_finite {f : ℂ → ℂ} {K : Set ℂ} (hK : IsCompact K) (hf : AnalyticOnNhd ℂ f K)
    (hne : ∀ u ∈ K, analyticOrderAt f u ≠ ⊤) : (zerosIn f K).Finite := by
  have hfin := (MeromorphicOn.divisor f K).finiteSupport hK
  refine hfin.subset fun u hu => ?_
  rw [Function.mem_support]
  have := one_le_divisor_of_zero hf hu.1 hu.2 (hne u hu.1)
  omega


/-! ### the per-disc bound -/

/-- Every point of the closed disc about `pt σ₀ t` of radius `R` has `|Im| ≥ |t| − R` and
`Re ≥ σ₀ − R`. -/
lemma mem_closedBall_pt_bounds {σ₀ t R : ℝ} {z : ℂ} (hz : z ∈ closedBall (pt σ₀ t) R) :
    σ₀ - R ≤ z.re ∧ z.re ≤ σ₀ + R ∧ |t| - R ≤ |z.im| ∧ |z.im| ≤ |t| + R := by
  rw [mem_closedBall, dist_eq_norm] at hz
  have h1 := Complex.abs_re_le_norm (z - pt σ₀ t)
  have h2 := Complex.abs_im_le_norm (z - pt σ₀ t)
  rw [Complex.sub_re, pt_re] at h1
  rw [Complex.sub_im, pt_im] at h2
  have h3 := abs_sub_abs_le_abs_sub z.im t
  have h4 := abs_sub_abs_le_abs_sub t z.im
  rw [abs_sub_comm t z.im] at h4
  rw [abs_le] at h1
  refine ⟨by linarith [h1.1], by linarith [h1.2], by linarith, by linarith⟩

/-- **The per-disc bound.** For `|t| ≥ R + 1`, the zeros within `R/2` of `pt σ₀ t` number at most
`(log C' + N log (1 + |t| + R) − log c) / log 2`, where `C' = max C 1`. -/
theorem disc_count_le {f : ℂ → ℂ} {σ₀ R C c : ℝ} {N : ℕ} (hR : 0 < R) (hC : 0 < C) (hc : 0 < c)
    (hf : ∀ z : ℂ, 1 ≤ |z.im| → AnalyticAt ℂ f z)
    (hgrow : ∀ z : ℂ, σ₀ - R ≤ z.re → 1 ≤ |z.im| → ‖f z‖ ≤ C * (1 + |z.im|) ^ N)
    (hlow : ∀ t : ℝ, c ≤ ‖f (pt σ₀ t)‖) (t : ℝ) (ht : R + 1 ≤ |t|) :
    ((zerosIn f (closedBall (pt σ₀ t) (R / 2))).ncard : ℝ) * Real.log 2
      ≤ Real.log (max C 1) + N * Real.log (1 + |t| + R) - Real.log c := by
  have hball : AnalyticOnNhd ℂ f (closedBall (pt σ₀ t) R) := by
    intro z hz
    have := mem_closedBall_pt_bounds hz
    exact hf z (by linarith [this.2.2.1])
  have hcen : f (pt σ₀ t) ≠ 0 := by
    intro h; have := hlow t; rw [h, norm_zero] at this; linarith
  have hJ := jensen_count_disc hR hball hcen
  refine le_trans hJ ?_
  have habs : |R| = R := abs_of_pos hR
  -- the circle average is bounded by the growth
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
    have hg := hgrow z hzb.1 hzim
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

/-! ### the band count -/

lemma ncard_biUnion_le {ι α : Type*} (s : Finset ι) (t : ι → Set α) :
    (⋃ i ∈ s, t i).ncard ≤ ∑ i ∈ s, (t i).ncard := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_left ih _)

/-- The band `a ≤ Re z ≤ b`, `1 ≤ |Im z| ≤ T`: the zeros counted by `N(T)`. -/
def band (a b T : ℝ) : Set ℂ := {z | a ≤ z.re ∧ z.re ≤ b ∧ 1 ≤ |z.im| ∧ |z.im| ≤ T}

/-- The closed upper half-strip `α ≤ Re z ≤ β`, `Im z ≥ 1`. -/
def upStrip (α β : ℝ) : Set ℂ := {z | α ≤ z.re ∧ z.re ≤ β ∧ 1 ≤ z.im}

/-- The closed lower half-strip `α ≤ Re z ≤ β`, `Im z ≤ −1`. -/
def downStrip (α β : ℝ) : Set ℂ := {z | α ≤ z.re ∧ z.re ≤ β ∧ z.im ≤ -1}

lemma isLinearMap_im : IsLinearMap ℝ (fun z : ℂ => z.im) :=
  ⟨fun x y => Complex.add_im x y, fun c z => by simp⟩

lemma convex_upStrip (α β : ℝ) : Convex ℝ (upStrip α β) := by
  have : upStrip α β = ({z : ℂ | α ≤ z.re} ∩ {z | z.re ≤ β}) ∩ {z | 1 ≤ z.im} := by
    ext z; simp [upStrip, and_assoc]
  rw [this]
  exact ((convex_halfSpace_ge isLinearMap_re α).inter (convex_halfSpace_le isLinearMap_re β)).inter
    (convex_halfSpace_ge isLinearMap_im 1)

lemma convex_downStrip (α β : ℝ) : Convex ℝ (downStrip α β) := by
  have : downStrip α β = ({z : ℂ | α ≤ z.re} ∩ {z | z.re ≤ β}) ∩ {z | z.im ≤ -1} := by
    ext z; simp [downStrip, and_assoc]
  rw [this]
  exact ((convex_halfSpace_ge isLinearMap_re α).inter (convex_halfSpace_le isLinearMap_re β)).inter
    (convex_halfSpace_le isLinearMap_im (-1))

lemma isCompact_rectIcc (a b c d : ℝ) :
    IsCompact {z : ℂ | a ≤ z.re ∧ z.re ≤ b ∧ c ≤ z.im ∧ z.im ≤ d} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact (isClosed_le continuous_const Complex.continuous_re).inter
      ((isClosed_le Complex.continuous_re continuous_const).inter
        ((isClosed_le continuous_const Complex.continuous_im).inter
          (isClosed_le Complex.continuous_im continuous_const)))
  · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := |a| + |b| + |c| + |d|)).subset ?_
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    obtain ⟨h1, h2, h3, h4⟩ := hz
    have hre : |z.re| ≤ |a| + |b| := by
      rw [abs_le]; constructor <;> linarith [neg_abs_le a, le_abs_self b, abs_nonneg a, abs_nonneg b]
    have him : |z.im| ≤ |c| + |d| := by
      rw [abs_le]; constructor <;> linarith [neg_abs_le c, le_abs_self d, abs_nonneg c, abs_nonneg d]
    calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ |a| + |b| + |c| + |d| := by linarith

/-- A point of the band at height `s · Im z ≥ R + 1` (`s = ±1`) lies within `R/2` of the centre
`pt σ₀ (s (R + 1 + j + 1/2))` with `j = ⌊s · Im z − (R + 1)⌋₊`. -/
lemma mem_closedBall_centre {a σ₀ R : ℝ} (ha : a ≤ σ₀) (hR : R = 2 * (σ₀ - a) + 1) {z : ℂ}
    (hre : a ≤ z.re ∧ z.re ≤ σ₀) {s : ℝ} (hs : |s| = 1) (hsy : R + 1 ≤ s * z.im) :
    z ∈ closedBall (pt σ₀ (s * (R + 1 + ⌊s * z.im - (R + 1)⌋₊ + 1 / 2))) (R / 2) := by
  rw [mem_closedBall, dist_eq_norm]
  set j : ℕ := ⌊s * z.im - (R + 1)⌋₊ with hj
  have h0 : 0 ≤ s * z.im - (R + 1) := by linarith
  have hjle : (j : ℝ) ≤ s * z.im - (R + 1) := Nat.floor_le h0
  have hjlt : s * z.im - (R + 1) < j + 1 := Nat.lt_floor_add_one _
  have hs2 : s * s = 1 := by
    have := sq_abs s; rw [hs] at this; nlinarith
  have him : |(z - pt σ₀ (s * (R + 1 + j + 1 / 2))).im| ≤ 1 / 2 := by
    rw [Complex.sub_im, pt_im]
    have : z.im - s * (R + 1 + j + 1 / 2) = s * (s * z.im - (R + 1 + j + 1 / 2)) := by
      linear_combination (-z.im) * hs2
    rw [this, abs_mul, hs, one_mul, abs_le]
    constructor <;> linarith
  have hre' : |(z - pt σ₀ (s * (R + 1 + j + 1 / 2))).re| ≤ σ₀ - a := by
    rw [Complex.sub_re, pt_re, abs_le]; constructor <;> linarith [hre.1, hre.2]
  calc ‖z - pt σ₀ (s * (R + 1 + j + 1 / 2))‖
      ≤ |(z - pt σ₀ (s * (R + 1 + j + 1 / 2))).re| + |(z - pt σ₀ (s * (R + 1 + j + 1 / 2))).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ R / 2 := by
        have : R / 2 = σ₀ - a + 1 / 2 := by rw [hR]; ring
        linarith

/-- **The Riemann–von Mangoldt upper bound** for a function analytic on `|Im z| ≥ 1` with
polynomial growth to the right of `Re z = σ₀ − R` and a lower bound on `Re z = σ₀`: the zeros in
`a ≤ Re z ≤ σ₀`, `1 ≤ |Im z| ≤ T` number `O(T log T)`. -/
theorem exists_ncard_band_le_mul_log {f : ℂ → ℂ} {a σ₀ C c : ℝ} {N : ℕ} (ha : a ≤ σ₀) (hC : 0 < C)
    (hc : 0 < c) (hf : ∀ z : ℂ, 1 ≤ |z.im| → AnalyticAt ℂ f z)
    (hgrow : ∀ z : ℂ, σ₀ - (2 * (σ₀ - a) + 1) ≤ z.re → 1 ≤ |z.im| →
      ‖f z‖ ≤ C * (1 + |z.im|) ^ N)
    (hlow : ∀ t : ℝ, c ≤ ‖f (pt σ₀ t)‖) :
    ∃ K : ℝ, ∀ T : ℝ, 2 ≤ T → ((zerosIn f (band a σ₀ T)).ncard : ℝ) ≤ K * T * Real.log T := by
  set R : ℝ := 2 * (σ₀ - a) + 1 with hRdef
  have hR : 0 < R := by rw [hRdef]; linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcen : ∀ t, f (pt σ₀ t) ≠ 0 := fun t h => by
    have := hlow t; rw [h, norm_zero] at this; linarith
  -- the low band, two compact convex pieces
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
  -- the disc centres and the per-disc bound
  set tj : ℕ → ℝ := fun j => R + 1 + j + 1 / 2 with htj
  have htjpos : ∀ j : ℕ, 0 < tj j := fun j => by simp only [htj]; positivity
  have hdisc : ∀ (j : ℕ) (s : ℝ), |s| = 1 →
      ((zerosIn f (closedBall (pt σ₀ (s * tj j)) (R / 2))).ncard : ℝ) * Real.log 2
        ≤ Real.log (max C 1) + N * Real.log (1 + tj j + R) - Real.log c := by
    intro j s hs
    have habs : |s * tj j| = tj j := by rw [abs_mul, hs, one_mul, abs_of_pos (htjpos j)]
    have := disc_count_le hR hC hc hf hgrow hlow (s * tj j)
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
  -- the constants
  set D : ℝ := Real.log (max C 1) + N * Real.log (2 * R + 3) + |Real.log c| with hD
  have hD0 : 0 ≤ D := by
    have h1 : 0 ≤ Real.log (max C 1) := Real.log_nonneg (le_max_right _ _)
    have h2 : 0 ≤ Real.log (2 * R + 3) := Real.log_nonneg (by linarith)
    have h3 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have h4 := abs_nonneg (Real.log c)
    rw [hD]; nlinarith
  set C₀ : ℝ := (zerosIn f Kp).ncard + (zerosIn f Km).ncard with hC₀
  have hC₀0 : 0 ≤ C₀ := by rw [hC₀]; positivity
  refine ⟨C₀ / (2 * Real.log 2) + 4 * (D / Real.log 2 + N) / Real.log 2, fun T hT => ?_⟩
  set L := Real.log T with hL
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hT
  set K : ℕ := ⌊T⌋₊ + 1 with hK
  have hKle : (K : ℝ) ≤ 2 * T := by
    rw [hK]; push_cast
    have := Nat.floor_le (by linarith : (0 : ℝ) ≤ T); linarith
  -- per-disc bound in terms of L
  have hdiscL : ∀ j ∈ Finset.range K, ∀ s : ℝ, |s| = 1 →
      ((zerosIn f (closedBall (pt σ₀ (s * tj j)) (R / 2))).ncard : ℝ)
        ≤ (D + N * L) / Real.log 2 := by
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
  -- finiteness of the cover
  have hfin : (((zerosIn f Kp ∪ zerosIn f Km)
        ∪ ⋃ j ∈ Finset.range K, zerosIn f (closedBall (pt σ₀ (1 * tj j)) (R / 2)))
        ∪ ⋃ j ∈ Finset.range K, zerosIn f (closedBall (pt σ₀ ((-1) * tj j)) (R / 2))).Finite :=
    ((hKpfin.union hKmfin).union
      ((Finset.range K).finite_toSet.biUnion fun j _ => hdfin j 1 (by simp))).union
      ((Finset.range K).finite_toSet.biUnion fun j _ => hdfin j (-1) (by simp))
  -- the union bound, in ℕ
  have hnat : (zerosIn f (band a σ₀ T)).ncard ≤ (zerosIn f Kp).ncard + (zerosIn f Km).ncard
      + ∑ j ∈ Finset.range K, (zerosIn f (closedBall (pt σ₀ (1 * tj j)) (R / 2))).ncard
      + ∑ j ∈ Finset.range K, (zerosIn f (closedBall (pt σ₀ ((-1) * tj j)) (R / 2))).ncard := by
    refine (Set.ncard_le_ncard hcov hfin).trans ?_
    refine (Set.ncard_union_le _ _).trans ?_
    exact add_le_add ((Set.ncard_union_le _ _).trans
      (add_le_add (Set.ncard_union_le _ _) (ncard_biUnion_le _ _))) (ncard_biUnion_le _ _)
  -- cast and bound the sums
  have hb0 : 0 ≤ (D + N * L) / Real.log 2 := by
    apply div_nonneg _ hl2.le
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith
  have hsum1 : (∑ j ∈ Finset.range K,
      ((zerosIn f (closedBall (pt σ₀ (1 * tj j)) (R / 2))).ncard : ℝ))
        ≤ K * ((D + N * L) / Real.log 2) := by
    have := Finset.sum_le_card_nsmul (Finset.range K)
      (fun j => ((zerosIn f (closedBall (pt σ₀ (1 * tj j)) (R / 2))).ncard : ℝ))
      ((D + N * L) / Real.log 2) (fun j hj => hdiscL j hj 1 (by simp))
    simpa [nsmul_eq_mul] using this
  have hsum2 : (∑ j ∈ Finset.range K,
      ((zerosIn f (closedBall (pt σ₀ ((-1) * tj j)) (R / 2))).ncard : ℝ))
        ≤ K * ((D + N * L) / Real.log 2) := by
    have := Finset.sum_le_card_nsmul (Finset.range K)
      (fun j => ((zerosIn f (closedBall (pt σ₀ ((-1) * tj j)) (R / 2))).ncard : ℝ))
      ((D + N * L) / Real.log 2) (fun j hj => hdiscL j hj (-1) (by simp))
    simpa [nsmul_eq_mul] using this
  have hcast : ((zerosIn f (band a σ₀ T)).ncard : ℝ) ≤ C₀
      + (∑ j ∈ Finset.range K, ((zerosIn f (closedBall (pt σ₀ (1 * tj j)) (R / 2))).ncard : ℝ))
      + ∑ j ∈ Finset.range K, ((zerosIn f (closedBall (pt σ₀ ((-1) * tj j)) (R / 2))).ncard : ℝ) := by
    rw [hC₀]; exact_mod_cast hnat
  have hKb := mul_le_mul_of_nonneg_right hKle hb0
  have hmain : ((zerosIn f (band a σ₀ T)).ncard : ℝ)
      ≤ C₀ + 2 * (2 * T) * ((D + N * L) / Real.log 2) := by linarith
  have hTL : 2 * Real.log 2 ≤ T * L := by nlinarith
  calc ((zerosIn f (band a σ₀ T)).ncard : ℝ)
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

namespace RankinSelbergDelta.RankinSelberg

open Complex UpperHalfPlane MeasureTheory Set Filter RankinSelbergDelta.Eisenstein
open scoped Real Topology Modular

variable {F : Type*} [FunLike F ℍ ℂ] (k : ℤ)
  [cf : CuspFormClass F (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma 1)) k]

/-- `Gfull k f` is analytic at every point with `|Im s| ≥ 1`. -/
theorem analyticAt_Gfull_of_one_le_abs_im (f : F) (hk : 0 < k) {z : ℂ} (hz : 1 ≤ |z.im|) :
    AnalyticAt ℂ (Gfull k f) z := by
  have hz0 : z ≠ 0 := by
    intro h; rw [h, Complex.zero_im, abs_zero] at hz; linarith
  have hz1 : z ≠ 1 := by
    intro h; rw [h, Complex.one_im, abs_zero] at hz; linarith
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  filter_upwards [eventually_ne_nhds hz0, eventually_ne_nhds hz1] with w hw0 hw1
  exact differentiableAt_Gfull k f hk hw0 hw1

include cf in
/-- **The Riemann–von Mangoldt upper bound for the Rankin–Selberg square.** There is an abscissa
`σ₀ ≥ 2` (so that the band `0 ≤ Re s ≤ σ₀` contains the critical strip `0 ≤ Re s ≤ 1`, and
`G ≠ 0` on `Re s > 1` anyway) and a constant `K` with
`#{zeros of G in 0 ≤ Re s ≤ σ₀, 1 ≤ |Im s| ≤ T} ≤ K T log T` for all `T ≥ 2`. -/
theorem exists_ncard_zeros_Gfull_le_mul_log (f : F) (hk : 0 < k)
    (hf : IsHeckeEigenCoeffs (rsCoeff f) k) :
    ∃ σ₀ : ℝ, 2 ≤ σ₀ ∧ ∃ K : ℝ, ∀ T : ℝ, 2 ≤ T →
      ((RankinSelbergDelta.ZeroCount.zerosIn (Gfull k f) (RankinSelbergDelta.ZeroCount.band 0 σ₀ T)).ncard : ℝ)
        ≤ K * T * Real.log T := by
  obtain ⟨σ₀, hσ₀, hlow⟩ := exists_norm_Gfull_ge k f hk hf
  obtain ⟨C, N, hC, hgrow⟩ := exists_norm_Gfull_le_halfStrip k f hk (⌈σ₀⌉₊ + 1)
  refine ⟨σ₀, hσ₀, ?_⟩
  refine RankinSelbergDelta.ZeroCount.exists_ncard_band_le_mul_log (a := 0) (σ₀ := σ₀) (C := C)
    (c := 3 / 8) (N := N) (by linarith) hC
    (by norm_num : (0 : ℝ) < 3 / 8) (fun z hz => analyticAt_Gfull_of_one_le_abs_im k f hk hz)
    ?_ ?_
  · intro z hz hzim
    apply hgrow z _ hzim
    have := Nat.le_ceil σ₀
    push_cast
    linarith
  · intro t
    have hpt : RankinSelbergDelta.ZeroCount.pt σ₀ t = (σ₀ : ℂ) + Complex.I * t := by
      apply Complex.ext <;> simp [RankinSelbergDelta.ZeroCount.pt]
    rw [hpt]
    exact hlow t

end RankinSelbergDelta.RankinSelberg

/-! ### the prime side of the explicit formula.
On `Re s > 1`, `−G'/G(s) = ∑_{n ≥ 2} Λ_G(n) e^{−s log n}` with `Λ_G = rsVonMangoldt ≥ 0`, by termwise
differentiation of the log-series `G = exp(∑ dlvpTerm)` (`dlvpG_rs_eq`) on the open half-plane
`Re z > 1 + ε` (`hasDerivAt_tsum_of_isPreconnected`, majorant `(2/ε)‖dlvpTerm Λ (1 + ε/2) n‖`). This
is the side of the explicit formula that exists only because `G` has an Euler product. -/

namespace RankinSelbergDelta.RankinSelberg

open Complex UpperHalfPlane MeasureTheory Set Filter RankinSelbergDelta.Eisenstein
open scoped Real Topology Modular

variable {F : Type*} [FunLike F ℍ ℂ] (k : ℤ)
  [cf : CuspFormClass F (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma 1)) k]

/-- The summand of the von Mangoldt series of `G`: `Λ(n) e^{−s log n}` for `n ≥ 2`, `0` otherwise. -/
noncomputable def vmTerm (Λ : ℕ → ℝ) (s : ℂ) (n : ℕ) : ℂ :=
  if 2 ≤ n then (Λ n : ℂ) * Complex.exp (-(s * (Real.log n : ℂ))) else 0

/-- Termwise derivative of the log-series: `d/ds dlvpTerm Λ s n = −vmTerm Λ s n`. -/
lemma hasDerivAt_dlvpTerm (Λ : ℕ → ℝ) (n : ℕ) (z : ℂ) :
    HasDerivAt (fun w => dlvpTerm Λ w n) (-vmTerm Λ z n) z := by
  unfold dlvpTerm vmTerm
  split_ifs with hn
  · have hlog : (Real.log n : ℂ) ≠ 0 := by
      have : (0 : ℝ) < Real.log n := Real.log_pos (by exact_mod_cast hn)
      exact_mod_cast this.ne'
    have h := (((hasDerivAt_id' z).mul_const (Real.log n : ℂ)).neg.cexp).const_mul
      ((Λ n : ℂ) / (Real.log n : ℂ))
    convert h using 1
    simp only [Pi.neg_apply]
    field_simp
  · simpa using hasDerivAt_const z (0 : ℂ)

/-- The majorant: for `Re z ≥ 1 + ε`, `‖vmTerm Λ z n‖ ≤ (2/ε) ‖dlvpTerm Λ (1 + ε/2) n‖`. -/
lemma norm_vmTerm_le_majorant (Λ : ℕ → ℝ) (hΛ : ∀ n, 0 ≤ Λ n) {ε : ℝ} (hε : 0 < ε) {z : ℂ}
    (hz : 1 + ε ≤ z.re) (n : ℕ) :
    ‖vmTerm Λ z n‖ ≤ (2 / ε) * ‖dlvpTerm Λ ((1 + ε / 2 : ℝ) : ℂ) n‖ := by
  unfold vmTerm dlvpTerm
  split_ifs with hn
  · have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    have hlog : 0 < Real.log n := Real.log_pos hn1
    rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp, norm_div, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hΛ n), abs_of_pos hlog]
    have hre1 : (-(z * (Real.log n : ℂ))).re = -(z.re * Real.log n) := by
      rw [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    have hre2 : (-(((1 + ε / 2 : ℝ) : ℂ) * (Real.log n : ℂ))).re = -((1 + ε / 2) * Real.log n) := by
      rw [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
    rw [hre1, hre2]
    -- `log n · e^{−(ε/2) log n} ≤ 2/ε`
    set E : ℝ := Real.exp (ε / 2 * Real.log n) with hE
    have hEpos : 0 < E := Real.exp_pos _
    have hkey : Real.log n * Real.exp (-(ε / 2 * Real.log n)) ≤ 2 / ε := by
      have h2 : ε / 2 * Real.log n ≤ E - 1 := by
        have := Real.log_le_sub_one_of_pos hEpos
        rwa [hE, Real.log_exp] at this
      rw [Real.exp_neg, ← hE, ← div_eq_mul_inv, div_le_iff₀ hEpos]
      calc Real.log n = (ε / 2 * Real.log n) / (ε / 2) := by field_simp
        _ ≤ E / (ε / 2) := div_le_div_of_nonneg_right (by linarith) (by positivity)
        _ = 2 / ε * E := by field_simp
    have hsplit : Real.exp (-(z.re * Real.log n))
        ≤ Real.exp (-((1 + ε / 2) * Real.log n)) * Real.exp (-(ε / 2 * Real.log n)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [hlog.le]
    set A : ℝ := Real.exp (-((1 + ε / 2) * Real.log n)) with hA
    have hApos : 0 < A := Real.exp_pos _
    calc Λ n * Real.exp (-(z.re * Real.log n))
        ≤ Λ n * (A * Real.exp (-(ε / 2 * Real.log n))) :=
          mul_le_mul_of_nonneg_left hsplit (hΛ n)
      _ ≤ Λ n * (A * ((2 / ε) / Real.log n)) := by
          apply mul_le_mul_of_nonneg_left _ (hΛ n)
          apply mul_le_mul_of_nonneg_left _ hApos.le
          rw [le_div_iff₀ hlog]
          linarith [hkey]
      _ = 2 / ε * (Λ n / Real.log n * A) := by field_simp
  · simp

include cf in
/-- **The prime side of the explicit formula.** On `Re s > 1`,
`logDeriv G s = −∑' n, vmTerm Λ_G s n`, i.e. `−G'/G(s) = ∑_{n ≥ 2} Λ_G(n) e^{−s log n}` with
`Λ_G = rsVonMangoldt (rsCoeff f) k ≥ 0` (`rsVonMangoldt_nonneg`). -/
theorem logDeriv_Gfull_eq_neg_tsum (f : F) (hk : 0 < k) (hf : IsHeckeEigenCoeffs (rsCoeff f) k)
    {s : ℂ} (hs : 1 < s.re) :
    logDeriv (Gfull k f) s = -∑' n, vmTerm (rsVonMangoldt (rsCoeff f) k) s n := by
  set Λ := rsVonMangoldt (rsCoeff f) k with hΛdef
  have hΛ : ∀ n, 0 ≤ Λ n := rsVonMangoldt_nonneg _ _
  set ε : ℝ := (s.re - 1) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  set t : Set ℂ := {z | 1 + ε < z.re} with ht
  have htopen : IsOpen t := isOpen_lt continuous_const Complex.continuous_re
  have htconn : IsPreconnected t :=
    (convex_halfSpace_gt RankinSelbergDelta.ZeroCount.isLinearMap_re (1 + ε)).isPreconnected
  have hst : s ∈ t := by show 1 + ε < s.re; rw [hε]; linarith
  have hmaj : Summable fun n => (2 / ε) * ‖dlvpTerm Λ ((1 + ε / 2 : ℝ) : ℂ) n‖ :=
    (summable_norm_iff.mpr (summable_dlvpTerm_rs k f hk hf (s := ((1 + ε / 2 : ℝ) : ℂ))
      (by simp only [Complex.ofReal_re]; linarith))).mul_left _
  have hL : HasDerivAt (fun z => ∑' n, dlvpTerm Λ z n) (∑' n, -vmTerm Λ s n) s :=
    hasDerivAt_tsum_of_isPreconnected hmaj htopen htconn (fun n z _ => hasDerivAt_dlvpTerm Λ n z)
      (fun n z hz => by
        rw [norm_neg]
        exact norm_vmTerm_le_majorant Λ hΛ hεpos (le_of_lt hz) n)
      hst (summable_dlvpTerm_rs k f hk hf hs) hst
  have hGeq : Gfull k f =ᶠ[𝓝 s] fun z => Complex.exp (∑' n, dlvpTerm Λ z n) := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (show s ∈ {z : ℂ | 1 < z.re} from hs)] with z hz
    rw [Gfull_eq k f hk hz, ← dlvpG_rs_eq k f hk hf hz]
    rfl
  have hexp : HasDerivAt (fun z => Complex.exp (∑' n, dlvpTerm Λ z n))
      (Complex.exp (∑' n, dlvpTerm Λ s n) * ∑' n, -vmTerm Λ s n) s := hL.cexp
  rw [logDeriv_apply, hGeq.deriv_eq, hGeq.eq_of_nhds, hexp.deriv, tsum_neg]
  field_simp

end RankinSelbergDelta.RankinSelberg
