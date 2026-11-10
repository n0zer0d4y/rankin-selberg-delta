import Mathlib

/-!
# The simple pole of ζ at s = 1, as a residue limit

`(s − 1) ζ(s) → 1` on the punctured neighbourhood of `1`, from Mathlib's
`tendsto_riemannZeta_sub_one_div`. This is the form of the pole hypothesis used by the abstract
de la Vallée Poussin theorem (`trs_ne_zero`, `dlvpG_ne_zero`), checked here on ζ.
-/
namespace RankinSelbergDelta.Continuation

open Complex Filter Topology

/-- **ζ has a simple pole at s = 1 with residue 1**. The residue limit
    `(s − 1)·ζ(s) → 1` on the punctured neighbourhood of 1, from Mathlib's
    `tendsto_riemannZeta_sub_one_div`. This is the H2 hypothesis (`hres`) of `dlvpG_ne_zero` /
    `trs_ne_zero` for `G = riemannZeta`, `c = 1`. -/
theorem riemannZeta_residue_one :
    Tendsto (fun s : ℂ => (s - 1) * riemannZeta s) (𝓝[≠] (1 : ℂ)) (𝓝 1) := by
  have hb := tendsto_riemannZeta_sub_one_div
  have hsub : Tendsto (fun s : ℂ => s - 1) (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
    have h1 : Tendsto (fun s : ℂ => s - 1) (𝓝 (1 : ℂ)) (𝓝 ((1 : ℂ) - 1)) :=
      (continuous_sub_right (1 : ℂ)).tendsto (1 : ℂ)
    simpa using h1.mono_left nhdsWithin_le_nhds
  have hprod : Tendsto (fun s : ℂ => (s - 1) * (riemannZeta s - 1 / (s - 1)))
      (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
    simpa using hsub.mul hb
  have key : (fun s : ℂ => (s - 1) * riemannZeta s) =ᶠ[𝓝[≠] (1 : ℂ)]
      fun s => (s - 1) * (riemannZeta s - 1 / (s - 1)) + 1 := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
    field_simp
    ring
  rw [tendsto_congr' key]
  simpa using hprod.add_const 1

end RankinSelbergDelta.Continuation
