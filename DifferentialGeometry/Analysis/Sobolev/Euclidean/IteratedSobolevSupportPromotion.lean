import DifferentialGeometry.Analysis.Sobolev.Euclidean.Density
import DifferentialGeometry.Analysis.Sobolev.Euclidean.MultiplyQuantK

/-!
# Support-aware interior-to-global promotion for iterated Euclidean Sobolev membership

The σ-compact patching file shows that, without a support hypothesis, local
`W^{k,p}` membership on every precompact interior subdomain does **not** imply
global `W^{k,p}` membership for `k ≥ 1`: the iterated weak partials can fail to
be globally `L^p` (the concrete obstruction is `d = 1`, `p = 2`,
`Ω = (0, 1)`, `u(x) = x^(-0.2)`).

This file supplies the structural input that makes the promotion go through:
the function is *essentially supported in a compact subset* `K` of the
precompact subdomain. Concretely, if

* `u` lies in `W^{k,p}` on a precompact open subdomain `Ω'` with
  `closure Ω' ⊆ Ω`,
* `u` is globally `L^p` on `Ω`, and
* `u` vanishes almost everywhere off a compact subset `K ⊆ Ω'`,

then `u` lies in `W^{k,p}` on the whole of `Ω`.

The proof multiplies `u` by a smooth cutoff `χ` that equals `1` on a
neighbourhood of `K` and is compactly supported inside `Ω'`. The product
`χ · u` is `W^{k,p}` on `Ω'` (smooth-multiplier closure), has compact support
inside `Ω'`, and is almost everywhere equal to `u` on `Ω` (because `u` is
almost everywhere zero where `χ` differs from `1`). Extension by zero and a.e.
invariance then deliver the global membership.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Euclidean

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- **Support-aware interior-to-global promotion for `MemWkp`.**

If `u` is iterated-Sobolev regular (`W^{k,p}`) on a precompact open subdomain
`Ω'` with `closure Ω' ⊆ Ω`, is globally `L^p` on `Ω`, and vanishes almost
everywhere off a compact subset `K ⊆ Ω'`, then `u` is iterated-Sobolev regular
on the whole domain `Ω`.

Mathematically, `u` is essentially supported in `K`; multiplying by a smooth
cutoff that equals `1` near `K` and is compactly supported inside `Ω'` produces
a compactly supported `W^{k,p}(Ω')` function almost everywhere equal to `u` on
`Ω`. Extension by zero then yields the global membership. -/
theorem MemWkp_of_memWkp_precompact_of_ae_zero_off_compact
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ⊤)
    {Ω Ω' K : Set E} {u : E → ℝ}
    (hΩ_open : IsOpen Ω) (hΩ'_open : IsOpen Ω')
    (hK_compact : IsCompact K) (hKΩ' : K ⊆ Ω')
    (hΩ'_cl : closure Ω' ⊆ Ω)
    (_hu_global_Lp : MemLp u p ((volume : Measure E).restrict Ω))
    (hu_ae_zero : u =ᵐ[(volume : Measure E).restrict (Ω \ K)] 0)
    (hu_precompact : MemWkp (d := d) k p u Ω') :
    MemWkp (d := d) k p u Ω := by
  classical
  -- `Ω' ⊆ Ω` follows from `closure Ω' ⊆ Ω`.
  have hΩ'Ω : Ω' ⊆ Ω := subset_closure.trans hΩ'_cl
  -- A smooth cutoff `χ`, equal to `1` on a neighbourhood `cthickening δ K` of
  -- `K`, compactly supported with `tsupport χ ⊆ Ω'`.
  obtain ⟨δ, χ, hδ_pos, _hδ_sub, hχ_smooth, hχ_compact, _hχ_range,
      hχ_one, hχ_supp⟩ :=
    exists_smooth_cutoff_with_neighborhood (d := d) hK_compact hΩ'_open hKΩ'
  -- `cthickening δ K` is a closed (hence measurable) neighbourhood of `K`.
  set N : Set E := Metric.cthickening δ K with hN_def
  have hN_closed : IsClosed N := Metric.isClosed_cthickening
  have hN_meas : MeasurableSet N := hN_closed.measurableSet
  have hK_sub_N : K ⊆ N := Metric.self_subset_cthickening K
  -- The cutoff product `χ · u`.
  set v : E → ℝ := fun x => χ x * u x with hv_def
  -- Step 1: `χ · u` is `W^{k,p}` on `Ω'`.
  -- A smooth compactly supported function has uniformly bounded iterated
  -- derivatives up to any finite order.
  obtain ⟨C, _hC_nn, hC_bound⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport (d := d)
      hχ_smooth hχ_compact k
  have hv_memWkp_Ω' : MemWkp (d := d) k p v Ω' :=
    MemWkp.smul_smooth_bounded (d := d) k hp hΩ'_open hχ_smooth
      (fun j _hj x _hx => hC_bound x j _hj) hu_precompact
  -- Step 2: `χ · u` has topological support inside `Ω'` and is compactly
  -- supported.
  have hv_tsupp : tsupport v ⊆ Ω' :=
    (tsupport_smul_subset_left χ u).trans hχ_supp
  have hv_compact : HasCompactSupport v := hχ_compact.mul_right
  -- Step 3: `χ · u` is `W^{k,p}` on `Ω` by extension by zero.
  have hv_memWkp_Ω : MemWkp (d := d) k p v Ω :=
    MemWkp.extend_zero (d := d) hp hp_top hΩ'_open hΩ_open hΩ'Ω
      hv_memWkp_Ω' hv_tsupp hv_compact
  -- Step 4: `χ · u` is almost everywhere equal to `u` on `Ω`.
  -- On `Ω ∩ N` the cutoff equals `1`; on `Ω \ N ⊆ Ω \ K` the function `u`
  -- vanishes almost everywhere, hence so does `χ · u`.
  have hv_ae_eq_u : v =ᵐ[(volume : Measure E).restrict Ω] u := by
    have h_split : Ω = (Ω ∩ N) ∪ (Ω \ N) := by
      rw [Set.inter_union_diff]
    have h_on_inter : v =ᵐ[(volume : Measure E).restrict (Ω ∩ N)] u := by
      refine (ae_restrict_iff' (hΩ_open.measurableSet.inter hN_meas)).mpr ?_
      refine Filter.Eventually.of_forall fun x hx => ?_
      have hxN : x ∈ N := hx.2
      simp only [hv_def, hχ_one x hxN, one_mul]
    have h_on_diff : v =ᵐ[(volume : Measure E).restrict (Ω \ N)] u := by
      -- `Ω \ N ⊆ Ω \ K`, so `u` is a.e. zero on `Ω \ N`.
      have h_sub : Ω \ N ⊆ Ω \ K := Set.diff_subset_diff_right hK_sub_N
      have hu_zero_diff : u =ᵐ[(volume : Measure E).restrict (Ω \ N)] 0 :=
        hu_ae_zero.filter_mono
          (ae_mono (Measure.restrict_mono_set volume h_sub))
      -- Where `u` is zero, `χ · u` is zero, hence equal to `u`.
      filter_upwards [hu_zero_diff] with x hx
      simp only [hv_def, hx, Pi.zero_apply, mul_zero]
    have h_union : v =ᵐ[(volume : Measure E).restrict ((Ω ∩ N) ∪ (Ω \ N))] u := by
      rw [Filter.EventuallyEq, ae_restrict_union_eq]
      exact ⟨h_on_inter, h_on_diff⟩
    rwa [← h_split] at h_union
  -- Step 5: transfer the global membership from `χ · u` back to `u`.
  exact (MemWkp_congr_ae (d := d) hp hΩ_open hv_ae_eq_u).mp hv_memWkp_Ω

end Euclidean
end Sobolev
end Analysis
end DifferentialGeometry
