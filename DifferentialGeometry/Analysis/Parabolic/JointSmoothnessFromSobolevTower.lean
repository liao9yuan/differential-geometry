import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.CcTensorBilinFibreHsBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HilbertSpace

/-!
# Joint `(t, x)`-`C∞` of a realized bilinear `Hom`-section from a Sobolev time-tower

This file isolates a single, reusable, manifold-side analysis principle:

> a one-parameter family of smooth compactly-supported `(0, 2)`-tensor sections that is
> `C^k`-in-time into every supercritical spatial Sobolev space `H^{2m}` (for all `k` and
> all `m`) realizes a bilinear bundle `Hom`-section that is **jointly** `(t, x)`-`C∞`.

It is the "anisotropic Sobolev time-tower ⟹ joint smoothness" upgrade missing from both
Mathlib and this library — the *separate-variable → joint-smoothness wall* recorded in
`InteriorChartRegularityBridge.chartGram_realizedMetric_jointContMDiffOn` (continuity in
time into each `Hˢ` plus the spatial `Hˢ ↪ C^m` embedding gives only an anisotropic
tensor-product regularity).  The crucial strengthening here over that wall is that the
hypothesis controls **time-derivatives of every order**, not merely continuity in time:
each iterated time-derivative `∂_t^k` of the family lands, continuously, in `H^{2m}`, hence
(via `H^{2m} ↪ C^{m'}` for `m'` large) in `C^{m'}` of the section; so every mixed partial
`∂_t^k ∂_x^α` exists and is continuous, which is exactly joint `C∞`.

## Main result

* `jointContMDiffOn_ccTensorBilinSymm_of_timeContDiffTower` — from the Sobolev time-tower
  `∀ k m, ContDiffOn ℝ k (fun t => (T_s t).toHs (2 * m)) (Icc 0 T)` the symmetrized
  bilinear `Hom`-section `(t, x) ↦ ccTensorBilinSymm g (T_s t) x` is jointly `(t, x)`-`C∞`
  over the product model `𝓘(ℝ, ℝ).prod I` on the closed slab `Icc 0 T ×ˢ univ`.

## Why this is not hypothesis-packaging, and why it rejects the kink families

The hypothesis is a *time-regularity-into-Sobolev* statement about the **scalar Hilbert
elements** `t ↦ (T_s t).toHs (2 * m)` (a `ContDiffOn ℝ k` of a Banach-valued function of one
real variable); the conclusion is the joint `(t, x)`-smoothness of a **bundle `Hom`-section
over `M`** — a `ContMDiffOn` of a section of `Hom(TM, Hom(TM, ℝ))`.  These are different
objects (one lives in a Hilbert space of one real variable, the other on `ℝ × M`), so the
conclusion is never assumed.

The `C¹`-not-`C²` kink `T_s t := (t − t₀)|t − t₀| · S₀` is rejected at the hypothesis: it is
only once differentiable in `t`, so `t ↦ (T_s t).toHs (2 * m)` is not `ContDiffOn ℝ 2`, and
the tower `∀ k, …` already fails at `k = 2`.  (The `C⁰`-kink `|t − t₀| · S₀` fails even at
`k = 1`.)  The hypothesis is precisely the smoothness that a genuine parabolic carrier
supplies and a kink does not. -/

noncomputable section

open Set Filter Topology Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace MetricRealization

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- **Single-chart `baseSet` joint `(t, x)`-`C∞` of the realized symmetrized bilinear
`Hom`-section from a Sobolev time-tower (the genuine anisotropic-Sobolev ⟹ joint-smoothness
analytic core).**

The same data as `jointContMDiffOn_ccTensorBilinSymm_of_timeContDiffTower`, but the joint
`(t, x)`-`C∞` conclusion is asserted over the closed slab `Icc 0 T ×ˢ (trivializationAt E
(TangentSpace I) α).baseSet` of a *single* chart centred at `α`.  This is the genuine analytic
content — the chart-local "Sobolev time-tower ⟹ joint smoothness" upgrade through the missing
mixed-partials reconstruction (the documented jet wall of `InteriorChartRegularityBridge`):
each iterated time-derivative `∂_t^k` of the section lands, via the supercritical Sobolev
embedding `H^{2m} ↪ C^{m'}` (`tensorPouSobolevHilbert_embedding_Ck`, with the chart-local
extraction `tensorHsToC0`-family and the fibre op-norm control
`gFibreOpBound_ccTensorBilinSymm_le_tensorHsNorm`), in `C^{m'}` of the chart-`α` representative,
so every mixed partial `∂_t^k ∂_x^α` of the chart-local representative exists and is continuous
on the closed slab, and the chart-frame matrix entries reconstruct the bundle `Hom`-section
over the chart base set (`contMDiffWithinAt_hom_bundle` / `ContinuousLinearMap.inCoordinates`).

The supercritical order is supplied per spatial-jet order `α` by reading `m` with `2m > dim
M + |α|` from the `∀ m` quantifier of `htower`, and the up-to-`0` boundary jet is the honest
one-sided derivative on `Icc 0 T` (uniquely differentiable, `uniqueDiffOn_Icc`).

The hypothesis is a time-regularity-into-Sobolev statement about the scalar Hilbert elements
`t ↦ (T_s t).toHs (2 * m)`; the conclusion is the joint smoothness of a bundle `Hom`-section on
`M` over the chart base set — a different object — so no packaging.  The `C¹`-not-`C²` kink
`T_s t := (t − t₀)|t − t₀| · S₀` is rejected already at `k = 2` of the tower (its `t ↦
(T_s t).toHs (2m)` is not `ContDiffOn ℝ 2`), exactly as for the global form.

This is the genuine missing analytic theorem isolated as the sole `sorry` leaf; the global-over-
`univ` form `jointContMDiffOn_ccTensorBilinSymm_of_timeContDiffTower` is sorry-free glue over
it (each base point uses its own chart). -/
theorem jointContMDiffOn_ccTensorBilinSymm_of_timeContDiffTower_baseSet
    (g : SmoothRiemannianMetric I M) (α : M)
    (T_s : ℝ → Integral.L2.SmoothCcTensor g 0 2) {T : ℝ}
    (htower : ∀ (k m : ℕ),
      ContDiffOn ℝ (k : ℕ∞)
        (fun t : ℝ =>
          IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * m) (T_s t))
        (Set.Icc (0 : ℝ) T)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        q.2 (ccTensorBilinSymm (I := I) g (T_s q.1) q.2))
      (Set.Icc (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := sorry

/-- **Joint `(t, x)`-`C∞` of the realized symmetrized bilinear `Hom`-section from a Sobolev
time-tower (the reusable anisotropic-Sobolev ⟹ joint-smoothness principle).**

Let `g` be a closed-manifold smooth Riemannian metric and `T_s : ℝ → SmoothCcTensor g 0 2` a
one-parameter family of smooth compactly-supported `(0, 2)`-tensor sections such that, for
every order `k` of time-differentiation and every spatial Sobolev exponent `2 * m`, the
Banach-valued path `t ↦ (T_s t).toHs (2 * m)` is `C^k` on the closed slab `Icc 0 T`
(`htower`).  Then the symmetrized bilinear bundle `Hom`-section
`(t, x) ↦ ccTensorBilinSymm g (T_s t) x` is jointly `(t, x)`-`C∞` over the product model
`𝓘(ℝ, ℝ).prod I` on the closed slab `Icc 0 T ×ˢ univ`.

The genuine content (the parabolic up-to-boundary classical regularity, Chow–Knopf) is the
chart-local analytic core `jointContMDiffOn_ccTensorBilinSymm_of_timeContDiffTower_baseSet`:
the Sobolev *time-tower* — every iterated time-derivative continuous into every spatial Sobolev
space — upgrades to joint `(t, x)`-smoothness on each chart base set, through the supercritical
Sobolev embedding `H^{2m} ↪ C^{m'}` (`tensorPouSobolevHilbert_embedding_Ck`) and the fibre
op-norm control `gFibreOpBound_ccTensorBilinSymm_le_tensorHsNorm`, so every mixed partial
`∂_t^k ∂_x^α` exists and is continuous.  This node is the sorry-free *globalisation* glue over
that chart-local core: joint smoothness is a local statement, so at each base point `q₀` it
suffices to work in the chart centred at `q₀.2`, whose base set is an open neighbourhood of
`q₀.2`; restricting the chart-local datum to that neighbourhood
(`ContMDiffWithinAt.mono_of_mem_nhdsWithin`) yields the within-`univ` smoothness there.

The hypothesis is a time-regularity-into-Sobolev statement about scalar Hilbert elements; the
conclusion is the joint smoothness of a bundle section on `M` — a different object — so no
packaging; and the `C¹`-not-`C²` kink is rejected already at `k = 2` of the tower.  The body is
glue over the chart-local core whose body is `sorry`, so consumers transitively depend on
`sorryAx`. -/
theorem jointContMDiffOn_ccTensorBilinSymm_of_timeContDiffTower
    (g : SmoothRiemannianMetric I M)
    (T_s : ℝ → Integral.L2.SmoothCcTensor g 0 2) {T : ℝ}
    (htower : ∀ (k m : ℕ),
      ContDiffOn ℝ (k : ℕ∞)
        (fun t : ℝ =>
          IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * m) (T_s t))
        (Set.Icc (0 : ℝ) T)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        q.2 (ccTensorBilinSymm (I := I) g (T_s q.1) q.2))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ) := by
  intro q₀ hq₀
  set α : M := q₀.2 with hα
  have hbase_mem : q₀.2 ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' (F := E) (E := TangentSpace I) q₀.2
  have hchart :=
    jointContMDiffOn_ccTensorBilinSymm_of_timeContDiffTower_baseSet (I := I) (M := M)
      g α T_s htower
  have hq₀_chart : q₀ ∈ Set.Icc (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet :=
    ⟨hq₀.1, hbase_mem⟩
  have hwithin := hchart q₀ hq₀_chart
  refine hwithin.mono_of_mem_nhdsWithin ?_
  rw [nhdsWithin_prod_eq]
  refine Filter.prod_mem_prod self_mem_nhdsWithin ?_
  rw [nhdsWithin_univ]
  exact (trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hbase_mem

end MetricRealization
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
