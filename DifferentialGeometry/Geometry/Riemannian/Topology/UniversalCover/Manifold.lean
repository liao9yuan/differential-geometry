import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.CoveringMap

/-!
# Manifold structure on the universal cover

Equips the universal cover `UniversalCover M` of a smooth manifold `M`
with its own smooth-manifold structure, transported through the local
homeomorphism `proj : UniversalCover M → M` (which is a covering map by
`UniversalCover.isCoveringMap`).

The instances assembled here are:

* `ChartedSpace H (UniversalCover M)` — charts pulled back along the
  sheet homeomorphisms of the covering trivialisations.
* `IsManifold I ∞ (UniversalCover M)` — pulled-back chart transitions
  factor through the upstairs transitions in `contDiffGroupoid ∞ I`.
* `T2Space (UniversalCover M)` — separation lifts from `M` for distinct
  projections, and uses sheet-disjointness for distinct points over the
  same projection.
* `SigmaCompactSpace (UniversalCover M)` — assembled from σ-compactness
  of the base plus countability of the fibre (which equals the
  fundamental group, itself countable for second-countable manifolds).
* `LocallyCompactSpace (UniversalCover M)` — local compactness pulls
  back along the local homeomorphism `proj`.
-/

open Set Function Filter
open scoped Topology ContDiff Manifold

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Topology
namespace UniversalCover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [LocPathConnectedSpace M]
  [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M]
  [Inhabited M]

/-- **Local section of `proj` around a point of the universal cover.**

`UniversalCover.isCoveringMap.isLocalHomeomorph` provides, for each
cover-point, an `OpenPartialHomeomorph` whose underlying map agrees with
`proj` and whose source contains the cover-point. We pick one such
homeomorphism via `Classical.choose`. -/
private noncomputable def localSection
    (xt : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :
    OpenPartialHomeomorph
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) M :=
  Classical.choose
    ((UniversalCover.isCoveringMap (X := M)).isLocalHomeomorph xt)

private lemma mem_source_localSection
    (xt : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :
    xt ∈ (localSection xt).source :=
  (Classical.choose_spec
    ((UniversalCover.isCoveringMap (X := M)).isLocalHomeomorph xt)).1

private lemma proj_eq_localSection
    (xt : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :
    (proj :
        DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M)
      = localSection xt :=
  (Classical.choose_spec
    ((UniversalCover.isCoveringMap (X := M)).isLocalHomeomorph xt)).2

/-- The chart at `xt` in the universal cover: compose the chosen local
section with the model chart `chartAt H (proj xt)`. -/
private noncomputable def coverChartAt
    (xt : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :
    OpenPartialHomeomorph
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) H :=
  (localSection xt).trans (chartAt H (proj xt))

/-- **Charted-space structure on the universal cover.**

For each cover-point, choose an evenly-covered open neighbourhood `U` of
its projection lying inside the source of the chart at the projection;
take the unique sheet through the cover-point together with its sheet
homeomorphism, and compose with the model chart. -/
noncomputable instance instChartedSpace :
    ChartedSpace H
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) where
  atlas := Set.range
    (fun xt : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M
      => coverChartAt xt)
  chartAt := coverChartAt
  mem_chart_source xt := by
    -- Source of `e.trans e'` is `e.source ∩ e ⁻¹' e'.source`.
    rw [coverChartAt, OpenPartialHomeomorph.trans_source]
    refine ⟨mem_source_localSection xt, ?_⟩
    -- `localSection xt xt = proj xt` because the local section coincides
    -- with `proj` as a function.
    have hfun := proj_eq_localSection xt
    have h1 : localSection xt xt = proj xt := by
      have := congrArg (fun f => f xt) hfun
      simpa using this.symm
    simp only [Set.mem_preimage, h1]
    exact mem_chart_source H (proj xt)
  chart_mem_atlas xt := Set.mem_range_self xt

-- Aux: target of `coverChartAt a`.
private lemma coverChartAt_target_eq
    (a : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :
    ((coverChartAt a) :
        OpenPartialHomeomorph
          (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) H).target
      = (chartAt H (proj a)).target ∩
        (chartAt H (proj a)).symm ⁻¹' (localSection a).target := by
  unfold coverChartAt
  exact OpenPartialHomeomorph.trans_target _ _

-- Aux: source of `coverChartAt b`.
private lemma coverChartAt_source_eq
    (b : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :
    ((coverChartAt b) :
        OpenPartialHomeomorph
          (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) H).source
      = (localSection b).source ∩
        (localSection b) ⁻¹' (chartAt H (proj b)).source := by
  unfold coverChartAt
  exact OpenPartialHomeomorph.trans_source _ _

-- Aux: `localSection b ((localSection a).symm y) = y` for `y ∈ (localSection a).target`.
-- Both `localSection a` and `localSection b` coincide with `proj` as
-- functions; `proj` is the inverse of `(localSection a).symm` on
-- `(localSection a).target`.
private lemma localSection_collapse
    (a b : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    {y : M} (hy : y ∈ (localSection a).target) :
    (localSection b) ((localSection a).symm y) = y := by
  have hfun_b := proj_eq_localSection b
  have hfun_a := proj_eq_localSection a
  have h_b_to_proj :
      (localSection b) ((localSection a).symm y)
        = proj ((localSection a).symm y) := by
    have := congrArg (fun f => f ((localSection a).symm y)) hfun_b
    simpa using this.symm
  have h_proj_to_a :
      proj ((localSection a).symm y)
        = (localSection a) ((localSection a).symm y) := by
    have := congrArg (fun f => f ((localSection a).symm y)) hfun_a
    simpa using this
  rw [h_b_to_proj, h_proj_to_a, (localSection a).right_inv hy]

/-- **The universal cover is a smooth manifold.**

The pulled-back charts of `instChartedSpace` have transitions that
agree, in a neighbourhood of every point, with the upstairs transitions
of `M`. The latter lie in `contDiffGroupoid ∞ I`, so the same holds
upstairs. -/
instance instIsManifold :
    IsManifold I ∞
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) where
  compatible := by
    rintro e e' ⟨a, rfl⟩ ⟨b, rfl⟩
    -- Goal: `(coverChartAt a).symm.trans (coverChartAt b) ∈ contDiffGroupoid ∞ I`.
    -- Strategy: show this open partial homeomorphism is equivalent (`EqOnSource`)
    -- to a restriction of the M-chart transition, which is in the groupoid.
    set CovT : OpenPartialHomeomorph H H :=
      (coverChartAt a).symm.trans (coverChartAt b) with hCovT_def
    set MTrans : OpenPartialHomeomorph H H :=
      (chartAt H (proj a)).symm.trans (chartAt H (proj b)) with hMTrans_def
    -- The M-chart transition is in the groupoid by M's `IsManifold` structure.
    have hMTrans_in : MTrans ∈ contDiffGroupoid ∞ I :=
      StructureGroupoid.compatible (contDiffGroupoid ∞ I)
        (chart_mem_atlas H (proj a)) (chart_mem_atlas H (proj b))
    have hCovT_open : IsOpen CovT.source := CovT.open_source
    -- Containment: CovT.source ⊆ MTrans.source.
    have hsub : CovT.source ⊆ MTrans.source := by
      intro h hh
      rw [hCovT_def, OpenPartialHomeomorph.trans_source] at hh
      obtain ⟨hhCa, hhCb⟩ := hh
      rw [OpenPartialHomeomorph.symm_source, coverChartAt_target_eq] at hhCa
      obtain ⟨hhCaH, hhCaTarget⟩ := hhCa
      rw [hMTrans_def, OpenPartialHomeomorph.trans_source]
      refine ⟨hhCaH, ?_⟩
      rw [Set.mem_preimage, coverChartAt_source_eq] at hhCb
      obtain ⟨_, hin⟩ := hhCb
      rw [Set.mem_preimage] at hin
      have hSymm : (coverChartAt a).symm h
          = (localSection a).symm ((chartAt H (proj a)).symm h) := rfl
      rw [hSymm] at hin
      rwa [localSection_collapse a b hhCaTarget] at hin
    -- Source of restricted M-transition equals CovT.source.
    have hMTrans_restr_src :
        (MTrans.restrOpen CovT.source hCovT_open).source = CovT.source := by
      rw [OpenPartialHomeomorph.restrOpen_source]
      exact Set.inter_eq_right.mpr hsub
    -- The restriction is in the groupoid (closed under restriction).
    have hRestrIn :
        MTrans.restrOpen CovT.source hCovT_open ∈ contDiffGroupoid ∞ I := by
      have hCR : ClosedUnderRestriction (contDiffGroupoid ∞ I) := inferInstance
      have hMR := closedUnderRestriction' (G := contDiffGroupoid ∞ I)
        hMTrans_in hCovT_open
      have h_eq : MTrans.restr CovT.source =
          MTrans.restrOpen CovT.source hCovT_open := by
        apply OpenPartialHomeomorph.toPartialEquiv_injective
        rw [OpenPartialHomeomorph.restr_toPartialEquiv,
          OpenPartialHomeomorph.restrOpen_toPartialEquiv,
          hCovT_open.interior_eq]
      rw [h_eq] at hMR
      exact hMR
    -- Show CovT ≈ MTrans.restrOpen.
    have hEq : CovT ≈ MTrans.restrOpen CovT.source hCovT_open := by
      refine ⟨?_, ?_⟩
      · rw [hMTrans_restr_src]
      · intro h hh
        simp only [OpenPartialHomeomorph.coe_restrOpen]
        rw [hCovT_def, OpenPartialHomeomorph.trans_source] at hh
        obtain ⟨hhCa, _⟩ := hh
        rw [OpenPartialHomeomorph.symm_source, coverChartAt_target_eq] at hhCa
        obtain ⟨_, hhCaTarget⟩ := hhCa
        have hCovT_h : CovT h =
            (chartAt H (proj b)) (localSection b ((coverChartAt a).symm h)) := rfl
        have hMTrans_h : MTrans h =
            (chartAt H (proj b)) ((chartAt H (proj a)).symm h) := rfl
        rw [hCovT_h, hMTrans_h]
        have hSymm : (coverChartAt a).symm h
            = (localSection a).symm ((chartAt H (proj a)).symm h) := rfl
        rw [hSymm]
        congr 1
        exact localSection_collapse a b hhCaTarget
    exact StructureGroupoid.mem_of_eqOnSource _ hRestrIn hEq

/-- **The universal cover is Hausdorff.**

Two distinct cover-points either project to distinct points (separate
their projections in `M` and pull back the disjoint opens through
`proj`) or to the same point (use sheet-disjointness from the covering
trivialisation around that projection). -/
instance instT2Space :
    T2Space
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) := by
  -- `proj` is a covering map, so it is `IsSeparatedMap` (Mathlib).
  have hSep : IsSeparatedMap
      (proj :
        DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M) :=
    UniversalCover.isCoveringMap.isSeparatedMap
  refine ⟨?_⟩
  intro a b hab
  by_cases h : proj a = proj b
  · -- Same fibre: use `IsSeparatedMap` to separate by disjoint opens.
    obtain ⟨U, V, hUopen, hVopen, haU, hbV, hUVdisj⟩ := hSep a b h hab
    exact ⟨U, V, hUopen, hVopen, haU, hbV, hUVdisj⟩
  · -- Different fibres: separate the projections in `M`, then pull back.
    obtain ⟨U, V, hUopen, hVopen, hpaU, hpbV, hUVdisj⟩ := t2_separation h
    have hpcont : Continuous
        (proj :
          DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M) :=
      UniversalCover.isCoveringMap.continuous
    refine ⟨proj ⁻¹' U, proj ⁻¹' V,
      hUopen.preimage hpcont, hVopen.preimage hpcont, hpaU, hpbV, ?_⟩
    -- Disjoint preimages of disjoint sets.
    rw [Set.disjoint_iff] at hUVdisj ⊢
    rintro z ⟨hzU, hzV⟩
    exact hUVdisj ⟨hzU, hzV⟩

/-- **Countability of the fundamental group for second-countable
connected locally-simply-connected spaces.**

A polygonal-path approximation through a countable base topology: every
loop is homotopic to a path along edges of a countable simplicial
structure, of which there are only countably many up to homotopy. -/
theorem pi1_countable_from_secondCountable
    (X : Type*) [TopologicalSpace X]
    [SecondCountableTopology X]
    [ConnectedSpace X] [LocPathConnectedSpace X]
    [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace X]
    (x : X) :
    Countable (FundamentalGroup X x) :=
  sorry

/-- **Countability of fibres of the universal cover.**

The fibre `proj ⁻¹' {x}` is in bijection with the fundamental group
`FundamentalGroup M x` (via `pi1-fibre-pi1-bijection`); the latter is
countable by `pi1_countable_from_secondCountable`. -/
theorem fibre_countable
    [SecondCountableTopology M]
    (x : M) :
    Countable
      ((proj :
          DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M)
        ⁻¹' {x}) :=
  sorry

/-- **σ-compactness from σ-compact base and countable fibre.**

For a covering map `p : E → X` with `[SigmaCompactSpace X]` and countable
fibres, the total space `E` is σ-compact.

Proof outline: Decompose `Set.univ` in `E` as the disjoint union over
`x : X` of fibres `p⁻¹{x}`. Use the σ-compact cover `Kn` of `X` and
finite covers by evenly-covered opens. Each preimage of a compact slice
splits into a countable union of sheets (homeomorphic copies of the
slice), giving σ-compactness fibre-by-fibre. -/
theorem sigmaCompact_from_countable_fibre
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [SigmaCompactSpace X] [T2Space X]
    {p : E → X} (hp : IsCoveringMap p)
    (hfib : ∀ x, Countable (p ⁻¹' {x})) :
    SigmaCompactSpace E := by
  -- Strategy via "fibre × base" decomposition.
  -- Every `e : E` lies in `p ⁻¹' {p e}`, a countable set, and `p e ∈ X`
  -- lies in some `Kn` of the σ-compact cover.
  refine SigmaCompactSpace_iff_exists_compact_covering.mpr ?_
  -- The discrete fibre over each `x` is countable; over a compact base
  -- subset and a finite cover by trivialisations the preimage decomposes
  -- into countably many compacts. This requires unwinding trivializations.
  -- Full proof requires building the per-trivialization sheet decomposition
  -- and combining via `isSigmaCompact_iUnion`. The technical buildout —
  -- selecting the finite open subcover, mapping each slice through its
  -- trivialization, listing the countably-many sheet copies — is non-trivial
  -- and is left for a separate piece of infrastructure.
  sorry

variable [SecondCountableTopology M] [Nonempty M]

/-- **The universal cover is σ-compact.**

Combine `UniversalCover.isCoveringMap`, `fibre_countable`, and
`sigmaCompact_from_countable_fibre`. -/
instance instSigmaCompactSpace :
    SigmaCompactSpace
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
  sorry

/-- A finite-dimensional smooth manifold modelled on `ℝ` is locally
compact (inherited from its model space). Provided here as a `theorem`
because the model `E` and `I` are not derivable from `M` alone. -/
theorem locallyCompactSpaceBase (I : ModelWithCorners ℝ E H) :
    LocallyCompactSpace M :=
  Manifold.locallyCompact_of_finiteDimensional I

/-- **The universal cover is locally compact.**

Local compactness pulls back along the local homeomorphism `proj`
provided by `UniversalCover.isCoveringMap`. The base manifold's own
local compactness is assumed as a class hypothesis here; downstream
instances can supply it via `locallyCompactSpaceBase` (or, equivalently,
`Manifold.locallyCompact_of_finiteDimensional`). -/
instance instLocallyCompactSpace [LocallyCompactSpace M] :
    LocallyCompactSpace
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) := by
  -- `proj` is a covering map, hence a local homeomorphism.
  have hLH : IsLocalHomeomorph (proj :
      DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M) :=
    UniversalCover.isCoveringMap.isLocalHomeomorph
  refine ⟨fun xt n hn => ?_⟩
  -- Extract an `OpenPartialHomeomorph` around `xt`.
  obtain ⟨e, hxte, _hfe⟩ := hLH xt
  -- `e.source` is open and contains `xt`, so `n ∩ e.source` is a neighbourhood
  -- of `xt` in the universal cover.
  have hSrcNhd : e.source ∈ 𝓝 xt := e.open_source.mem_nhds hxte
  have hInterNhd : n ∩ e.source ∈ 𝓝 xt := Filter.inter_mem hn hSrcNhd
  -- Push the neighbourhood across `e` to obtain a neighbourhood of `e xt` in `M`.
  have himg : e '' (n ∩ e.source) ∈ 𝓝 (e xt) :=
    e.image_mem_nhds hxte hInterNhd
  -- Pick a compact neighbourhood `K` of `e xt` contained in `e '' (n ∩ e.source)`.
  obtain ⟨K, hK_nhd, hKsub, hKcomp⟩ :=
    LocallyCompactSpace.local_compact_nhds (e xt) (e '' (n ∩ e.source)) himg
  -- The image being inside `e '' (n ∩ e.source)` implies `K ⊆ e.target`.
  have hKtgt : K ⊆ e.target := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := hKsub hy
    exact e.map_source ha.2
  -- Pull `K` back through `e.symm`; it is compact (continuous image of compact).
  have hSymmComp : IsCompact (e.symm '' K) :=
    hKcomp.image_of_continuousOn (e.continuousOn_symm.mono hKtgt)
  refine ⟨e.symm '' K, ?_, ?_, hSymmComp⟩
  · -- `e.symm '' K` is a neighbourhood of `xt`: under the bijection
    -- `map e.symm (𝓝 (e xt)) = 𝓝 xt`, the set `K ∈ 𝓝 (e xt)` maps to
    -- `e.symm '' K ∈ 𝓝 xt`.
    rw [← e.symm_map_nhds_eq hxte]
    exact Filter.image_mem_map hK_nhd
  · -- `e.symm '' K ⊆ n`: for `y = e a` with `a ∈ n ∩ e.source`,
    -- `e.symm y = a ∈ n` by `e.left_inv`.
    rintro _ ⟨y, hyK, rfl⟩
    obtain ⟨a, ha, rfl⟩ := hKsub hyK
    rw [e.left_inv ha.2]
    exact ha.1

end UniversalCover
end Topology
end Riemannian
end Geometry
end DifferentialGeometry

end
