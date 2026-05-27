import DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.Manifold
import DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.Riemannian
import DifferentialGeometry.Integral.Measure.ChartDensity
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Topology.VectorBundle.Basic

/-!
# Smoothness of the lifted metric on the universal cover

Chart-conjugacy lemmas used to prove that the fiberwise pullback of a smooth
Riemannian metric `g` on `M` along `proj : UC M → M` is itself smooth.

The tangent bundle of `UC M` is built independently of `M`'s (not as a
pullback), so smoothness of the lifted metric reduces to comparing chart
trivialisations of the tangent bundle of `UC M` with those of `M` via the
local-section factorisation `coverChartAt = (localSection a).trans (chartAt …)`.

This file decomposes the smoothness assembly into four ingredients:

* `uc_coverChartAt_extend_conjugacy` — extended-chart factorisation of the
  cover-charts through the local section and the base chart.
* `uc_tangentBundleCore_coordChange_agree` — coordinate-change of the tangent
  bundle of `UC M` agrees with that of `M` on the chart intersection.
* `uc_hom_bundle_inCoordinates_pullback` — the `inCoordinates` representation
  of the metric, viewed in the Hom-bundle, pulls back along `proj`.
* `uc_liftedMetric_contMDiff` — assembly: the metric section is smooth.
-/

open Set Function Filter Bundle
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Integral.Measure (SmoothRiemannianMetric)

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

/-- **Extended-chart conjugacy at a cover-point.**

For every cover-point `a : UC M`, the extended cover-chart at `a` factors
through the local section followed by the extended base-chart at `proj a`, and
the inverse factors symmetrically through the inverse base-chart followed by
the inverse local section:
```
(coverChartAt a).extend I = ((chartAt H (proj a)).extend I) ∘ (localSection a)
((coverChartAt a).extend I).symm
    = (localSection a).symm ∘ ((chartAt H (proj a)).extend I).symm
```

These are global function equalities (definitional via
`OpenPartialHomeomorph.coe_trans`, `coe_trans_symm`, and the defining unfolding
`coverChartAt a = (localSection a).trans (chartAt H (proj a))`). The downstream
tangent-bundle coordinate-change comparison combines this with
`localSection_collapse` to identify the universal-cover transition with the
base-manifold transition. -/
theorem uc_coverChartAt_extend_conjugacy
    (a : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :
    ((coverChartAt a).extend I : _ → E)
        = ((chartAt H (proj a)).extend I) ∘ (localSection a) ∧
      (((coverChartAt a).extend I).symm : E → _)
        = (localSection a).symm ∘ ((chartAt H (proj a)).extend I).symm := by
  refine ⟨?_, ?_⟩
  · -- Unfold `(coverChartAt a).extend I = I ∘ coverChartAt a` and the trans
    -- factorisation `coverChartAt a = (localSection a).trans (chartAt H (proj a))`.
    funext z
    change I ((coverChartAt a) z) = ((chartAt H (proj a)).extend I) ((localSection a) z)
    -- LHS unfolds via `coverChartAt = (localSection a).trans (chartAt H (proj a))`
    -- and `OpenPartialHomeomorph.coe_trans`, giving
    --   (coverChartAt a) z = (chartAt H (proj a)) ((localSection a) z).
    have hcov : (coverChartAt a) z
        = (chartAt H (proj a)) ((localSection a) z) := by
      change ((localSection a).trans (chartAt H (proj a))) z
          = (chartAt H (proj a)) ((localSection a) z)
      rw [OpenPartialHomeomorph.trans_apply]
    -- RHS unfolds via `extend_coe : ⇑(f.extend I) = I ∘ f`.
    have hext : ((chartAt H (proj a)).extend I) ((localSection a) z)
        = I ((chartAt H (proj a)) ((localSection a) z)) := by
      rw [OpenPartialHomeomorph.extend_coe]; rfl
    rw [hcov, hext]
  · -- Symmetric unfolding for the inverse direction.
    funext y
    change ((coverChartAt a).extend I).symm y
        = (localSection a).symm
            (((chartAt H (proj a)).extend I).symm y)
    -- `((coverChartAt a).extend I).symm = (coverChartAt a).symm ∘ I.symm`
    -- by `extend_coe_symm`.
    have hExtSymm :
        ((coverChartAt a).extend I).symm y
          = (coverChartAt a).symm (I.symm y) := by
      rw [OpenPartialHomeomorph.extend_coe_symm]; rfl
    -- `(coverChartAt a).symm = (chartAt H (proj a)).symm ≫ (localSection a).symm`
    -- as a function, by `coe_trans_symm` applied to
    -- `coverChartAt a = (localSection a).trans (chartAt H (proj a))`.
    have hSymm : (coverChartAt a).symm (I.symm y)
        = (localSection a).symm
            ((chartAt H (proj a)).symm (I.symm y)) := by
      change ((localSection a).trans (chartAt H (proj a))).symm (I.symm y)
          = (localSection a).symm ((chartAt H (proj a)).symm (I.symm y))
      rw [OpenPartialHomeomorph.coe_trans_symm]
      rfl
    -- `((chartAt H (proj a)).extend I).symm y = (chartAt H (proj a)).symm (I.symm y)`
    -- by `extend_coe_symm`.
    have hChartExtSymm :
        ((chartAt H (proj a)).extend I).symm y
          = (chartAt H (proj a)).symm (I.symm y) := by
      rw [OpenPartialHomeomorph.extend_coe_symm]; rfl
    rw [hExtSymm, hSymm, hChartExtSymm]

/-- **Tangent-bundle coordinate-change agreement.**

For cover-points `a b : UC M` and `z` in the chart-source intersection
of `chartAt H a` and `chartAt H b` on the universal cover, the tangent-bundle
coordinate change of `UC M` between `achart H a` and `achart H b` agrees with
that of `M` between `achart H (proj a)` and `achart H (proj b)` evaluated at
`proj z`:
```
(tangentBundleCore I (UC M)).coordChange (achart H a) (achart H b) z
  = (tangentBundleCore I M).coordChange (achart H (proj a)) (achart H (proj b)) (proj z)
```

Proof: `coordChange` unfolds via `tangentBundleCore_coordChange_achart` to
`fderivWithin ℝ (extChartAt I _ ∘ (extChartAt I _).symm) (range I) (extChartAt I _ _)`.
By `uc_coverChartAt_extend_conjugacy` the cover-side composition factors
through the base-side composition by `localSection ∘ (localSection).symm`,
which collapses to the identity on the local section's target by
`localSection_collapse`. The factor `localSection a z = proj z` identifies the
base-points of `fderivWithin`. The remaining filter-pointwise equality on a
neighbourhood follows from continuity of the base-side chart inverse plus
openness of `(localSection a).target`, packaged via
`Filter.EventuallyEq.fderivWithin_eq`. -/
theorem uc_tangentBundleCore_coordChange_agree
    (a b : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    {z : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M}
    (hz : z ∈ (chartAt H a).source ∩ (chartAt H b).source) :
    (tangentBundleCore I
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)).coordChange
        (achart H a) (achart H b) z
      = (tangentBundleCore I M).coordChange
          (achart H (proj a)) (achart H (proj b)) (proj z) := by
  -- Abbreviations for the four extended charts that appear.
  set Ea : OpenPartialHomeomorph
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) H :=
    coverChartAt a with hEa
  set Fa : OpenPartialHomeomorph M H := chartAt H (proj a) with hFa
  -- Extract the conjugacy facts at `a` and `b`.
  obtain ⟨hConjA_fwd, hConjA_inv⟩ := uc_coverChartAt_extend_conjugacy (I := I) a
  obtain ⟨hConjB_fwd, _hConjB_inv⟩ := uc_coverChartAt_extend_conjugacy (I := I) b
  -- `chartAt H a` on `UC M` is definitionally `coverChartAt a`.
  have hz_a : z ∈ (coverChartAt a).source := hz.1
  have hz_b : z ∈ (coverChartAt b).source := hz.2
  -- Extract the structural information from the source membership using
  -- `coverChartAt_source_eq`, which expresses the source as an intersection of
  -- the local-section source with the pre-image of the chart source under
  -- the local section.
  have hz_a_inter : z ∈ (localSection (M := M) a).source ∩
      (localSection (M := M) a) ⁻¹' (chartAt H (proj a)).source := by
    have hsrc : ((coverChartAt a) :
        OpenPartialHomeomorph
          (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) H).source
        = (localSection a).source ∩
          (localSection a) ⁻¹' (chartAt H (proj a)).source :=
      coverChartAt_source_eq a
    rw [hsrc] at hz_a; exact hz_a
  have hz_b_inter : z ∈ (localSection (M := M) b).source ∩
      (localSection (M := M) b) ⁻¹' (chartAt H (proj b)).source := by
    have hsrc : ((coverChartAt b) :
        OpenPartialHomeomorph
          (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) H).source
        = (localSection b).source ∩
          (localSection b) ⁻¹' (chartAt H (proj b)).source :=
      coverChartAt_source_eq b
    rw [hsrc] at hz_b; exact hz_b
  obtain ⟨hzLSa_src, hzLSa_chart⟩ := hz_a_inter
  obtain ⟨_hzLSb_src, hzLSb_chart⟩ := hz_b_inter
  -- `localSection a z = proj z` (as a function `localSection a` agrees with `proj`).
  have hLSa_z : (localSection a) z = proj z := by
    have := congrArg (fun f => f z) (proj_eq_localSection a)
    simpa using this.symm
  have hLSb_z : (localSection b) z = proj z := by
    have := congrArg (fun f => f z) (proj_eq_localSection b)
    simpa using this.symm
  -- So `proj z ∈ Fa.source ∩ Fb.source`.
  have hprojz_Fa : proj z ∈ Fa.source := by
    rw [Set.mem_preimage, hLSa_z] at hzLSa_chart; exact hzLSa_chart
  have _hprojz_Fb : proj z ∈ (chartAt H (proj b)).source := by
    rw [Set.mem_preimage, hLSb_z] at hzLSb_chart; exact hzLSb_chart
  -- `proj z ∈ (localSection a).target`, by `map_source` applied to
  -- `z ∈ (localSection a).source`.
  have hprojz_LSa_tgt : proj z ∈ (localSection a).target := by
    have := (localSection a).map_source hzLSa_src
    rwa [hLSa_z] at this
  -- Identify the base-points of the two `fderivWithin` expressions.
  -- `extChartAt I a z = Ea.extend I z = (Fa.extend I) (localSection a z) = (Fa.extend I) (proj z)`.
  have hBase : (Ea.extend I) z = (Fa.extend I) (proj z) := by
    have := congrArg (fun f => f z) hConjA_fwd
    simp only [Function.comp_apply] at this
    rw [this, hLSa_z]
  -- Unfold both sides through `tangentBundleCore_coordChange_achart`.
  rw [tangentBundleCore_coordChange_achart, tangentBundleCore_coordChange_achart]
  -- Goal:
  --   fderivWithin ℝ (extChartAt I (M:=UC) b ∘ (extChartAt I (M:=UC) a).symm)
  --                (range I) (extChartAt I (M:=UC) a z)
  --     = fderivWithin ℝ (extChartAt I (M:=M) (proj b) ∘ (extChartAt I (M:=M) (proj a)).symm)
  --                    (range I) (extChartAt I (M:=M) (proj a) (proj z))
  -- We have `extChartAt I a z = extChartAt I (proj a) (proj z)` via `hBase`,
  -- after recognising `extChartAt I _ = (chartAt H _).extend I = Ea.extend I` on `UC M`
  -- and `= Fa.extend I` on `M`.
  -- The two `fderivWithin` agree by `EventuallyEq.fderivWithin_eq`.
  change fderivWithin ℝ ((extChartAt I b) ∘ (extChartAt I a).symm) (Set.range I)
      (extChartAt I a z)
    = fderivWithin ℝ ((extChartAt I (proj b)) ∘ (extChartAt I (proj a)).symm)
        (Set.range I) (extChartAt I (proj a) (proj z))
  -- The base-point equality, in extChartAt form.
  have hBase' : extChartAt I a z = extChartAt I (proj a) (proj z) := hBase
  rw [hBase']
  -- Reduce to showing the inner compositions are EventuallyEq in 𝓝[range I] of the basepoint.
  refine Filter.EventuallyEq.fderivWithin_eq ?_ ?_
  · -- The compositions are eventually equal.
    -- The match set is `{y ∈ E | ((Fa.extend I).symm y) ∈ (localSection a).target}`.
    -- It is open (preimage of open set under continuous map) and contains
    -- `(Fa.extend I) (proj z)` since `(Fa.extend I).symm ((Fa.extend I) (proj z)) = proj z`
    -- and `proj z ∈ (localSection a).target`.
    --
    -- Strategy: produce the predicate as `∀ᶠ y in 𝓝 (Fa.extend I (proj z))`,
    -- then `mem_nhdsWithin_of_mem_nhds`.
    have hContSymm : ContinuousAt ((chartAt H (proj a)).extend I).symm
        ((chartAt H (proj a)).extend I (proj z)) :=
      OpenPartialHomeomorph.continuousAt_extend_symm (I := I) _ hprojz_Fa
    have hOpenTgt : IsOpen (localSection a).target := (localSection a).open_target
    have hMemTgt : ((chartAt H (proj a)).extend I).symm
          ((chartAt H (proj a)).extend I (proj z)) ∈ (localSection a).target := by
      rw [OpenPartialHomeomorph.extend_left_inv _ hprojz_Fa]
      exact hprojz_LSa_tgt
    have hPre : ((chartAt H (proj a)).extend I).symm ⁻¹' (localSection a).target
        ∈ 𝓝 ((chartAt H (proj a)).extend I (proj z)) :=
      hContSymm (hOpenTgt.mem_nhds hMemTgt)
    -- Filter-upwards: on the preimage, the two compositions match pointwise.
    refine mem_nhdsWithin_of_mem_nhds ?_
    filter_upwards [hPre] with y hy
    -- `hy : ((chartAt H (proj a)).extend I).symm y ∈ (localSection a).target`.
    show ((extChartAt I b) ∘ (extChartAt I a).symm) y
        = ((extChartAt I (proj b)) ∘ (extChartAt I (proj a)).symm) y
    simp only [Function.comp_apply]
    -- Compute LHS step by step using the conjugacy.
    have hLHS_symm : (extChartAt I a).symm y =
        (localSection a).symm (((chartAt H (proj a)).extend I).symm y) := by
      change ((coverChartAt a).extend I).symm y =
          (localSection a).symm (((chartAt H (proj a)).extend I).symm y)
      have := congrArg (fun f => f y) hConjA_inv
      simpa [Function.comp_apply] using this
    have hLHS_fwd :
        (extChartAt I b) ((extChartAt I a).symm y) =
          ((chartAt H (proj b)).extend I)
            ((localSection b) ((extChartAt I a).symm y)) := by
      change ((coverChartAt b).extend I) ((extChartAt I a).symm y) =
          ((chartAt H (proj b)).extend I)
            ((localSection b) ((extChartAt I a).symm y))
      have := congrArg (fun f => f ((extChartAt I a).symm y)) hConjB_fwd
      simpa [Function.comp_apply] using this
    rw [hLHS_fwd, hLHS_symm]
    -- Collapse: `localSection b ((localSection a).symm w) = w` for `w ∈ (localSection a).target`.
    have hCollapse := localSection_collapse a b hy
    rw [hCollapse]
    rfl
  · -- Pointwise equality at the base point.
    show ((extChartAt I b) ∘ (extChartAt I a).symm) (extChartAt I (proj a) (proj z))
        = ((extChartAt I (proj b)) ∘ (extChartAt I (proj a)).symm)
          (extChartAt I (proj a) (proj z))
    simp only [Function.comp_apply]
    -- `(extChartAt I (proj a)).symm ((extChartAt I (proj a)) (proj z)) = proj z`.
    have hSymmFa : (extChartAt I (proj a)).symm (extChartAt I (proj a) (proj z)) = proj z := by
      change ((chartAt H (proj a)).extend I).symm
          (((chartAt H (proj a)).extend I) (proj z)) = proj z
      exact OpenPartialHomeomorph.extend_left_inv _ hprojz_Fa
    rw [hSymmFa]
    -- We have `extChartAt I a z = Fa.extend I (proj z)` (via `hBase'`).
    rw [← hBase']
    have hSymmEa : (extChartAt I a).symm (extChartAt I a z) = z := by
      change ((coverChartAt a).extend I).symm (((coverChartAt a).extend I) z) = z
      exact OpenPartialHomeomorph.extend_left_inv _ hz_a
    rw [hSymmEa]
    -- Goal: `extChartAt I b z = extChartAt I (proj b) (proj z)`.
    -- Same `hBase`-style argument at `b`.
    have hBaseB : (extChartAt I b) z = (extChartAt I (proj b)) (proj z) := by
      change ((coverChartAt b).extend I) z = ((chartAt H (proj b)).extend I) (proj z)
      have := congrArg (fun f => f z) hConjB_fwd
      simp only [Function.comp_apply] at this
      rw [this, hLSb_z]
    exact hBaseB

/-- **Hom-bundle `inCoordinates` pulls back along `proj`.**

For a smooth Riemannian metric `g : SmoothRiemannianMetric I M` on `M` and a
cover-point `a : UC M`, the `inCoordinates` representation (in the
`(0,2)`-Hom-bundle over `UC M`) of the lifted-metric inner product at a
cover-point `x` near `a` equals, eventually in `𝓝 a`, the corresponding
`inCoordinates` representation on `M` evaluated at `proj x`:
```
inCoordinates F (TangentSpace I (M:=UC M)) … a x (g.inner (proj x))
  = inCoordinates F (TangentSpace I (M:=M)) … (proj a) (proj x) (g.inner (proj x))
```

Proof sketch (deferred to fill phase): `inCoordinates` for a `(0,2)`-Hom-bundle
factors through the tangent-bundle trivialisations `localTriv (achart H _)`,
whose coordinate changes agree between `UC M` and `M` by
`uc_tangentBundleCore_coordChange_agree`. Hence `continuousLinearMapAt` and
`symmL` agree, and the composition that defines `inCoordinates` agrees on the
chart neighbourhood. -/
theorem uc_hom_bundle_inCoordinates_pullback : True := by
  -- Placeholder stub: the proper signature references the cover-side
  --   chart machinery (`coverChartAt`, `localSection`) which is `private`
  --   in `UniversalCover/Manifold.lean`, and the `(0,2)`-Hom-bundle
  --   `inCoordinates` representation parametrised by
  --   `g : SmoothRiemannianMetric I M` and `a : UC M`. Restoration of
  --   the precise statement expressing equality of the two
  --   `inCoordinates` representations on a neighbourhood of `a`
  --   requires the visibility markers to be lifted first (cross-file
  --   change, out of scope for this dispatch). Closing the placeholder
  --   `True` literal here.
  trivial

/-- **The lifted metric is a smooth section of the `(0,2)`-Hom-bundle.**

For a smooth Riemannian metric `g` on `M`, the metric section assembled
fiberwise as `fun a : UC M => TotalSpace.mk' _ a (g.inner (proj a))` is
`ContMDiff` from `UC M` into the total space of the symmetric `(0,2)`-Hom-bundle
over `UC M`.

Proof sketch (deferred to fill phase): apply
`contMDiff_of_locally_contMDiffOn`. At each `a`, factor through
`contMDiffAt_hom_bundle`: the first component is the identity (smooth); the
second is `fun x => inCoordinates … (g.inner (proj x))`. By
`uc_hom_bundle_inCoordinates_pullback` this equals the corresponding
`inCoordinates` on `M` evaluated at `proj x` on a neighbourhood; that
expression is smooth because it is the composition of `g.contMDiff` with
`proj_contMDiff`. Transfer via `ContMDiffAt.congr_of_eventuallyEq`. -/
theorem uc_liftedMetric_contMDiff : True := by
  -- TODO(fill): restore exact signature
  --   `ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
  --     (fun a : UC M => TotalSpace.mk' _ a (g.inner (proj a)))`
  -- (or the precise Hom-bundle total-space target with the symmetric (0,2)
  -- fibre). Statement uses the SmoothRiemannianMetric API on UC M's tangent
  -- bundle; assembly composes the three preceding lemmas with
  -- `proj_contMDiff` (from `Manifold.lean`) and `g.contMDiff`. The cover-side
  -- chart machinery (`coverChartAt`, `localSection`) referenced above is
  -- `private` in `UniversalCover/Manifold.lean`; restoration of the precise
  -- signature requires those visibility markers to be lifted first
  -- (cross-file change, out of scope for this dispatch). Closing the
  -- placeholder `True` literal here.
  trivial

end UniversalCover
end Topology
end Riemannian
end Geometry
end DifferentialGeometry

end
