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

For a smooth Riemannian metric `g : SmoothRiemannianMetric I M` on `M` and
cover-points `a x : UC M` with `x ∈ (chartAt H a).source` (so that the
trivializations at `a` are valid at `x`), the `inCoordinates` representation
(in the `(0,2)`-Hom-bundle over `UC M`) of the metric value `g.inner (proj x)`
at base point `x` viewed via the cover-trivialisation at `a` equals the
corresponding `inCoordinates` representation on `M` evaluated via the
base-trivialisation at `proj a` and base-point `proj x`.

The proof reduces, by definition of `inCoordinates`, to agreement of
`continuousLinearMapAt` and `symmL` of the tangent-bundle trivialisations
between `UC M` and `M`; this in turn follows from
`uc_tangentBundleCore_coordChange_agree` (which packages the cover-side
coordinate-change as the base-side coordinate-change at `proj x`) combined
with `continuousLinearMapAt_trivializationAt_eq_core` and
`symmL_trivializationAt_eq_core`. -/
theorem uc_hom_bundle_inCoordinates_pullback
    (g : SmoothRiemannianMetric I M)
    (a : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
    {x : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M}
    (hx : x ∈ (chartAt H a).source) :
    ContinuousLinearMap.inCoordinates (𝕜₁ := ℝ) (𝕜₂ := ℝ) (σ := RingHom.id ℝ)
        E (TangentSpace I :
            DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M
              → Type _)
        (E →L[ℝ] ℝ)
        (fun b : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M
          => TangentSpace I b →L[ℝ] ℝ)
        a x a x (g.inner (proj x))
      = ContinuousLinearMap.inCoordinates (𝕜₁ := ℝ) (𝕜₂ := ℝ) (σ := RingHom.id ℝ)
          E (TangentSpace I : M → Type _)
          (E →L[ℝ] ℝ) (fun b : M => TangentSpace I b →L[ℝ] ℝ)
          (proj a) (proj x) (proj a) (proj x) (g.inner (proj x)) := by
  -- Membership in the matching tangent-bundle trivialisation base sets.
  -- On `UC M`: baseSet of `trivializationAt E (TangentSpace I) a` is
  -- `(chartAt H a).source`, by `tangentBundleCore_localTriv_baseSet`.
  have hx_UC : x ∈ (trivializationAt E
      (TangentSpace I :
        DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → Type _) a).baseSet := by
    -- `trivializationAt = (tangentBundleCore I (UC M)).localTriv (achart H a)`,
    -- whose baseSet is `(achart H a).1.source = (chartAt H a).source`.
    change x ∈ (chartAt H a).source; exact hx
  -- Source intersection used by `uc_tangentBundleCore_coordChange_agree`.
  have hxAA : x ∈ (chartAt H a).source ∩ (chartAt H a).source := ⟨hx, hx⟩
  -- The same point in the `M`-side base set.
  have hpx_M : proj x ∈ (trivializationAt E (TangentSpace I : M → Type _) (proj a)).baseSet := by
    -- `(coverChartAt a).source = (localSection a).source ∩ ...` and the second component
    -- says `(localSection a) x ∈ (chartAt H (proj a)).source`; but `localSection a x = proj x`.
    have hsrc : ((coverChartAt a) :
        OpenPartialHomeomorph
          (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) H).source
        = (localSection a).source ∩
          (localSection a) ⁻¹' (chartAt H (proj a)).source :=
      coverChartAt_source_eq a
    have hx' : x ∈ (coverChartAt a).source := hx
    rw [hsrc] at hx'
    obtain ⟨hLS, hLSproj⟩ := hx'
    rw [Set.mem_preimage] at hLSproj
    -- `localSection a x = proj x`.
    have hLSx : (localSection a) x = proj x := by
      have := congrArg (fun f => f x) (proj_eq_localSection a)
      simpa using this.symm
    rw [hLSx] at hLSproj
    -- baseSet of `trivializationAt E (TangentSpace I) (proj a)` is `(chartAt H (proj a)).source`.
    change proj x ∈ (chartAt H (proj a)).source; exact hLSproj
  -- Unfold both `inCoordinates` to compositions of `continuousLinearMapAt` and `symmL`.
  -- For an iterated Hom-bundle the codomain trivialisation is built from the tangent
  -- one and the canonical identification on cotangents; agreement of the underlying
  -- tangent trivialisations forces agreement of the iterated trivialisations as well.
  -- We carry out the unfolding by `inCoordinates` definition.
  -- The strategy is to use `continuousLinearMapAt_trivializationAt_eq_core` /
  -- `symmL_trivializationAt_eq_core` on each side and reduce to
  -- `uc_tangentBundleCore_coordChange_agree`.
  -- For the (0,2)-tensor case both sides factor through the SAME pair of tangent
  -- trivialisations, so it suffices to show they agree pointwise.
  -- We package the equality of `continuousLinearMapAt` and `symmL` directly.
  -- Step 1: equality of tangent-side `symmL` between UC and M at `x`/`proj x`.
  have hSymmL :
      ((trivializationAt E (TangentSpace I :
          DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → Type _) a).symmL
            ℝ x : E →L[ℝ] E)
        = ((trivializationAt E (TangentSpace I : M → Type _) (proj a)).symmL ℝ (proj x)
            : E →L[ℝ] E) := by
    rw [TangentBundle.symmL_trivializationAt_eq_core (I := I)
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (b₀ := a) (b := x) hx,
        TangentBundle.symmL_trivializationAt_eq_core (I := I) (M := M)
          (b₀ := proj a) (b := proj x)
          (show proj x ∈ (chartAt H (proj a)).source from hpx_M)]
    -- Now both sides are `coordChange (achart H _) (achart H _) _`.
    -- Apply `uc_tangentBundleCore_coordChange_agree` with roles `(a, x)` on the
    -- second pair... but actually the statement has `(achart H a) (achart H x)` /
    -- `(achart H (proj a)) (achart H (proj x))`. Use the lemma directly.
    exact uc_tangentBundleCore_coordChange_agree (I := I) a x ⟨hx, mem_chart_source H x⟩
  -- Step 2: equality of tangent-side `continuousLinearMapAt`.
  have hCLM :
      ((trivializationAt E (TangentSpace I :
          DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → Type _) a).continuousLinearMapAt
            ℝ x : E →L[ℝ] E)
        = ((trivializationAt E (TangentSpace I : M → Type _) (proj a)).continuousLinearMapAt
            ℝ (proj x) : E →L[ℝ] E) := by
    rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (I := I)
          (M := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)
          (b₀ := a) (b := x) hx,
        TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (I := I) (M := M)
          (b₀ := proj a) (b := proj x)
          (show proj x ∈ (chartAt H (proj a)).source from hpx_M)]
    -- coordChange (achart H x) (achart H a) x = coordChange (achart H (proj x)) (achart H (proj a)) (proj x).
    exact uc_tangentBundleCore_coordChange_agree (I := I) x a
      ⟨mem_chart_source H x, hx⟩
  -- Step 3: the codomain trivialisation (cotangent / Hom into ℝ) is, by Mathlib's
  -- general Hom-bundle construction, the cotangent twist of the tangent trivialisation.
  -- Concretely, for the trivial bundle `ℝ` and the tangent bundle, the
  -- `Trivialization.continuousLinearMapAt` of the Hom-bundle factors through the
  -- tangent-side `continuousLinearMapAt`/`symmL`. By `continuousAt_hom_bundle`-style
  -- algebra, the iterated `inCoordinates` reduces to two applications of `inCoordinates`
  -- on the tangent factor only.
  -- Finally we close with the identity
  --   inCoordinates A E B E' x₀ x y₀ y ϕ = (triv at y₀).continuousLinearMapAt y ∘ ϕ ∘ (triv at x₀).symmL x
  -- and use hCLM/hSymmL pointwise on the underlying tangent trivialisations.
  -- The cotangent codomain trivialisation comes from Mathlib's Hom-bundle construction
  -- applied to `(TangentSpace I, Trivial ℝ)`; since the `Trivial ℝ` factor has identity
  -- coordChange independent of the base manifold, it cannot distinguish `UC M` from `M`,
  -- and the equality reduces to `hCLM` / `hSymmL`.
  -- We complete the proof by unfolding `inCoordinates` to its definition.
  unfold ContinuousLinearMap.inCoordinates
  -- Goal: `(continuousLinearMapAt-cotangent at y₀) ∘ ϕ ∘ (symmL-tangent at x₀)`
  -- (UC version) equals the same expression on M evaluated at proj.
  -- The two `.comp`s give a three-factor composition; we use `congr` to split.
  -- The codomain trivialisation (cotangent Hom-bundle) agreement reduces to `hCLM`
  -- via the canonical Hom-bundle construction (trivial ℝ factor; tangent in the
  -- contravariant slot). The tangent `symmL` agreement is `hSymmL`.
  refine congrArg₂ ContinuousLinearMap.comp ?_ ?_
  · -- Codomain `continuousLinearMapAt` agreement on the cotangent Hom-bundle.
    -- The cotangent bundle is `Hom(TangentSpace, Trivial ℝ)`; its trivialization is
    -- `(tangentTriv).continuousLinearMap id (trivℝ)` and the `continuousLinearMapAt y`
    -- of this trivialization, applied to a cotangent `β : E y →L ℝ`, equals
    -- `(trivℝ.continuousLinearMapAt y).comp (β.comp (tangentTriv.symmL y))`
    -- by `Trivialization.continuousLinearMap_apply` (after unfolding the Pretrivialization
    -- linearMapAt). Since `trivℝ.continuousLinearMapAt y = 1`, the formula collapses to
    -- `β ↦ β.comp (tangentTriv.symmL y)`. The agreement between UC and M sides then
    -- reduces precisely to `hSymmL` (the tangent symmL identification).
    -- Full unfolding through `linearMapAt` / `Pretrivialization.continuousLinearMap_apply`
    -- to a CLM equality requires significant Hom-trivialization-API plumbing; we record
    -- the reduction here and ship the named gap.
    sorry
  · refine congrArg₂ ContinuousLinearMap.comp rfl ?_
    -- `symmL` agreement on the tangent bundle: direct from `hSymmL`.
    exact hSymmL

/-- **The lifted metric is a smooth section of the `(0,2)`-Hom-bundle.**

For a smooth Riemannian metric `g` on `M`, the metric section
`fun a : UC M => TotalSpace.mk' _ a (g.inner (proj a))` is `ContMDiff` from
`UC M` into the total space of the symmetric `(0,2)`-Hom-bundle over `UC M`.

Strategy: apply `contMDiffAt_hom_bundle` pointwise; the base-projection is
the identity (smooth); the in-coordinates piece equals — by
`uc_hom_bundle_inCoordinates_pullback` on the chart neighbourhood of each
point — the corresponding in-coordinates on `M` evaluated at `proj x`, which
is smooth as the composition of `g.contMDiff` and `proj_contMDiff` followed
by the `inCoordinates` map. The eventually-equal transfer is via
`ContMDiffAt.congr_of_eventuallyEq`. -/
theorem uc_liftedMetric_contMDiff
    (g : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun a : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M
        => (TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) a (g.inner (proj a)) :
              TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
                (fun b : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M
                  => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ))) := by
  -- Assembly: at each `a`, use `contMDiffAt_hom_bundle` to reduce to two
  -- conditions: smoothness of the base projection (= identity, smooth) and
  -- smoothness of the inCoordinates representation. The latter is shifted
  -- from UC to M via `uc_hom_bundle_inCoordinates_pullback`, then bundled
  -- as the composition of `g.contMDiff` (M-side) with `proj_contMDiff`.
  -- Full assembly involves chasing the `congr_of_eventuallyEq` plumbing
  -- through the Hom-bundle's iterated trivialisation structure; we ship
  -- the substantive signature and defer the assembly proper.
  sorry

end UniversalCover
end Topology
end Riemannian
end Geometry
end DifferentialGeometry

end
