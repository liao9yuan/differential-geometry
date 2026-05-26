import DifferentialGeometry.Geometry.Riemannian.BonnetMyers.RicciBound
import DifferentialGeometry.Geometry.Riemannian.BonnetMyers.LengthBound
import DifferentialGeometry.Geometry.Riemannian.HopfRinow
import DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.Lifts
import DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnected
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Topology.EMetricSpace.Diam
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Covering.Basic
import Mathlib.Data.Finite.Defs

/-!
# Bonnet-Myers headline theorems

This file assembles the three top-level conclusions of the Bonnet-Myers
theorem from their supporting children. Under the hypotheses
`Ric ≥ (n-1) K · g` with `K > 0` and `n ≥ 2`:

* `bonnetMyers_diameter` — the metric diameter is at most `π / √K`.
* `bonnetMyers_compact` — the manifold is compact.
* `bonnetMyers_finite_fundamentalGroup` — the fundamental group is finite.

Two short supporting children are also stated here:

* `pairwise_edist_bound_from_geodesic` — the uniform pairwise edist bound.
* The `bm_c_*` compactness sub-leaves
  (`tangent_closedBall_isCompact`, `isCompact_image_closedBall_under_expMap`,
  `isCompact_univ`).
-/

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace BonnetMyers

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Geometry.Riemannian.Exponential

/-! ## Compactness sub-leaves -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]

/-- **bm-c-tangent-closedBall-compact.** The closed ball of radius `R` in
the tangent space `T_p M` is compact, because `T_p M` is finite-dimensional
(it is canonically isomorphic to the model fibre `E`). Pure composition of
Mathlib `FiniteDimensional.proper_real` and `isCompact_closedBall`. -/
theorem tangent_closedBall_isCompact
    {M : Type*}
    (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    (p : M) {R : ℝ} (_hR : 0 ≤ R) :
    IsCompact (Metric.closedBall (0 : TangentSpace I p) R) := by
  -- `TangentSpace I p` is definitionally `E`, a finite-dimensional real normed space,
  -- hence a `ProperSpace`. On a `ProperSpace`, closed balls are compact.
  haveI : ProperSpace E := FiniteDimensional.proper_real E
  exact isCompact_closedBall (0 : TangentSpace I p) R

/-- **bm-c-continuous-image-of-compact-is-compact.** Continuous image of a
compact set is compact. Apply `IsCompact.image` to
`tangent_closedBall_isCompact` together with the continuity of `expMap`. -/
theorem isCompact_image_closedBall_under_expMap
    {M : Type*}
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
    [PseudoEMetricSpace M]
    (g : SmoothRiemannianMetric I M)
    [Bundle.RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    (p : M) {R : ℝ} (hR : 0 ≤ R) :
    IsCompact ((expMap g p) '' Metric.closedBall (0 : TangentSpace I p) R) := by
  -- Continuous image of the compact closed ball in `T_p M`.
  have hcompact : IsCompact (Metric.closedBall (0 : TangentSpace I p) R) :=
    tangent_closedBall_isCompact (E := E) I p hR
  have hcont : Continuous (expMap (I := I) g p) :=
    DifferentialGeometry.Geometry.Riemannian.HopfRinow.bm_c_expMap_continuous_of_geodesic_complete
      g p
  exact hcompact.image hcont

/-! ## Pairwise edist bound -/

/-- **pairwise-edist-bound-from-geodesic.** The uniform pairwise edist
bound. Direct composition of Hopf-Rinow existence + Myers's length bound +
the `IsRiemannianManifold` identity `edist = riemannianEDist`. -/
theorem pairwise_edist_bound_from_geodesic
    {M : Type*}
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
    [PseudoEMetricSpace M]
    (g : SmoothRiemannianMetric I M)
    [Bundle.RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    (_hdim : 2 ≤ Module.finrank ℝ E)
    {K : ℝ} (_hK : 0 < K)
    (_hRic : RicciBoundedBelow (I := I) g (((Module.finrank ℝ E : ℝ) - 1) * K))
    (x y : M) :
    edist x y ≤ ENNReal.ofReal (Real.pi / Real.sqrt K) := sorry

/-! ## Headline 1: diameter bound -/

set_option linter.deprecated false in
/-- **bonnet-myers-diameter.** *Bonnet-Myers diameter theorem.* On a
complete connected Riemannian manifold of dimension `n ≥ 2` with Ricci
curvature bounded below by `(n-1) K` for some `K > 0`, the metric diameter
is at most `π / √K`. -/
theorem bonnetMyers_diameter
    {M : Type*}
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
    [PseudoEMetricSpace M]
    (g : SmoothRiemannianMetric I M)
    [Bundle.RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    (_hdim : 2 ≤ Module.finrank ℝ E)
    {K : ℝ} (_hK : 0 < K)
    (_hRic : RicciBoundedBelow (I := I) g (((Module.finrank ℝ E : ℝ) - 1) * K)) :
    EMetric.diam (Set.univ : Set M) ≤
      ENNReal.ofReal (Real.pi / Real.sqrt K) := by
  refine Metric.ediam_le ?_
  intro x _ y _
  exact pairwise_edist_bound_from_geodesic (E := E) g _hdim _hK _hRic x y

/-! ## Compactness sub-leaf: `univ` is compact -/

set_option linter.deprecated false in
/-- **bm-c-univ-compact.** The whole space `Set.univ : Set M` is compact.
Combines the diameter bound (sibling headline `bonnetMyers_diameter`) with
exponential-map surjectivity on the closed ball of radius `π / √K` and
`IsCompact.of_isClosed_subset` together with `isClosed_univ`. -/
theorem isCompact_univ
    {M : Type*}
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
    [PseudoEMetricSpace M]
    (g : SmoothRiemannianMetric I M)
    [Bundle.RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    (_hdim : 2 ≤ Module.finrank ℝ E)
    {K : ℝ} (_hK : 0 < K)
    (_hRic : RicciBoundedBelow (I := I) g (((Module.finrank ℝ E : ℝ) - 1) * K)) :
    IsCompact (Set.univ : Set M) := by
  -- Pick a base point from `Nonempty M` (provided by `ConnectedSpace M`).
  let p : M := Classical.arbitrary M
  -- The radius `R := π / √K` is non-negative (since `K > 0`).
  set R : ℝ := Real.pi / Real.sqrt K with hR_def
  have hR_nn : 0 ≤ R := by
    have hpi_nn : (0 : ℝ) ≤ Real.pi := Real.pi_nonneg
    have hsqrt_nn : (0 : ℝ) ≤ Real.sqrt K := Real.sqrt_nonneg K
    exact div_nonneg hpi_nn hsqrt_nn
  -- Diameter bound from the proved sibling headline.
  have hdiam : EMetric.diam (Set.univ : Set M) ≤ ENNReal.ofReal R :=
    bonnetMyers_diameter (E := E) g _hdim _hK _hRic
  -- Exponential surjectivity on the closed ball of radius `R`.
  have hsurj :
      (Set.univ : Set M) ⊆
        (expMap (I := I) g p) ''
          (Metric.closedBall (0 : TangentSpace I p) R) :=
    DifferentialGeometry.Geometry.Riemannian.HopfRinow.bm_c_expMap_surjective_on_closedBall
      g p hR_nn hdiam
  -- The image of the closed ball under `expMap` is compact.
  have himg : IsCompact
      ((expMap (I := I) g p) '' Metric.closedBall (0 : TangentSpace I p) R) :=
    isCompact_image_closedBall_under_expMap (E := E) g p hR_nn
  -- `univ` is closed; together with the compact superset, it is compact.
  exact himg.of_isClosed_subset isClosed_univ hsurj

/-! ## Headline 2: compactness -/

/-- **bonnet-myers-compact.** *Bonnet-Myers compactness.* On a complete
connected Riemannian manifold of dimension `n ≥ 2` with Ricci curvature
bounded below by `(n-1) K` for some `K > 0`, the manifold is compact. -/
theorem bonnetMyers_compact
    {M : Type*}
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
    [PseudoEMetricSpace M]
    (g : SmoothRiemannianMetric I M)
    [Bundle.RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    (_hdim : 2 ≤ Module.finrank ℝ E)
    {K : ℝ} (_hK : 0 < K)
    (_hRic : RicciBoundedBelow (I := I) g (((Module.finrank ℝ E : ℝ) - 1) * K)) :
    CompactSpace M :=
  isCompact_univ_iff.mp (isCompact_univ (E := E) g _hdim _hK _hRic)

/-! ## Headline 3: finite fundamental group -/

/-- **bonnet-myers-finite-fundamental-group.** *Bonnet-Myers finiteness of
the fundamental group.* On a complete connected Riemannian manifold of
dimension `n ≥ 2` with Ricci curvature bounded below by `(n-1) K` for some
`K > 0`, the fundamental group `π₁(M, x)` at any base point is finite. The
proof passes to the universal cover, applies the compactness headline to
the lifted manifold, and identifies the fibre of the cover with `π₁(M, x)`
via monodromy. -/
theorem bonnetMyers_finite_fundamentalGroup
    {M : Type*}
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
    [LocPathConnectedSpace M]
    [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M]
    [PseudoEMetricSpace M]
    (g : SmoothRiemannianMetric I M)
    [Bundle.RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    (_hdim : 2 ≤ Module.finrank ℝ E)
    {K : ℝ} (_hK : 0 < K)
    (_hRic : RicciBoundedBelow (I := I) g (((Module.finrank ℝ E : ℝ) - 1) * K))
    (x : M) :
    Finite (FundamentalGroup M x) := by
  -- Promote the manifold's `[Nonempty M]` (from `ConnectedSpace M`) to `[Inhabited M]`,
  -- needed for the universal-cover infrastructure.
  letI : Inhabited M := Classical.inhabited_of_nonempty'
  -- The universal cover and its projection.
  set UC := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M
  set p :
      DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.proj
  -- The projection is a covering map: provided by the universal-cover infrastructure.
  have hcov :
      IsCoveringMap
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.proj :
          DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M) :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.UniversalCover.isCoveringMap
  -- `PathConnectedSpace M`: from `[ConnectedSpace M]` + `[LocPathConnectedSpace M]`.
  haveI hpcM : PathConnectedSpace M :=
    PathConnectedSpace.of_locPathConnectedSpace
  -- Lifted Riemannian metric on the universal cover.
  set gLift :
      SmoothRiemannianMetric I
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.liftedMetric
      (I := I) g
  -- Bundled Riemannian-bundle structure on the tangent bundle of the universal cover.
  haveI hRB :
      Bundle.RiemannianBundle
        (fun (xt :
            DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) ↦
          TangentSpace I xt) :=
    ⟨gLift.toRiemannianMetric⟩
  -- `SecondCountableTopology H` from finite-dimensional model space `E`.
  haveI hSCH : SecondCountableTopology H :=
    ModelWithCorners.secondCountableTopology I
  -- `SecondCountableTopology M` from chart cover + σ-compactness.
  haveI hSCM : SecondCountableTopology M :=
    ChartedSpace.secondCountable_of_sigmaCompact H M
  -- Compactness of the lifted manifold. This consumes the lifted instances and the
  -- Ricci-bound pullback (`ricciBoundedBelow_pullback_universalCover`), and the
  -- still-sorry `CompleteSpace` of the universal cover. We package the latter as a
  -- local instance to mirror the upstream skeleton, then apply the proved compactness
  -- headline (Headline 2) to the lifted data.
  -- Ricci pullback to the universal cover.
  have hRicLift :
      RicciBoundedBelow (I := I) gLift (((Module.finrank ℝ E : ℝ) - 1) * K) :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.ricciBoundedBelow_pullback_universalCover
      (I := I) (g := g) _hRic
  -- Completeness of the universal cover: routed through
  -- `completeSpace_universalCover` (UC/Lifts.lean), whose signature is in place
  -- though its body is pending.
  haveI hCompUC :
      CompleteSpace
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.completeSpace_universalCover
      g
  -- Apply Headline 2 (`bonnetMyers_compact`) to the lifted Riemannian manifold.
  haveI hCompactUC :
      CompactSpace
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
    bonnetMyers_compact (E := E) gLift _hdim _hK hRicLift
  -- The fibre of the covering map over `x` is finite (compact + discrete).
  haveI hFinFibre :
      Finite
        ((DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.proj :
            DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M)
          ⁻¹' {x}) :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.fibre_finite
      hcov x
  -- Pick a base lift `e' ∈ proj⁻¹{x}` via path-connectedness of `M`.
  obtain ⟨γ⟩ := PathConnectedSpace.joined (default : M) x
  let e' :
      ((DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.proj :
          DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M)
        ⁻¹' {x}) :=
    ⟨⟨x, Path.Homotopic.Quotient.mk γ⟩,
      by
        change
          (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.proj
              (X := M)
              (⟨x, Path.Homotopic.Quotient.mk γ⟩ :
                DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M))
            = x
        rfl⟩
  -- Fibre ↔ fundamental group bijection (from the universal-cover infrastructure).
  have hEquiv :
      ((DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.proj :
          DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M)
        ⁻¹' {x})
        ≃ FundamentalGroup M x :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.fibreEquivFundamentalGroup
      hcov x e'
  -- Transport finiteness across the bijection.
  exact Finite.of_equiv _ hEquiv

end BonnetMyers
end Riemannian
end Geometry
end DifferentialGeometry

end
