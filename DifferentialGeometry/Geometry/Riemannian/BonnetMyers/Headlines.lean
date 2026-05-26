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
    IsCompact (Metric.closedBall (0 : TangentSpace I p) R) := sorry

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
    (p : M) {R : ℝ} (_hR : 0 ≤ R) :
    IsCompact ((expMap g p) '' Metric.closedBall (0 : TangentSpace I p) R) := sorry

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
    IsCompact (Set.univ : Set M) := sorry

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
      ENNReal.ofReal (Real.pi / Real.sqrt K) := sorry

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
    CompactSpace M := sorry

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
    Finite (FundamentalGroup M x) := sorry

end BonnetMyers
end Riemannian
end Geometry
end DifferentialGeometry

end
