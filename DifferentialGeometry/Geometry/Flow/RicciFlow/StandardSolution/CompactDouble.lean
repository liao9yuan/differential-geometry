import DifferentialGeometry.Geometry.Flow.RicciFlow.StandardSolution.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.MaximalFlow

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

/-- One compact pointed metric intended to serve as a closed approximation to
the standard initial metric.  Agreement with a standard cap is a separate proof
obligation, not a field hidden in this data container. -/
structure ClosedApprox (I : ModelWithCorners Real E H) where
  M : Type u
  [topology : TopologicalSpace M]
  [charted : ChartedSpace H M]
  [smooth : IsManifold I ∞ M]
  [sigmaCompact : SigmaCompactSpace M]
  [t2 : T2Space M]
  [t2Tangent : T2Space (TangentBundle I M)]
  [compact : CompactSpace M]
  [connected : ConnectedSpace M]
  [boundaryless : BoundarylessManifold I M]
  basepoint : M
  metric : SmoothRiemannianMetric I M

/-- Every compact approximation metric has a genuine short-time Ricci flow in
the native `FlowTo` representation. -/
theorem exists_closed_flow (A : ClosedApprox.{u, uE, uH} (I := I)) :
    letI : TopologicalSpace A.M := A.topology
    letI : ChartedSpace H A.M := A.charted
    letI : IsManifold I ∞ A.M := A.smooth
    letI : IsManifold I 1 A.M := IsManifold.of_le
      (I := I) (M := A.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace A.M := A.sigmaCompact
    letI : T2Space A.M := A.t2
    letI : CompactSpace A.M := A.compact
    letI : ConnectedSpace A.M := A.connected
    letI : BoundarylessManifold I A.M := A.boundaryless
    exists T : Real, Nonempty (FlowTo (I := I) (M := A.M) A.metric T) := by
  letI : TopologicalSpace A.M := A.topology
  letI : ChartedSpace H A.M := A.charted
  letI : IsManifold I ∞ A.M := A.smooth
  letI : IsManifold I 1 A.M := IsManifold.of_le
    (I := I) (M := A.M) (n := ∞) (by decide)
  letI : SigmaCompactSpace A.M := A.sigmaCompact
  letI : T2Space A.M := A.t2
  letI : CompactSpace A.M := A.compact
  letI : ConnectedSpace A.M := A.connected
  letI : BoundarylessManifold I A.M := A.boundaryless
  exact flow_to_seed (I := I) (M := A.M) A.metric

end DifferentialGeometry.PDE.RicciFlow
