import DifferentialGeometry.Geometry.Curvature.Realized.MetricFamily
import DifferentialGeometry.Geometry.Connection.LeviCivita.KoszulFormula

noncomputable section

namespace DifferentialGeometry
namespace Integral
namespace Connection

open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

noncomputable def stationaryMetricFamily
    (g : SmoothRiemannianMetric I M) :
    RealizedMetricFamily (I := I) (M := M) Real where
  metric := fun _ => g
  connection := fun _ => leviCivitaConnectionOfMetric (I := I) g
  metricCompatible := fun _ =>
    DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_isMetricCompatible
      (I := I) g

end Connection
end Integral
end DifferentialGeometry
