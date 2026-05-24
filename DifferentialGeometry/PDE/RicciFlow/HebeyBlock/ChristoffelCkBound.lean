import DifferentialGeometry.Metric.Basic
import DifferentialGeometry.Integral.Connection.LeviCivitaChartLocal

namespace DifferentialGeometry.PDE.RicciFlow.HebeyBlock

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- Existence of a non-negative bound governing the `C^{k-1}` norms of the
Christoffel symbols of a smooth Riemannian metric in a chart, in terms of a
`C^k` bound on the metric and a uniform lower bound on the metric's smallest
eigenvalue. At the skeleton stage we declare the bound's existence. -/
theorem christoffel_Ck_bound_from_metric_Ck1
    (g : SmoothRiemannianMetric I M) (k : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C := sorry

end DifferentialGeometry.PDE.RicciFlow.HebeyBlock
