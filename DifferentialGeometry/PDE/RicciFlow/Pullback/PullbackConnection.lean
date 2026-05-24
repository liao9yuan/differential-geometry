import DifferentialGeometry.PDE.RicciFlow.Pullback.Metric
import DifferentialGeometry.Integral.Connection.LeviCivita

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

-- order 452: pullback-connection construction
noncomputable def pullback_connection_construct
    (g : SmoothRiemannianMetric I M)
    (Φ : M ≃ₘ⟮I, I⟯ M) :
    True := sorry

-- order 453: pullback connection is torsion-free
theorem pullback_connection_torsion_free
    (g : SmoothRiemannianMetric I M)
    (Φ : M ≃ₘ⟮I, I⟯ M) :
    True := sorry

-- order 454: pullback connection is metric-compatible
theorem pullback_connection_metric_compatible
    (g : SmoothRiemannianMetric I M)
    (Φ : M ≃ₘ⟮I, I⟯ M) :
    True := sorry

end DifferentialGeometry.PDE.RicciFlow.Pullback
