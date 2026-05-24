import DifferentialGeometry.PDE.RicciFlow.Pullback.Metric
import DifferentialGeometry.PDE.RicciFlow.Pullback.PullbackConnection
import DifferentialGeometry.Integral.Connection.LeviCivita

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem levi_civita_pullback_conjugation
    (g : SmoothRiemannianMetric I M)
    (Φ : M ≃ₘ⟮I, I⟯ M) :
    True := sorry

theorem levi_civita_pullback_conjugation_finalize
    (g : SmoothRiemannianMetric I M)
    (Φ : M ≃ₘ⟮I, I⟯ M) :
    True := sorry

end DifferentialGeometry.PDE.RicciFlow.Pullback
