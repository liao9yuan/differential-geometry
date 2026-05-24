import DifferentialGeometry.PDE.RicciFlow.Pullback.Metric
import DifferentialGeometry.PDE.RicciFlow.Pullback.LeviCivitaConjugation
import DifferentialGeometry.PDE.RicciFlow.Pullback.RiemannConjugation
import DifferentialGeometry.PDE.RicciFlow.Pullback.RicciTraceConjugation
import DifferentialGeometry.PDE.RicciFlow.Pullback.MLieBracketNaturality
import DifferentialGeometry.Integral.Connection.Ricci
import DifferentialGeometry.Integral.Connection.Curvature
import DifferentialGeometry.Integral.Connection.CurvatureBundling

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem ricci_pullback_naturality
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M)
    (x : M) (v w : TangentSpace I x) :
    True := sorry

end DifferentialGeometry.PDE.RicciFlow.Pullback
