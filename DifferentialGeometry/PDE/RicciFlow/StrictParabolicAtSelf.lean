import DifferentialGeometry.PDE.RicciFlow.DeTurckRHS
import DifferentialGeometry.PDE.RicciFlow.PrincipalSymbol
import DifferentialGeometry.PDE.ParabolicShortTime
import DifferentialGeometry.PDE.DeTurck.Symbol
import DifferentialGeometry.PDE.DeTurck.StrictParabolicity
import DifferentialGeometry.PDE.DeTurck.RicciLinearization.RicciPrincipalPart
import DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.DeTurckCorrectionSymbol

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.PDE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

theorem deTurckRicciRHS_isStrictlyParabolic_at_self
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    IsStrictlyParabolicMetricRHS (I := I)
      (deTurckRicciRHS (I := I) g_bg) g₀ := sorry

theorem deTurckRicciRHS_principal_symbol_equals_deTurckSymbol
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    True := sorry

theorem bridge_symbol_equality_to_is_strictly_parabolic_metric_rhs
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    True := sorry

end DifferentialGeometry.PDE.RicciFlow
