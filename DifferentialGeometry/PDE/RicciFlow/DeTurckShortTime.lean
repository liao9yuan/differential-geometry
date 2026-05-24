import DifferentialGeometry.Metric.Basic
import DifferentialGeometry.PDE.ParabolicShortTime
import DifferentialGeometry.PDE.RicciFlow.DeTurckRHS
import DifferentialGeometry.PDE.RicciFlow.StrictParabolicAtSelf
import DifferentialGeometry.PDE.RicciFlow.SmoothQuasilinear
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.Eigenbasis
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.HeatSemigroup
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MaxReg
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.QuasilinearStrong
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.LiftMetric
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.PointwiseDeriv

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.PDE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

theorem deTurckRicci_shortTime_exists
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ T : ℝ, ∃ g_DT : ℝ → SmoothRiemannianMetric I M,
      IsQuasilinearMetricParabolicSolution (I := I)
        (deTurckRicciRHS (I := I) g_bg) g₀ T g_DT := sorry

end DifferentialGeometry.PDE.RicciFlow
