import DifferentialGeometry.PDE.RicciFlow.DeTurckRHS
import DifferentialGeometry.PDE.ParabolicShortTime
import DifferentialGeometry.PDE.RicciFlow.StrictParabolicAtSelf
import DifferentialGeometry.Integral.Connection.Ricci
import DifferentialGeometry.PDE.DeTurck.VectorFieldSmooth
import DifferentialGeometry.PDE.DeTurck.LieDerivativeMetric
import DifferentialGeometry.Geometry.Curvature.Ricci
import DifferentialGeometry.Geometry.Curvature.Riemann
import Mathlib.Geometry.Manifold.ContMDiff.Basic

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

theorem deTurckRicciRHS_isSmoothQuasilinear
    (g_bg : SmoothRiemannianMetric I M) :
    IsSmoothQuasilinearMetricRHS (I := I)
      (deTurckRicciRHS (I := I) g_bg) := sorry

theorem deturckvf_chart_smooth_in_g_jet
    (g : SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M) :
    True := sorry

theorem deturckvf_chart_component_smooth_in_g_input
    (g_bg : SmoothRiemannianMetric I M) :
    True := sorry

theorem liederivmetric_chart_smooth_in_g_w_jet
    (g : SmoothRiemannianMetric I M) :
    True := sorry

theorem liederivmetric_chart_component_smooth_in_g_w_input
    (g : SmoothRiemannianMetric I M) :
    True := sorry

theorem combine_smoothness_of_summands
    (g_bg g : SmoothRiemannianMetric I M) :
    True := sorry

theorem linearity_in_second_derivatives
    (g_bg g : SmoothRiemannianMetric I M) :
    True := sorry

theorem chartRicci_affine_in_d2g
    (g : SmoothRiemannianMetric I M) :
    True := sorry

end DifferentialGeometry.PDE.RicciFlow
