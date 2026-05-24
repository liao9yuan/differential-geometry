import DifferentialGeometry.PDE.RicciFlow.DeTurckShortTime
import DifferentialGeometry.PDE.RicciFlow.SobolevEmbedding
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.LiftMetric
import DifferentialGeometry.PDE.RicciFlow.DeTurckRHS
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.MaxRegSpace
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1
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
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

theorem deTurckRicci_solution_spatial_C1_time_continuous
    (g_bg : SmoothRiemannianMetric I M) :
    True := sorry

theorem maxreg_solution_in_c1_via_sobolev_embedding
    (g_bg : SmoothRiemannianMetric I M) :
    True := sorry

theorem c1_norm_time_continuous_from_h1_time_derivative
    (g_bg : SmoothRiemannianMetric I M) :
    True := sorry

theorem deturck_vf_continuous_in_c1_input
    (g_bg : SmoothRiemannianMetric I M) :
    True := sorry

end DifferentialGeometry.PDE.RicciFlow
