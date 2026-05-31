/-
The spectral strong (`timeH1`) DeTurck-remainder solution on the carrier Sobolev
scale, with its Duhamel-fixed-point identification and forcing fixed-point
equation. Skeleton stub for the short-time-existence blueprint (GAP 1, ROUTE B
spectral strong existence).
-/
import DifferentialGeometry.PDE.RicciFlow.ShortTimeExistence
import DifferentialGeometry.PDE.RicciFlow.HamiltonDeTurckPullbackFlat
import DifferentialGeometry.PDE.RicciFlow.Pullback.EvaluationFormChainRule
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckRemainderStrongExists
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.DeTurckGeometricNonlinearity
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.EigenCombination
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.TensorHsRealize
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.ChartLocalPicard
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.ChartOverlapUniqueness
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.BareFlowFromJointC1
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace.VariationalLiftFlatIdentity
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothDependence.GlobalClosedManifold

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.ODE
open DifferentialGeometry.PDE.RicciFlow.Pullback
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem deturck_mildsolution_timeh1
    (g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : Module.finrank ℝ E < 2 * (a - 2))
    (u₀ : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2)) :
    ∃ T : ℝ, ∃ (hT : 0 < T) (hT1 : T ≤ 1)
        (u : MaxRegSolutionSpace (I := I) (M := M) (a : ℝ) T)
        (gforce : timeL2 (tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ)) T),
        ContinuousOn (timeH1.toFun u) (Set.Icc 0 T) ∧
          timeH1.trace0 _ T u =
            tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
              (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) u₀ ∧
          u = maxRegDuhamelMap (I := I) (M := M) (a : ℝ) hT hT1 u₀ gforce ∧
          gforce =ᵐ[timeMeasure T]
            (fun t => deTurckGeometricN (I := I) g_bg a
              (maxRegDuhamelSolFieldHa1 (I := I) (M := M) (a : ℝ) hT hT1 u₀ gforce t)) := sorry

end DifferentialGeometry.PDE.RicciFlow
