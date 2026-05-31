/-
Continuity of the conjugating family's pushforward in time, the interior
identification of the diffeomorphism family with the chart-cover flow, and the
`t = 0` right-continuity of the moving pushforward. Skeleton stubs for the
short-time-existence blueprint (GAP 2, flow-continuity).
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

theorem flow_pushforward_continuous_in_time
    (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)) (T : ℝ) :
    (∀ (x : M) (v : TangentSpace I x), ContinuousOn
      (fun s : ℝ => (mfderiv I I (Φ_fam s : M → M) x v : E)) (Set.Icc 0 T))
    ∧ (∀ x : M, ContinuousWithinAt (fun s : ℝ => (Φ_fam s : M → M) x) (Set.Ici (0 : ℝ)) 0) := sorry

theorem flow_family_identification
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g₀ : SmoothRiemannianMetric I M)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)) (Φ : ℝ → M → M) :
    ∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, (Φ_fam s : M → M) x = Φ s x := sorry

theorem joint_smooth_moving_mfderiv_continuous
    (Φ : ℝ → M → M) :
    (∀ x : M, ContinuousWithinAt (fun s : ℝ => Φ s x) (Set.Ici (0 : ℝ)) 0)
    ∧ (∀ (x : M) (v : TangentSpace I x),
        ContinuousWithinAt (fun s : ℝ => (mfderiv I I (fun y : M => Φ s y) x v : E))
          (Set.Ici (0 : ℝ)) 0) := sorry

end DifferentialGeometry.PDE.RicciFlow
