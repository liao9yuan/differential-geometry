/-
The per-chart forward Picard local flow, the forward-uniqueness glue into one
interior flow carrying the bare velocity, and the chart-cover orbit linchpin.
Skeleton stubs for the short-time-existence blueprint (GAP 2, interior flow).
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

theorem interior_local_flow_existence
    (X_DT : ℝ → ∀ x : M, TangentSpace I x) (α : M)
    (hCont : ContinuousOn (Function.uncurry (fun t x => X_DT t x))
      (Set.univ : Set (ℝ × M)))
    (hLip : ∃ L K r : ℝ, 0 < L ∧ 0 < r ∧ 0 ≤ K ∧
      ∀ t ∈ Set.Icc (0 : ℝ) L,
        LipschitzOnWith (Real.toNNReal K)
          (fun y : E => (X_DT t ((chartAt H α).symm (I.symm y)) : E))
          (Metric.ball (I ((chartAt H α) α)) r)) :
    ∃ T : ℝ, 0 < T ∧ ∃ r' : ℝ, 0 < r' ∧
      ∃ flow : E → ℝ → E,
        (∀ y ∈ Metric.closedBall (I ((chartAt H α) α)) r',
          flow y 0 = y ∧
          ∀ t ∈ Set.Icc (0 : ℝ) T,
            HasDerivWithinAt (flow y)
              ((X_DT t ((chartAt H α).symm (I.symm (flow y t)))) : E)
              (Set.Icc (0 : ℝ) T) t) := sorry

theorem interior_flow_uniqueness_glue
    (X : ℝ → ∀ x : M, TangentSpace I x) (hX : AutonomizedFieldJointC1 (I := I) X)
    (T : ℝ) (hT : 0 < T)
    (hper : ∀ α : M, ChartLocalPicardData (I := I) X α)
    (hperNeg : ∀ α : M, ChartLocalPicardData (I := I) (fun t x => -(X t x)) α)
    (hTle : ∀ α : M, T ≤ (hper α).T)
    (hTleNeg : ∀ α : M, T ≤ (hperNeg α).T)
    (hSmoothX_chart : ∀ α : M, ContDiff ℝ ∞ (Function.uncurry fun t y =>
      (X t ((chartAt H α).symm (I.symm y)) : E)))
    (hSmoothNegX_chart : ∀ α : M, ContDiff ℝ ∞ (Function.uncurry fun t y =>
      ((-X t ((chartAt H α).symm (I.symm y))) : E))) :
    ∃ Φcc : ℝ → M → M, (∀ x : M, Φcc 0 x = x) ∧
      (∀ x : M, ∃ α : M, ∀ s : ℝ, Φcc s x =
        (chartAt H α).symm (I.symm ((hper α).flow (I ((chartAt H α) x)) s))) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) T, ∃ d : M ≃ₘ⟮I, I⟯ M, ∀ x : M, d x = Φcc t x) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φcc s x) (Set.Ici (0 : ℝ)) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φcc t x)))) := sorry

theorem chartcover_orbit_is_bare_integral_curve
    (X : ℝ → ∀ x : M, TangentSpace I x) (hX : AutonomizedFieldJointC1 (I := I) X)
    (T : ℝ) (hT : 0 < T) (Φcc : ℝ → M → M)
    (hΦcc0 : ∀ x : M, Φcc 0 x = x)
    (hper : ∀ α : M, ChartLocalPicardData (I := I) X α)
    (hTle : ∀ α : M, T ≤ (hper α).T)
    (hrepr : ∀ x : M, ∃ α : M, x ∈ (hper α).U ∧ ∀ s : ℝ, Φcc s x =
      (chartAt H α).symm (I.symm ((hper α).flow (I ((chartAt H α) x)) s))) :
    ∀ t : ℝ, 0 < t → t < T → ∀ x : M, HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φcc s x)
      (Set.Ici (0 : ℝ)) t ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φcc t x))) := sorry

end DifferentialGeometry.PDE.RicciFlow
