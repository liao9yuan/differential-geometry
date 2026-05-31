/-
Global cutoff extension of the interior jointly-smooth field to a globally smooth
autonomized field, and the joint-`C∞` ⇒ autonomized-`C¹` predicate for the
cutoff. Skeleton stubs for the short-time-existence blueprint (GAP 2, field
globalization).
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

theorem interior_field_global_cutoff_extension
    (X_DT : ℝ → ∀ x : M, TangentSpace I x) (T : ℝ)
    (hint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X_DT q.1 q.2) : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    {a b : ℝ} (hab : 0 < a) (hab' : a < b) (hbT : b < T) :
    ∃ (Xt : ℝ → ∀ x : M, TangentSpace I x) (δ : ℝ), 0 < δ ∧
      (∀ s ∈ Set.Ioo (a - δ) (b + δ), ∀ x : M, Xt s x = X_DT s x) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
        (fun q : ℝ × M => (TotalSpace.mk' E q.2 (Xt q.1 q.2) : TangentBundle I M)) ∧
      AutonomizedFieldJointC1 (I := I) Xt := sorry

theorem deturck_vf_autonomized_c1
    (Xt : ℝ → ∀ x : M, TangentSpace I x)
    (hXt : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (Xt q.1 q.2) : TangentBundle I M))) :
    AutonomizedFieldJointC1 (I := I) Xt := sorry

end DifferentialGeometry.PDE.RicciFlow
