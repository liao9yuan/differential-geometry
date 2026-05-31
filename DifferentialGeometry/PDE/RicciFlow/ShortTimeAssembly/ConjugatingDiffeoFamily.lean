/-
The conjugating diffeomorphism family: integrate the negated DeTurck field to a
smooth family of diffeomorphisms anchored at the identity, carrying the bare
backward orbit ODE on the interior. Skeleton stub for the short-time-existence
blueprint (GAP 2, diffeomorphism family).
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

theorem conjugating_diffeo_family
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (T_DT : ℝ) (hDT : 0 < T_DT)
    (h_reg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (deTurckVF (I := I) (g_DT q.1) g_bg q.2)
        : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T_DT ×ˢ Set.univ)) :
    ∃ T : ℝ, 0 < T ∧ T ≤ T_DT ∧ ∃ Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M),
      Φ_fam 0 = _root_.Diffeomorph.refl I M ∞ ∧
      ∀ x : M, ∀ s ∈ Set.Ioo (0 : ℝ) T,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => (Φ_fam u : M → M) x)
          (Set.Ici (0 : ℝ)) s
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (-(deTurckVF (I := I) (g_DT s) g_bg ((Φ_fam s : M → M) x)))) := sorry

end DifferentialGeometry.PDE.RicciFlow
