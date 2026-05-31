/-
Joint smoothness and up-to-`t = 0` continuity of the time-dependent DeTurck
vector field on the open interior, plus the chart-Gram joint-`C∞` interface.
Skeleton stubs for the short-time-existence blueprint (GAP 2, flow regularity).
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

theorem deturck_vf_joint_smoothness
    (g_bg : SmoothRiemannianMetric I M)
    (g_DT : ℝ → SmoothRiemannianMetric I M) (T : ℝ)
    (h_gDT : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M =>
          Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) x₀ i j
            (extChartAt I x₀ q.2))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.univ)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (deTurckVF (I := I) (g_DT q.1) g_bg q.2)
        : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) := sorry

theorem deturck_vf_continuous_up_to_zero
    (g₀ : SmoothRiemannianMetric I M)
    (g_DT : ℝ → SmoothRiemannianMetric I M) (T : ℝ)
    (h_gram0 : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun q : ℝ × E =>
          Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j q.2)
        (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target))
    (h_partial : ∀ (α : M) (l i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun q : ℝ × E =>
          Integral.DivergenceTheorem.partialDeriv (E := E) l
            (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j) q.2)
        (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target))
    (h_partial2 : ∀ (α : M) (m l i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun q : ℝ × E =>
          Integral.DivergenceTheorem.partialDeriv (E := E) m
            (Integral.DivergenceTheorem.partialDeriv (E := E) l
              (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) α i j)) q.2)
        (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target)) :
    (ContinuousOn (fun q : ℝ × M => (deTurckVF (I := I) (g_DT q.1) g₀ q.2 : TangentSpace I q.2))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ))
    ∧ (∀ (α : M) (k : Fin (Module.finrank ℝ E)),
        ContinuousOn (fun q : ℝ × E =>
          fderiv ℝ (fun y : E =>
            DeTurckLinearization.chartDeTurckVFComp (I := I) (g_DT q.1) g₀ α k y) q.2)
          (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target)) := sorry

theorem deturck_solution_joint_smooth
    (g_DT : ℝ → SmoothRiemannianMetric I M) (T : ℝ)
    (h_smooth : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M =>
          Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT q.1) x₀ i j
            (extChartAt I x₀ q.2))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.univ)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2
        (deTurckVF (I := I) (g_DT q.1) (g_DT 0) q.2) : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) :=
  -- This is `deturck_vf_joint_smoothness` specialised to the background metric
  -- `g_bg := g_DT 0`.  The smoothness hypothesis `h_smooth` is literally the
  -- chart-Gram joint-`C∞` hypothesis `h_gDT` of that theorem (it only constrains
  -- the evolving family `g_DT q.1`, not the background), so it transports verbatim.
  deturck_vf_joint_smoothness (I := I) (g_DT 0) g_DT T h_smooth

end DifferentialGeometry.PDE.RicciFlow
