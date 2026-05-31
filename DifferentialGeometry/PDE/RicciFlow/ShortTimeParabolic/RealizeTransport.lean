/-
The realize-layer transport from the carrier-scale spectral derivative to the
geometric DeTurck–Ricci right-hand side: the carrier-scale realize-evaluate
functional and its factorization, the push of the within-derivative through it,
and the spectral→geometric reconciliation at the solution. Skeleton stubs for the
short-time-existence blueprint (GAP 1, transport layer).
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

theorem realize_eval_carrier_factorization
    (g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (x : M) (v w : TangentSpace I x) :
    ∃ ℓ_a : tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ) →L[ℝ] ℝ,
      ∀ u₂ : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2),
        (hfs : (Function.support u₂.coeff).Finite) →
        (∃ δ' : ℝ, δ' < 1 ∧
          gFibreOpBound (I := I) (M := M) g_bg
            (tensorHsBilinSymm (I := I) g_bg u₂ hfs) δ') →
          (realizeMetricMap (I := I) g_bg a u₂).inner x v w
            = g_bg.inner x v w +
              ℓ_a (tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
                (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) u₂) := sorry

theorem pointwise_deriv_through_realize
    (g_bg : SmoothRiemannianMetric I M) (a : ℕ) {T : ℝ}
    (u₂ : ℝ → tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2))
    (u_car' : ℝ → tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ))
    (x : M) (v w : TangentSpace I x)
    (ℓ_a : tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ) →L[ℝ] ℝ)
    (hreal : ∀ s : ℝ,
      (realizeMetricMap (I := I) g_bg a (u₂ s)).inner x v w
        = g_bg.inner x v w +
          ℓ_a (tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
            (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ s)))
    (hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt
        (fun s : ℝ => tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
          (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ s))
        (u_car' t) (Set.Ici 0) t) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt
        (fun s : ℝ => (realizeMetricMap (I := I) g_bg a (u₂ s)).inner x v w)
        (ℓ_a (u_car' t)) (Set.Ici 0) t := sorry

theorem rhs_matches_deturck_at_solution
    (g_bg : SmoothRiemannianMetric I M) (a : ℕ) {T : ℝ}
    (u₂ : ℝ → tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2))
    (ℓ_a : tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ) →L[ℝ] ℝ)
    (x : M) (v w : TangentSpace I x) :
    ∀ t ∈ Set.Ico (0 : ℝ) T,
      ℓ_a (scaleLaplacianFun (I := I) (M := M) (u₂ t) +
          deTurckGeometricN (I := I) g_bg a
            (tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
              (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ t)))
        = deTurckRicciRHS (I := I) g_bg (realizeMetricMap (I := I) g_bg a (u₂ t)) x v w := sorry

end DifferentialGeometry.PDE.RicciFlow
