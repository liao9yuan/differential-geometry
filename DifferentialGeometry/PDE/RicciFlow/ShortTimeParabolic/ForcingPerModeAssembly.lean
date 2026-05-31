/-
Interior continuity of the DeTurck geometric forcing (M2) and the term-by-term
per-mode assembly of the interior time-derivative (M3). Skeleton stubs for the
short-time-existence blueprint (GAP 1, spectral M2/M3).
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

/-- **Interior continuity of the continuous DeTurck forcing.**

Re-anchored away from the finite-support-gated `deTurckGeometricN` (globally
discontinuous: it jumps to `0` off the non-open finite-support locus, so
`s ↦ deTurckGeometricN g_bg a (u₁ s)` is genuinely discontinuous on the infinite-
support path) onto the *same* continuous realize-based nonlinearity `N_cont` as
in `deturckN_hscale_lipschitz` (binder/construction shape kept IDENTICAL).

As in `permode_sum_hasderivat`, the order-`(a+1)` carrier `u₁` is anchored to an
order-`(a+2)` lift `u₂` via `hu₁`, so the solution field's continuity in the
higher norm is available. The construction data `N_cont`, `repr`, `Nsec` and the
construction/realize-identity hypotheses `hN_coeff`, `hNsec_realize`,
`hrepr_small` are exactly those of `deturckN_hscale_lipschitz` (the *same*
continuous nonlinearity): coordinate/realize identities about `N_cont`'s
coordinates and `Nsec`'s bilinear extraction, NOT the continuity conclusion. The
`hcont`/`hball` hypotheses confine the carrier to the ball where the realize
construction is valid.

The conclusion is the continuity of `s ↦ N_cont (u₁ s)` (the *continuous*
nonlinearity), which is TRUE and dependency-sufficient: it follows in the fill
phase from the continuity of `u₁` (through `u₂`), of the linear realize
`ccTensorBilinSymm`, and of the eigenbasis-coordinate packaging. -/
theorem forcing_continuous_interior
    (g_bg : SmoothRiemannianMetric I M) (a : ℕ) {T : ℝ}
    (u₂ : ℝ → tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2))
    (u₁ : ℝ → tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1))
    (u₀ : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2)) (R : ℝ)
    (hu₁ : ∀ s, u₁ s = tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
      (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))
    (N_cont : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1) →
      tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ))
    (repr : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1) →
      DifferentialGeometry.Integral.L2.SmoothCcTensor g_bg 0 2)
    (Nsec : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1) →
      DifferentialGeometry.Integral.L2.SmoothCcTensor g_bg 0 2)
    (hN_coeff : ∀ (u : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1))
        (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g_bg 0 2),
      (N_cont u).coeff i =
        tensorL2Coeff_ofCompact (I := I) (M := M)
          (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M) g_bg 0 2)
          (DifferentialGeometry.Integral.L2.SmoothCcTensor.toL2 (Nsec u)) i)
    (hNsec_realize : ∀ (u : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1))
        (x : M) (v w : TangentSpace I x),
      ccTensorBilinSymm (I := I) g_bg (Nsec u) x v w =
        ccTensorBilinSymm (I := I) g_bg (repr u) x v w)
    (hrepr_small : ∀ u : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1),
      ∃ δ' : ℝ, δ' < 1 ∧
        gFibreOpBound (I := I) (M := M) g_bg
          (ccTensorBilinSymm (I := I) g_bg (repr u)) δ')
    (hcont : ∀ ε : ℝ, 0 < ε → ContinuousOn u₁ (Set.Icc ε T))
    (hball : ∀ ε : ℝ, 0 < ε → ∀ s ∈ Set.Icc ε T,
      u₁ s ∈ Metric.closedBall
        (tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
          (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) u₀) R) :
    ∀ ε : ℝ, 0 < ε →
      ContinuousOn (fun s => (N_cont (u₁ s) :
        tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ))) (Set.Icc ε T) := sorry

theorem permode_sum_hasderivat
    (g_bg : SmoothRiemannianMetric I M) (a : ℕ) {T : ℝ}
    (u : MaxRegSolutionSpace (I := I) (M := M) (a : ℝ) T)
    (u₂ : ℝ → tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2))
    (u₁ : ℝ → tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1))
    (hu₂ : ∀ s, tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
      (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ s) = timeH1.toFun u s)
    (hu₁ : ∀ s, u₁ s = tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
      (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s)) :
    ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt (fun r => (timeH1.toFun u r : tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ)))
        (scaleLaplacianFun (I := I) (M := M) (u₂ s) +
          deTurckGeometricN (I := I) g_bg a (u₁ s)) s := sorry

end DifferentialGeometry.PDE.RicciFlow
