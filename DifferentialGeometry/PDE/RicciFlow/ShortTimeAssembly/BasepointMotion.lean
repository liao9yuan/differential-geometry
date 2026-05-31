/-
The basepoint-motion datum for the moving-basepoint metric slot: the derivative of
the frozen metric along the conjugating orbit equals the negative metric-transport
residual, with the curve-level datum and the directional-derivative identity.
Skeleton stubs for the short-time-existence blueprint (GAP 2, basepoint motion).
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

-- The base-point-motion curve `s ↦ g.inner (Φ_fam s x) (frozen v) (frozen w)` is the
-- composite of the orbit `s ↦ Φ_fam s x` (with `horbit` giving the manifold velocity
-- `-(X (Φ_fam t x))` at `t`) and the scalar map `p ↦ g.inner p (frozen v) (frozen w)`.  Its
-- within-set derivative at `t` is, by the chain rule, the directional derivative of that scalar
-- metric map along `-(X α)`, which `basepoint_directional_deriv_eq_neg_residual` evaluates to
-- `-metricTransportResidual`.  The chain rule (`MDifferentiableAt.comp_hasMFDerivWithinAt`,
-- then `hasMFDerivWithinAt_iff_hasFDerivWithinAt`) requires the manifold-differentiability of
-- the scalar metric map `p ↦ g.inner p a b` at `α` for the FROZEN tangent vectors `a`, `b`.
-- That regularity is the metric-coefficient (chart-Gram-matrix) smoothness, the same content
-- as the value identity in `basepoint_directional_deriv_eq_neg_residual`: it is the genuine
-- open analytic input of the base-point-motion piece (the metric-coefficient directional
-- derivative read as the Christoffel pairing `metricTransportResidual`).  The constant-`E`
-- section `fun p => a` is NOT a smooth tangent vector field on a curved manifold, so the
-- standard `inner_bundle`/`clm_bundle_apply₂` smoothness combinators do not apply directly;
-- this must be discharged in chart coordinates from the smooth chart-Gram-matrix entries.
theorem basepoint_metric_along_curve
    (g : SmoothRiemannianMetric I M) (X : Cₛ^∞⟮I; E, (TangentSpace I)⟯)
    (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)) (t : ℝ) (x : M) (v w : TangentSpace I x)
    (horbit : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (-(X (Φ_fam t x))))) :
    HasDerivWithinAt
      (fun s : ℝ => g.inner ((Φ_fam s : M → M) x)
        (mfderiv I I (Φ_fam t : M → M) x v) (mfderiv I I (Φ_fam t : M → M) x w))
      (-metricTransportResidual (I := I) g X Φ_fam t x v w) (Set.Ici 0) t := sorry

-- GENUINE OPEN ANALYTIC INPUT (the single base-point-motion gap, isolated here).
-- The directional derivative of the scalar metric map `p ↦ g.inner p a b` (`a`, `b` the frozen
-- pushforwards) along the orbit velocity `-(X α)` equals `-metricTransportResidual`.  Mathematically
-- this is the chart metric-compatibility identity: differentiating the Gram-matrix coefficients of
-- `g` along `X` produces the symmetric Christoffel pairing `g(Γ(X̃,a),b) + g(a,Γ(X̃,b))` (=
-- `metricTransportResidual`), via `∇g = 0` (`LeviCivita_isMetricCompatible`) and the covariant
-- derivative of a chart-constant section being the Christoffel correction (`christoffelCorrection`).
-- The project does not yet carry the chart-coordinate metric-coefficient-derivative lemma nor the
-- covariant-derivative-of-a-constant-chart-section identity needed to assemble this; building them
-- (the metric-coefficient directional derivative read as the Christoffel pairing) is the remaining
-- analytic obligation.  It is NOT covered by the paired-residual pushforward-kinetic tower
-- (`variational_flow_flat_paired_residual_*`), which differentiates the FROZEN-base-point
-- pushforward-kinetic curve `s ↦ g.inner (Φ_fam t x) (mfderiv (Φ_fam s) …)`, a genuinely different
-- curve from the base-point-motion curve `s ↦ g.inner (Φ_fam s x) (frozen …)` here.
theorem basepoint_directional_deriv_eq_neg_residual
    (g : SmoothRiemannianMetric I M) (X : Cₛ^∞⟮I; E, (TangentSpace I)⟯)
    (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)) (t : ℝ) (x : M) (v w : TangentSpace I x) :
    mfderiv I 𝓘(ℝ) (fun p : M => g.inner p (mfderiv I I (Φ_fam t : M → M) x v)
      (mfderiv I I (Φ_fam t : M → M) x w)) (Φ_fam t x) (-(X (Φ_fam t x)))
    = -metricTransportResidual (I := I) g X Φ_fam t x v w := sorry

theorem basepoint_motion_datum
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (horbit : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (-(deTurckVF (I := I) (g_DT t) g_bg (Φ_fam t x))))) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt
        (fun s : ℝ => (g_DT t).inner ((Φ_fam s : M → M) x)
          (mfderiv I I (Φ_fam t : M → M) x v) (mfderiv I I (Φ_fam t : M → M) x w))
        (-metricTransportResidual (I := I) (g_DT t)
            (deTurckVF (I := I) (g_DT t) g_bg) Φ_fam t x v w) (Set.Ici 0) t := by
  -- Per interior point, this is exactly `basepoint_metric_along_curve` instantiated with the
  -- frozen metric `g := g_DT t` and the DeTurck field `X := deTurckVF (g_DT t) g_bg`: the orbit
  -- velocity `-deTurckVF (g_DT t) g_bg (Φ_fam t x)` supplied by `horbit` matches the
  -- `-(X (Φ_fam t x))` velocity that node consumes (`X (Φ_fam t x)` unfolds definitionally to
  -- `deTurckVF (g_DT t) g_bg (Φ_fam t x)`).  Pure specialisation; no new analytic content.
  intro t ht x v w
  exact basepoint_metric_along_curve (I := I) (g_DT t)
    (deTurckVF (I := I) (g_DT t) g_bg) Φ_fam t x v w (horbit t ht x)

end DifferentialGeometry.PDE.RicciFlow
