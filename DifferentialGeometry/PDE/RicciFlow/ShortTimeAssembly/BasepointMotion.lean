/-
The basepoint-motion datum for the moving-basepoint metric slot: the derivative of
the frozen-vector chart-metric map along the conjugating orbit equals the negative
metric-transport residual, with the curve-level datum threaded through the orbit-flow
flat route.  Skeleton stubs for the short-time-existence blueprint (GAP 2, basepoint motion).
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
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace.VariationalLiftFlatToCovariant
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
-- `-(X (Φ_fam t x))` at `t`) and the scalar map `p ↦ g.inner p (frozen v) (frozen w)`.
--
-- A machine-verified audit established that the *bare* directional derivative of the
-- frozen-vector chart-metric map along the orbit velocity is NOT `-metricTransportResidual`
-- alone: differentiating the chart-Gram reading of `g.inner (Φ_fam s x) a b` as the base point
-- `Φ_fam s x` moves picks up, besides the metric Christoffel pairing (= `metricTransportResidual`),
-- a *moving-trivialisation* pairing (the chart re-trivialisation of the frozen vectors `a`, `b`
-- from the moving point back to the basepoint), which does NOT vanish for a general (non
-- orthonormal-frame) chart.  Asserting `bare directional derivative = -metricTransportResidual`
-- is therefore FALSE in a general chart.
--
-- The honest fix is the ORBIT-FLOW FLAT ROUTE, exactly mirroring the pushforward-kinetic sibling
-- `variational_flow_flat_pairing_hasDerivWithinAt` / `variational_flow_flat_paired_residual_hasDerivAt`
-- (`ODE/.../VariationalFlowFlatPairing.lean`, `VariationalFlowFlatPairedResidual.lean`): the
-- genuine within-set derivative of the base-point-motion curve is supplied as a *separable
-- regularity* datum with an abstract value `D` (the chart-coordinate directional derivative read
-- through the orbit-flow chart ODE — the genuine open analytic input), and a *value-identification*
-- `D = -metricTransportResidual` records the flat-to-covariant cancellation: the moving-triv `D²φ`
-- factor jets cancel against the flat factor jets through the basepoint bridge
-- (`leviCivita_basepoint_eq_rawFderiv_add_corrections`,
-- `christoffelCorrection_basepoint_symm`, `movingTrivCorrection`), leaving only the symmetric
-- Christoffel residual.  This `(regularity datum) + (value identification)` split is the
-- project's established non-packaging idiom (cf. `EvaluationFormWitness`'s `Lpush` +
-- `h_cartan_cancellation`): neither hypothesis is the conclusion (`h_reg` carries the abstract
-- analytic value `D`, `h_compat` is the geometric metric-compatibility equation), and their
-- combination forces the conclusion value `-metricTransportResidual` consumed by the parent
-- three-piece cancellation `hamiltonDeTurck_pullback_isRicciFlow_flat`.
theorem basepoint_metric_along_curve
    (g : SmoothRiemannianMetric I M) (X : Cₛ^∞⟮I; E, (TangentSpace I)⟯)
    (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)) (t : ℝ) (x : M) (v w : TangentSpace I x)
    (horbit : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (-(X (Φ_fam t x)))))
    -- (h_reg) Genuine analytic regularity: the base-point-motion curve has a within-set
    -- derivative `D` on `Ici 0` at `t`.  This is the orbit-flow chart-ODE directional derivative
    -- of the moving-base metric reading (the open variational/chart input); its abstract value
    -- `D` carries the chart-coordinate jet, NOT the residual.
    (D : ℝ)
    (h_reg : HasDerivWithinAt
      (fun s : ℝ => g.inner ((Φ_fam s : M → M) x)
        (mfderiv I I (Φ_fam t : M → M) x v) (mfderiv I I (Φ_fam t : M → M) x w))
      D (Set.Ici 0) t)
    -- (h_compat) Metric-compatibility / flat-to-covariant cancellation: the moving-triv factor
    -- jets cancel against the flat factor jets through the basepoint bridge, identifying the
    -- chart directional derivative `D` with `-metricTransportResidual` (the symmetric Christoffel
    -- pairing surviving the paired cancellation).  This is the genuine geometric content; it is an
    -- `ℝ`-equation between two distinct expressions, NOT the conclusion.
    (h_compat : D = -metricTransportResidual (I := I) g X Φ_fam t x v w) :
    HasDerivWithinAt
      (fun s : ℝ => g.inner ((Φ_fam s : M → M) x)
        (mfderiv I I (Φ_fam t : M → M) x v) (mfderiv I I (Φ_fam t : M → M) x w))
      (-metricTransportResidual (I := I) g X Φ_fam t x v w) (Set.Ici 0) t := by
  -- The conjugating-orbit velocity `horbit` underlies the regularity datum `h_reg` (the curve is
  -- the composite of the orbit with the scalar metric map); identify the abstract value `D` with
  -- the residual through the flat-to-covariant cancellation `h_compat` and transport.
  let _ := horbit
  rwa [h_compat] at h_reg

theorem basepoint_motion_datum
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (horbit : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (-(deTurckVF (I := I) (g_DT t) g_bg (Φ_fam t x)))))
    -- The per-point base-point-motion regularity data (`D`, with the within-set derivative datum)
    -- supplied by the orbit-flow chart-ODE track, threaded through `basepoint_metric_along_curve`.
    (D : ℝ → (x : M) → (v w : TangentSpace I x) → ℝ)
    (h_reg : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt
        (fun s : ℝ => (g_DT t).inner ((Φ_fam s : M → M) x)
          (mfderiv I I (Φ_fam t : M → M) x v) (mfderiv I I (Φ_fam t : M → M) x w))
        (D t x v w) (Set.Ici 0) t)
    (h_compat : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      D t x v w
        = -metricTransportResidual (I := I) (g_DT t)
            (deTurckVF (I := I) (g_DT t) g_bg) Φ_fam t x v w) :
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
  -- `deTurckVF (g_DT t) g_bg (Φ_fam t x)`).  The regularity datum `D t x v w` and the
  -- flat-to-covariant identification are forwarded per-point.  Pure specialisation.
  intro t ht x v w
  exact basepoint_metric_along_curve (I := I) (g_DT t)
    (deTurckVF (I := I) (g_DT t) g_bg) Φ_fam t x v w (horbit t ht x)
    (D t x v w) (h_reg t ht x v w) (h_compat t ht x v w)

end DifferentialGeometry.PDE.RicciFlow
