import DifferentialGeometry.Algebra.Basic
import DifferentialGeometry.Algebra.Metric
import DifferentialGeometry.Geometry.Connection
import DifferentialGeometry.Operators.Laplacian
import DifferentialGeometry.Operators.Gradient
import DifferentialGeometry.Flows.RicciFlow.Basic
import DifferentialGeometry.Flows.RicciFlow.Evolution.ScalarCurvature
import DifferentialGeometry.Flows.RicciFlow.Evolution.Gradient
import DifferentialGeometry.Flows.RicciFlow.Evolution.Laplacian

set_option autoImplicit false
set_option linter.style.longLine false

variable {Time R V : Type}
variable [CommRing R] [AddCommGroup V] [Module R V]
variable [DerivationAction R V] [LieBracket V] [TraceOperator R V]
variable [DerivationRules R V] [LieDerivationRules R V] [TraceLinearityRules R V]
variable [Invertible (2 : R)]
variable [TimeDerivative Time R] [TimeDerivative Time V]
variable [TimeDerivativeRules Time R V] [ActionTimeDerivativeRules Time R V]

/-!
# Ricci Flow Calculus Interface

This file extracts the key Ricci flow evolution properties proven in the `Evolution` folder
 into an integrated calculus interface (`RicciFlowCalculus`).

Note that the class here is supported by instance `instRicciFlowCalculus`, not axioms.
-/

class RicciFlowCalculus
  (g_fam : Time → MetricDuality R V)
  (conn_fam : Time → AffineConnection R V)
  [MetricTimeDerivativeRules Time R V g_fam]
  [∀ s, MetricTraceOperator R V ((g_fam s).toNonDegenerateMetric.toMetricTensor)]
  [RicciFlow Time (fun t => (g_fam t).toNonDegenerateMetric.toMetricTensor) conn_fam] where

  -- 1. Laplacian Evolution
  dt_laplacian : ∀ (u : R) t,
    TimeDerivative.partial_t (fun s => TraceOperator.trace (fun X => (g_fam s).raise (hessianForm (conn_fam s) u) X)) t =
    (2:R) * tensorInnerProduct (g_fam t) (ricciForm (conn_fam t)) (hessianForm (conn_fam t) u) -
    TraceOperator.trace (fun X => (g_fam t).raise (partial_conn_form g_fam conn_fam u t) X)

  -- 2. Gradient Squared Evolution
  dt_grad_sq : ∀ (u : Time → R) t,
    TimeDerivative.partial_t (fun s => (g_fam s).g (grad (g_fam s) (u s)) (grad (g_fam s) (u s))) t =
    (2:R) * ricciForm (conn_fam t) (grad (g_fam t) (u t)) (grad (g_fam t) (u t)) +
    (2:R) * (g_fam t).g (grad (g_fam t) (u t)) (grad (g_fam t) (TimeDerivative.partial_t u t))

  -- 3. Scalar Curvature Evolution
  dt_R : ∀ (t : Time),
    (∀ s, ScalarCurvature (conn_fam s) ((g_fam s).toNonDegenerateMetric.toMetricTensor) =
          TraceOperator.trace (fun X => (g_fam s).raise (ricciForm (conn_fam s)) X)) →
    TimeDerivative.partial_t (fun s => ScalarCurvature (conn_fam s) ((g_fam s).toNonDegenerateMetric.toMetricTensor)) t =
    (2:R) * tensorNormSq (g_fam t) (ricciForm (conn_fam t)) +
    TraceOperator.trace (fun X => (g_fam t).raise (partial_ricci_form conn_fam t) X)

instance instRicciFlowCalculus
  {Time R V : Type}
  [CommRing R] [AddCommGroup V] [Module R V]
  [DerivationAction R V] [LieBracket V] [TraceOperator R V]
  [DerivationRules R V] [LieDerivationRules R V] [TraceLinearityRules R V]
  [Invertible (2 : R)]
  [TimeDerivative Time R] [TimeDerivative Time V]
  [TimeDerivativeRules Time R V] [ActionTimeDerivativeRules Time R V]
  (g_fam : Time → MetricDuality R V)
  (conn_fam : Time → AffineConnection R V)
  [MetricTimeDerivativeRules Time R V g_fam]
  [∀ s, MetricTraceOperator R V ((g_fam s).toNonDegenerateMetric.toMetricTensor)]
  [RicciFlow Time (fun t => (g_fam t).toNonDegenerateMetric.toMetricTensor) conn_fam] :
  RicciFlowCalculus g_fam conn_fam where
  dt_laplacian := by
    intro u t
    exact laplacian_evolution g_fam conn_fam u t
  dt_grad_sq := by
    intro u t
    exact gradient_squared_evolution g_fam conn_fam u t
  dt_R := by
    intro t h_trace
    exact scalar_curvature_evolution g_fam conn_fam h_trace t
