import DifferentialGeometry.Synthetic.Operator.Time
import DifferentialGeometry.Synthetic.Algebra.VectorField
import DifferentialGeometry.Synthetic.Algebra.Metric
import DifferentialGeometry.Synthetic.Geometry.Connection
import DifferentialGeometry.Synthetic.Operator.Laplacian
import DifferentialGeometry.Synthetic.Operator.Gradient
import DifferentialGeometry.Synthetic.Flow.RicciFlow.Basic
import DifferentialGeometry.Synthetic.Flow.RicciFlow.Evolution.ScalarCurvature
import DifferentialGeometry.Synthetic.Flow.RicciFlow.Evolution.Gradient
import DifferentialGeometry.Synthetic.Flow.RicciFlow.Evolution.Laplacian

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

open DifferentialGeometry TensorAlgebra

variable {Time R V : Type}
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
variable [AbstractDerivationAction R V] [AbstractLieBracket V]
variable [DerivationRules R V] [LieDerivationRules R V]
variable [Invertible (2 : R)]
variable [TimeDerivative Time R] [TimeDerivative Time V]
variable [TimeDerivativeRules Time R V] [ActionTimeDerivativeRules Time R V] [TensorTimeCalculus Time R V]

/-!
# Ricci Flow Calculus Interface

This file extracts the key Ricci flow evolution properties proven in the `Evolution` folder
 into an integrated calculus interface (`RicciFlowCalculus`).

Note that the class here is supported by instance `instRicciFlowCalculus`, not axioms.
-/

class RicciFlowCalculus
  (g_fam : Time → MetricDuality R V)
  (conn_fam : Time → AbstractAffineConnection R V)
  [MetricTimeDerivativeRules Time R V g_fam]
  [∀ s, TensorInnerProductRules R V (g_fam s)]
  [∀ s, AffineTensorCalculus (conn_fam s)]
  [∀ s, RiemannCurvatureTensorOp (conn_fam s)]
  [RicciFlow Time (fun t => (g_fam t).toNonDegenerateMetric.toAbstractMetricTensor) conn_fam]
  [∀ s, MetricCompatible (conn_fam s) (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor] where

  -- 1. Laplacian Evolution
  dt_laplacian : ∀ (u : R) t,
    TimeDerivative.partial_t (fun s => tensor_eval (metric_trace (g_fam s) (0: Fin 2) (0: Fin 1) (hessianForm (g_fam s) (conn_fam s) u)) ![] ![]) t =
    (2:R) * tensorInnerProduct (g_fam t) (ricciForm (conn_fam t)) (hessianForm (g_fam t) (conn_fam t) u) +
    tensor_eval (metric_trace (g_fam t) (0: Fin 2) (0: Fin 1) (TensorTimeCalculus.partial_t_tensor t (fun s => hessianForm (g_fam s) (conn_fam s) u))) ![] ![]

  -- 2. Gradient Squared Evolution
  dt_grad_sq : ∀ (u : Time → R) t,
    TimeDerivative.partial_t (fun s => (g_fam s).g (grad (g_fam s) (u s)) (grad (g_fam s) (u s))) t =
    (2:R) * tensor_eval (ricciForm (conn_fam t)) ![(grad (g_fam t) (u t)), (grad (g_fam t) (u t))] ![] +
    (2:R) * (g_fam t).g (grad (g_fam t) (u t)) (grad (g_fam t) (TimeDerivative.partial_t u t))

  -- 3. Scalar Curvature Evolution
  dt_R : ∀ (t : Time),
    (∀ s, ScalarCurvature (g_fam s) (conn_fam s) =
          tensor_eval (metric_trace (g_fam s) (0: Fin 2) (0: Fin 1) (ricciForm (conn_fam s))) ![] ![]) →
    TimeDerivative.partial_t (fun s => ScalarCurvature (g_fam s) (conn_fam s)) t =
    (2:R) * tensorNormSq (g_fam t) (ricciForm (conn_fam t)) +
    tensor_eval (metric_trace (g_fam t) (0: Fin 2) (0: Fin 1) (TensorTimeCalculus.partial_t_tensor t (fun s => ricciForm (conn_fam s)))) ![] ![]

instance instRicciFlowCalculus
  {Time R V : Type}
  [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
  [AbstractDerivationAction R V] [AbstractLieBracket V]
  [DerivationRules R V] [LieDerivationRules R V]
  [Invertible (2 : R)]
  [TimeDerivative Time R] [TimeDerivative Time V]
  [TimeDerivativeRules Time R V] [ActionTimeDerivativeRules Time R V] [TensorTimeCalculus Time R V]
  (g_fam : Time → MetricDuality R V)
  (conn_fam : Time → AbstractAffineConnection R V)
  [MetricTimeDerivativeRules Time R V g_fam]
  [∀ s, TensorInnerProductRules R V (g_fam s)]
  [∀ s, AffineTensorCalculus (conn_fam s)]
  [∀ s, RiemannCurvatureTensorOp (conn_fam s)]
  [RicciFlow Time (fun t => (g_fam t).toNonDegenerateMetric.toAbstractMetricTensor) conn_fam]
  [∀ s, MetricCompatible (conn_fam s) (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor] :
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
