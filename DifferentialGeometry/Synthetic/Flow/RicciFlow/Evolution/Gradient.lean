import DifferentialGeometry.Synthetic.Algebra.VectorField
import DifferentialGeometry.Synthetic.Algebra.Metric
import DifferentialGeometry.Synthetic.Algebra.Metric
import DifferentialGeometry.Synthetic.Geometry.Connection
import DifferentialGeometry.Synthetic.Geometry.Curvature
import DifferentialGeometry.Synthetic.Operator.Gradient
import DifferentialGeometry.Synthetic.Operator.Time
import DifferentialGeometry.Synthetic.Operator.Variation
import DifferentialGeometry.Synthetic.Flow.RicciFlow.Basic
import DifferentialGeometry.Synthetic.Geometry.RicciTensor
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

open AbstractDerivationAction

open DifferentialGeometry TensorAlgebra

variable {R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
variable [AbstractDerivationAction R V] [AbstractLieBracket V] [TraceOperator R V]
variable [DerivationRules R V] [LieDerivationRules R V] [TraceLinearityRules R V]

/-!
# Evolution of the Gradient under Ricci Flow

This file establishes how the gradient vector field of a time-independent
scalar function evolves when the background metric shifts according to
the Ricci flow equation.
-/

/--
Mathematical Identity: $\partial_t (\nabla u) = 2 \text{Rc}^\sharp (\nabla u)$
Evolution of the gradient of a time-independent scalar function under Ricci flow.
-/
lemma gradient_evolution {Time : Type}
  [TimeDerivative Time R] [TimeDerivative Time V]
  [TimeDerivativeRules Time R V] [ActionTimeDerivativeRules Time R V]
  (g_fam : Time → MetricDuality R V)
  (conn_fam : Time → AbstractAffineConnection R V)
  [MetricTimeDerivativeRules Time R V g_fam]
  [∀ s, AffineTensorCalculus (conn_fam s)] [∀ s, RiemannCurvatureTensorOp (conn_fam s)]
  [RicciFlow Time (fun t => (g_fam t).toNonDegenerateMetric.toAbstractMetricTensor) conn_fam]
  (u : R) (t : Time) :
  TimeDerivative.partial_t (fun s => grad (g_fam s) u) t =
  (2:R) • (g_fam t).raise (ricciForm (conn_fam t)) (grad (g_fam t) u) := by
  apply (g_fam t).toNonDegenerateMetric.eq_of_forall_g_eq
  intro Y
  have h1 : (fun s => (g_fam s).g (grad (g_fam s) u) Y) = fun s => action Y u := by
    funext s
    exact g_grad (g_fam s) u Y
  have h2 : TimeDerivative.partial_t (fun s => (g_fam s).g (grad (g_fam s) u) Y) t = TimeDerivative.partial_t (fun _ => action Y u) t := by
    rw [h1]
  have h3 : TimeDerivative.partial_t (fun _ => action Y u) t = 0 := MetricTimeDerivativeRules.t_const_R g_fam (action Y u) t
  have h4 : TimeDerivative.partial_t (fun s => (g_fam s).g (grad (g_fam s) u) Y) t =
            tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![(grad (g_fam t) u), Y] ![] +
            (g_fam t).g (TimeDerivative.partial_t (fun s => grad (g_fam s) u) t) Y +
            (g_fam t).g (grad (g_fam t) u) (TimeDerivative.partial_t (fun s => Y) t) := by
    exact MetricTimeDerivativeRules.t_metric (fun s => grad (g_fam s) u) (fun s => Y) t
  have h5 : TimeDerivative.partial_t (fun _ => Y) t = 0 := MetricTimeDerivativeRules.t_const_V g_fam Y t
  have h6 : (g_fam t).g (grad (g_fam t) u) (TimeDerivative.partial_t (fun s => Y) t) = 0 := by
    rw [h5]
    exact metric_zero_right ((g_fam t).toNonDegenerateMetric.toAbstractMetricTensor) _
  have h7 : 0 = tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![(grad (g_fam t) u), Y] ![] +
                (g_fam t).g (TimeDerivative.partial_t (fun s => grad (g_fam s) u) t) Y := by
    calc 0 = TimeDerivative.partial_t (fun _ => action Y u) t := h3.symm
         _ = TimeDerivative.partial_t (fun s => (g_fam s).g (grad (g_fam s) u) Y) t := h2.symm
         _ = tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![(grad (g_fam t) u), Y] ![] +
             (g_fam t).g (TimeDerivative.partial_t (fun s => grad (g_fam s) u) t) Y +
             (g_fam t).g (grad (g_fam t) u) (TimeDerivative.partial_t (fun s => Y) t) := h4
         _ = tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![(grad (g_fam t) u), Y] ![] +
             (g_fam t).g (TimeDerivative.partial_t (fun s => grad (g_fam s) u) t) Y + 0 := by rw [h6]
         _ = tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![(grad (g_fam t) u), Y] ![] +
             (g_fam t).g (TimeDerivative.partial_t (fun s => grad (g_fam s) u) t) Y := by abel
  have h8 : (g_fam t).g (TimeDerivative.partial_t (fun s => grad (g_fam s) u) t) Y =
            - tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![(grad (g_fam t) u), Y] ![] := by
    calc (g_fam t).g (TimeDerivative.partial_t (fun s => grad (g_fam s) u) t) Y
        = tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![(grad (g_fam t) u), Y] ![] +
          (g_fam t).g (TimeDerivative.partial_t (fun s => grad (g_fam s) u) t) Y -
          tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![(grad (g_fam t) u), Y] ![] := by abel
      _ = 0 - tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![(grad (g_fam t) u), Y] ![] := by rw [← h7]
      _ = - tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![(grad (g_fam t) u), Y] ![] := by abel
  have h9 : (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) = (- (2:R)) • ricciForm (conn_fam t) :=
    RicciFlow.evolution t
  have h10 : tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![(grad (g_fam t) u), Y] ![] =
             (- (2:R)) * tensor_eval (ricciForm (conn_fam t)) ![(grad (g_fam t) u), Y] ![] := by
    have hsmul : tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![(grad (g_fam t) u), Y] ![] = tensor_eval ((- (2:R)) • ricciForm (conn_fam t)) ![(grad (g_fam t) u), Y] ![] := by rw [h9]
    rw [hsmul]
    exact tensor_eval_smul (- (2:R)) (ricciForm (conn_fam t)) ![(grad (g_fam t) u), Y] ![]
  have h11 : (g_fam t).g (TimeDerivative.partial_t (fun s => grad (g_fam s) u) t) Y =
             (2:R) * tensor_eval (ricciForm (conn_fam t)) ![(grad (g_fam t) u), Y] ![] := by
    rw [h8, h10]
    ring
  have h12 : (g_fam t).g ((2:R) • (g_fam t).raise (ricciForm (conn_fam t)) (grad (g_fam t) u)) Y =
             (2:R) * ((g_fam t).g ((g_fam t).raise (ricciForm (conn_fam t)) (grad (g_fam t) u)) Y) := by
    exact (g_fam t).toNonDegenerateMetric.toAbstractMetricTensor.bilinear_smul_left (2:R) _ Y
  have h13 : (g_fam t).g ((g_fam t).raise (ricciForm (conn_fam t)) (grad (g_fam t) u)) Y =
             tensor_eval (ricciForm (conn_fam t)) ![(grad (g_fam t) u), Y] ![] := (g_fam t).g_raise _ _ _
  rw [h13] at h12
  rw [h11, ← h12]

/--
Mathematical Identity: $\partial_t |\nabla u|^2 = 2 \text{Rc}(\nabla u, \nabla u) + 2 g(\nabla u, \nabla (\partial_t u))$
Evolution of the squared gradient of a time-dependent scalar function under Ricci flow.
-/
lemma gradient_squared_evolution {Time : Type}
  [TimeDerivative Time R] [TimeDerivative Time V]
  [TimeDerivativeRules Time R V] [ActionTimeDerivativeRules Time R V]
  (g_fam : Time → MetricDuality R V)
  (conn_fam : Time → AbstractAffineConnection R V)
  [MetricTimeDerivativeRules Time R V g_fam]
  [∀ s, AffineTensorCalculus (conn_fam s)] [∀ s, RiemannCurvatureTensorOp (conn_fam s)]
  [RicciFlow Time (fun t => (g_fam t).toNonDegenerateMetric.toAbstractMetricTensor) conn_fam]
  (u : Time → R) (t : Time) :
  TimeDerivative.partial_t (fun s => (g_fam s).g (grad (g_fam s) (u s)) (grad (g_fam s) (u s))) t =
  (2:R) * tensor_eval (ricciForm (conn_fam t)) ![(grad (g_fam t) (u t)), (grad (g_fam t) (u t))] ![]
  + (2:R) * (g_fam t).g (grad (g_fam t) (u t)) (grad (g_fam t) (TimeDerivative.partial_t u t)) := by
  let Y := fun s => grad (g_fam s) (u s)
  let Z := Y t

  have h1 : TimeDerivative.partial_t (fun s => (g_fam s).g (Y s) (Y s)) t =
    tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![(Y t), (Y t)] ![] +
    (g_fam t).g (TimeDerivative.partial_t Y t) (Y t) +
    (g_fam t).g (Y t) (TimeDerivative.partial_t Y t) :=
    MetricTimeDerivativeRules.t_metric Y Y t

  have h2 : (g_fam t).g (Y t) (TimeDerivative.partial_t Y t) =
            (g_fam t).g (TimeDerivative.partial_t Y t) (Y t) :=
    (g_fam t).symm _ _

  have h1b : TimeDerivative.partial_t (fun s => (g_fam s).g (Y s) (Y s)) t =
    tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![(Y t), (Y t)] ![] +
    (2:R) * (g_fam t).g (TimeDerivative.partial_t Y t) (Y t) := by
    rw [h1, h2]
    ring

  have pt_Z : TimeDerivative.partial_t (fun s => Z) t = 0 := MetricTimeDerivativeRules.t_const_V g_fam Z t

  have h3 : TimeDerivative.partial_t (fun s => (g_fam s).g (Y s) Z) t =
    tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![(Y t), Z] ![] +
    (g_fam t).g (TimeDerivative.partial_t Y t) Z +
    (g_fam t).g (Y t) (TimeDerivative.partial_t (fun s => Z) t) :=
    MetricTimeDerivativeRules.t_metric Y (fun s => Z) t

  have h4 : (g_fam t).g (Y t) (TimeDerivative.partial_t (fun s => Z) t) = 0 := by
    rw [pt_Z]
    exact metric_zero_right ((g_fam t).toNonDegenerateMetric.toAbstractMetricTensor) (Y t)

  have h5 : TimeDerivative.partial_t (fun s => (g_fam s).g (Y s) Z) t =
    tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![(Y t), Z] ![] +
    (g_fam t).g (TimeDerivative.partial_t Y t) Z := by
    rw [h3, h4]
    abel

  have h6 : (fun s => (g_fam s).g (Y s) Z) = (fun s => action Z (u s)) := by
    funext s
    exact g_grad (g_fam s) (u s) Z

  have h7 : TimeDerivative.partial_t (fun s => (g_fam s).g (Y s) Z) t =
            TimeDerivative.partial_t (fun s => action Z (u s)) t := by
    rw [h6]

  have h8 : TimeDerivative.partial_t (fun s => action Z (u s)) t =
            action Z (TimeDerivative.partial_t u t) :=
    ActionTimeDerivativeRules.t_action Z u t

  have h9 : tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![(Y t), Z] ![] +
            (g_fam t).g (TimeDerivative.partial_t Y t) Z =
            action Z (TimeDerivative.partial_t u t) := by
    rw [← h5, h7, h8]

  have h10 : (g_fam t).g (TimeDerivative.partial_t Y t) (Y t) =
             action (Y t) (TimeDerivative.partial_t u t) -
             tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![(Y t), (Y t)] ![] := by
    change tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![(Y t), (Y t)] ![] + (g_fam t).g (TimeDerivative.partial_t Y t) (Y t) = action (Y t) (TimeDerivative.partial_t u t) at h9
    calc (g_fam t).g (TimeDerivative.partial_t Y t) (Y t)
       = tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![(Y t), (Y t)] ![] +
         (g_fam t).g (TimeDerivative.partial_t Y t) (Y t)
         - tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![(Y t), (Y t)] ![] := by ring
     _ = action (Y t) (TimeDerivative.partial_t u t) -
         tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![(Y t), (Y t)] ![] := by rw [h9]

  have h13 : action (Y t) (TimeDerivative.partial_t u t) =
             (g_fam t).g (Y t) (grad (g_fam t) (TimeDerivative.partial_t u t)) := by
    have hs := g_grad (g_fam t) (TimeDerivative.partial_t u t) (Y t)
    have h_symm := (g_fam t).symm (grad (g_fam t) (TimeDerivative.partial_t u t)) (Y t)
    rw [← hs, h_symm]

  have h14 : (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) =
             (- (2:R)) • ricciForm (conn_fam t) :=
    RicciFlow.evolution t

  have h15 : tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![(Y t), (Y t)] ![] =
             (- (2:R)) * tensor_eval (ricciForm (conn_fam t)) ![(Y t), (Y t)] ![] := by
    have hsmul : tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![(Y t), (Y t)] ![] = tensor_eval ((- (2:R)) • ricciForm (conn_fam t)) ![(Y t), (Y t)] ![] := by rw [h14]
    rw [hsmul]
    exact tensor_eval_smul (- (2:R)) (ricciForm (conn_fam t)) ![(Y t), (Y t)] ![]

  calc TimeDerivative.partial_t (fun s => (g_fam s).g (Y s) (Y s)) t
     = tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![(Y t), (Y t)] ![] +
       (2:R) * (g_fam t).g (TimeDerivative.partial_t Y t) (Y t) := h1b
   _ = tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![(Y t), (Y t)] ![] +
       (2:R) * (action (Y t) (TimeDerivative.partial_t u t) - tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![(Y t), (Y t)] ![]) := by rw [h10]
   _ = (2:R) * action (Y t) (TimeDerivative.partial_t u t) - tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![(Y t), (Y t)] ![] := by ring
   _ = (2:R) * (g_fam t).g (Y t) (grad (g_fam t) (TimeDerivative.partial_t u t)) - (- (2:R)) * tensor_eval (ricciForm (conn_fam t)) ![(Y t), (Y t)] ![] := by rw [h13, h15]
   _ = (2:R) * tensor_eval (ricciForm (conn_fam t)) ![(Y t), (Y t)] ![] + (2:R) * (g_fam t).g (Y t) (grad (g_fam t) (TimeDerivative.partial_t u t)) := by ring
