import DifferentialGeometry.Synthetic.Algebra.VectorField
import DifferentialGeometry.Synthetic.Algebra.Metric
import DifferentialGeometry.Synthetic.Algebra.Trace
import DifferentialGeometry.Synthetic.Geometry.Connection
import DifferentialGeometry.Synthetic.Geometry.Curvature
import DifferentialGeometry.Synthetic.Operator.Time
import DifferentialGeometry.Synthetic.Operator.Variation
import DifferentialGeometry.Synthetic.Flow.RicciFlow.Basic
import DifferentialGeometry.Synthetic.Geometry.RicciTensor
import DifferentialGeometry.Synthetic.Analysis.TensorInnerProduct
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

open AbstractDerivationAction
open AbstractLieBracket

open DifferentialGeometry TensorAlgebra

variable {R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
variable [AbstractDerivationAction R V] [AbstractLieBracket V] [TraceOperator R V]
variable [DerivationRules R V] [LieDerivationRules R V] [TraceLinearityRules R V]
variable [Invertible (2 : R)]

def partial_ricci_form {Time R V : Type}
  [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] [AbstractDerivationAction R V] [AbstractLieBracket V] [TraceOperator R V] [DerivationRules R V] [LieDerivationRules R V] [TraceLinearityRules R V]
  [TimeDerivative Time R] [TimeDerivative Time V]
  [TimeDerivativeRules Time R V]
  (conn_fam : Time → AbstractAffineConnection R V)
  (t : Time) : AbstractBilinearForm R V :=
  TensorAlgebra.fromBilinear
    { toFun := fun X =>
        { toFun := fun Y => TimeDerivative.partial_t (fun s => tensor_eval (ricciForm (conn_fam s)) ![X, Y] ![]) t
          map_add' := fun Y1 Y2 => by
            have h : (fun s => tensor_eval (ricciForm (conn_fam s)) ![X, (Y1 + Y2)] ![]) = fun s => tensor_eval (ricciForm (conn_fam s)) ![X, Y1] ![] + tensor_eval (ricciForm (conn_fam s)) ![X, Y2] ![] := by
              funext s; exact tensor_eval_add_right (ricciForm (conn_fam s)) X Y1 Y2
            rw [h, TimeDerivativeRules.t_add V]
          map_smul' := fun c Y => by
            have h : (fun s => tensor_eval (ricciForm (conn_fam s)) ![X, (c • Y)] ![]) = fun s => c * tensor_eval (ricciForm (conn_fam s)) ![X, Y] ![] := by
              funext s; exact tensor_eval_smul_right (ricciForm (conn_fam s)) c X Y
            rw [h, TimeDerivativeRules.t_smul V c]
            rfl }
      map_add' := fun X1 X2 => LinearMap.ext fun Y => by
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
        have h : (fun s => tensor_eval (ricciForm (conn_fam s)) ![(X1 + X2), Y] ![]) = fun s => tensor_eval (ricciForm (conn_fam s)) ![X1, Y] ![] + tensor_eval (ricciForm (conn_fam s)) ![X2, Y] ![] := by
          funext s; exact tensor_eval_add_left (ricciForm (conn_fam s)) X1 X2 Y
        rw [h, TimeDerivativeRules.t_add V]
      map_smul' := fun c X => LinearMap.ext fun Y => by
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, RingHom.id_apply]
        have h : (fun s => tensor_eval (ricciForm (conn_fam s)) ![(c • X), Y] ![]) = fun s => c * tensor_eval (ricciForm (conn_fam s)) ![X, Y] ![] := by
          funext s; exact tensor_eval_smul_left (ricciForm (conn_fam s)) c X Y
        rw [h, TimeDerivativeRules.t_smul V c]
        rfl }

lemma partial_ricci_form_eval {Time : Type} [TimeDerivative Time R] [TimeDerivative Time V] [TimeDerivativeRules Time R V]
  (conn_fam : Time → AbstractAffineConnection R V) (t : Time) (X Y : V) :
  tensor_eval (partial_ricci_form conn_fam t) ![X, Y] ![] = TimeDerivative.partial_t (fun s => tensor_eval (ricciForm (conn_fam s)) ![X, Y] ![]) t := by
  dsimp [partial_ricci_form]
  rw [TensorAlgebra.tensor_eval_fromBilinear]
  rfl

lemma ricci_raise_variation {Time : Type}
  [TimeDerivative Time R] [TimeDerivative Time V]
  [TimeDerivativeRules Time R V]
  (g_fam : Time → MetricDuality R V)
  (conn_fam : Time → AbstractAffineConnection R V)
  [MetricTimeDerivativeRules Time R V g_fam]

  (X Y : V) (t : Time) :
  (g_fam t).g (TimeDerivative.partial_t (fun s => (g_fam s).raise (ricciForm (conn_fam s)) X) t) Y =
  - tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![((g_fam t).raise (ricciForm (conn_fam t)) X), Y] ![]
  + tensor_eval (partial_ricci_form conn_fam t) ![X, Y] ![] := by
  have raise_def : ∀ s, (g_fam s).g ((g_fam s).raise (ricciForm (conn_fam s)) X) Y = tensor_eval (ricciForm (conn_fam s)) ![X, Y] ![] := fun s => (g_fam s).g_raise (ricciForm (conn_fam s)) X Y
  have t_both : TimeDerivative.partial_t (fun s => (g_fam s).g ((g_fam s).raise (ricciForm (conn_fam s)) X) Y) t = TimeDerivative.partial_t (fun s => tensor_eval (ricciForm (conn_fam s)) ![X, Y] ![]) t := by
    congr 1; funext s; exact raise_def s
  have t_metric_val : TimeDerivative.partial_t (fun s => (g_fam s).g ((g_fam s).raise (ricciForm (conn_fam s)) X) Y) t =
    tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![((g_fam t).raise (ricciForm (conn_fam t)) X), Y] ![] +
    (g_fam t).g (TimeDerivative.partial_t (fun s => (g_fam s).raise (ricciForm (conn_fam s)) X) t) Y +
    (g_fam t).g ((g_fam t).raise (ricciForm (conn_fam t)) X) (TimeDerivative.partial_t (fun _ => Y) t) :=
    MetricTimeDerivativeRules.t_metric (fun s => (g_fam s).raise (ricciForm (conn_fam s)) X) (fun _ => Y) t
  have t_Y : TimeDerivative.partial_t (fun _ => Y) t = 0 := MetricTimeDerivativeRules.t_const_V g_fam Y t
  rw [t_Y] at t_metric_val
  have h_zero : (g_fam t).g ((g_fam t).raise (ricciForm (conn_fam t)) X) 0 = 0 := metric_zero_right _ _
  rw [h_zero, add_zero] at t_metric_val
  rw [t_metric_val] at t_both
  have h_ricci : TimeDerivative.partial_t (fun s => tensor_eval (ricciForm (conn_fam s)) ![X, Y] ![]) t = tensor_eval (partial_ricci_form conn_fam t) ![X, Y] ![] := (partial_ricci_form_eval conn_fam t X Y).symm
  rw [h_ricci] at t_both
  calc (g_fam t).g (TimeDerivative.partial_t (fun s => (g_fam s).raise (ricciForm (conn_fam s)) X) t) Y
    _ = tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![((g_fam t).raise (ricciForm (conn_fam t)) X), Y] ![] + (g_fam t).g (TimeDerivative.partial_t (fun s => (g_fam s).raise (ricciForm (conn_fam s)) X) t) Y - tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![((g_fam t).raise (ricciForm (conn_fam t)) X), Y] ![] := by abel
    _ = tensor_eval (partial_ricci_form conn_fam t) ![X, Y] ![] - tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![((g_fam t).raise (ricciForm (conn_fam t)) X), Y] ![] := by rw [t_both]
    _ = - tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![((g_fam t).raise (ricciForm (conn_fam t)) X), Y] ![] + tensor_eval (partial_ricci_form conn_fam t) ![X, Y] ![] := by abel

/--
$\partial_t R = \Delta R + 2 |\text{Ric}|^2$
books/Poincare_Conjecture_Blueprint/chapter03b.tex, around line 583
-/
lemma scalar_curvature_evolution {Time : Type}
  [TimeDerivative Time R] [TimeDerivative Time V]
  [TimeDerivativeRules Time R V]
  (g_fam : Time → MetricDuality R V)
  (conn_fam : Time → AbstractAffineConnection R V)
  [MetricTimeDerivativeRules Time R V g_fam]
  [∀ s, MetricTraceOperator R V ((g_fam s).toNonDegenerateMetric.toAbstractMetricTensor)]
  [RicciFlow Time (fun t => (g_fam t).toNonDegenerateMetric.toAbstractMetricTensor) conn_fam]

  (h_trace_R : ∀ s, ScalarCurvature (conn_fam s) ((g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) =
                    TraceOperator.trace (fun X => (g_fam s).raise (ricciForm (conn_fam s)) X))
  (t : Time) [IR : TensorInnerProductRules R V (g_fam t)] :
  TimeDerivative.partial_t (fun s => ScalarCurvature (conn_fam s) ((g_fam s).toNonDegenerateMetric.toAbstractMetricTensor)) t =
  (2:R) * tensorNormSq (g_fam t) (ricciForm (conn_fam t))
  + TraceOperator.trace (fun X => (g_fam t).raise (partial_ricci_form conn_fam t) X) := by
  have rewrite_R : (fun s => ScalarCurvature (conn_fam s) ((g_fam s).toNonDegenerateMetric.toAbstractMetricTensor)) =
                   (fun s => TraceOperator.trace (fun X => (g_fam s).raise (ricciForm (conn_fam s)) X)) := by
    funext s
    exact h_trace_R s
  rw [rewrite_R]
  have product_rule : TimeDerivative.partial_t (fun s => TraceOperator.trace (fun X => (g_fam s).raise (ricciForm (conn_fam s)) X)) t =
                      TraceOperator.trace (fun X => TimeDerivative.partial_t (fun s => (g_fam s).raise (ricciForm (conn_fam s)) X) t) :=
    MetricTimeDerivativeRules.t_trace g_fam (fun s X => (g_fam s).raise (ricciForm (conn_fam s)) X) t
  rw [product_rule]
  have partial_raise_eq : ∀ X, TimeDerivative.partial_t (fun s => (g_fam s).raise (ricciForm (conn_fam s)) X) t =
                          - (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise (ricciForm (conn_fam t)) X)
                          + (g_fam t).raise (partial_ricci_form conn_fam t) X := by
    intro X
    apply (g_fam t).toNonDegenerateMetric.eq_of_forall_g_eq
    intro Z
    have h1 := ricci_raise_variation g_fam conn_fam X Z t
    rw [h1]
    have h2 : (g_fam t).g (- (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise (ricciForm (conn_fam t)) X) + (g_fam t).raise (partial_ricci_form conn_fam t) X) Z =
              (g_fam t).g (- (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise (ricciForm (conn_fam t)) X)) Z +
              (g_fam t).g ((g_fam t).raise (partial_ricci_form conn_fam t) X) Z := by
      exact (g_fam t).bilinear_add_left _ _ _
    rw [h2]
    have h3 : (g_fam t).g (- (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise (ricciForm (conn_fam t)) X)) Z =
              - (g_fam t).g ((g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise (ricciForm (conn_fam t)) X)) Z := metric_neg_left _ _ _
    rw [h3]
    have h5 : (g_fam t).g ((g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise (ricciForm (conn_fam t)) X)) Z =
              tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![((g_fam t).raise (ricciForm (conn_fam t)) X), Z] ![] := (g_fam t).g_raise _ _ _
    have h6 : (g_fam t).g ((g_fam t).raise (partial_ricci_form conn_fam t) X) Z =
              tensor_eval (partial_ricci_form conn_fam t) ![X, Z] ![] := (g_fam t).g_raise _ _ _
    rw [h5, h6]
  have trace_eq : (TraceOperator.trace (fun X => TimeDerivative.partial_t (fun s => (g_fam s).raise (ricciForm (conn_fam s)) X) t) : R) =
                  TraceOperator.trace (fun X => - (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise (ricciForm (conn_fam t)) X) + (g_fam t).raise (partial_ricci_form conn_fam t) X) := by
    congr 1
    funext X
    exact partial_raise_eq X
  rw [trace_eq]
  have trace_add : (TraceOperator.trace (fun X => - (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise (ricciForm (conn_fam t)) X) + (g_fam t).raise (partial_ricci_form conn_fam t) X) : R) =
                   TraceOperator.trace (fun X => - (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise (ricciForm (conn_fam t)) X)) +
                   TraceOperator.trace (fun X => (g_fam t).raise (partial_ricci_form conn_fam t) X) := by
    have split_eq : (fun X => - (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise (ricciForm (conn_fam t)) X) + (g_fam t).raise (partial_ricci_form conn_fam t) X) =
                    (fun X => - (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise (ricciForm (conn_fam t)) X)) +
                    (fun X => (g_fam t).raise (partial_ricci_form conn_fam t) X) := rfl
    rw [split_eq]
    exact TraceLinearityRules.trace_add
  rw [trace_add]
  have trace_neg1 : (TraceOperator.trace (fun X => - (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise (ricciForm (conn_fam t)) X)) : R) =
                    -(1:R) * TraceOperator.trace (fun X => (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise (ricciForm (conn_fam t)) X)) := by
    have smul_eq : (fun X => - (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise (ricciForm (conn_fam t)) X)) =
                   (fun X => -(1:R) • (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise (ricciForm (conn_fam t)) X)) := by
      funext X
      exact (neg_one_smul R _).symm
    rw [smul_eq]
    exact TraceLinearityRules.trace_smul
  rw [trace_neg1]
  have h_rf : (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) = (-(2:R)) • (ricciForm (conn_fam t)) := RicciFlow.evolution t
  have h_raise_rf : ∀ Z, (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) Z =
                         (-(2:R)) • (g_fam t).raise (ricciForm (conn_fam t)) Z := by
    intro Z
    rw [h_rf]
    exact raise_smul (g_fam t) (ricciForm (conn_fam t)) (-(2:R)) Z
  have inner_prod_sub : (TraceOperator.trace (fun X => (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise (ricciForm (conn_fam t)) X)) : R) =
                        -(2:R) * TraceOperator.trace (fun X => (g_fam t).raise (ricciForm (conn_fam t)) ((g_fam t).raise (ricciForm (conn_fam t)) X)) := by
    have eq_func : (fun X => (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise (ricciForm (conn_fam t)) X)) =
                   (fun X => (-(2:R)) • (g_fam t).raise (ricciForm (conn_fam t)) ((g_fam t).raise (ricciForm (conn_fam t)) X)) := by
      funext X
      exact h_raise_rf ((g_fam t).raise (ricciForm (conn_fam t)) X)
    rw [eq_func]
    exact TraceLinearityRules.trace_smul
  rw [inner_prod_sub]
  have def_inner : tensorNormSq (g_fam t) (ricciForm (conn_fam t)) =
                   TraceOperator.trace (fun X => (g_fam t).raise (ricciForm (conn_fam t)) ((g_fam t).raise (ricciForm (conn_fam t)) X)) := IR.inner_trace _ _
  rw [← def_inner]
  ring
