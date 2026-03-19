import DifferentialGeometry.Algebra.VectorField
import DifferentialGeometry.Algebra.Metric
import DifferentialGeometry.Algebra.Trace
import DifferentialGeometry.Geometry.Connection
import DifferentialGeometry.Geometry.Curvature
import DifferentialGeometry.Operators.Time
import DifferentialGeometry.Operators.Variation
import DifferentialGeometry.Flows.RicciFlow.Basic
import DifferentialGeometry.Analysis.RicciTensor
import DifferentialGeometry.Analysis.TensorInnerProduct
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open AbstractDerivationAction
open AbstractLieBracket

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V]
variable [AbstractDerivationAction R V] [AbstractLieBracket V] [TraceOperator R V]
variable [DerivationRules R V] [LieDerivationRules R V] [TraceLinearityRules R V]
variable [Invertible (2 : R)]

def partial_ricci_form {Time : Type}
  [TimeDerivative Time R] [TimeDerivative Time V]
  [TimeDerivativeRules Time R V]
  (conn_fam : Time → AbstractAffineConnection R V)
  (t : Time) : SmoothBilinearForm R V where
  val := fun X Y => TimeDerivative.partial_t (fun s => ricciForm (conn_fam s) X Y) t
  add_left := fun X1 X2 Y => by
    have heq : (fun s => ricciForm (conn_fam s) (X1 + X2) Y) = (fun s => ricciForm (conn_fam s) X1 Y + ricciForm (conn_fam s) X2 Y) := by
      funext s
      exact (ricciForm (conn_fam s)).add_left X1 X2 Y
    rw [heq]
    exact TimeDerivativeRules.t_add V _ _ t
  smul_left := fun c X Y => by
    have heq : (fun s => ricciForm (conn_fam s) (c • X) Y) = (fun s => c * ricciForm (conn_fam s) X Y) := by
      funext s
      exact (ricciForm (conn_fam s)).smul_left c X Y
    rw [heq]
    exact TimeDerivativeRules.t_smul V c _ t
  add_right := fun X Y1 Y2 => by
    have heq : (fun s => ricciForm (conn_fam s) X (Y1 + Y2)) = (fun s => ricciForm (conn_fam s) X Y1 + ricciForm (conn_fam s) X Y2) := by
      funext s
      exact (ricciForm (conn_fam s)).add_right X Y1 Y2
    rw [heq]
    exact TimeDerivativeRules.t_add V _ _ t
  smul_right := fun c X Y => by
    have heq : (fun s => ricciForm (conn_fam s) X (c • Y)) = (fun s => c * ricciForm (conn_fam s) X Y) := by
      funext s
      exact (ricciForm (conn_fam s)).smul_right c X Y
    rw [heq]
    exact TimeDerivativeRules.t_smul V c _ t

lemma ricci_raise_variation {Time : Type}
  [TimeDerivative Time R] [TimeDerivative Time V]
  [TimeDerivativeRules Time R V]
  (g_fam : Time → MetricDuality R V)
  (conn_fam : Time → AbstractAffineConnection R V)
  [MetricTimeDerivativeRules Time R V g_fam]
  (X Y : V) (t : Time) :
  (g_fam t).g (TimeDerivative.partial_t (fun s => (g_fam s).raise (ricciForm (conn_fam s)) X) t) Y =
  - (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t).val ((g_fam t).raise (ricciForm (conn_fam t)) X) Y
  + (partial_ricci_form conn_fam t).val X Y := by
  have raise_def : ∀ s, (g_fam s).g ((g_fam s).raise (ricciForm (conn_fam s)) X) Y = ricciForm (conn_fam s) X Y := fun s => (g_fam s).g_raise (ricciForm (conn_fam s)) X Y
  have t_both : TimeDerivative.partial_t (fun s => (g_fam s).g ((g_fam s).raise (ricciForm (conn_fam s)) X) Y) t = TimeDerivative.partial_t (fun s => ricciForm (conn_fam s) X Y) t := by
    congr 1; funext s; exact raise_def s
  have t_metric_val : TimeDerivative.partial_t (fun s => (g_fam s).g ((g_fam s).raise (ricciForm (conn_fam s)) X) Y) t =
    (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t).val ((g_fam t).raise (ricciForm (conn_fam t)) X) Y +
    (g_fam t).g (TimeDerivative.partial_t (fun s => (g_fam s).raise (ricciForm (conn_fam s)) X) t) Y +
    (g_fam t).g ((g_fam t).raise (ricciForm (conn_fam t)) X) (TimeDerivative.partial_t (fun _ => Y) t) :=
    MetricTimeDerivativeRules.t_metric (fun s => (g_fam s).raise (ricciForm (conn_fam s)) X) (fun _ => Y) t
  have t_Y : TimeDerivative.partial_t (fun _ => Y) t = 0 := MetricTimeDerivativeRules.t_const_V g_fam Y t
  rw [t_Y] at t_metric_val
  have h_zero : (g_fam t).g ((g_fam t).raise (ricciForm (conn_fam t)) X) 0 = 0 := metric_zero_right _ _
  rw [h_zero, add_zero] at t_metric_val
  rw [t_metric_val] at t_both
  have h_ricci : TimeDerivative.partial_t (fun s => ricciForm (conn_fam s) X Y) t = (partial_ricci_form conn_fam t).val X Y := rfl
  rw [h_ricci] at t_both
  calc (g_fam t).g (TimeDerivative.partial_t (fun s => (g_fam s).raise (ricciForm (conn_fam s)) X) t) Y
    _ = (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t).val ((g_fam t).raise (ricciForm (conn_fam t)) X) Y + (g_fam t).g (TimeDerivative.partial_t (fun s => (g_fam s).raise (ricciForm (conn_fam s)) X) t) Y - (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t).val ((g_fam t).raise (ricciForm (conn_fam t)) X) Y := by abel
    _ = (partial_ricci_form conn_fam t).val X Y - (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t).val ((g_fam t).raise (ricciForm (conn_fam t)) X) Y := by rw [t_both]
    _ = - (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t).val ((g_fam t).raise (ricciForm (conn_fam t)) X) Y + (partial_ricci_form conn_fam t).val X Y := by abel

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
  (t : Time) :
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
              (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t).val ((g_fam t).raise (ricciForm (conn_fam t)) X) Z := (g_fam t).g_raise _ _ _
    have h6 : (g_fam t).g ((g_fam t).raise (partial_ricci_form conn_fam t) X) Z =
              (partial_ricci_form conn_fam t).val X Z := (g_fam t).g_raise _ _ _
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
                   TraceOperator.trace (fun X => (g_fam t).raise (ricciForm (conn_fam t)) ((g_fam t).raise (ricciForm (conn_fam t)) X)) := rfl
  rw [← def_inner]
  ring
