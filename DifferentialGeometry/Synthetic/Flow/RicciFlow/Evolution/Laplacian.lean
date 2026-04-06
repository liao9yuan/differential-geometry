import DifferentialGeometry.Synthetic.Algebra.VectorField
import DifferentialGeometry.Synthetic.Algebra.Metric
import DifferentialGeometry.Synthetic.Algebra.Trace
import DifferentialGeometry.Synthetic.Geometry.Connection
import DifferentialGeometry.Synthetic.Geometry.Curvature
import DifferentialGeometry.Synthetic.Operator.Hessian
import DifferentialGeometry.Synthetic.Operator.Laplacian
import DifferentialGeometry.Synthetic.Operator.Time
import DifferentialGeometry.Synthetic.Operator.Variation
import DifferentialGeometry.Synthetic.Operator.Bochner
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

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
variable [AbstractDerivationAction R V] [AbstractLieBracket V] [TraceOperator R V]
variable [DerivationRules R V] [LieDerivationRules R V] [TraceLinearityRules R V]
variable [Invertible (2 : R)]

def partial_conn_form {Time R V : Type}
  [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] [AbstractDerivationAction R V] [AbstractLieBracket V] [TraceOperator R V] [DerivationRules R V]
  [TimeDerivative Time R] [TimeDerivative Time V]
  [TimeDerivativeRules Time R V] [ActionTimeDerivativeRules Time R V]
  (g_fam : Time → MetricDuality R V)
  (conn_fam : Time → AbstractAffineConnection R V)
  [MetricTimeDerivativeRules Time R V g_fam]
  (u : R) (t : Time) : AbstractBilinearForm R V :=
  TensorAlgebra.fromBilinear
    { toFun := fun X =>
        { toFun := fun Y => TimeDerivative.partial_t (fun s => action ((conn_fam s).nabla X Y) u) t
          map_add' := fun Y1 Y2 => by
            have h : (fun s => action ((conn_fam s).nabla X (Y1 + Y2)) u) = fun s => action ((conn_fam s).nabla X Y1) u + action ((conn_fam s).nabla X Y2) u := by
              funext s; rw [(conn_fam s).nabla_add_right X Y1 Y2, DerivationRules.action_add_left]
            rw [h, TimeDerivativeRules.t_add V]
          map_smul' := fun c Y => by
            have h : (fun s => action ((conn_fam s).nabla X (c • Y)) u) = fun s => c * action ((conn_fam s).nabla X Y) u + action X c * action Y u := by
              funext s
              have step1 : (conn_fam s).nabla X (c • Y) = action X c • Y + c • (conn_fam s).nabla X Y := (conn_fam s).leibniz c X Y
              rw [step1, DerivationRules.action_add_left]
              have sa1 : action (action X c • Y) u = action X c * action Y u := DerivationRules.action_smul_left _ _ u
              have sa2 : action (c • (conn_fam s).nabla X Y) u = c * action ((conn_fam s).nabla X Y) u := DerivationRules.action_smul_left _ _ u
              rw [sa1, sa2, add_comm]
            rw [h, TimeDerivativeRules.t_add V, TimeDerivativeRules.t_smul V c, MetricTimeDerivativeRules.t_const_R g_fam (action X c * action Y u) t, add_zero]
            rfl }
      map_add' := fun X1 X2 => LinearMap.ext fun Y => by
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
        have h : (fun s => action ((conn_fam s).nabla (X1 + X2) Y) u) = fun s => action ((conn_fam s).nabla X1 Y) u + action ((conn_fam s).nabla X2 Y) u := by
          funext s; rw [(conn_fam s).nabla_add_left X1 X2 Y, DerivationRules.action_add_left]
        rw [h, TimeDerivativeRules.t_add V]
      map_smul' := fun c X => LinearMap.ext fun Y => by
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, RingHom.id_apply]
        have h : (fun s => action ((conn_fam s).nabla (c • X) Y) u) = fun s => c * action ((conn_fam s).nabla X Y) u := by
          funext s; rw [(conn_fam s).nabla_smul_left c X Y, DerivationRules.action_smul_left]
        rw [h, TimeDerivativeRules.t_smul V c]
        rfl }

lemma partial_conn_form_eval {Time R V : Type}
  [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] [AbstractDerivationAction R V] [AbstractLieBracket V] [TraceOperator R V] [DerivationRules R V]
  [TimeDerivative Time R] [TimeDerivative Time V]
  [TimeDerivativeRules Time R V] [ActionTimeDerivativeRules Time R V]
  (g_fam : Time → MetricDuality R V)
  (conn_fam : Time → AbstractAffineConnection R V)
  [MetricTimeDerivativeRules Time R V g_fam]
  (u : R) (X Y : V) (t : Time) :
  eval02 (partial_conn_form g_fam conn_fam u t) X Y = TimeDerivative.partial_t (fun s => action ((conn_fam s).nabla X Y) u) t := by
  dsimp [partial_conn_form]
  rw [eval02_fromBilinear]
  rfl

lemma hessian_raise_variation {Time : Type}
  [TimeDerivative Time R] [TimeDerivative Time V]
  [TimeDerivativeRules Time R V] [ActionTimeDerivativeRules Time R V]
  (g_fam : Time → MetricDuality R V)
  (conn_fam : Time → AbstractAffineConnection R V)
  [MetricTimeDerivativeRules Time R V g_fam]
  [∀ s, MetricCompatible (conn_fam s) (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor]

  (u : R) (X Y : V) (t : Time) :
  (g_fam t).g (TimeDerivative.partial_t (fun s => (g_fam s).raise (hessianForm (g_fam s) (conn_fam s) u) X) t) Y =
  - eval02 (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise (hessianForm (g_fam t) (conn_fam t) u) X) Y
  - eval02 (partial_conn_form g_fam conn_fam u t) X Y := by
  have raise_def : ∀ s, (g_fam s).g ((g_fam s).raise (hessianForm (g_fam s) (conn_fam s) u) X) Y = eval02 (hessianForm (g_fam s) (conn_fam s) u) X Y := fun s => (g_fam s).g_raise (hessianForm (g_fam s) (conn_fam s) u) X Y
  have t_both : TimeDerivative.partial_t (fun s => (g_fam s).g ((g_fam s).raise (hessianForm (g_fam s) (conn_fam s) u) X) Y) t = TimeDerivative.partial_t (fun s => eval02 (hessianForm (g_fam s) (conn_fam s) u) X Y) t := by
    congr 1; funext s; exact raise_def s
  have t_metric_val : TimeDerivative.partial_t (fun s => (g_fam s).g ((g_fam s).raise (hessianForm (g_fam s) (conn_fam s) u) X) Y) t =
    eval02 (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise (hessianForm (g_fam t) (conn_fam t) u) X) Y +
    (g_fam t).g (TimeDerivative.partial_t (fun s => (g_fam s).raise (hessianForm (g_fam s) (conn_fam s) u) X) t) Y +
    (g_fam t).g ((g_fam t).raise (hessianForm (g_fam t) (conn_fam t) u) X) (TimeDerivative.partial_t (fun _ => Y) t) :=
    MetricTimeDerivativeRules.t_metric (fun s => (g_fam s).raise (hessianForm (g_fam s) (conn_fam s) u) X) (fun _ => Y) t
  have t_Y : TimeDerivative.partial_t (fun _ => Y) t = 0 := MetricTimeDerivativeRules.t_const_V g_fam Y t
  rw [t_Y] at t_metric_val
  have h_zero : (g_fam t).g ((g_fam t).raise (hessianForm (g_fam t) (conn_fam t) u) X) 0 = 0 := metric_zero_right _ _
  rw [h_zero, add_zero] at t_metric_val
  rw [t_metric_val] at t_both
  have h_hess : ∀ s, eval02 (hessianForm (g_fam s) (conn_fam s) u) X Y = action X (action Y u) - action ((conn_fam s).nabla X Y) u := by
    intro s
    exact eval02_hessianForm (g_fam s) (conn_fam s) u X Y
  have t_hess : TimeDerivative.partial_t (fun s => eval02 (hessianForm (g_fam s) (conn_fam s) u) X Y) t = TimeDerivative.partial_t (fun s => action X (action Y u) - action ((conn_fam s).nabla X Y) u) t := by
    congr 1; funext s; exact h_hess s
  rw [t_hess] at t_both
  have heq : (fun s => action X (action Y u) - action ((conn_fam s).nabla X Y) u) = (fun s => action X (action Y u) + (-1:R) * action ((conn_fam s).nabla X Y) u) := by
    funext s
    ring
  rw [heq] at t_both
  have t_add_rule : TimeDerivative.partial_t (fun s => action X (action Y u) + (-1:R) * action ((conn_fam s).nabla X Y) u) t =
                    TimeDerivative.partial_t (fun s => action X (action Y u)) t + TimeDerivative.partial_t (fun s => (-1:R) * action ((conn_fam s).nabla X Y) u) t := TimeDerivativeRules.t_add V _ _ t
  rw [t_add_rule] at t_both
  have t_smul_rule : TimeDerivative.partial_t (fun s => (-1:R) * action ((conn_fam s).nabla X Y) u) t = (-1:R) * TimeDerivative.partial_t (fun s => action ((conn_fam s).nabla X Y) u) t := TimeDerivativeRules.t_smul V (-1:R) _ t
  rw [t_smul_rule] at t_both
  have t_const : TimeDerivative.partial_t (fun s => action X (action Y u)) t = 0 := MetricTimeDerivativeRules.t_const_R g_fam (action X (action Y u)) t
  rw [t_const, zero_add] at t_both
  have t_both_eq : (-1:R) * TimeDerivative.partial_t (fun s => action ((conn_fam s).nabla X Y) u) t = - TimeDerivative.partial_t (fun s => action ((conn_fam s).nabla X Y) u) t := by ring
  rw [t_both_eq] at t_both
  have h_conn : TimeDerivative.partial_t (fun s => action ((conn_fam s).nabla X Y) u) t = eval02 (partial_conn_form g_fam conn_fam u t) X Y := by exact (partial_conn_form_eval g_fam conn_fam u X Y t).symm
  rw [h_conn] at t_both
  calc (g_fam t).g (TimeDerivative.partial_t (fun s => (g_fam s).raise (hessianForm (g_fam s) (conn_fam s) u) X) t) Y
    _ = eval02 (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise (hessianForm (g_fam t) (conn_fam t) u) X) Y + (g_fam t).g (TimeDerivative.partial_t (fun s => (g_fam s).raise (hessianForm (g_fam s) (conn_fam s) u) X) t) Y - eval02 (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise (hessianForm (g_fam t) (conn_fam t) u) X) Y := by abel
    _ = - eval02 (partial_conn_form g_fam conn_fam u t) X Y - eval02 (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise (hessianForm (g_fam t) (conn_fam t) u) X) Y := by rw [t_both]
    _ = - eval02 (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise (hessianForm (g_fam t) (conn_fam t) u) X) Y - eval02 (partial_conn_form g_fam conn_fam u t) X Y := by abel


/--
$\partial_t (\Delta u) = 2 \langle \text{Rc}, \text{Hess}(u) \rangle - \text{tr}_g \langle \partial_t \Gamma, \nabla u \rangle$
books/Poincare_Conjecture_Blueprint/chapter03b.tex, implicitly around line 572
-/
lemma laplacian_evolution {Time : Type}
  [TimeDerivative Time R] [TimeDerivative Time V]
  [TimeDerivativeRules Time R V] [ActionTimeDerivativeRules Time R V]
  (g_fam : Time → MetricDuality R V)
  (conn_fam : Time → AbstractAffineConnection R V)
  [MetricTimeDerivativeRules Time R V g_fam]
  [RicciFlow Time (fun t => (g_fam t).toNonDegenerateMetric.toAbstractMetricTensor) conn_fam]
  [∀ s, MetricCompatible (conn_fam s) (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor]
  (u : R) (t : Time) [IR : TensorInnerProductRules R V (g_fam t)] :
  TimeDerivative.partial_t (fun s => TraceOperator.trace (fun X => (g_fam s).raise (hessianForm (g_fam s) (conn_fam s) u) X)) t =
  (2:R) * tensorInnerProduct (g_fam t) (ricciForm (conn_fam t)) (hessianForm (g_fam t) (conn_fam t) u)
  - TraceOperator.trace (fun X => (g_fam t).raise (partial_conn_form g_fam conn_fam u t) X) := by
  have product_rule : TimeDerivative.partial_t (fun s => TraceOperator.trace (fun X => (g_fam s).raise (hessianForm (g_fam s) (conn_fam s) u) X)) t =
                      TraceOperator.trace (fun X => TimeDerivative.partial_t (fun s => (g_fam s).raise (hessianForm (g_fam s) (conn_fam s) u) X) t) :=
    MetricTimeDerivativeRules.t_trace g_fam (fun s X => (g_fam s).raise (hessianForm (g_fam s) (conn_fam s) u) X) t
  rw [product_rule]
  have partial_raise_eq : ∀ X, TimeDerivative.partial_t (fun s => (g_fam s).raise (hessianForm (g_fam s) (conn_fam s) u) X) t =
                          - (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise (hessianForm (g_fam t) (conn_fam t) u) X)
                          - (g_fam t).raise (partial_conn_form g_fam conn_fam u t) X := by
    intro X
    apply (g_fam t).toNonDegenerateMetric.eq_of_forall_g_eq
    intro Z
    have h1 := hessian_raise_variation g_fam conn_fam u X Z t
    rw [h1]
    have h2 : (g_fam t).g (- (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise (hessianForm (g_fam t) (conn_fam t) u) X) - (g_fam t).raise (partial_conn_form g_fam conn_fam u t) X) Z =
              (g_fam t).g (- (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise (hessianForm (g_fam t) (conn_fam t) u) X)) Z +
              (g_fam t).g (- (g_fam t).raise (partial_conn_form g_fam conn_fam u t) X) Z := by
      have sub_eq : - (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise (hessianForm (g_fam t) (conn_fam t) u) X) - (g_fam t).raise (partial_conn_form g_fam conn_fam u t) X =
                    - (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise (hessianForm (g_fam t) (conn_fam t) u) X) + - (g_fam t).raise (partial_conn_form g_fam conn_fam u t) X := sub_eq_add_neg _ _
      rw [sub_eq]
      exact (g_fam t).bilinear_add_left _ _ _
    rw [h2]
    have h3 : (g_fam t).g (- (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise (hessianForm (g_fam t) (conn_fam t) u) X)) Z =
              - (g_fam t).g ((g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise (hessianForm (g_fam t) (conn_fam t) u) X)) Z := metric_neg_left _ _ _
    have h4 : (g_fam t).g (- (g_fam t).raise (partial_conn_form g_fam conn_fam u t) X) Z =
              - (g_fam t).g ((g_fam t).raise (partial_conn_form g_fam conn_fam u t) X) Z := metric_neg_left _ _ _
    rw [h3, h4]
    have h5 : (g_fam t).g ((g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise (hessianForm (g_fam t) (conn_fam t) u) X)) Z =
              eval02 (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise (hessianForm (g_fam t) (conn_fam t) u) X) Z := (g_fam t).g_raise _ _ _
    have h6 : (g_fam t).g ((g_fam t).raise (partial_conn_form g_fam conn_fam u t) X) Z =
              eval02 (partial_conn_form g_fam conn_fam u t) X Z := (g_fam t).g_raise _ _ _
    rw [h5, h6]
    exact sub_eq_add_neg _ _
  have trace_eq : (TraceOperator.trace (fun X => TimeDerivative.partial_t (fun s => (g_fam s).raise (hessianForm (g_fam s) (conn_fam s) u) X) t) : R) =
                  TraceOperator.trace (fun X => - (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise (hessianForm (g_fam t) (conn_fam t) u) X) - (g_fam t).raise (partial_conn_form g_fam conn_fam u t) X) := by
    congr 1
    funext X
    exact partial_raise_eq X
  rw [trace_eq]
  have trace_sub : (TraceOperator.trace (fun X => - (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise (hessianForm (g_fam t) (conn_fam t) u) X) - (g_fam t).raise (partial_conn_form g_fam conn_fam u t) X) : R) =
                   TraceOperator.trace (fun X => - (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise (hessianForm (g_fam t) (conn_fam t) u) X)) +
                   TraceOperator.trace (fun X => - (g_fam t).raise (partial_conn_form g_fam conn_fam u t) X) := by
    have split_eq : (fun X => - (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise (hessianForm (g_fam t) (conn_fam t) u) X) - (g_fam t).raise (partial_conn_form g_fam conn_fam u t) X) =
                    (fun X => - (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise (hessianForm (g_fam t) (conn_fam t) u) X)) +
                    (fun X => - (g_fam t).raise (partial_conn_form g_fam conn_fam u t) X) := by
      funext X
      exact sub_eq_add_neg _ _
    rw [split_eq]
    exact TraceLinearityRules.trace_add
  rw [trace_sub]
  have trace_neg1 : (TraceOperator.trace (fun X => - (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise (hessianForm (g_fam t) (conn_fam t) u) X)) : R) =
                    -(1:R) * TraceOperator.trace (fun X => (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise (hessianForm (g_fam t) (conn_fam t) u) X)) := by
    have smul_eq : (fun X => - (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise (hessianForm (g_fam t) (conn_fam t) u) X)) =
                   (fun X => -(1:R) • (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise (hessianForm (g_fam t) (conn_fam t) u) X)) := by
      funext X
      exact (neg_one_smul R _).symm
    rw [smul_eq]
    exact TraceLinearityRules.trace_smul
  have trace_neg2 : (TraceOperator.trace (fun X => - (g_fam t).raise (partial_conn_form g_fam conn_fam u t) X) : R) =
                    -(1:R) * TraceOperator.trace (fun X => (g_fam t).raise (partial_conn_form g_fam conn_fam u t) X) := by
    have smul_eq : (fun X => - (g_fam t).raise (partial_conn_form g_fam conn_fam u t) X) =
                   (fun X => -(1:R) • (g_fam t).raise (partial_conn_form g_fam conn_fam u t) X) := by
      funext X
      exact (neg_one_smul R _).symm
    rw [smul_eq]
    exact TraceLinearityRules.trace_smul
  rw [trace_neg1, trace_neg2]
  have h_rf : (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) = (-(2:R)) • (ricciForm (conn_fam t)) := RicciFlow.evolution t
  have h_raise_rf : ∀ Z, (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) Z =
                         (-(2:R)) • (g_fam t).raise (ricciForm (conn_fam t)) Z := by
    intro Z
    rw [h_rf]
    exact raise_smul (g_fam t) (ricciForm (conn_fam t)) (-(2:R)) Z
  have inner_prod_sub : (TraceOperator.trace (fun X => (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise (hessianForm (g_fam t) (conn_fam t) u) X)) : R) =
                        -(2:R) * TraceOperator.trace (fun X => (g_fam t).raise (ricciForm (conn_fam t)) ((g_fam t).raise (hessianForm (g_fam t) (conn_fam t) u) X)) := by
    have eq_func : (fun X => (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise (hessianForm (g_fam t) (conn_fam t) u) X)) =
                   (fun X => (-(2:R)) • (g_fam t).raise (ricciForm (conn_fam t)) ((g_fam t).raise (hessianForm (g_fam t) (conn_fam t) u) X)) := by
      funext X
      exact h_raise_rf ((g_fam t).raise (hessianForm (g_fam t) (conn_fam t) u) X)
    rw [eq_func]
    exact TraceLinearityRules.trace_smul
  rw [inner_prod_sub]
  have def_inner : tensorInnerProduct (g_fam t) (ricciForm (conn_fam t)) (hessianForm (g_fam t) (conn_fam t) u) =
                   TraceOperator.trace (fun X => (g_fam t).raise (ricciForm (conn_fam t)) ((g_fam t).raise (hessianForm (g_fam t) (conn_fam t) u) X)) := IR.inner_trace _ _
  rw [← def_inner]
  ring
