import DifferentialGeometry.Synthetic.Algebra.VectorField
import DifferentialGeometry.Synthetic.Algebra.Metric
import DifferentialGeometry.Synthetic.Algebra.Trace
import DifferentialGeometry.Synthetic.Geometry.Connection
import DifferentialGeometry.Synthetic.Geometry.Curvature
import DifferentialGeometry.Synthetic.Geometry.RicciTensor
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
  [∀ s, RiemannCurvatureTensorOp (conn_fam s)]
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
  (conn_fam : Time → AbstractAffineConnection R V) [∀ s, RiemannCurvatureTensorOp (conn_fam s)] (t : Time) (X Y : V) :
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
  [∀ s, RiemannCurvatureTensorOp (conn_fam s)]

  (X Y : V) (t : Time) :
  (g_fam t).g (TimeDerivative.partial_t (fun s => (g_fam s).raise (ricciForm (conn_fam s)) X) t) Y =
  - tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![((g_fam t).raise (ricciForm (conn_fam t)) X), Y] ![]
  + tensor_eval (partial_ricci_form conn_fam t) ![X, Y] ![] := by
  sorry

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
  [∀ s, AffineTensorCalculus (conn_fam s)] [∀ s, RiemannCurvatureTensorOp (conn_fam s)]
  [RicciFlow Time (fun t => (g_fam t).toNonDegenerateMetric.toAbstractMetricTensor) conn_fam]

  (h_trace_R : ∀ s, ScalarCurvature (g_fam s) (conn_fam s) =
                    TraceOperator.trace (fun X => (g_fam s).raise (ricciForm (conn_fam s)) X))
  (t : Time) [IR : TensorInnerProductRules R V (g_fam t)] :
  TimeDerivative.partial_t (fun s => ScalarCurvature (g_fam s) (conn_fam s)) t =
  (2:R) * tensorNormSq (g_fam t) (ricciForm (conn_fam t))
  + TraceOperator.trace (fun X => (g_fam t).raise (partial_ricci_form conn_fam t) X) := by
  sorry
