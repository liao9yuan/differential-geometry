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

variable {R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
variable [AbstractDerivationAction R V] [AbstractLieBracket V] [TraceOperator R V]
variable [DerivationRules R V] [LieDerivationRules R V] [TraceLinearityRules R V]
variable [Invertible (2 : R)]

def partial_conn_form {Time R V : Type}
  [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] [AbstractDerivationAction R V] [AbstractLieBracket V] [TraceOperator R V] [DerivationRules R V]
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
  [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] [AbstractDerivationAction R V] [AbstractLieBracket V] [TraceOperator R V] [DerivationRules R V]
  [TimeDerivative Time R] [TimeDerivative Time V]
  [TimeDerivativeRules Time R V] [ActionTimeDerivativeRules Time R V]
  (g_fam : Time → MetricDuality R V)
  (conn_fam : Time → AbstractAffineConnection R V)
  [MetricTimeDerivativeRules Time R V g_fam]
  (u : R) (X Y : V) (t : Time) :
  tensor_eval (partial_conn_form g_fam conn_fam u t) ![X, Y] ![] = TimeDerivative.partial_t (fun s => action ((conn_fam s).nabla X Y) u) t := by
  dsimp [partial_conn_form]
  rw [TensorAlgebra.tensor_eval_fromBilinear]
  rfl

lemma hessian_raise_variation {Time : Type}
  [TimeDerivative Time R] [TimeDerivative Time V]
  [TimeDerivativeRules Time R V] [ActionTimeDerivativeRules Time R V]
  (g_fam : Time → MetricDuality R V)
  (conn_fam : Time → AbstractAffineConnection R V)
  [MetricTimeDerivativeRules Time R V g_fam]
  [∀ s, AffineTensorCalculus (conn_fam s)] [∀ s, RiemannCurvatureTensorOp (conn_fam s)]
  [∀ s, MetricCompatible (conn_fam s) (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor]

  (u : R) (X Y : V) (t : Time) :
  (g_fam t).g (TimeDerivative.partial_t (fun s => (g_fam s).raise (hessianForm (g_fam s) (conn_fam s) u) X) t) Y =
  - tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![((g_fam t).raise (hessianForm (g_fam t) (conn_fam t) u) X), Y] ![]
  - tensor_eval (partial_conn_form g_fam conn_fam u t) ![X, Y] ![] := by
  sorry


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
  [∀ s, AffineTensorCalculus (conn_fam s)] [∀ s, RiemannCurvatureTensorOp (conn_fam s)]
  [RicciFlow Time (fun t => (g_fam t).toNonDegenerateMetric.toAbstractMetricTensor) conn_fam]
  [∀ s, MetricCompatible (conn_fam s) (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor]
  (u : R) (t : Time) [IR : TensorInnerProductRules R V (g_fam t)] :
  TimeDerivative.partial_t (fun s => TraceOperator.trace (fun X => (g_fam s).raise (hessianForm (g_fam s) (conn_fam s) u) X)) t =
  (2:R) * tensorInnerProduct (g_fam t) (ricciForm (conn_fam t)) (hessianForm (g_fam t) (conn_fam t) u)
  - TraceOperator.trace (fun X => (g_fam t).raise (partial_conn_form g_fam conn_fam u t) X) := by
  sorry
