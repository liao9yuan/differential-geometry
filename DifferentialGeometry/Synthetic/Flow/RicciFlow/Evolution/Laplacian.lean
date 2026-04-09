import DifferentialGeometry.Synthetic.Operator.Time
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
variable [AbstractDerivationAction R V] [AbstractLieBracket V]
variable [DerivationRules R V] [LieDerivationRules R V]
variable [Invertible (2 : R)]



lemma hessian_raise_variation {Time : Type}
  [TimeDerivative Time R] [TimeDerivative Time V]
  [TimeDerivativeRules Time R V] [ActionTimeDerivativeRules Time R V] [TensorTimeCalculus Time R V]
  (g_fam : Time → MetricDuality R V)
  (conn_fam : Time → AbstractAffineConnection R V)
  [MetricTimeDerivativeRules Time R V g_fam]
  [∀ s, AffineTensorCalculus (conn_fam s)] [∀ s, RiemannCurvatureTensorOp (conn_fam s)]
  [∀ s, MetricCompatible (conn_fam s) (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor]

  (u : R) (X Y : V) (t : Time) :
  (g_fam t).g (TimeDerivative.partial_t (fun s => (g_fam s).raise (hessianForm (g_fam s) (conn_fam s) u) X) t) Y =
  - tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![((g_fam t).raise (hessianForm (g_fam t) (conn_fam t) u) X), Y] ![]
  + tensor_eval (TensorTimeCalculus.partial_t_tensor t (fun s => hessianForm (g_fam s) (conn_fam s) u)) ![X, Y] ![] := by
  have h1 : (fun s => (g_fam s).g ((g_fam s).raise (hessianForm (g_fam s) (conn_fam s) u) X) Y) = (fun s => tensor_eval (hessianForm (g_fam s) (conn_fam s) u) ![X, Y] ![]) := by
    funext s; exact (g_fam s).g_raise (hessianForm (g_fam s) (conn_fam s) u) X Y
  have h2 : TimeDerivative.partial_t (fun s => (g_fam s).g ((g_fam s).raise (hessianForm (g_fam s) (conn_fam s) u) X) Y) t = TimeDerivative.partial_t (fun s => tensor_eval (hessianForm (g_fam s) (conn_fam s) u) ![X, Y] ![]) t := by rw [h1]
  have h3 : TimeDerivative.partial_t (fun s => tensor_eval (hessianForm (g_fam s) (conn_fam s) u) ![X, Y] ![]) t = tensor_eval (TensorTimeCalculus.partial_t_tensor t (fun s => hessianForm (g_fam s) (conn_fam s) u)) ![X, Y] ![] := (TensorTimeCalculus.t_eval (fun s => hessianForm (g_fam s) (conn_fam s) u) ![X, Y] ![] t).symm
  have h4 := MetricTimeDerivativeRules.t_metric (g_fam := g_fam) (fun s => (g_fam s).raise (hessianForm (g_fam s) (conn_fam s) u) X) (fun _ => Y) t
  have h5 : TimeDerivative.partial_t (fun _ => Y) t = 0 := MetricTimeDerivativeRules.t_const_V g_fam Y t
  have h6 : (g_fam t).g ((g_fam t).raise (hessianForm (g_fam t) (conn_fam t) u) X) (TimeDerivative.partial_t (fun _ => Y) t) = 0 := by
    rw [h5]; exact metric_zero_right _ _
  rw [h6, add_zero] at h4
  linarith


/--
$\partial_t (\Delta u) = 2 \langle \text{Rc}, \text{Hess}(u) \rangle - \text{tr}_g \langle \partial_t \Gamma, \nabla u \rangle$
books/Poincare_Conjecture_Blueprint/chapter03b.tex, implicitly around line 572
-/
lemma laplacian_evolution {Time : Type}
  [TimeDerivative Time R] [TimeDerivative Time V]
  [TimeDerivativeRules Time R V] [ActionTimeDerivativeRules Time R V] [TensorTimeCalculus Time R V]
  (g_fam : Time → MetricDuality R V)
  (conn_fam : Time → AbstractAffineConnection R V)
  [MetricTimeDerivativeRules Time R V g_fam]
  [∀ s, AffineTensorCalculus (conn_fam s)] [∀ s, RiemannCurvatureTensorOp (conn_fam s)]
  [RicciFlow Time (fun t => (g_fam t).toNonDegenerateMetric.toAbstractMetricTensor) conn_fam]
  [∀ s, MetricCompatible (conn_fam s) (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor]
  (u : R) (t : Time) [IR : TensorInnerProductRules R V (g_fam t)] :
  TimeDerivative.partial_t (fun s => tensor_eval (metric_trace (g_fam s) (0: Fin 2) (0: Fin 1) (hessianForm (g_fam s) (conn_fam s) u)) ![] ![]) t =
  (2:R) * tensorInnerProduct (g_fam t) (ricciForm (conn_fam t)) (hessianForm (g_fam t) (conn_fam t) u)
  + tensor_eval (metric_trace (g_fam t) (0: Fin 2) (0: Fin 1) (TensorTimeCalculus.partial_t_tensor t (fun s => hessianForm (g_fam s) (conn_fam s) u))) ![] ![] := by
  -- Step 1: Apply the product rule for metric trace with varying tensor
  have h_prod := MetricTimeDerivativeRules.t_metric_trace_varying (g_fam := g_fam) (fun s => hessianForm (g_fam s) (conn_fam s) u) t IR
  -- Step 2: Substitute the Ricci flow equation: metric_var_form = -2 • Ric
  have h_ricci : metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t = (-(2:R)) • ricciForm (conn_fam t) :=
    RicciFlow.evolution t
  -- Step 3: Compute -⟨-2 Ric, Hess⟩ = 2⟨Ric, Hess⟩
  have h_inner : - tensorInnerProduct (g_fam t) ((-(2:R)) • ricciForm (conn_fam t)) (hessianForm (g_fam t) (conn_fam t) u) =
    (2:R) * tensorInnerProduct (g_fam t) (ricciForm (conn_fam t)) (hessianForm (g_fam t) (conn_fam t) u) := by
    rw [tensor_inner_smul_left]
    ring
  rw [h_prod, h_ricci, h_inner]
