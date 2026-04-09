import DifferentialGeometry.Synthetic.Operator.Time
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
variable [AbstractDerivationAction R V] [AbstractLieBracket V]
variable [Invertible (2 : R)]
lemma ricci_raise_variation {Time : Type}
  [TimeDerivative Time R] [TimeDerivative Time V]
  [TimeDerivativeRules Time R V] [TensorTimeCalculus Time R V]
  (g_fam : Time → MetricDuality R V)
  (conn_fam : Time → AbstractAffineConnection R V)
  [MetricTimeDerivativeRules Time R V g_fam]
  [∀ s, RiemannCurvatureTensorOp (conn_fam s)]

  (X Y : V) (t : Time) :
  (g_fam t).g (TimeDerivative.partial_t (fun s => (g_fam s).raise (ricciForm (conn_fam s)) X) t) Y =
  - tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![((g_fam t).raise (ricciForm (conn_fam t)) X), Y] ![]
  + tensor_eval (TensorTimeCalculus.partial_t_tensor t (fun s => ricciForm (conn_fam s))) ![X, Y] ![] := by
  have h1 : (fun s => (g_fam s).g ((g_fam s).raise (ricciForm (conn_fam s)) X) Y) = (fun s => tensor_eval (ricciForm (conn_fam s)) ![X, Y] ![]) := by
    funext s; exact (g_fam s).g_raise (ricciForm (conn_fam s)) X Y
  have h2 : TimeDerivative.partial_t (fun s => (g_fam s).g ((g_fam s).raise (ricciForm (conn_fam s)) X) Y) t = TimeDerivative.partial_t (fun s => tensor_eval (ricciForm (conn_fam s)) ![X, Y] ![]) t := by rw [h1]
  have h3 : TimeDerivative.partial_t (fun s => tensor_eval (ricciForm (conn_fam s)) ![X, Y] ![]) t = tensor_eval (TensorTimeCalculus.partial_t_tensor t (fun s => ricciForm (conn_fam s))) ![X, Y] ![] := (TensorTimeCalculus.t_eval (fun s => ricciForm (conn_fam s)) ![X, Y] ![] t).symm
  have h4 := MetricTimeDerivativeRules.t_metric (g_fam := g_fam) (fun s => (g_fam s).raise (ricciForm (conn_fam s)) X) (fun _ => Y) t
  have h5 : TimeDerivative.partial_t (fun _ => Y) t = 0 := MetricTimeDerivativeRules.t_const_V g_fam Y t
  have h6 : (g_fam t).g ((g_fam t).raise (ricciForm (conn_fam t)) X) (TimeDerivative.partial_t (fun _ => Y) t) = 0 := by
    rw [h5]; exact metric_zero_right _ _
  rw [h6, add_zero] at h4
  linarith

/--
$\partial_t R = \Delta R + 2 |\text{Ric}|^2$
books/Poincare_Conjecture_Blueprint/chapter03b.tex, around line 583
-/
lemma scalar_curvature_evolution {Time : Type}
  [TimeDerivative Time R] [TimeDerivative Time V]
  [TimeDerivativeRules Time R V] [TensorTimeCalculus Time R V]
  (g_fam : Time → MetricDuality R V)
  (conn_fam : Time → AbstractAffineConnection R V)
  [MetricTimeDerivativeRules Time R V g_fam]
  [∀ s, AffineTensorCalculus (conn_fam s)] [∀ s, RiemannCurvatureTensorOp (conn_fam s)]
  [RicciFlow Time (fun t => (g_fam t).toNonDegenerateMetric.toAbstractMetricTensor) conn_fam]

  (h_trace_R : ∀ s, ScalarCurvature (g_fam s) (conn_fam s) =
                    tensor_eval (metric_trace (g_fam s) (0: Fin 2) (0: Fin 1) (ricciForm (conn_fam s))) ![] ![])
  (t : Time) [IR : TensorInnerProductRules R V (g_fam t)] :
  TimeDerivative.partial_t (fun s => ScalarCurvature (g_fam s) (conn_fam s)) t =
  (2:R) * tensorNormSq (g_fam t) (ricciForm (conn_fam t))
  + tensor_eval (metric_trace (g_fam t) (0: Fin 2) (0: Fin 1) (TensorTimeCalculus.partial_t_tensor t (fun s => ricciForm (conn_fam s)))) ![] ![] := by
  -- Step 1: Rewrite ScalarCurvature using the trace hypothesis
  have h_rw : (fun s => ScalarCurvature (g_fam s) (conn_fam s)) = (fun s => tensor_eval (metric_trace (g_fam s) (0: Fin 2) (0: Fin 1) (ricciForm (conn_fam s))) ![] ![]) := by
    funext s; exact h_trace_R s
  rw [h_rw]
  -- Step 2: Apply the product rule for metric trace with varying tensor
  have h_prod := MetricTimeDerivativeRules.t_metric_trace_varying (g_fam := g_fam) (fun s => ricciForm (conn_fam s)) t IR
  -- Step 3: Substitute the Ricci flow equation: metric_var_form = -2 • Ric
  have h_ricci : metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t = (-(2:R)) • ricciForm (conn_fam t) :=
    RicciFlow.evolution t
  -- Step 4: Compute -⟨-2 Ric, Ric⟩ = 2⟨Ric, Ric⟩ = 2 * tensorNormSq
  have h_inner : - tensorInnerProduct (g_fam t) ((-(2:R)) • ricciForm (conn_fam t)) (ricciForm (conn_fam t)) =
    (2:R) * tensorNormSq (g_fam t) (ricciForm (conn_fam t)) := by
    rw [tensor_inner_smul_left]
    unfold tensorNormSq
    ring
  rw [h_prod, h_ricci, h_inner]
