import DifferentialGeometry.Synthetic.Algebra.VectorField
import DifferentialGeometry.Synthetic.Algebra.Metric
import DifferentialGeometry.Synthetic.Algebra.Metric
import DifferentialGeometry.Synthetic.Geometry.Connection
import DifferentialGeometry.Synthetic.Geometry.Curvature
import DifferentialGeometry.Synthetic.Operator.Variation
import DifferentialGeometry.Synthetic.Flow.RicciFlow.Basic
import DifferentialGeometry.Synthetic.Geometry.RicciTensor
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

open AbstractDerivationAction

open DifferentialGeometry TensorAlgebra

variable {R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
variable [AbstractDerivationAction R V] [AbstractLieBracket V]
variable [DerivationRules R V]

/-!
# Evolution of the Connection under Ricci Flow

This file establishes the evolution equation for the Levi-Civita connection
under the Ricci flow equation.
-/



variable [TraceOperator R V] [LieDerivationRules R V] [TraceLinearityRules R V]
variable [Invertible (2 : R)]

/-- The covariant derivative of the Ricci form at time t. -/
def ricci_cov_deriv {Time : Type} [TimeDerivative Time R] [TimeDerivativeRules Time R V]
  (g_fam : Time → MetricDuality R V) (conn_fam : Time → AbstractAffineConnection R V) (t : Time) (X Y Z : V) : R :=
  action X (tensor_eval (ricciForm (conn_fam t)) ![Y, Z] ![])
  - tensor_eval (ricciForm (conn_fam t)) ![((nabla_fam g_fam t).nabla X Y), Z] ![]
  - tensor_eval (ricciForm (conn_fam t)) ![Y, ((nabla_fam g_fam t).nabla X Z)] ![]

/--
Mathematical Identity: $\partial_t \Gamma_{ij}^k = - g^{kl} ( \nabla_i R_{jl} + \nabla_j R_{il} - \nabla_l R_{ij} )$
books/Poincare_Conjecture_Blueprint/chapter03b.tex, around line 397 (Corollary: Evolution of Christoffel Symbols under Ricci Flow)
-/
lemma connection_evolution {Time : Type}
  [TimeDerivative Time R] [TimeDerivative Time V]
  [TimeDerivativeRules Time R V] [ActionTimeDerivativeRules Time R V]
  (g_fam : Time → MetricDuality R V)
  (conn_fam : Time → AbstractAffineConnection R V)
  [MetricTimeDerivativeRules Time R V g_fam]
  [RicciFlow Time (fun t => (g_fam t).toNonDegenerateMetric.toAbstractMetricTensor) conn_fam]
  (X Y Z : V) (t : Time) :
  (g_fam t).g (TimeDerivative.partial_t (fun s => (nabla_fam g_fam s).nabla X Y) t) Z =
  - ricci_cov_deriv g_fam conn_fam t X Y Z
  - ricci_cov_deriv g_fam conn_fam t Y X Z
  + ricci_cov_deriv g_fam conn_fam t Z X Y := by
  have h_metric_var : ∀ A B, tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![A, B] ![] = (- (2:R)) * tensor_eval (ricciForm (conn_fam t)) ![A, B] ![] := by
    have heq : metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t = (- (2:R)) • ricciForm (conn_fam t) := RicciFlow.evolution t
    intro A B
    have heq_eval : tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![A, B] ![] = tensor_eval ((- (2:R)) • ricciForm (conn_fam t)) ![A, B] ![] := by rw [heq]
    rw [heq_eval]
    exact tensor_eval_smul (- (2:R)) (ricciForm (conn_fam t)) ![A, B] ![]

  have h_cov_eq : ∀ A B C : V, h_cov_deriv g_fam t A B C = (- (2:R)) * ricci_cov_deriv g_fam conn_fam t A B C := by
    intro A B C
    dsimp [h_cov_deriv, ricci_cov_deriv]
    have hm : ∀ Y Z : V, tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![Y, Z] ![] = (- (2:R)) * tensor_eval (ricciForm (conn_fam t)) ![Y, Z] ![] := by
      intro Y Z
      exact h_metric_var Y Z
    rw [hm B C, hm ((nabla_fam g_fam t).nabla A B) C, hm B ((nabla_fam g_fam t).nabla A C)]
    rw [action_mul_const A (- (2:R)) (tensor_eval (ricciForm (conn_fam t)) ![B, C] ![]) (action_neg_two A)]
    ring
  have h_variation := connection_variation g_fam X Y Z t
  have h_rhs : h_cov_deriv g_fam t X Y Z + h_cov_deriv g_fam t Y X Z - h_cov_deriv g_fam t Z X Y =
    2 * (- ricci_cov_deriv g_fam conn_fam t X Y Z - ricci_cov_deriv g_fam conn_fam t Y X Z + ricci_cov_deriv g_fam conn_fam t Z X Y) := by
    rw [h_cov_eq X Y Z, h_cov_eq Y X Z, h_cov_eq Z X Y]
    ring
  rw [h_rhs] at h_variation
  have h_cancel : ∀ (W : R) (U : R), 2 * W = 2 * U → W = U := by
    intro W U h_eq
    calc W = ⅟2 * (2 * W) := by rw [← mul_assoc, invOf_mul_self, one_mul]
      _ = ⅟2 * (2 * U) := by rw [h_eq]
      _ = U := by rw [← mul_assoc, invOf_mul_self, one_mul]
  apply h_cancel
  exact h_variation
