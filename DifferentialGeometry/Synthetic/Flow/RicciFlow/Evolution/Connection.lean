import DifferentialGeometry.Synthetic.Operator.Time
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
import DifferentialGeometry.Synthetic.Analysis.TensorCalculus
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



variable [LieDerivationRules R V]
variable [Invertible (2 : R)]

/-- The covariant derivative of the Ricci form at time t. -/
def ricci_cov_deriv {Time : Type} [TimeDerivative Time R] [TimeDerivativeRules Time R V]
  (g_fam : Time → MetricDuality R V) (conn_fam : Time → AbstractAffineConnection R V)
  [∀ s, AffineTensorCalculus (conn_fam s)] [∀ s, RiemannCurvatureTensorOp (conn_fam s)] (t : Time) (X Y Z : V) : R :=
  action X (tensor_eval (ricciForm (conn_fam t)) ![Y, Z] ![])
  - tensor_eval (ricciForm (conn_fam t)) ![((nabla_fam g_fam t).nabla X Y), Z] ![]
  - tensor_eval (ricciForm (conn_fam t)) ![Y, ((nabla_fam g_fam t).nabla X Z)] ![]

/--
Mathematical Identity: $\partial_t \Gamma_{ij}^k = - g^{kl} ( \nabla_i R_{jl} + \nabla_j R_{il} - \nabla_l R_{ij} )$
books/Poincare_Conjecture_Blueprint/chapter03b.tex, around line 397 (Corollary: Evolution of Christoffel Symbols under Ricci Flow)
-/
lemma connection_evolution {Time : Type}
  [TimeDerivative Time R] [TimeDerivative Time V]
  [TimeDerivativeRules Time R V] [ActionTimeDerivativeRules Time R V] [TensorTimeCalculus Time R V]
  (g_fam : Time → MetricDuality R V)
  (conn_fam : Time → AbstractAffineConnection R V)
  [MetricTimeDerivativeRules Time R V g_fam]
  [∀ s, AffineTensorCalculus (conn_fam s)] [∀ s, RiemannCurvatureTensorOp (conn_fam s)]
  [RicciFlow Time (fun t => (g_fam t).toNonDegenerateMetric.toAbstractMetricTensor) conn_fam]
  (X Y Z : V) (t : Time) :
  (g_fam t).g (TimeDerivative.partial_t (fun s => (nabla_fam g_fam s).nabla X Y) t) Z =
  - ricci_cov_deriv g_fam conn_fam t X Y Z
  - ricci_cov_deriv g_fam conn_fam t Y X Z
  + ricci_cov_deriv g_fam conn_fam t Z X Y := by
  -- Ricci Flow evolution: metric_var_form = -2 • Rc
  have evol : metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t =
    (- (2:R)) • ricciForm (conn_fam t) := RicciFlow.evolution t
  -- Tensor evaluation distributes scalar: tensor_eval(-2 • Rc) = -2 * tensor_eval(Rc)
  have eval_eq : ∀ P Q : V,
    tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![P, Q] ![] =
    (- (2:R)) * tensor_eval (ricciForm (conn_fam t)) ![P, Q] ![] := by
    intro P Q
    rw [evol]
    exact tensor_eval_smul (- (2:R)) (ricciForm (conn_fam t)) ![P, Q] ![]
  -- h_cov_deriv = -2 * ricci_cov_deriv (metric variation is -2 Rc)
  have h_eq : ∀ A B C : V,
    h_cov_deriv g_fam t A B C = (- (2:R)) * ricci_cov_deriv g_fam conn_fam t A B C := by
    intro A B C
    unfold h_cov_deriv ricci_cov_deriv
    rw [eval_eq B C, eval_eq ((nabla_fam g_fam t).nabla A B) C, eval_eq B ((nabla_fam g_fam t).nabla A C)]
    rw [action_mul_const A (- (2:R)) _ (action_neg_two A)]
    ring
  -- Palatini identity: 2*g(∂_t ∇_X Y, Z) = h_cov(X,Y,Z) + h_cov(Y,X,Z) - h_cov(Z,X,Y)
  have palatini := connection_variation g_fam X Y Z t
  rw [h_eq X Y Z, h_eq Y X Z, h_eq Z X Y] at palatini
  -- Factor out -2 and equate with 2 * goal
  have algebra : (- (2:R)) * ricci_cov_deriv g_fam conn_fam t X Y Z +
    (- (2:R)) * ricci_cov_deriv g_fam conn_fam t Y X Z -
    (- (2:R)) * ricci_cov_deriv g_fam conn_fam t Z X Y =
    2 * (- ricci_cov_deriv g_fam conn_fam t X Y Z -
    ricci_cov_deriv g_fam conn_fam t Y X Z +
    ricci_cov_deriv g_fam conn_fam t Z X Y) := by ring
  rw [algebra] at palatini
  -- Cancel factor of 2
  exact mul_left_cancel₀ (Invertible.ne_zero (2:R)) palatini

