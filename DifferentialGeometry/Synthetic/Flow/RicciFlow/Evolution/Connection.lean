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



variable [TraceOperator R V] [LieDerivationRules R V] [TraceLinearityRules R V]
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
  [TimeDerivativeRules Time R V] [ActionTimeDerivativeRules Time R V]
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
  sorry

