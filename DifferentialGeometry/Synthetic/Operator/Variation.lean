import DifferentialGeometry.Synthetic.Algebra.VectorField
import DifferentialGeometry.Synthetic.Algebra.BilinearForm
import DifferentialGeometry.Synthetic.Algebra.Metric
import DifferentialGeometry.Synthetic.Algebra.Metric
import DifferentialGeometry.Synthetic.Algebra.Trace
import DifferentialGeometry.Synthetic.Analysis.TensorInnerProduct
import DifferentialGeometry.Synthetic.Geometry.Connection
import DifferentialGeometry.Synthetic.Geometry.Curvature
import DifferentialGeometry.Synthetic.Operator.Time
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# Time Derivatives and Variation
Defines generic time derivatives and variation of metric.
-/

open AbstractDerivationAction AbstractLieBracket DifferentialGeometry TensorAlgebra

variable {R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]




-- 3. Metric Variation Form
/-- Operator for metric variation.
Constructed explicitly from bilinear function of metric derivative.
-/
def metric_var_form {Time R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
  [TimeDerivative Time R] [TimeDerivative Time V] [TimeDerivativeRules Time R V] [TensorTimeCalculus Time R V]
  (g_fam : Time → AbstractMetricTensor R V) (t : Time) : AbstractBilinearForm R V :=
  TensorTimeCalculus.partial_t_tensor t (fun s => (g_fam s).g_tensor)

lemma metric_var_form_eval {Time R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
  [TimeDerivative Time R] [TimeDerivative Time V] [TimeDerivativeRules Time R V] [TensorTimeCalculus Time R V] (g_fam : Time → AbstractMetricTensor R V) (t : Time) (X Y : V) :
  tensor_eval (metric_var_form g_fam t) ![X, Y] ![] = TimeDerivative.partial_t (fun s => tensor_eval ((g_fam s).g_tensor) ![X, Y] ![]) t := by
  sorry

-- 4. Metric Time Derivative Calculus Axioms
/-- Product rule and constant rules for time derivatives involving the metric. -/
class MetricTimeDerivativeRules (Time R V : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
  [TimeDerivative Time R] [TimeDerivative Time V]
  [TimeDerivativeRules Time R V] [TensorTimeCalculus Time R V]
  (g_fam : Time → MetricDuality R V) where
  t_const_R : ∀ (c : R) (t : Time), TimeDerivative.partial_t (fun _ => c) t = 0
  t_const_V : ∀ (X : V) (t : Time), TimeDerivative.partial_t (fun _ => X) t = 0
  t_metric : ∀ (X Y : Time → V) (t : Time),
    TimeDerivative.partial_t (fun s => (g_fam s).g (X s) (Y s)) t =
    tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![(X t), (Y t)] ![] +
    (g_fam t).g (TimeDerivative.partial_t X t) (Y t) +
    (g_fam t).g (X t) (TimeDerivative.partial_t Y t)

lemma metric_zero_right {R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] (metric : AbstractMetricTensor R V) (X : V) : metric.g X 0 = 0 := by
  have h1 : metric.g X (0 + 0) = metric.g X 0 + metric.g X 0 := by
    have h1a : metric.g (0 + 0) X = metric.g 0 X + metric.g 0 X := metric.bilinear_add_left 0 0 X
    have h1b : metric.g X (0 + 0) = metric.g (0 + 0) X := metric.symm X (0 + 0)
    have h1c : metric.g X 0 = metric.g 0 X := metric.symm X 0
    rw [h1b, h1a, ← h1c]
  calc metric.g X 0 = metric.g X 0 + metric.g X 0 - metric.g X 0 := by abel
    _ = metric.g X (0 + 0) - metric.g X 0 := by rw [← h1]
    _ = metric.g X 0 - metric.g X 0 := by rw [add_zero]
    _ = 0 := by abel

lemma metric_zero_left {R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] (metric : AbstractMetricTensor R V) (X : V) : metric.g 0 X = 0 := by
  have h1 : metric.g 0 X = metric.g X 0 := metric.symm 0 X
  rw [h1]
  exact metric_zero_right metric X

-- 5. Inverse Metric Variation
/-- Variation of the raised index tensor (inverse metric). -/
lemma raise_variation {Time R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
  [TimeDerivative Time R] [TimeDerivative Time V] [TimeDerivativeRules Time R V] [TensorTimeCalculus Time R V]
  (g_fam : Time → MetricDuality R V) [MetricTimeDerivativeRules Time R V g_fam]
  (T : AbstractBilinearForm R V) (X Y : V) (t : Time) :
  (g_fam t).g (TimeDerivative.partial_t (fun s => (g_fam s).raise T X) t) Y =
  - tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![((g_fam t).raise T X), Y] ![] := by
  sorry

-- 6. Metric Trace Variation
/-- Time variation of the trace of a fixed metric. -/
lemma tr_g_variation {Time R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
  [TimeDerivative Time R] [TimeDerivative Time V]
  [TimeDerivativeRules Time R V] [TensorTimeCalculus Time R V]
  (g_fam : Time → MetricDuality R V) [MetricTimeDerivativeRules Time R V g_fam]
  (T : AbstractBilinearForm R V) (t : Time) [IR : TensorInnerProductRules R V (g_fam t)] :
  TimeDerivative.partial_t (fun s => tensor_eval (metric_trace (g_fam s) (0: Fin 2) (0: Fin 1) T) ![] ![]) t =
  - tensorInnerProduct (g_fam t) (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) T := by
  sorry

-- 7. Variation of the Connection (Palatini Identity)



variable [AbstractDerivationAction R V] [AbstractLieBracket V] [DerivationRules R V] [Invertible (2 : R)]

/-- The unique Levi-Civita connection associated to a metric family at time s. -/
abbrev nabla_fam {Time : Type} (g_fam : Time → MetricDuality R V) (t : Time) : AbstractAffineConnection R V :=
  koszul_connection (g_fam t)

/-- The covariant derivative of the symmetric bilinear form h = ∂_t g at time t.
(∇_X h)(Y, Z) = X(h(Y, Z)) - h(∇_X Y, Z) - h(Y, ∇_X Z)
-/
def h_cov_deriv {Time : Type} [TimeDerivative Time R] [TimeDerivative Time V] [TimeDerivativeRules Time R V] [TensorTimeCalculus Time R V]
  (g_fam : Time → MetricDuality R V) (t : Time) (X Y Z : V) : R :=
  action X (tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![Y, Z] ![])
  - tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![((nabla_fam g_fam t).nabla X Y), Z] ![]
  - tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![Y, ((nabla_fam g_fam t).nabla X Z)] ![]

/-- Palatini identity for the variation of the Levi-Civita connection. -/
lemma connection_variation {Time : Type} [TimeDerivative Time R] [TimeDerivative Time V]
  [TimeDerivativeRules Time R V] [ActionTimeDerivativeRules Time R V] [TensorTimeCalculus Time R V]
  (g_fam : Time → MetricDuality R V) [MetricTimeDerivativeRules Time R V g_fam]
  (X Y Z : V) (t : Time) :
  2 * (g_fam t).g (TimeDerivative.partial_t (fun s => (nabla_fam g_fam s).nabla X Y) t) Z =
  h_cov_deriv g_fam t X Y Z + h_cov_deriv g_fam t Y X Z - h_cov_deriv g_fam t Z X Y := by
  sorry
