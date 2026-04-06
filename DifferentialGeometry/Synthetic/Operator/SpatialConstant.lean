import DifferentialGeometry.Synthetic.Algebra.VectorField
import DifferentialGeometry.Synthetic.Algebra.Metric
import DifferentialGeometry.Synthetic.Geometry.Connection
import DifferentialGeometry.Synthetic.Operator.Gradient
import DifferentialGeometry.Synthetic.Operator.Laplacian
import DifferentialGeometry.Synthetic.Algebra.Trace
import DifferentialGeometry.Synthetic.Operator.Variation
import DifferentialGeometry.Synthetic.Algebra.Trace
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

open DifferentialGeometry TensorAlgebra

variable (R V : Type)
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] [AbstractDerivationAction R V] [AbstractLieBracket V] [DerivationRules R V]

class IsSpatialConstant (c : R) : Prop where
  action_zero : ∀ X : V, AbstractDerivationAction.action X c = 0

variable {R V}

lemma grad_zero (metric : MetricDuality R V) (c : R) [IsSpatialConstant R V c] : grad metric c = 0 := by
  apply metric.toNonDegenerateMetric.eq_of_forall_g_eq
  intro X
  have h1 : metric.g (grad metric c) X = AbstractDerivationAction.action X c := g_grad metric c X
  have h2 : metric.g 0 X = 0 := metric_zero_left metric.toNonDegenerateMetric.toAbstractMetricTensor X
  rw [h1, h2]
  exact IsSpatialConstant.action_zero X

lemma laplacian_zero (metric : MetricDuality R V) (conn : AbstractAffineConnection R V) [AffineTensorCalculus conn] (c : R) [IsSpatialConstant R V c] : laplacian metric conn c = 0 := by
  sorry

lemma grad_smul (metric : MetricDuality R V) (c f : R) [IsSpatialConstant R V c] : grad metric (c * f) = c • grad metric f := by
  apply metric.toNonDegenerateMetric.eq_of_forall_g_eq
  intro X
  have h1 : metric.g (grad metric (c * f)) X = AbstractDerivationAction.action X (c * f) := g_grad metric (c * f) X
  have h2 : AbstractDerivationAction.action X (c * f) = AbstractDerivationAction.action X c * f + c * AbstractDerivationAction.action X f := DerivationRules.action_smul_right X c f
  have hz : AbstractDerivationAction.action X c = 0 := IsSpatialConstant.action_zero X
  rw [hz, zero_mul, zero_add] at h2
  have h5 : c * metric.g (grad metric f) X = c * AbstractDerivationAction.action X f := by rw [g_grad metric f X]
  have h6 : metric.g (c • grad metric f) X = c * metric.g (grad metric f) X := metric.toNonDegenerateMetric.toAbstractMetricTensor.bilinear_smul_left c (grad metric f) X
  rw [h1, h2, ← h5, ← h6]

lemma laplacian_const_smul (metric : MetricDuality R V) (conn : AbstractAffineConnection R V) [AffineTensorCalculus conn] (c f : R) [IsSpatialConstant R V c] : laplacian metric conn (c * f) = c * laplacian metric conn f := by
  sorry
