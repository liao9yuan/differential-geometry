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
  have h1 : grad metric c = 0 := grad_zero metric c
  have h2 : laplacian metric conn (0:R) = 0 := by
    have hsub := laplacian_sub metric conn (0:R) (0:R)
    have hz1 : (0:R) - (0:R) = (0:R) := sub_self (0:R)
    rw [hz1] at hsub
    have hz2 : laplacian metric conn (0:R) - laplacian metric conn (0:R) = 0 := sub_self (laplacian metric conn (0:R))
    rw [hz2] at hsub
    exact hsub
  have h3 : grad metric (0:R) = 0 := by
    have hc0 : IsSpatialConstant R V 0 := ⟨fun X => by rw [action_zero X]⟩
    exact grad_zero metric 0
  have h_lap_c : laplacian metric conn c = tensor_eval (metric_trace metric (0: Fin 2) (0: Fin 1) (lower_index metric.toNonDegenerateMetric.toAbstractMetricTensor (0: Fin 1) (covariant_differential metric conn (grad metric c)))) ![] ![] := rfl
  have h_lap_0 : laplacian metric conn 0 = tensor_eval (metric_trace metric (0: Fin 2) (0: Fin 1) (lower_index metric.toNonDegenerateMetric.toAbstractMetricTensor (0: Fin 1) (covariant_differential metric conn (grad metric 0)))) ![] ![] := rfl
  rw [h_lap_c]
  rw [h1]
  rw [← h3]
  rw [← h_lap_0]
  exact h2

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
  apply laplacian_smul
  exact IsSpatialConstant.action_zero
