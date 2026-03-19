import DifferentialGeometry.Algebra.VectorField
import DifferentialGeometry.Algebra.Metric
import DifferentialGeometry.Geometry.Connection
import DifferentialGeometry.Operators.Gradient
import DifferentialGeometry.Operators.Laplacian
import DifferentialGeometry.Analysis.TraceRankOne
import DifferentialGeometry.Operators.Variation
import DifferentialGeometry.Algebra.Trace
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open DifferentialGeometry.Bridge TensorAlgebra

variable (R V : Type)
variable [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] [AbstractDerivationAction R V] [AbstractLieBracket V] [DerivationRules R V]

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

lemma laplacian_zero (metric : MetricDuality R V) [MetricTraceOperator R V metric.toNonDegenerateMetric.toAbstractMetricTensor] (conn : AbstractAffineConnection R V) (c : R) [IsSpatialConstant R V c] [TraceOperator R V] [TraceLinearityRules R V]
  [MetricTraceRules R V metric.toNonDegenerateMetric.toAbstractMetricTensor] : laplacian metric.toNonDegenerateMetric.toAbstractMetricTensor conn c = 0 := by
  have hl : Hess conn c = fun X Y => 0 := by
    funext X Y
    dsimp [Hess]
    have hz1 : AbstractDerivationAction.action Y c = 0 := IsSpatialConstant.action_zero Y
    have hz2 : AbstractDerivationAction.action (conn.nabla X Y) c = 0 := IsSpatialConstant.action_zero (conn.nabla X Y)
    rw [hz1]
    have hz3 : AbstractDerivationAction.action X (0:R) = 0 := by
      have h1 : AbstractDerivationAction.action X ((0:R) + (0:R)) = AbstractDerivationAction.action X (0:R) + AbstractDerivationAction.action X (0:R) := DerivationRules.action_add_right X (0:R) (0:R)
      have h2 : AbstractDerivationAction.action X ((0:R) + (0:R)) = AbstractDerivationAction.action X (0:R) := by
        have h0 : (0:R) + (0:R) = (0:R) := add_zero 0
        rw [h0]
      rw [h2] at h1
      calc AbstractDerivationAction.action X (0:R) = AbstractDerivationAction.action X (0:R) + AbstractDerivationAction.action X (0:R) - AbstractDerivationAction.action X (0:R) := by ring
        _ = AbstractDerivationAction.action X (0:R) - AbstractDerivationAction.action X (0:R) := by rw [← h1]
        _ = 0 := by ring
    rw [hz3, hz2, sub_zero]
  dsimp [laplacian]
  rw [hl]
  have h_trace_add : MetricTraceOperator.metric_trace metric.toNonDegenerateMetric.toAbstractMetricTensor (fun X Y => 0 + 0) = MetricTraceOperator.metric_trace metric.toNonDegenerateMetric.toAbstractMetricTensor (fun X Y => 0) + MetricTraceOperator.metric_trace metric.toNonDegenerateMetric.toAbstractMetricTensor (fun X Y => 0) := MetricTraceRules.trace_add _ _
  have h_add_zero : (fun (X Y : V) => (0:R) + (0:R)) = (fun X Y => (0:R)) := by
    funext X Y
    exact add_zero 0
  rw [h_add_zero] at h_trace_add
  have h_trace_eq : MetricTraceOperator.metric_trace metric.toNonDegenerateMetric.toAbstractMetricTensor (fun X Y => 0) + MetricTraceOperator.metric_trace metric.toNonDegenerateMetric.toAbstractMetricTensor (fun X Y => 0) = MetricTraceOperator.metric_trace metric.toNonDegenerateMetric.toAbstractMetricTensor (fun X Y => 0) := h_trace_add.symm
  calc MetricTraceOperator.metric_trace metric.toNonDegenerateMetric.toAbstractMetricTensor (fun X Y => 0)
    _ = MetricTraceOperator.metric_trace metric.toNonDegenerateMetric.toAbstractMetricTensor (fun X Y => 0) + MetricTraceOperator.metric_trace metric.toNonDegenerateMetric.toAbstractMetricTensor (fun X Y => 0) - MetricTraceOperator.metric_trace metric.toNonDegenerateMetric.toAbstractMetricTensor (fun X Y => 0) := by ring
    _ = MetricTraceOperator.metric_trace metric.toNonDegenerateMetric.toAbstractMetricTensor (fun X Y => 0) - MetricTraceOperator.metric_trace metric.toNonDegenerateMetric.toAbstractMetricTensor (fun X Y => 0) := by rw [h_trace_eq]
    _ = 0 := by ring

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

lemma laplacian_smul (metric : MetricDuality R V) [MetricTraceOperator R V metric.toNonDegenerateMetric.toAbstractMetricTensor] (conn : AbstractAffineConnection R V) (c f : R) [IsSpatialConstant R V c] [MetricTraceRules R V metric.toNonDegenerateMetric.toAbstractMetricTensor] : laplacian metric.toNonDegenerateMetric.toAbstractMetricTensor conn (c * f) = c * laplacian metric.toNonDegenerateMetric.toAbstractMetricTensor conn f := by
  have hs : Hess conn (c * f) = fun X Y => c * Hess conn f X Y := by
    funext X Y
    dsimp [Hess]
    have h1 : AbstractDerivationAction.action Y (c * f) = c * AbstractDerivationAction.action Y f := by
      have h1a : AbstractDerivationAction.action Y (c * f) = AbstractDerivationAction.action Y c * f + c * AbstractDerivationAction.action Y f := DerivationRules.action_smul_right Y c f
      have hzc : AbstractDerivationAction.action Y c = 0 := IsSpatialConstant.action_zero Y
      rw [hzc, zero_mul, zero_add] at h1a
      exact h1a
    rw [h1]
    have h2 : AbstractDerivationAction.action X (c * AbstractDerivationAction.action Y f) = c * AbstractDerivationAction.action X (AbstractDerivationAction.action Y f) := by
      have h2a : AbstractDerivationAction.action X (c * AbstractDerivationAction.action Y f) = AbstractDerivationAction.action X c * AbstractDerivationAction.action Y f + c * AbstractDerivationAction.action X (AbstractDerivationAction.action Y f) := DerivationRules.action_smul_right X c (AbstractDerivationAction.action Y f)
      have hzcx : AbstractDerivationAction.action X c = 0 := IsSpatialConstant.action_zero X
      rw [hzcx, zero_mul, zero_add] at h2a
      exact h2a
    rw [h2]
    have h3 : AbstractDerivationAction.action (conn.nabla X Y) (c * f) = c * AbstractDerivationAction.action (conn.nabla X Y) f := by
      have h3a : AbstractDerivationAction.action (conn.nabla X Y) (c * f) = AbstractDerivationAction.action (conn.nabla X Y) c * f + c * AbstractDerivationAction.action (conn.nabla X Y) f := DerivationRules.action_smul_right (conn.nabla X Y) c f
      have hzcn : AbstractDerivationAction.action (conn.nabla X Y) c = 0 := IsSpatialConstant.action_zero (conn.nabla X Y)
      rw [hzcn, zero_mul, zero_add] at h3a
      exact h3a
    rw [h3]
    ring
  dsimp [laplacian]
  rw [hs]
  exact MetricTraceRules.trace_smul c (Hess conn f)
