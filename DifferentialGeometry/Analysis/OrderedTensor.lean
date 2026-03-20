import DifferentialGeometry.Algebra.BilinearForm
import DifferentialGeometry.Algebra.Metric
import DifferentialGeometry.Operators.Hessian
import DifferentialGeometry.Operators.Laplacian
import DifferentialGeometry.Operators.Gradient
import DifferentialGeometry.Operators.Bochner
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Maximum Principle
Analytical concepts such as maximum principles, positivity, and spatial extremum principles.
-/

open DifferentialGeometry.Bridge TensorAlgebra

variable {R V : Type} [CommRing R] [PartialOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
variable [AbstractDerivationAction R V] [AbstractLieBracket V] [DerivationRules R V]

/-- Positive semi-definite condition for bilinear forms. -/
-- Defines when a smooth bilinear form is positive semi-definite (T(X,X) >= 0 for all X).
def IsPositiveSemiDefinite (T : AbstractBilinearForm R V) : Prop := ∀ X : V, 0 ≤ eval02 T X X

/-- Strictly positive definite condition for bilinear forms. -/
-- Defines when a smooth bilinear form is strictly positive definite.
def IsPositiveDefinite (T : AbstractBilinearForm R V) : Prop := ∀ X : V, X ≠ 0 → 0 < eval02 T X X

/-- Algebraic condition for a spatial maximum. -/
-- Axiomatizes the algebraic conditions of a scalar function satisfying a spatial maximum principle.
class SpatialMaximum (metric : MetricDuality R V) (conn : AbstractAffineConnection R V) [MetricCompatible conn metric.toNonDegenerateMetric.toAbstractMetricTensor] (f : R) : Prop where
  grad_zero : grad metric f = 0
  hessian_neg_semi_def : IsPositiveSemiDefinite (-(1:R) • hessianForm metric conn f)

/-- Trace property for positive semi-definite forms. -/
-- Axiomatizes that the trace of a positive semi-definite form is non-negative.
class TraceOrderRules (metric : AbstractMetricTensor R V) [MetricTraceOperator R V metric] where
  trace_nonneg : ∀ T : AbstractBilinearForm R V, IsPositiveSemiDefinite T → 0 ≤ MetricTraceOperator.metric_trace metric (eval02 T)

/-- Non-positive Laplacian at a spatial maximum. -/
-- Lemma that at a SpatialMaximum, the Laplacian is <= 0.
lemma laplacian_nonpos_at_max
    (metric : MetricDuality R V)
    [MetricTraceOperator R V metric.toNonDegenerateMetric.toAbstractMetricTensor] [TraceOrderRules metric.toNonDegenerateMetric.toAbstractMetricTensor]
    (conn : AbstractAffineConnection R V) [MetricCompatible conn metric.toNonDegenerateMetric.toAbstractMetricTensor] (f : R)
    [SpatialMaximum metric conn f] [MetricTraceRules R V metric.toNonDegenerateMetric.toAbstractMetricTensor] :
    laplacian metric.toNonDegenerateMetric.toAbstractMetricTensor conn f ≤ 0 := by
  have h_hess := SpatialMaximum.hessian_neg_semi_def (metric := metric) (conn := conn) (f := f)
  have h_trace := TraceOrderRules.trace_nonneg (metric := metric.toNonDegenerateMetric.toAbstractMetricTensor) (-(1:R) • hessianForm metric conn f) h_hess
  have hc : MetricTraceOperator.metric_trace metric.toNonDegenerateMetric.toAbstractMetricTensor (eval02 (-(1:R) • hessianForm metric conn f)) = MetricTraceOperator.metric_trace metric.toNonDegenerateMetric.toAbstractMetricTensor (fun X Y => -(1:R) * eval02 (hessianForm metric conn f) X Y) := by
    congr 1
    funext A B
    exact eval02_smul (hessianForm metric conn f) (-(1:R)) A B
  have h_smul := MetricTraceRules.trace_smul (metric := metric.toNonDegenerateMetric.toAbstractMetricTensor) (-(1:R)) (eval02 (hessianForm metric conn f))
  rw [hc, h_smul] at h_trace
  have h_lap : laplacian metric.toNonDegenerateMetric.toAbstractMetricTensor conn f = MetricTraceOperator.metric_trace metric.toNonDegenerateMetric.toAbstractMetricTensor (eval02 (hessianForm metric conn f)) := by
    dsimp [laplacian]
    congr 1
    funext A B
    have h_hess_eval : eval02 (hessianForm metric conn f) A B = Hess conn f A B := by
      exact eval02_hessianForm metric conn f A B
    exact h_hess_eval.symm
  rw [← h_lap] at h_trace
  have h_neg_one : -(1:R) * laplacian metric.toNonDegenerateMetric.toAbstractMetricTensor conn f = - laplacian metric.toNonDegenerateMetric.toAbstractMetricTensor conn f := by ring
  rw [h_neg_one] at h_trace
  exact neg_nonneg.mp h_trace
