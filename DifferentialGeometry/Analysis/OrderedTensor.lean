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

variable {R V : Type} [CommRing R] [PartialOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V]
variable [DerivationAction R V] [LieBracket V] [DerivationRules R V]

/-- Positive semi-definite condition for bilinear forms. -/
-- Defines when a smooth bilinear form is positive semi-definite (T(X,X) >= 0 for all X).
def IsPositiveSemiDefinite (T : SmoothBilinearForm R V) : Prop := ∀ X : V, 0 ≤ T X X

/-- Strictly positive definite condition for bilinear forms. -/
-- Defines when a smooth bilinear form is strictly positive definite.
def IsPositiveDefinite (T : SmoothBilinearForm R V) : Prop := ∀ X : V, X ≠ 0 → 0 < T X X

/-- Algebraic condition for a spatial maximum. -/
-- Axiomatizes the algebraic conditions of a scalar function satisfying a spatial maximum principle.
class SpatialMaximum (metric : MetricTensor R V) [MusicalIsomorphism R V metric] (conn : AffineConnection R V) (f : R) : Prop where
  grad_zero : grad metric f = 0
  hessian_neg_semi_def : IsPositiveSemiDefinite (-(1:R) • hessianForm conn f)

/-- Trace property for positive semi-definite forms. -/
-- Axiomatizes that the trace of a positive semi-definite form is non-negative.
class TraceOrderRules (metric : MetricTensor R V) [MetricTraceOperator R V metric] where
  trace_nonneg : ∀ T : SmoothBilinearForm R V, IsPositiveSemiDefinite T → 0 ≤ MetricTraceOperator.metric_trace metric T

/-- Non-positive Laplacian at a spatial maximum. -/
-- Lemma that at a SpatialMaximum, the Laplacian is <= 0.
lemma laplacian_nonpos_at_max
    (metric : MetricTensor R V) [iso : MusicalIsomorphism R V metric]
    [MetricTraceOperator R V metric] [TraceOrderRules metric]
    (conn : AffineConnection R V) (f : R)
    [SpatialMaximum metric conn f] [MetricTraceRules R V metric] :
    laplacian metric conn f ≤ 0 := by
  have h_hess := SpatialMaximum.hessian_neg_semi_def (metric := metric) (conn := conn) (f := f)
  have h_trace := TraceOrderRules.trace_nonneg (metric := metric) (-(1:R) • hessianForm conn f) h_hess
  have hc : MetricTraceOperator.metric_trace metric (-(1:R) • hessianForm conn f).val = MetricTraceOperator.metric_trace metric (fun X Y => -(1:R) * ((hessianForm conn f) X Y)) := rfl
  have h_smul := MetricTraceRules.trace_smul (metric := metric) (-(1:R)) (hessianForm conn f).val
  rw [hc, h_smul] at h_trace
  have h_lap : laplacian metric conn f = MetricTraceOperator.metric_trace metric (hessianForm conn f) := rfl
  rw [← h_lap] at h_trace
  have h_neg_one : -(1:R) * laplacian metric conn f = - laplacian metric conn f := by ring
  rw [h_neg_one] at h_trace
  exact neg_nonneg.mp h_trace
