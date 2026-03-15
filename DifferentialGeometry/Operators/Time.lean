import DifferentialGeometry.Algebra.Basic
import DifferentialGeometry.Algebra.Metric
import DifferentialGeometry.Geometry.Connection
import DifferentialGeometry.Operators.Gradient
import DifferentialGeometry.Operators.Laplacian
import DifferentialGeometry.Operators.Variation
import Mathlib.Algebra.Order.Ring.Defs

set_option autoImplicit false
set_option linter.style.longLine false

/--
This axiomatizes the existence of 1/t, its derivative rule ∂_t (1/t) = -1/t^2, and its positivity.
-/
class TimeWeight (R : Type) [CommRing R] [PartialOrder R] (Time : Type) [TimeDerivative Time R] where
  inv_t : Time → R
  dt_inv_t : ∀ t, TimeDerivative.partial_t inv_t t = - (inv_t t)^2
  inv_t_nonneg : ∀ t, (0:R) ≤ inv_t t

/-- Single-variable calculus rules for scalar time derivatives. -/
class ScalarTimeDerivativeRules (R : Type) [CommRing R] (Time : Type) [TimeDerivative Time R] where
  /-- Product rule for addition: $\partial_t(f + g) = \partial_t f + \partial_t g$ -/
  dt_add : ∀ (f g : Time → R) t, TimeDerivative.partial_t (fun s => f s + g s) t = TimeDerivative.partial_t f t + TimeDerivative.partial_t g t
  /-- Product rule for subtraction: $\partial_t(f - g) = \partial_t f - \partial_t g$ -/
  dt_sub : ∀ (f g : Time → R) t, TimeDerivative.partial_t (fun s => f s - g s) t = TimeDerivative.partial_t f t - TimeDerivative.partial_t g t
  /-- Linearity for scalar multiplication: $\partial_t(cf) = c \partial_t f$ -/
  dt_smul : ∀ (c : R) (f : Time → R) t, TimeDerivative.partial_t (fun s => c * f s) t = c * TimeDerivative.partial_t f t
  /-- Product rule for multiplication: $\partial_t(fg) = (\partial_t f)g + f(\partial_t g)$ -/
  dt_mul : ∀ (f g : Time → R) t, TimeDerivative.partial_t (fun s => f s * g s) t = TimeDerivative.partial_t f t * g t + f t * TimeDerivative.partial_t g t


variable {R V : Type}
variable [CommRing R] [AddCommGroup V] [Module R V] [DerivationAction R V]

class StaticMetricTimeRules
  (Time : Type)
  [TimeDerivative Time R]
  [TimeDerivative Time V]
  (metric : MetricDuality R V)
  [MetricTraceOperator R V metric.toNonDegenerateMetric.toMetricTensor]
  (conn : AffineConnection R V) where
  dt_laplacian : ∀ (f : Time → R) t,
    TimeDerivative.partial_t (fun s => laplacian metric.toNonDegenerateMetric.toMetricTensor conn (f s)) t =
    laplacian metric.toNonDegenerateMetric.toMetricTensor conn (TimeDerivative.partial_t f t)
  dt_grad : ∀ (f : Time → R) t,
    TimeDerivative.partial_t (fun s => grad metric (f s)) t = grad metric (TimeDerivative.partial_t f t)
  dt_metric_g : ∀ (X : Time → V) t,
    TimeDerivative.partial_t (fun s => metric.g (X s) (X s)) t =
    (2:R) * metric.g (X t) (TimeDerivative.partial_t X t)
