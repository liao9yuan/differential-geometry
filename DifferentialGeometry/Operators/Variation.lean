import DifferentialGeometry.Algebra.Basic
import DifferentialGeometry.Geometry.Metric

set_option autoImplicit false

/--
A formal derivative operator with respect to a time-like parameter.
Provides `partial_t` : (Time → α) → Time → α.
-/
class TimeDerivative (Time α : Type) where
  partial_t : (Time → α) → Time → α

export TimeDerivative (partial_t)

variable {Time α R V : Type}
variable [Add R] [Mul R] [Sub R] [Neg R]
variable [Add V] [Sub V] [Neg V] [ScalarMul R V]

-- To avoid polluting global typeclass resolution with generic instances,
-- we use `variable` to inject the assumption that our 2-tensors
-- can be differentiated with respect to `Time`.
variable [TimeDerivative Time (V → V → R)]

/--
The metric variation. Takes a parameterized family of metrics and computes
the variation at a specific time `t`.
-/
def metric_var (metric_family : Time → MetricTensor R V) (t : Time) : V → V → R :=
  partial_t (fun τ => (metric_family τ).g) t
