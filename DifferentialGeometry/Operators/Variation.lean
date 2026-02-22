import DifferentialGeometry.Algebra.Basic
import DifferentialGeometry.Geometry.Metric

set_option autoImplicit false

/-- Formal time derivative operator.
Input: (Time → α, Time)
Output: α -/
class TimeDerivative (Time α : Type) where
  partial_t : (Time → α) → Time → α

export TimeDerivative (partial_t)

variable {Time α R V : Type}
variable [Add R] [Mul R] [Sub R] [Neg R]
variable [Add V] [Sub V] [Neg V] [ScalarMul R V]

variable [TimeDerivative Time (V → V → R)]

/-- Metric variation evaluate at time `t`.
Input: (Time → MetricTensor R V, Time)
Output: V → V → R -/
def metric_var (metric_family : Time → MetricTensor R V) (t : Time) : V → V → R :=
  partial_t (fun τ => (metric_family τ).g) t
