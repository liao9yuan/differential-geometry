import DifferentialGeometry.Algebra.Basic
import DifferentialGeometry.Geometry.Metric
import DifferentialGeometry.Operators.Hessian

set_option autoImplicit false

variable {R V : Type}
variable [Add R] [Mul R] [Sub R] [Neg R]
variable [Add V] [Sub V] [Neg V] [ScalarMul R V]
variable [DerivationAction R V]

/--
The Laplacian of a function `u` is the metric trace of its Hessian.
$\Delta u = \text{tr}_g (\nabla^2 u)$
-/
def laplacian (metric : MetricTensor R V) [MetricTraceOperator R V metric]
    (conn : AffineConnection R V) (u : R) : R :=
  MetricTraceOperator.metric_trace metric (Hess conn u)
