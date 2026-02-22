import DifferentialGeometry.Algebra.Basic
import DifferentialGeometry.Geometry.Metric

set_option autoImplicit false

variable {R V : Type}
variable [Add R] [Mul R] [Sub R] [Neg R]
variable [Add V] [Sub V] [Neg V] [ScalarMul R V]
variable [DerivationAction R V]

open DerivationAction

/--
The gradient operator for a metric tensor.
Provides a vector field `grad u` for a scalar function `u` such that
$g(\text{grad } u, X) = X(u)$ for all vector fields $X$.
-/
class Gradient (R V : Type) [Add R] [Mul R] [Add V] [ScalarMul R V]
    [DerivationAction R V] (metric : MetricTensor R V) where
  grad : R → V
  grad_prop : ∀ u : R, ∀ X : V, metric.g (grad u) X = action X u
