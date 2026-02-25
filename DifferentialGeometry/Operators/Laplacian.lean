import DifferentialGeometry.Algebra.Basic
import DifferentialGeometry.Algebra.Metric
import DifferentialGeometry.Operators.Hessian
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic

set_option autoImplicit false

variable {R V : Type}
variable [CommRing R] [AddCommGroup V] [Module R V]
variable [DerivationAction R V]

/-- Laplacian of a function defined as the metric trace of its Hessian: `Δu = tr_g(∇²u)`.
Input: (MetricTensor R V, AffineConnection R V, R)
Output: R -/
def laplacian (metric : MetricTensor R V) [MetricTraceOperator R V metric]
    (conn : AffineConnection R V) (u : R) : R :=
  MetricTraceOperator.metric_trace metric (Hess conn u)
