import DifferentialGeometry.Algebra.Basic
import DifferentialGeometry.Geometry.Metric

set_option autoImplicit false

variable {R V : Type}
variable [Add R] [Mul R] [Sub R] [Neg R]
variable [Add V] [Sub V] [Neg V] [ScalarMul R V]
variable [DerivationAction R V]

open DerivationAction

/--
The musical isomorphism (sharp operator) mapping covector-like operations to vector fields.
-/
class MusicalIsomorphism (R V : Type) [Add R] [Mul R] [Add V] [ScalarMul R V] (metric : MetricTensor R V) where
  sharp : (V → R) → V

/--
The computable gradient operator for a metric tensor.
Provides a vector field `grad u` for a scalar function `u` using the sharp operator.
-/
def grad (metric : MetricTensor R V) [iso : MusicalIsomorphism R V metric] (u : R) : V :=
  iso.sharp (fun X => action X u)
