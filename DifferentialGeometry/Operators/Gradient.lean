import DifferentialGeometry.Algebra.Basic
import DifferentialGeometry.Geometry.Metric

set_option autoImplicit false
set_option linter.style.longLine false

variable {R V : Type}
variable [Add R] [Mul R] [Sub R] [Neg R]
variable [Add V] [Sub V] [Neg V] [ScalarMul R V]
variable [DerivationAction R V]

open DerivationAction

/-- Musical isomorphism mapping covectors to vector fields (sharp operator).
Input: (V → R)
Output: V -/
class MusicalIsomorphism (R V : Type) [Add R] [Mul R] [Add V] [ScalarMul R V] (metric : MetricTensor R V) where
  sharp : (V → R) → V

/-- Gradient of a scalar function `u`.
Input: (MetricTensor R V, R)
Output: V -/
def grad (metric : MetricTensor R V) [iso : MusicalIsomorphism R V metric] (u : R) : V :=
  iso.sharp (fun X => action X u)
