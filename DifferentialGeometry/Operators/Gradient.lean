import DifferentialGeometry.Algebra.Basic
import DifferentialGeometry.Algebra.Metric
import DifferentialGeometry.Algebra.Musical

set_option autoImplicit false
set_option linter.style.longLine false

variable {R V : Type}
variable [CommRing R] [AddCommGroup V] [Module R V]
variable [ScalarMul R V] [DerivationAction R V]

open DerivationAction

/-- Gradient of a scalar function `u`.
Input: (MetricTensor R V, R)
Output: V -/
def grad (metric : MetricTensor R V) [iso : MusicalIsomorphism R V metric] (u : R) : V :=
  iso.sharp (fun X => action X u)
