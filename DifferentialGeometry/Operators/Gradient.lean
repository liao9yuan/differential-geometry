import DifferentialGeometry.Algebra.Basic
import DifferentialGeometry.Algebra.Metric
import DifferentialGeometry.Algebra.Musical

set_option autoImplicit false
set_option linter.style.longLine false

variable {R V : Type}
variable [CommRing R] [AddCommGroup V] [Module R V]
variable [DerivationAction R V]

open DerivationAction

/-- Gradient of a scalar function `u`.
Input: (MetricTensor R V, R)
Output: V -/
def grad (metric : MetricDuality R V) (u : R) : V :=
  metric.sharp (fun X => action X u)

lemma g_grad (metric : MetricDuality R V) (u : R) (X : V) :
  metric.g (grad metric u) X = action X u := by
  dsimp [grad]
  exact metric.g_sharp (fun Y => action Y u) X
