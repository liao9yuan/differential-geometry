import DifferentialGeometry.Algebra.Basic
import DifferentialGeometry.Geometry.Metric
import DifferentialGeometry.Geometry.Connection
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

/-!
# Metric Compatibility Example
Proof of metric compatibility consequences on the squared norm directional derivative.
-/

variable {R V : Type}
variable [CommRing R] [AddCommGroup V] [Module R V]
variable [DerivationAction R V]
variable (metric : MetricTensor R V)
variable (conn : AffineConnection R V) [MetricCompatible conn metric]

/-- Directional derivative of squared norm under metric compatibility: `X⟨Y, Y⟩ = 2⟨∇_X Y, Y⟩`.
Input: (V, V)
Output: Prop -/
theorem norm_sq_deriv (X Y : V) :
  DerivationAction.action X (metric.g Y Y) = metric.g (conn.nabla X Y) Y + metric.g (conn.nabla X Y) Y := by
  -- Step 1: Expand using metric compatibility: X ⟨Y, Y⟩ = ⟨∇_X Y, Y⟩ + ⟨Y, ∇_X Y⟩
  rw [MetricCompatible.compat (conn := conn) X Y Y]
  -- Step 2: Use the symmetry of the metric tensor: ⟨Y, ∇_X Y⟩ = ⟨∇_X Y, Y⟩
  rw [metric.symm Y (conn.nabla X Y)]

#check norm_sq_deriv
