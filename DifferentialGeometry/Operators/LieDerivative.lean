import DifferentialGeometry.Algebra.Basic
import DifferentialGeometry.Algebra.Metric
import DifferentialGeometry.Geometry.Connection
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Lie Derivative
Definition of the Lie derivative of a metric tensor.
-/

variable {R V : Type}
variable [CommRing R] [AddCommGroup V] [Module R V]

open DerivationAction
open LieBracket

-- Extracts the negative sign from the left argument of the metric tensor.
lemma metric_neg_left_local (metric : MetricTensor R V) (X Y : V) : metric.g (-X) Y = - metric.g X Y := by
  have h1 : metric.g (X + -X) Y = metric.g X Y + metric.g (-X) Y := metric.bilinear_add_left X (-X) Y
  have h3 : metric.g (0 + 0) Y = metric.g 0 Y + metric.g 0 Y := metric.bilinear_add_left 0 0 Y
  have h5 : metric.g 0 Y = 0 := by
    calc metric.g 0 Y = metric.g 0 Y + metric.g 0 Y - metric.g 0 Y := by ring
      _ = metric.g (0 + 0) Y - metric.g 0 Y := by rw [← h3]
      _ = metric.g 0 Y - metric.g 0 Y := by rw [add_zero]
      _ = 0 := by ring
  calc metric.g (-X) Y = metric.g X Y + metric.g (-X) Y - metric.g X Y := by ring
    _ = metric.g (X + -X) Y - metric.g X Y := by rw [← h1]
    _ = metric.g 0 Y - metric.g X Y := by rw [add_neg_cancel]
    _ = 0 - metric.g X Y := by rw [h5]
    _ = - metric.g X Y := by ring

-- Expands subtraction in the left argument of the metric tensor into a difference of values.
lemma metric_sub_left_local (metric : MetricTensor R V) (X Y Z : V) : metric.g (X - Y) Z = metric.g X Z - metric.g Y Z := by
  calc metric.g (X - Y) Z = metric.g (X + -Y) Z := by rw [sub_eq_add_neg]
    _ = metric.g X Z + metric.g (-Y) Z := metric.bilinear_add_left X (-Y) Z
    _ = metric.g X Z + - metric.g Y Z := by rw [metric_neg_left_local metric Y Z]
    _ = metric.g X Z - metric.g Y Z := by rw [sub_eq_add_neg]

-- Expands subtraction in the right argument of the metric tensor into a difference of values.
lemma metric_sub_right_local (metric : MetricTensor R V) (X Y Z : V) : metric.g X (Y - Z) = metric.g X Y - metric.g X Z := by
  calc metric.g X (Y - Z) = metric.g (Y - Z) X := metric.symm _ _
    _ = metric.g Y X - metric.g Z X := metric_sub_left_local metric Y Z X
    _ = metric.g X Y - metric.g X Z := by rw [metric.symm Y X, metric.symm Z X]

variable [DerivationAction R V]

/-- The Lie derivative of a metric tensor along a vector field. -/
def lieDerivMetric (metric : MetricTensor R V) [LieBracket V] (X Y Z : V) : R :=
  action X (metric.g Y Z) - metric.g (bracket X Y) Z - metric.g Y (bracket X Z)

-- Proves the Lie derivative of the metric tensor along X equals the symmetrized covariant derivative of X.
theorem lieDerivMetric_eq_nabla (metric : MetricTensor R V) (conn : AffineConnection R V) [LieBracket V] [MetricCompatible conn metric] [TorsionFree conn] (X Y Z : V) :
  lieDerivMetric metric X Y Z = metric.g (conn.nabla Y X) Z + metric.g Y (conn.nabla Z X) := by
  unfold lieDerivMetric
  rw [MetricCompatible.compat (conn := conn) X Y Z]
  have h1 : bracket X Y = conn.nabla X Y - conn.nabla Y X := (TorsionFree.torsion_zero (conn := conn) X Y).symm
  have h2 : bracket X Z = conn.nabla X Z - conn.nabla Z X := (TorsionFree.torsion_zero (conn := conn) X Z).symm
  rw [h1, h2]
  rw [metric_sub_left_local metric (conn.nabla X Y) (conn.nabla Y X) Z]
  rw [metric_sub_right_local metric Y (conn.nabla X Z) (conn.nabla Z X)]
  abel
