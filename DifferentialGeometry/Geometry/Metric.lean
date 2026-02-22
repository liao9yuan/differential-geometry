import DifferentialGeometry.Algebra.Basic

set_option autoImplicit false


/-!
# Riemannian Metric
Algebraic formulation of the metric tensor and associated trace operations.
-/

/-- Metric tensor structure enforcing symmetry and bilinearity.
Input: (V, V)
Output: R -/
structure MetricTensor (R V : Type) [Add R] [Mul R] [Add V] [ScalarMul R V] where
  g : V → V → R
  symm : ∀ X Y : V, g X Y = g Y X
  bilinear_add_left : ∀ X Y Z : V, g (X + Y) Z = g X Z + g Y Z
  bilinear_smul_left : ∀ (f : R) (X Y : V), g (f • X) Y = f * (g X Y)

/-- Trace operator associated with a specific metric tensor.
Input: (V → V → R)
Output: R -/
class MetricTraceOperator (R V : Type) [Add R] [Mul R] [Add V] [ScalarMul R V] (metric : MetricTensor R V) where
  metric_trace : (V → V → R) → R
