import DifferentialGeometry.Algebra.Basic

set_option autoImplicit false


/-!
# Riemannian Metric
Algebraic formulation of the metric tensor and metric-based operations.
-/

-- 1. Riemannian Metric
structure MetricTensor (R V : Type) [Add R] [Mul R] [Add V] [ScalarMul R V] where
  g : V → V → R
  symm : ∀ X Y : V, g X Y = g Y X
  bilinear_add_left : ∀ X Y Z : V, g (X + Y) Z = g X Z + g Y Z
  -- Note: Output is in R, so scalar multiplication on the output uses Ring Mul (*)
  bilinear_smul_left : ∀ (f : R) (X Y : V), g (f • X) Y = f * (g X Y)

-- 2. Metric Trace Operator (For raising indices to trace)
class MetricTraceOperator (R V : Type) [Add R] [Mul R] [Add V] [ScalarMul R V] (metric : MetricTensor R V) where
  metric_trace : (V → V → R) → R
