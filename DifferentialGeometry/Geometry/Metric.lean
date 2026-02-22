import DifferentialGeometry.Algebra.Basic
import DifferentialGeometry.Algebra.BilinearForm

set_option autoImplicit false
set_option linter.style.longLine false


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

/-- Axiomatic rules for the metric trace operator.
Input: (MetricTensor R V)
Output: Type -/
class MetricTraceRules (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] [ScalarMul R V]
  (metric : MetricTensor R V) [MetricTraceOperator R V metric] where
  trace_add : ∀ (T₁ T₂ : V → V → R),
    MetricTraceOperator.metric_trace metric (fun X Y => T₁ X Y + T₂ X Y) =
    MetricTraceOperator.metric_trace metric T₁ + MetricTraceOperator.metric_trace metric T₂
  trace_smul : ∀ (a : R) (T : V → V → R),
    MetricTraceOperator.metric_trace metric (fun X Y => a * T X Y) =
    a * MetricTraceOperator.metric_trace metric T
