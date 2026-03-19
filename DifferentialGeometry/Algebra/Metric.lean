import DifferentialGeometry.Algebra.VectorField
import DifferentialGeometry.Algebra.BilinearForm
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option linter.style.longLine false


/-!
# Riemannian Metric
Algebraic formulation of the metric tensor and associated trace operations.
-/

/-- Metric tensor structure enforcing symmetry and bilinearity.
Input: (V, V)
Output: R -/
structure AbstractMetricTensor (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] where
  g : V → V → R
  symm : ∀ X Y : V, g X Y = g Y X
  bilinear_add_left : ∀ X Y Z : V, g (X + Y) Z = g X Z + g Y Z
  bilinear_smul_left : ∀ (f : R) (X Y : V), g (f • X) Y = f * (g X Y)

lemma metric_neg_left {R V} [CommRing R] [AddCommGroup V] [Module R V] (metric : AbstractMetricTensor R V) (X Y : V) : metric.g (-X) Y = - metric.g X Y := by
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

lemma metric_sub_left {R V} [CommRing R] [AddCommGroup V] [Module R V] (metric : AbstractMetricTensor R V) (X Y Z : V) : metric.g (X - Y) Z = metric.g X Z - metric.g Y Z := by
  calc metric.g (X - Y) Z = metric.g (X + -Y) Z := by rw [sub_eq_add_neg]
    _ = metric.g X Z + metric.g (-Y) Z := metric.bilinear_add_left X (-Y) Z
    _ = metric.g X Z + - metric.g Y Z := by rw [metric_neg_left]
    _ = metric.g X Z - metric.g Y Z := by rw [sub_eq_add_neg]

/-- Trace operator associated with a specific metric tensor.
Input: (V → V → R)
Output: R -/
class MetricTraceOperator (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] (metric : AbstractMetricTensor R V) where
  metric_trace : (V → V → R) → R

/-- Axiomatic rules for the metric trace operator.
Input: (AbstractMetricTensor R V)
Output: Type -/
class MetricTraceRules (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V]
  (metric : AbstractMetricTensor R V) [MetricTraceOperator R V metric] where
  trace_add : ∀ (T₁ T₂ : V → V → R),
    MetricTraceOperator.metric_trace metric (fun X Y => T₁ X Y + T₂ X Y) =
    MetricTraceOperator.metric_trace metric T₁ + MetricTraceOperator.metric_trace metric T₂
  trace_smul : ∀ (a : R) (T : V → V → R),
    MetricTraceOperator.metric_trace metric (fun X Y => a * T X Y) =
    a * MetricTraceOperator.metric_trace metric T

/-- A metric tensor is non-degenerate if it implies equality of vector fields
when their inner products with all other vector fields are equal.
Input: (AbstractMetricTensor R V)
Output: Type -/
class NonDegenerateMetric (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] extends AbstractMetricTensor R V where
  eq_of_forall_g_eq : ∀ X Y : V, (∀ Z : V, g X Z = g Y Z) → X = Y

/-- Metric duality provides the musical isomorphism to convert bilinear forms to endomorphisms, and 1-forms to vector fields.
Input: (NonDegenerateMetric R V)
Output: Type -/
class MetricDuality (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] extends NonDegenerateMetric R V where
  raise : SmoothBilinearForm R V → (V → V)
  g_raise : ∀ (T : SmoothBilinearForm R V) (X Y : V), g (raise T X) Y = T X Y
  sharp : (V → R) → V
  flat : V → (V → R)
  sharp_add : ∀ f h : V → R, sharp (fun v => f v + h v) = sharp f + sharp h
  sharp_smul : ∀ (c : R) (f : V → R), sharp (fun v => c * f v) = c • (sharp f)
  sharp_g : ∀ Y : V, sharp (fun Z => g Y Z) = Y
  g_sharp : ∀ (f : V → R) (Z : V), g (sharp f) Z = f Z
  flat_def : ∀ (X Y : V), flat X Y = g X Y

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
variable (metric_duality : MetricDuality R V)

/-- Prove linearity of raise over addition. -/
lemma raise_add (T₁ T₂ : SmoothBilinearForm R V) (X : V) :
    metric_duality.raise (T₁ + T₂) X = metric_duality.raise T₁ X + metric_duality.raise T₂ X := by
  apply metric_duality.eq_of_forall_g_eq
  intro Z
  have h1 : metric_duality.g (metric_duality.raise (T₁ + T₂) X) Z = (T₁ + T₂) X Z := metric_duality.g_raise (T₁ + T₂) X Z
  have h2 : (T₁ + T₂) X Z = T₁ X Z + T₂ X Z := rfl
  have h3 : T₁ X Z = metric_duality.g (metric_duality.raise T₁ X) Z := by rw [metric_duality.g_raise T₁ X Z]
  have h4 : T₂ X Z = metric_duality.g (metric_duality.raise T₂ X) Z := by rw [metric_duality.g_raise T₂ X Z]
  have h5 : metric_duality.g (metric_duality.raise T₁ X + metric_duality.raise T₂ X) Z = metric_duality.g (metric_duality.raise T₁ X) Z + metric_duality.g (metric_duality.raise T₂ X) Z := metric_duality.bilinear_add_left _ _ _
  calc metric_duality.g (metric_duality.raise (T₁ + T₂) X) Z = T₁ X Z + T₂ X Z := by { rw [h1]; rfl }
    _ = metric_duality.g (metric_duality.raise T₁ X) Z + metric_duality.g (metric_duality.raise T₂ X) Z := by rw [h3, h4]
    _ = metric_duality.g (metric_duality.raise T₁ X + metric_duality.raise T₂ X) Z := by rw [h5]

/-- Prove linearity of raise over scalar multiplication. -/
lemma raise_smul (T : SmoothBilinearForm R V) (c : R) (X : V) :
    metric_duality.raise (c • T) X = c • metric_duality.raise T X := by
  apply metric_duality.eq_of_forall_g_eq
  intro Z
  have h1 : metric_duality.g (metric_duality.raise (c • T) X) Z = (c • T) X Z := metric_duality.g_raise (c • T) X Z
  -- (c • T) X Z = c * T X Z by definition
  have h3 : c * T X Z = c * metric_duality.g (metric_duality.raise T X) Z := by rw [metric_duality.g_raise T X Z]
  have h4 : metric_duality.g (c • metric_duality.raise T X) Z = c * metric_duality.g (metric_duality.raise T X) Z := metric_duality.bilinear_smul_left c _ Z
  calc metric_duality.g (metric_duality.raise (c • T) X) Z = c * T X Z := by { rw [h1]; rfl }
    _ = c * metric_duality.g (metric_duality.raise T X) Z := h3
    _ = metric_duality.g (c • metric_duality.raise T X) Z := by rw [h4]
