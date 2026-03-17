import DifferentialGeometry.Algebra.Basic
import DifferentialGeometry.Algebra.BilinearForm
import DifferentialGeometry.Algebra.Metric
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Musical Isomorphisms
Defines non-degenerate metrics and the metric duality (raising indices).
-/

/-- A metric tensor is non-degenerate if it implies equality of vector fields
when their inner products with all other vector fields are equal.
Input: (AbstractMetricTensor R V)
Output: Type -/
class NonDegenerateMetric (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] extends AbstractMetricTensor R V where
  eq_of_forall_g_eq : ∀ X Y : V, (∀ Z : V, g X Z = g Y Z) → X = Y

/-- Metric duality provides the musical isomorphism to convert bilinear forms to endomorphisms, and 1-forms to vector fields.
Input: (NonDegenerateMetric R V)
Output: Type -/
class MetricDuality (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] extends NonDegenerateMetric R V where
  raise : SmoothBilinearForm R V → (V → V)
  g_raise : ∀ (T : SmoothBilinearForm R V) (X Y : V), g (raise T X) Y = T X Y
  sharp : (V → R) → V
  flat : V → (V → R)
  sharp_add : ∀ f h : V → R, sharp (fun v => f v + h v) = sharp f + sharp h
  sharp_smul : ∀ (c : R) (f : V → R), sharp (fun v => c * f v) = c • (sharp f)
  sharp_g : ∀ Y : V, sharp (fun Z => g Y Z) = Y
  g_sharp : ∀ (f : V → R) (Z : V), g (sharp f) Z = f Z
  flat_def : ∀ (X Y : V), flat X Y = g X Y

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V]
variable (metric : MetricDuality R V)

/-- Prove linearity of raise over addition. -/
lemma raise_add (T₁ T₂ : SmoothBilinearForm R V) (X : V) :
    metric.raise (T₁ + T₂) X = metric.raise T₁ X + metric.raise T₂ X := by
  apply metric.eq_of_forall_g_eq
  intro Z
  have h1 : metric.g (metric.raise (T₁ + T₂) X) Z = (T₁ + T₂) X Z := metric.g_raise (T₁ + T₂) X Z
  have h2 : (T₁ + T₂) X Z = T₁ X Z + T₂ X Z := rfl
  have h3 : T₁ X Z = metric.g (metric.raise T₁ X) Z := by rw [metric.g_raise T₁ X Z]
  have h4 : T₂ X Z = metric.g (metric.raise T₂ X) Z := by rw [metric.g_raise T₂ X Z]
  have h5 : metric.g (metric.raise T₁ X + metric.raise T₂ X) Z = metric.g (metric.raise T₁ X) Z + metric.g (metric.raise T₂ X) Z := metric.bilinear_add_left _ _ _
  calc metric.g (metric.raise (T₁ + T₂) X) Z = T₁ X Z + T₂ X Z := by { rw [h1]; rfl }
    _ = metric.g (metric.raise T₁ X) Z + metric.g (metric.raise T₂ X) Z := by rw [h3, h4]
    _ = metric.g (metric.raise T₁ X + metric.raise T₂ X) Z := by rw [h5]

/-- Prove linearity of raise over scalar multiplication. -/
lemma raise_smul (T : SmoothBilinearForm R V) (c : R) (X : V) :
    metric.raise (c • T) X = c • metric.raise T X := by
  apply metric.eq_of_forall_g_eq
  intro Z
  have h1 : metric.g (metric.raise (c • T) X) Z = (c • T) X Z := metric.g_raise (c • T) X Z
  -- (c • T) X Z = c * T X Z by definition
  have h3 : c * T X Z = c * metric.g (metric.raise T X) Z := by rw [metric.g_raise T X Z]
  have h4 : metric.g (c • metric.raise T X) Z = c * metric.g (metric.raise T X) Z := metric.bilinear_smul_left c _ Z
  calc metric.g (metric.raise (c • T) X) Z = c * T X Z := by { rw [h1]; rfl }
    _ = c * metric.g (metric.raise T X) Z := h3
    _ = metric.g (c • metric.raise T X) Z := by rw [h4]
