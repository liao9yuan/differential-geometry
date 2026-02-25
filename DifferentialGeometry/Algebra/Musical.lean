import DifferentialGeometry.Algebra.Basic
import DifferentialGeometry.Algebra.Metric

set_option autoImplicit false
set_option linter.style.longLine false

/-- Musical isomorphisms identifying vector fields with 1-forms.
Input: (MetricTensor R V)
Output: Type -/
class MusicalIsomorphism (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] [ScalarMul R V] (metric : MetricTensor R V) where
  sharp : (V → R) → V
  flat : V → (V → R)
  sharp_add : ∀ f g : V → R, sharp (fun v => f v + g v) = sharp f + sharp g
  sharp_smul : ∀ (c : R) (f : V → R), sharp (fun v => c * f v) = ScalarMul.smul c (sharp f)
  sharp_g : ∀ Y : V, sharp (fun Z => metric.g Y Z) = Y
  g_sharp : ∀ (f : V → R) (Z : V), metric.g (sharp f) Z = f Z
  flat_def : ∀ (X Y : V), flat X Y = metric.g X Y
