import DifferentialGeometry.Algebra.Basic
import DifferentialGeometry.Algebra.BilinearForm
import DifferentialGeometry.Geometry.Metric
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Musical Endomorphisms
Algebraic formulation of the sharp operator raising indices via a non-degenerate metric.
-/

-- A metric is non-degenerate if it can distinguish all vectors
/-- Formalizes the non-degeneracy condition for a metric tensor. -/
class NonDegenerateMetric (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] [ScalarMul R V] (metric : MetricTensor R V) where
  eq_of_forall_g_eq : ∀ A B : V, (∀ Y : V, metric.g A Y = metric.g B Y) → A = B

-- The sharp operator turning a bilinear form into an endomorphism
/-- The musical isomorphism lifting a (0,2)-tensor to an endomorphism. -/
class MusicalEndomorphism (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] [ScalarMul R V] (metric : MetricTensor R V) where
  to_endo : SmoothBilinearForm R V → (V → V)
  g_endo : ∀ (T : SmoothBilinearForm R V) (X Y : V), metric.g (to_endo T X) Y = T X Y

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] [ScalarMul R V] {metric : MetricTensor R V}
variable [NonDegenerateMetric R V metric] [MusicalEndomorphism R V metric]

-- Proves that the lifted endomorphism preserves addition
/-- The sharp operator maps the sum of vectors linearly. -/
lemma endo_add (T : SmoothBilinearForm R V) (X₁ X₂ : V) :
    (MusicalEndomorphism.to_endo (metric := metric) T) (X₁ + X₂) =
    (MusicalEndomorphism.to_endo (metric := metric) T) X₁ + (MusicalEndomorphism.to_endo (metric := metric) T) X₂ := by
  apply NonDegenerateMetric.eq_of_forall_g_eq (R := R) (metric := metric)
  intro Y
  rw [metric.bilinear_add_left]
  rw [MusicalEndomorphism.g_endo]
  rw [MusicalEndomorphism.g_endo]
  rw [MusicalEndomorphism.g_endo]
  rw [T.add_left]

-- Proves that the lifted endomorphism preserves scalar multiplication
/-- The sharp operator maps scalar multiplication linearly. -/
lemma endo_smul (T : SmoothBilinearForm R V) (c : R) (X : V) :
    (MusicalEndomorphism.to_endo (metric := metric) T) (HSMul.hSMul c X) =
    ScalarMul.smul c ((MusicalEndomorphism.to_endo (metric := metric) T) X) := by
  apply NonDegenerateMetric.eq_of_forall_g_eq (R := R) (metric := metric)
  intro Y
  rw [metric.bilinear_smul_left]
  rw [MusicalEndomorphism.g_endo]
  rw [MusicalEndomorphism.g_endo]
  rw [T.smul_left]
