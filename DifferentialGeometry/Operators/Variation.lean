import DifferentialGeometry.Algebra.Basic
import DifferentialGeometry.Algebra.BilinearForm
import DifferentialGeometry.Geometry.Metric
import DifferentialGeometry.Geometry.Connection
import DifferentialGeometry.Geometry.Curvature
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Time Derivatives and Variation
Defines generic time derivatives, variation of metric, and Ricci bilinearity.
-/

open DerivationAction
open LieBracket

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V]

lemma smul_eq_hSMul (c : R) (W : V) : ScalarMul.smul c W = HSMul.hSMul c W := rfl

-- 1. Generic Time Derivative
class TimeDerivative (Time α : Type) where
  partial_t : (Time → α) → Time → α

-- 2. Time Derivative Rules
class TimeDerivativeRules (Time R V : Type) [CommRing R] [AddCommGroup V] [Module R V] [TimeDerivative Time R] where
  t_add : ∀ (f₁ f₂ : Time → R) (t : Time),
    TimeDerivative.partial_t (fun s => f₁ s + f₂ s) t = TimeDerivative.partial_t f₁ t + TimeDerivative.partial_t f₂ t
  t_smul : ∀ (c : R) (f : Time → R) (t : Time),
    TimeDerivative.partial_t (fun s => c * f s) t = c * TimeDerivative.partial_t f t

-- 3. Metric Variation Form
def metric_var_form {Time : Type} [TimeDerivative Time R] [TimeDerivativeRules Time R V]
  (g_fam : Time → MetricTensor R V) (t : Time) : SmoothBilinearForm R V where
  val := fun X Y => TimeDerivative.partial_t (fun s => (g_fam s).g X Y) t
  add_left := fun X₁ X₂ Y => by
    have h1 : (fun s => (g_fam s).g (X₁ + X₂) Y) = (fun s => (g_fam s).g X₁ Y + (g_fam s).g X₂ Y) := by
      funext s
      exact (g_fam s).bilinear_add_left X₁ X₂ Y
    rw [h1]
    exact TimeDerivativeRules.t_add V (fun s => (g_fam s).g X₁ Y) (fun s => (g_fam s).g X₂ Y) t
  smul_left := fun c X Y => by
    simp only [← smul_eq_hSMul c X]
    have h1 : (fun s => (g_fam s).g (ScalarMul.smul c X) Y) = (fun s => c * (g_fam s).g X Y) := by
      funext s
      have step := (g_fam s).bilinear_smul_left c X Y
      exact step
    rw [h1]
    exact TimeDerivativeRules.t_smul V c (fun s => (g_fam s).g X Y) t
  add_right := fun X Y₁ Y₂ => by
    have h1 : (fun s => (g_fam s).g X (Y₁ + Y₂)) = (fun s => (g_fam s).g X Y₁ + (g_fam s).g X Y₂) := by
      funext s
      have h2 : (g_fam s).g X (Y₁ + Y₂) = (g_fam s).g (Y₁ + Y₂) X := (g_fam s).symm _ _
      have h3 : (g_fam s).g (Y₁ + Y₂) X = (g_fam s).g Y₁ X + (g_fam s).g Y₂ X := (g_fam s).bilinear_add_left _ _ _
      have h4 : (g_fam s).g Y₁ X = (g_fam s).g X Y₁ := (g_fam s).symm _ _
      have h5 : (g_fam s).g Y₂ X = (g_fam s).g X Y₂ := (g_fam s).symm _ _
      rw [h2, h3, h4, h5]
    rw [h1]
    exact TimeDerivativeRules.t_add V (fun s => (g_fam s).g X Y₁) (fun s => (g_fam s).g X Y₂) t
  smul_right := fun c X Y => by
    simp only [← smul_eq_hSMul c Y]
    have h1 : (fun s => (g_fam s).g X (ScalarMul.smul c Y)) = (fun s => c * (g_fam s).g X Y) := by
      funext s
      have h2 : (g_fam s).g X (ScalarMul.smul c Y) = (g_fam s).g (ScalarMul.smul c Y) X := (g_fam s).symm _ _
      have step := (g_fam s).bilinear_smul_left c Y X
      have h3 : (g_fam s).g (ScalarMul.smul c Y) X = c * (g_fam s).g Y X := step
      have h4 : (g_fam s).g Y X = (g_fam s).g X Y := (g_fam s).symm _ _
      rw [h2, h3, h4]
    rw [h1]
    exact TimeDerivativeRules.t_smul V c (fun s => (g_fam s).g X Y) t

variable [DerivationAction R V] [LieBracket V] [TraceOperator R V]

-- 4. Ricci Form Rules and Wrapping
class RicciFormRules (conn : AffineConnection R V) where
  add_left : ∀ X₁ X₂ Y, Rc conn (X₁ + X₂) Y = Rc conn X₁ Y + Rc conn X₂ Y
  smul_left : ∀ a X Y, Rc conn (HSMul.hSMul a X) Y = a * Rc conn X Y
  add_right : ∀ X Y₁ Y₂, Rc conn X (Y₁ + Y₂) = Rc conn X Y₁ + Rc conn X Y₂
  smul_right : ∀ a X Y, Rc conn X (HSMul.hSMul a Y) = a * Rc conn X Y

def ricciForm (conn : AffineConnection R V) [RicciFormRules conn] : SmoothBilinearForm R V where
  val := fun X Y => Rc conn X Y
  add_left := RicciFormRules.add_left
  smul_left := RicciFormRules.smul_left
  add_right := RicciFormRules.add_right
  smul_right := RicciFormRules.smul_right
