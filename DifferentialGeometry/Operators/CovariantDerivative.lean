import DifferentialGeometry.Algebra.Basic
import DifferentialGeometry.Algebra.BilinearForm
import DifferentialGeometry.Geometry.Connection
import DifferentialGeometry.Algebra.Metric
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option linter.style.longLine false

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] [DerivationAction R V] [LieBracket V]

open DerivationAction

/-!
# Covariant Derivative of Tensors
Defines the covariant derivative of a (0,2)-tensor along a vector field.
-/

/-- Raw evaluation of the covariant derivative of a (0,2)-tensor T along a vector field X.
Input: (AffineConnection R V, V, SmoothBilinearForm R V, V, V)
Output: R -/
def rawCovDeriv (conn : AffineConnection R V) (X : V) (T : SmoothBilinearForm R V) (Y Z : V) : R :=
  action X (T Y Z) - T (conn.nabla X Y) Z - T Y (conn.nabla X Z)

section Linearity

variable (conn : AffineConnection R V) [DerivationRules R V] (X : V) (T : SmoothBilinearForm R V)

/-- Prove that the raw covariant derivative is additive with respect to the first vector field argument.
Input: (V, V, V)
Output: Prop -/
lemma rawCovDeriv_add_left (Y₁ Y₂ Z : V) :
  rawCovDeriv conn X T (Y₁ + Y₂) Z = rawCovDeriv conn X T Y₁ Z + rawCovDeriv conn X T Y₂ Z := by
  dsimp [rawCovDeriv]
  have h1 : T (Y₁ + Y₂) Z = T Y₁ Z + T Y₂ Z := T.add_left _ _ _
  rw [h1]
  have h2 : action X (T Y₁ Z + T Y₂ Z) = action X (T Y₁ Z) + action X (T Y₂ Z) := DerivationRules.action_add_right X _ _
  rw [h2]
  have h3 : conn.nabla X (Y₁ + Y₂) = conn.nabla X Y₁ + conn.nabla X Y₂ := conn.nabla_add_right X Y₁ Y₂
  rw [h3]
  have h4 : T (conn.nabla X Y₁ + conn.nabla X Y₂) Z = T (conn.nabla X Y₁) Z + T (conn.nabla X Y₂) Z := T.add_left _ _ _
  rw [h4]
  have h5 : T (Y₁ + Y₂) (conn.nabla X Z) = T Y₁ (conn.nabla X Z) + T Y₂ (conn.nabla X Z) := T.add_left _ _ _
  rw [h5]
  ring

/-- Prove that the raw covariant derivative is linear with respect to scalar multiplication on the first vector field argument.
Input: (R, V, V)
Output: Prop -/
lemma rawCovDeriv_smul_left (a : R) (Y Z : V) :
  rawCovDeriv conn X T (a • Y) Z = a * rawCovDeriv conn X T Y Z := by
  dsimp [rawCovDeriv]
  have h1 : T (a • Y) Z = a * T Y Z := T.smul_left a Y Z
  rw [h1]
  have h2 : action X (a * T Y Z) = action X a * T Y Z + a * action X (T Y Z) := DerivationRules.action_smul_right X a _
  rw [h2]
  have h3 : conn.nabla X (a • Y) = (action X a) • Y + a • (conn.nabla X Y) := conn.leibniz a X Y
  rw [h3]
  have h4 : T ((action X a) • Y + a • (conn.nabla X Y)) Z = T ((action X a) • Y) Z + T (a • (conn.nabla X Y)) Z := T.add_left _ _ _
  rw [h4]
  have h5 : T ((action X a) • Y) Z = action X a * T Y Z := T.smul_left _ _ _
  have h6 : T (a • (conn.nabla X Y)) Z = a * T (conn.nabla X Y) Z := T.smul_left _ _ _
  rw [h5, h6]
  have h7 : T (a • Y) (conn.nabla X Z) = a * T Y (conn.nabla X Z) := T.smul_left _ _ _
  rw [h7]
  ring

/-- Prove that the raw covariant derivative is additive with respect to the second vector field argument.
Input: (V, V, V)
Output: Prop -/
lemma rawCovDeriv_add_right (Y Z₁ Z₂ : V) :
  rawCovDeriv conn X T Y (Z₁ + Z₂) = rawCovDeriv conn X T Y Z₁ + rawCovDeriv conn X T Y Z₂ := by
  dsimp [rawCovDeriv]
  have h1 : T Y (Z₁ + Z₂) = T Y Z₁ + T Y Z₂ := T.add_right _ _ _
  rw [h1]
  have h2 : action X (T Y Z₁ + T Y Z₂) = action X (T Y Z₁) + action X (T Y Z₂) := DerivationRules.action_add_right X _ _
  rw [h2]
  have h3 : conn.nabla X (Z₁ + Z₂) = conn.nabla X Z₁ + conn.nabla X Z₂ := conn.nabla_add_right X Z₁ Z₂
  rw [h3]
  have h4 : T Y (conn.nabla X Z₁ + conn.nabla X Z₂) = T Y (conn.nabla X Z₁) + T Y (conn.nabla X Z₂) := T.add_right _ _ _
  rw [h4]
  have h5 : T (conn.nabla X Y) (Z₁ + Z₂) = T (conn.nabla X Y) Z₁ + T (conn.nabla X Y) Z₂ := T.add_right _ _ _
  rw [h5]
  ring

/-- Prove that the raw covariant derivative is linear with respect to scalar multiplication on the second vector field argument.
Input: (R, V, V)
Output: Prop -/
lemma rawCovDeriv_smul_right (a : R) (Y Z : V) :
  rawCovDeriv conn X T Y (a • Z) = a * rawCovDeriv conn X T Y Z := by
  dsimp [rawCovDeriv]
  have h1 : T Y (a • Z) = a * T Y Z := T.smul_right a Y Z
  rw [h1]
  have h2 : action X (a * T Y Z) = action X a * T Y Z + a * action X (T Y Z) := DerivationRules.action_smul_right X a _
  rw [h2]
  have h3 : conn.nabla X (a • Z) = (action X a) • Z + a • (conn.nabla X Z) := conn.leibniz a X Z
  rw [h3]
  have h4 : T Y ((action X a) • Z + a • (conn.nabla X Z)) = T Y ((action X a) • Z) + T Y (a • (conn.nabla X Z)) := T.add_right _ _ _
  rw [h4]
  have h5 : T Y ((action X a) • Z) = action X a * T Y Z := T.smul_right _ _ _
  have h6 : T Y (a • (conn.nabla X Z)) = a * T Y (conn.nabla X Z) := T.smul_right _ _ _
  rw [h5, h6]
  have h7 : T (conn.nabla X Y) (a • Z) = a * T (conn.nabla X Y) Z := T.smul_right _ _ _
  rw [h7]
  ring

end Linearity

/-- Covariant derivative of a (0,2)-tensor as an operator returning a new SmoothBilinearForm.
Input: (AffineConnection R V, V, SmoothBilinearForm R V)
Output: SmoothBilinearForm R V -/
def covDerivOp (conn : AffineConnection R V) [DerivationRules R V] (X : V) (T : SmoothBilinearForm R V) : SmoothBilinearForm R V where
  val := rawCovDeriv conn X T
  add_left := rawCovDeriv_add_left conn X T
  smul_left := rawCovDeriv_smul_left conn X T
  add_right := rawCovDeriv_add_right conn X T
  smul_right := rawCovDeriv_smul_right conn X T

/-- Conversion from MetricTensor to SmoothBilinearForm.
Input: (MetricTensor R V)
Output: SmoothBilinearForm R V -/
def metricToForm (metric : MetricTensor R V) : SmoothBilinearForm R V where
  val := metric.g
  add_left := metric.bilinear_add_left
  smul_left := metric.bilinear_smul_left
  add_right X Y₁ Y₂ := by
    calc metric.g X (Y₁ + Y₂) = metric.g (Y₁ + Y₂) X := metric.symm _ _
      _ = metric.g Y₁ X + metric.g Y₂ X := metric.bilinear_add_left _ _ _
      _ = metric.g X Y₁ + metric.g X Y₂ := by rw [metric.symm Y₁ X, metric.symm Y₂ X]
  smul_right a X Y := by
    calc metric.g X (a • Y) = metric.g (a • Y) X := metric.symm _ _
      _ = a * metric.g Y X := metric.bilinear_smul_left _ _ _
      _ = a * metric.g X Y := by rw [metric.symm Y X]

variable (conn : AffineConnection R V) (metric : MetricTensor R V) [DerivationRules R V] [MetricCompatible conn metric]

/-- The covariant derivative of the metric tensor with respect to a compatible connection is zero.
Prove that applying the `covDerivOp` operator to `g` mathematically yields the exact 0 bilinear form.
Input: (V)
Output: Prop -/
theorem metric_covDerivOp_zero (X : V) :
  covDerivOp conn X (metricToForm metric) = (0 : SmoothBilinearForm R V) := by
  ext Y Z
  dsimp [covDerivOp, rawCovDeriv, metricToForm]
  have h := MetricCompatible.compat (conn:=conn) (metric:=metric) X Y Z
  calc action X (metric.g Y Z) - metric.g (conn.nabla X Y) Z - metric.g Y (conn.nabla X Z)
    _ = (metric.g (conn.nabla X Y) Z + metric.g Y (conn.nabla X Z)) - metric.g (conn.nabla X Y) Z - metric.g Y (conn.nabla X Z) := by rw [h]
    _ = 0 := by ring
