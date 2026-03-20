import DifferentialGeometry.Algebra.VectorField
import DifferentialGeometry.Algebra.BilinearForm
import DifferentialGeometry.Geometry.Connection
import DifferentialGeometry.Algebra.Metric
import DifferentialGeometry.Analysis.TensorCalculus
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open AbstractDerivationAction DifferentialGeometry.Bridge TensorAlgebra

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] [AbstractDerivationAction R V] [AbstractLieBracket V]

/-!
# Covariant Derivative of Tensors
Defines the covariant derivative of a (0,2)-tensor along a vector field.
-/

/-- Raw evaluation of the covariant derivative of a (0,2)-tensor T along a vector field X.
Input: (AbstractAffineConnection R V, V, AbstractBilinearForm R V, V, V)
Output: R -/
def rawCovDeriv (conn : AbstractAffineConnection R V) (X : V) (T : AbstractBilinearForm R V) (Y Z : V) : R :=
  action X (eval02 T Y Z) - eval02 T (conn.nabla X Y) Z - eval02 T Y (conn.nabla X Z)

section Linearity

variable (conn : AbstractAffineConnection R V) [DerivationRules R V] (X : V) (T : AbstractBilinearForm R V)

/-- Prove that the raw covariant derivative is additive with respect to the first vector field argument.
Input: (V, V, V)
Output: Prop -/
lemma rawCovDeriv_add_left (Y₁ Y₂ Z : V) :
  rawCovDeriv conn X T (Y₁ + Y₂) Z = rawCovDeriv conn X T Y₁ Z + rawCovDeriv conn X T Y₂ Z := by
  dsimp [rawCovDeriv]
  have h1 : eval02 T (Y₁ + Y₂) Z = eval02 T Y₁ Z + eval02 T Y₂ Z := eval02_add_left T Y₁ Y₂ Z
  rw [h1]
  have h2 : action X (eval02 T Y₁ Z + eval02 T Y₂ Z) = action X (eval02 T Y₁ Z) + action X (eval02 T Y₂ Z) := DerivationRules.action_add_right X _ _
  rw [h2]
  have h3 : conn.nabla X (Y₁ + Y₂) = conn.nabla X Y₁ + conn.nabla X Y₂ := conn.nabla_add_right X Y₁ Y₂
  rw [h3]
  have h4 : eval02 T (conn.nabla X Y₁ + conn.nabla X Y₂) Z = eval02 T (conn.nabla X Y₁) Z + eval02 T (conn.nabla X Y₂) Z := eval02_add_left T _ _ Z
  rw [h4]
  have h5 : eval02 T (Y₁ + Y₂) (conn.nabla X Z) = eval02 T Y₁ (conn.nabla X Z) + eval02 T Y₂ (conn.nabla X Z) := eval02_add_left T Y₁ Y₂ _
  rw [h5]
  ring

/-- Prove that the raw covariant derivative is linear with respect to scalar multiplication on the first vector field argument.
Input: (R, V, V)
Output: Prop -/
lemma rawCovDeriv_smul_left (a : R) (Y Z : V) :
  rawCovDeriv conn X T (a • Y) Z = a * rawCovDeriv conn X T Y Z := by
  dsimp [rawCovDeriv]
  have h1 : eval02 T (a • Y) Z = a * eval02 T Y Z := eval02_smul_left T a Y Z
  rw [h1]
  have h2 : action X (a * eval02 T Y Z) = action X a * eval02 T Y Z + a * action X (eval02 T Y Z) := DerivationRules.action_smul_right X a _
  rw [h2]
  have h3 : conn.nabla X (a • Y) = (action X a) • Y + a • (conn.nabla X Y) := conn.leibniz a X Y
  rw [h3]
  have h4 : eval02 T ((action X a) • Y + a • (conn.nabla X Y)) Z = eval02 T ((action X a) • Y) Z + eval02 T (a • (conn.nabla X Y)) Z := eval02_add_left T _ _ Z
  rw [h4]
  have h5 : eval02 T ((action X a) • Y) Z = action X a * eval02 T Y Z := eval02_smul_left T _ _ _
  have h6 : eval02 T (a • (conn.nabla X Y)) Z = a * eval02 T (conn.nabla X Y) Z := eval02_smul_left T _ _ _
  rw [h5, h6]
  have h7 : eval02 T (a • Y) (conn.nabla X Z) = a * eval02 T Y (conn.nabla X Z) := eval02_smul_left T _ _ _
  rw [h7]
  ring

/-- Prove that the raw covariant derivative is additive with respect to the second vector field argument.
Input: (V, V, V)
Output: Prop -/
lemma rawCovDeriv_add_right (Y Z₁ Z₂ : V) :
  rawCovDeriv conn X T Y (Z₁ + Z₂) = rawCovDeriv conn X T Y Z₁ + rawCovDeriv conn X T Y Z₂ := by
  dsimp [rawCovDeriv]
  have h1 : eval02 T Y (Z₁ + Z₂) = eval02 T Y Z₁ + eval02 T Y Z₂ := eval02_add_right T Y Z₁ Z₂
  rw [h1]
  have h2 : action X (eval02 T Y Z₁ + eval02 T Y Z₂) = action X (eval02 T Y Z₁) + action X (eval02 T Y Z₂) := DerivationRules.action_add_right X _ _
  rw [h2]
  have h3 : conn.nabla X (Z₁ + Z₂) = conn.nabla X Z₁ + conn.nabla X Z₂ := conn.nabla_add_right X Z₁ Z₂
  rw [h3]
  have h4 : eval02 T Y (conn.nabla X Z₁ + conn.nabla X Z₂) = eval02 T Y (conn.nabla X Z₁) + eval02 T Y (conn.nabla X Z₂) := eval02_add_right T Y _ _
  rw [h4]
  have h5 : eval02 T (conn.nabla X Y) (Z₁ + Z₂) = eval02 T (conn.nabla X Y) Z₁ + eval02 T (conn.nabla X Y) Z₂ := eval02_add_right T _ Z₁ Z₂
  rw [h5]
  ring

/-- Prove that the raw covariant derivative is linear with respect to scalar multiplication on the second vector field argument.
Input: (R, V, V)
Output: Prop -/
lemma rawCovDeriv_smul_right (a : R) (Y Z : V) :
  rawCovDeriv conn X T Y (a • Z) = a * rawCovDeriv conn X T Y Z := by
  dsimp [rawCovDeriv]
  have h1 : eval02 T Y (a • Z) = a * eval02 T Y Z := eval02_smul_right T a Y Z
  rw [h1]
  have h2 : action X (a * eval02 T Y Z) = action X a * eval02 T Y Z + a * action X (eval02 T Y Z) := DerivationRules.action_smul_right X a _
  rw [h2]
  have h3 : conn.nabla X (a • Z) = (action X a) • Z + a • (conn.nabla X Z) := conn.leibniz a X Z
  rw [h3]
  have h4 : eval02 T Y ((action X a) • Z + a • (conn.nabla X Z)) = eval02 T Y ((action X a) • Z) + eval02 T Y (a • (conn.nabla X Z)) := eval02_add_right T _ _ _
  rw [h4]
  have h5 : eval02 T Y ((action X a) • Z) = action X a * eval02 T Y Z := eval02_smul_right T _ _ _
  have h6 : eval02 T Y (a • (conn.nabla X Z)) = a * eval02 T Y (conn.nabla X Z) := eval02_smul_right T _ _ _
  rw [h5, h6]
  have h7 : eval02 T (conn.nabla X Y) (a • Z) = a * eval02 T (conn.nabla X Y) Z := eval02_smul_right T _ _ _
  rw [h7]
  ring

end Linearity

class BilinearFormExt (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] where
  ext : ∀ (T₁ T₂ : AbstractBilinearForm R V), (∀ Y Z, eval02 T₁ Y Z = eval02 T₂ Y Z) → T₁ = T₂

variable (conn : AbstractAffineConnection R V) [DerivationRules R V] [AffineTensorCalculus conn]

/-- Covariant derivative of a (0,2)-tensor as an operator returning a new AbstractBilinearForm.
Input: (AbstractAffineConnection R V, V, AbstractBilinearForm R V)
Output: AbstractBilinearForm R V -/
def covDerivOp (X : V) (T : AbstractBilinearForm R V) : AbstractBilinearForm R V :=
  AffineTensorCalculus.nabla_tensor conn X T

lemma covDeriv_eval (X : V) (T : AbstractBilinearForm R V) (Y Z : V) :
  eval02 (covDerivOp conn X T) Y Z = rawCovDeriv conn X T Y Z := by
  dsimp [covDerivOp, rawCovDeriv, eval02]
  have h_scalar : ∀ (A : AbstractTensor R V 2 2),
    toScalar (AffineTensorCalculus.nabla_tensor conn X (contract (r:=0) (s:=0) (contract (r:=1) (s:=1) A))) =
    action X (toScalar (contract (r:=0) (s:=0) (contract (r:=1) (s:=1) A))) := by
    intro A
    have h_S : contract (r:=0) (s:=0) (contract (r:=1) (s:=1) A) = fromScalar (toScalar (contract (r:=0) (s:=0) (contract (r:=1) (s:=1) A))) :=
      (TensorAlgebra.fromScalar_toScalar _).symm
    nth_rw 1 [h_S]
    rw [AffineTensorCalculus.nabla_scalar X]
    rw [TensorAlgebra.toScalar_fromScalar]
  have h1 : action X (toScalar (contract (r:=0) (s:=0) (contract (r:=1) (s:=1) (TensorAlgebra.tensor_prod (r1:=0) (s1:=2) (r2:=2) (s2:=0) T (TensorAlgebra.tensor_prod (r1:=1) (s1:=0) (r2:=1) (s2:=0) (fromVector Y) (fromVector Z)))))) =
    toScalar (AffineTensorCalculus.nabla_tensor conn X (contract (r:=0) (s:=0) (contract (r:=1) (s:=1) (TensorAlgebra.tensor_prod (r1:=0) (s1:=2) (r2:=2) (s2:=0) T (TensorAlgebra.tensor_prod (r1:=1) (s1:=0) (r2:=1) (s2:=0) (fromVector Y) (fromVector Z)))))) :=
    (h_scalar _).symm
  have h2 : AffineTensorCalculus.nabla_tensor conn X (contract (r:=0) (s:=0) (contract (r:=1) (s:=1) (TensorAlgebra.tensor_prod (r1:=0) (s1:=2) (r2:=2) (s2:=0) T (TensorAlgebra.tensor_prod (r1:=1) (s1:=0) (r2:=1) (s2:=0) (fromVector Y) (fromVector Z))))) =
    contract (r:=0) (s:=0) (contract (r:=1) (s:=1) (AffineTensorCalculus.nabla_tensor conn X (TensorAlgebra.tensor_prod (r1:=0) (s1:=2) (r2:=2) (s2:=0) T (TensorAlgebra.tensor_prod (r1:=1) (s1:=0) (r2:=1) (s2:=0) (fromVector Y) (fromVector Z))))) := by
    rw [AffineTensorCalculus.nabla_contract X, AffineTensorCalculus.nabla_contract X]
  have h3 : AffineTensorCalculus.nabla_tensor conn X (TensorAlgebra.tensor_prod (r1:=0) (s1:=2) (r2:=2) (s2:=0) T (TensorAlgebra.tensor_prod (r1:=1) (s1:=0) (r2:=1) (s2:=0) (fromVector Y) (fromVector Z))) =
    TensorAlgebra.add (TensorAlgebra.tensor_prod (r1:=0) (s1:=2) (r2:=2) (s2:=0) (AffineTensorCalculus.nabla_tensor conn X T) (TensorAlgebra.tensor_prod (r1:=1) (s1:=0) (r2:=1) (s2:=0) (fromVector Y) (fromVector Z)))
      (TensorAlgebra.tensor_prod (r1:=0) (s1:=2) (r2:=2) (s2:=0) T (AffineTensorCalculus.nabla_tensor conn X (TensorAlgebra.tensor_prod (r1:=1) (s1:=0) (r2:=1) (s2:=0) (fromVector Y) (fromVector Z)))) := by
    rw [AffineTensorCalculus.nabla_tensor_prod X]
  have h4 : AffineTensorCalculus.nabla_tensor conn X (TensorAlgebra.tensor_prod (r1:=1) (s1:=0) (r2:=1) (s2:=0) (fromVector Y) (fromVector Z)) =
    TensorAlgebra.add (TensorAlgebra.tensor_prod (r1:=1) (s1:=0) (r2:=1) (s2:=0) (AffineTensorCalculus.nabla_tensor conn X (fromVector Y)) (fromVector Z))
      (TensorAlgebra.tensor_prod (r1:=1) (s1:=0) (r2:=1) (s2:=0) (fromVector Y) (AffineTensorCalculus.nabla_tensor conn X (fromVector Z))) := by
    rw [AffineTensorCalculus.nabla_tensor_prod X]
  have h5 : AffineTensorCalculus.nabla_tensor conn X (fromVector Y) = fromVector (conn.nabla X Y) := AffineTensorCalculus.nabla_vector X Y
  have h6 : AffineTensorCalculus.nabla_tensor conn X (fromVector Z) = fromVector (conn.nabla X Z) := AffineTensorCalculus.nabla_vector X Z
  rw [h5, h6] at h4
  rw [h4] at h3
  rw [TensorAlgebra.tensor_prod_add_right] at h3
  rw [h3] at h2
  rw [TensorAlgebra.contract_add, TensorAlgebra.contract_add] at h2
  rw [TensorAlgebra.contract_add, TensorAlgebra.contract_add] at h2
  rw [h2] at h1
  rw [TensorAlgebra.toScalar_add, TensorAlgebra.toScalar_add] at h1
  have he1 : toScalar (contract (r:=0) (s:=0) (contract (r:=1) (s:=1) (TensorAlgebra.tensor_prod (r1:=0) (s1:=2) (r2:=2) (s2:=0) T (TensorAlgebra.tensor_prod (r1:=1) (s1:=0) (r2:=1) (s2:=0) (fromVector Y) (fromVector Z))))) = eval02 T Y Z := rfl
  have he2 : toScalar (contract (r:=0) (s:=0) (contract (r:=1) (s:=1) (TensorAlgebra.tensor_prod (r1:=0) (s1:=2) (r2:=2) (s2:=0) (AffineTensorCalculus.nabla_tensor conn X T) (TensorAlgebra.tensor_prod (r1:=1) (s1:=0) (r2:=1) (s2:=0) (fromVector Y) (fromVector Z))))) = eval02 (AffineTensorCalculus.nabla_tensor conn X T) Y Z := rfl
  have he3 : toScalar (contract (r:=0) (s:=0) (contract (r:=1) (s:=1) (TensorAlgebra.tensor_prod (r1:=0) (s1:=2) (r2:=2) (s2:=0) T (TensorAlgebra.tensor_prod (r1:=1) (s1:=0) (r2:=1) (s2:=0) (fromVector (conn.nabla X Y)) (fromVector Z))))) = eval02 T (conn.nabla X Y) Z := rfl
  have he4 : toScalar (contract (r:=0) (s:=0) (contract (r:=1) (s:=1) (TensorAlgebra.tensor_prod (r1:=0) (s1:=2) (r2:=2) (s2:=0) T (TensorAlgebra.tensor_prod (r1:=1) (s1:=0) (r2:=1) (s2:=0) (fromVector Y) (fromVector (conn.nabla X Z)))))) = eval02 T Y (conn.nabla X Z) := rfl
  rw [he1, he2, he3, he4] at h1
  calc eval02 (AffineTensorCalculus.nabla_tensor conn X T) Y Z
    _ = action X (eval02 T Y Z) - eval02 T (conn.nabla X Y) Z - eval02 T Y (conn.nabla X Z) := by
      rw [h1]; ring

/-- Conversion from AbstractMetricTensor to AbstractBilinearForm.
Input: (AbstractMetricTensor R V)
Output: AbstractBilinearForm R V -/
def metricToForm (metric : AbstractMetricTensor R V) : AbstractBilinearForm R V :=
  metric.g_tensor

variable (conn : AbstractAffineConnection R V) (metric : AbstractMetricTensor R V) [DerivationRules R V] [MetricCompatible conn metric] [AffineTensorCalculus conn] [BilinearFormExt R V]

/-- The covariant derivative of the metric tensor with respect to a compatible connection is zero.
Prove that applying the `covDerivOp` operator to `g` mathematically yields the exact 0 bilinear form.
Input: (V)
Output: Prop -/
theorem metric_covDerivOp_zero (X : V) :
  covDerivOp conn X (metricToForm metric) = 0 := by
  dsimp [covDerivOp]
  apply BilinearFormExt.ext (covDerivOp conn X (metricToForm metric)) 0
  intro Y Z
  have h_eval : eval02 (covDerivOp conn X (metricToForm metric)) Y Z = rawCovDeriv conn X (metricToForm metric) Y Z := covDeriv_eval conn X (metricToForm metric) Y Z
  rw [h_eval]
  dsimp [rawCovDeriv, metricToForm]
  have heval_Y_Z : eval02 metric.g_tensor Y Z = metric.g Y Z := rfl
  have heval_nabla_Z : eval02 metric.g_tensor (conn.nabla X Y) Z = metric.g (conn.nabla X Y) Z := rfl
  have heval_Y_nabla : eval02 metric.g_tensor Y (conn.nabla X Z) = metric.g Y (conn.nabla X Z) := rfl
  rw [heval_Y_Z, heval_nabla_Z, heval_Y_nabla]
  have h := MetricCompatible.compat (conn:=conn) (metric:=metric) X Y Z
  have r0 : eval02 (0 : AbstractBilinearForm R V) Y Z = 0 := by
    have hc : fromCovector (0 : V →ₗ[R] R) = TensorAlgebra.smul (0:R) (fromCovector (0 : V →ₗ[R] R)) := by
      have hA : (0 : V →ₗ[R] R) = (0:R) • (0 : V →ₗ[R] R) := (zero_smul R (0 : V →ₗ[R] R)).symm
      conv => lhs; rw [hA]
      exact TensorAlgebra.fromCovector_smul (R:=R) (V:=V) 0 0
    have hP : (zero_tensor 0 2 : AbstractTensor R V 0 2) = TensorAlgebra.smul (0:R) (zero_tensor 0 2 : AbstractTensor R V 0 2) := by
      have ht : (zero_tensor 0 2 : AbstractTensor R V 0 2) = TensorAlgebra.tensor_prod (r1:=0) (s1:=1) (r2:=0) (s2:=1) (zero_tensor 0 1 : AbstractTensor R V 0 1) (fromCovector (0 : V →ₗ[R] R)) := zero_tensor_0_2_step
      calc (zero_tensor 0 2 : AbstractTensor R V 0 2)
         _ = TensorAlgebra.tensor_prod (r1:=0) (s1:=1) (r2:=0) (s2:=1) (zero_tensor 0 1 : AbstractTensor R V 0 1) (fromCovector (0 : V →ₗ[R] R)) := ht
         _ = TensorAlgebra.tensor_prod (zero_tensor 0 1 : AbstractTensor R V 0 1) (TensorAlgebra.smul (0:R) (fromCovector (0 : V →ₗ[R] R))) := by congr 1
         _ = TensorAlgebra.smul (0:R) (TensorAlgebra.tensor_prod (zero_tensor 0 1 : AbstractTensor R V 0 1) (fromCovector (0 : V →ₗ[R] R))) := TensorAlgebra.tensor_prod_smul_right (R:=R) (V:=V) 0 _ _
         _ = TensorAlgebra.smul (0:R) (zero_tensor 0 2 : AbstractTensor R V 0 2) := by rw [← ht]
    have hT : (0 : AbstractBilinearForm R V) = (0:R) • (0 : AbstractBilinearForm R V) := hP
    calc eval02 (0 : AbstractBilinearForm R V) Y Z
       _ = eval02 ((0:R) • (0 : AbstractBilinearForm R V)) Y Z := by nth_rw 1 [hT]
       _ = (0:R) * eval02 (0:AbstractBilinearForm R V) Y Z := eval02_smul (0 : AbstractBilinearForm R V) 0 Y Z
       _ = 0 := MulZeroClass.zero_mul _
  calc action X (metric.g Y Z) - metric.g (conn.nabla X Y) Z - metric.g Y (conn.nabla X Z)
    _ = (metric.g (conn.nabla X Y) Z + metric.g Y (conn.nabla X Z)) - metric.g (conn.nabla X Y) Z - metric.g Y (conn.nabla X Z) := by rw [h]
    _ = 0 := by ring
    _ = eval02 0 Y Z := r0.symm
