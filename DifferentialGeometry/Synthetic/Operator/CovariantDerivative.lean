import DifferentialGeometry.Synthetic.Algebra.VectorField
import DifferentialGeometry.Synthetic.Algebra.BilinearForm
import DifferentialGeometry.Synthetic.Geometry.Connection
import DifferentialGeometry.Synthetic.Algebra.Metric
import DifferentialGeometry.Synthetic.Analysis.TensorCalculus
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

open AbstractDerivationAction DifferentialGeometry TensorAlgebra

variable {R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] [AbstractDerivationAction R V] [AbstractLieBracket V]

/-!
# Covariant Derivative of Tensors
Defines the covariant derivative of a (0,2)-tensor along a vector field.
-/

/-- Raw evaluation of the covariant derivative of a (0,2)-tensor T along a vector field X.
Input: (AbstractAffineConnection R V, V, AbstractBilinearForm R V, V, V)
Output: R -/
def rawCovDeriv (conn : AbstractAffineConnection R V) (X : V) (T : AbstractBilinearForm R V) (Y Z : V) : R :=
  action X (tensor_eval T ![Y, Z] ![]) - tensor_eval T ![(conn.nabla X Y), Z] ![] - tensor_eval T ![Y, (conn.nabla X Z)] ![]

section Linearity

variable (conn : AbstractAffineConnection R V) [DerivationRules R V] (X : V) (T : AbstractBilinearForm R V)

/-- Prove that the raw covariant derivative is additive with respect to the first vector field argument.
Input: (V, V, V)
Output: Prop -/
lemma rawCovDeriv_add_left (Y₁ Y₂ Z : V) :
  rawCovDeriv conn X T (Y₁ + Y₂) Z = rawCovDeriv conn X T Y₁ Z + rawCovDeriv conn X T Y₂ Z := by
  dsimp [rawCovDeriv]
  have h1 : tensor_eval T ![(Y₁ + Y₂), Z] ![] = tensor_eval T ![Y₁, Z] ![] + tensor_eval T ![Y₂, Z] ![] := tensor_eval_add_left T Y₁ Y₂ Z
  rw [h1]
  have h2 : action X (tensor_eval T ![Y₁, Z] ![] + tensor_eval T ![Y₂, Z] ![]) = action X (tensor_eval T ![Y₁, Z] ![]) + action X (tensor_eval T ![Y₂, Z] ![]) := DerivationRules.action_add_right X _ _
  rw [h2]
  have h3 : conn.nabla X (Y₁ + Y₂) = conn.nabla X Y₁ + conn.nabla X Y₂ := conn.nabla_add_right X Y₁ Y₂
  rw [h3]
  have h4 : tensor_eval T ![(conn.nabla X Y₁ + conn.nabla X Y₂), Z] ![] = tensor_eval T ![(conn.nabla X Y₁), Z] ![] + tensor_eval T ![(conn.nabla X Y₂), Z] ![] := tensor_eval_add_left T _ _ Z
  rw [h4]
  have h5 : tensor_eval T ![(Y₁ + Y₂), (conn.nabla X Z)] ![] = tensor_eval T ![Y₁, (conn.nabla X Z)] ![] + tensor_eval T ![Y₂, (conn.nabla X Z)] ![] := tensor_eval_add_left T Y₁ Y₂ _
  rw [h5]
  ring

/-- Prove that the raw covariant derivative is linear with respect to scalar multiplication on the first vector field argument.
Input: (R, V, V)
Output: Prop -/
lemma rawCovDeriv_smul_left (a : R) (Y Z : V) :
  rawCovDeriv conn X T (a • Y) Z = a * rawCovDeriv conn X T Y Z := by
  dsimp [rawCovDeriv]
  have h1 : tensor_eval T ![(a • Y), Z] ![] = a * tensor_eval T ![Y, Z] ![] := tensor_eval_smul_left T a Y Z
  rw [h1]
  have h2 : action X (a * tensor_eval T ![Y, Z] ![]) = action X a * tensor_eval T ![Y, Z] ![] + a * action X (tensor_eval T ![Y, Z] ![]) := DerivationRules.action_smul_right X a _
  rw [h2]
  have h3 : conn.nabla X (a • Y) = (action X a) • Y + a • (conn.nabla X Y) := conn.leibniz a X Y
  rw [h3]
  have h4 : tensor_eval T ![((action X a) • Y + a • (conn.nabla X Y)), Z] ![] = tensor_eval T ![((action X a) • Y), Z] ![] + tensor_eval T ![(a • (conn.nabla X Y)), Z] ![] := tensor_eval_add_left T _ _ Z
  rw [h4]
  have h5 : tensor_eval T ![((action X a) • Y), Z] ![] = action X a * tensor_eval T ![Y, Z] ![] := tensor_eval_smul_left T _ _ _
  have h6 : tensor_eval T ![(a • (conn.nabla X Y)), Z] ![] = a * tensor_eval T ![(conn.nabla X Y), Z] ![] := tensor_eval_smul_left T _ _ _
  rw [h5, h6]
  have h7 : tensor_eval T ![(a • Y), (conn.nabla X Z)] ![] = a * tensor_eval T ![Y, (conn.nabla X Z)] ![] := tensor_eval_smul_left T _ _ _
  rw [h7]
  ring

/-- Prove that the raw covariant derivative is additive with respect to the second vector field argument.
Input: (V, V, V)
Output: Prop -/
lemma rawCovDeriv_add_right (Y Z₁ Z₂ : V) :
  rawCovDeriv conn X T Y (Z₁ + Z₂) = rawCovDeriv conn X T Y Z₁ + rawCovDeriv conn X T Y Z₂ := by
  dsimp [rawCovDeriv]
  have h1 : tensor_eval T ![Y, (Z₁ + Z₂)] ![] = tensor_eval T ![Y, Z₁] ![] + tensor_eval T ![Y, Z₂] ![] := tensor_eval_add_right T Y Z₁ Z₂
  rw [h1]
  have h2 : action X (tensor_eval T ![Y, Z₁] ![] + tensor_eval T ![Y, Z₂] ![]) = action X (tensor_eval T ![Y, Z₁] ![]) + action X (tensor_eval T ![Y, Z₂] ![]) := DerivationRules.action_add_right X _ _
  rw [h2]
  have h3 : conn.nabla X (Z₁ + Z₂) = conn.nabla X Z₁ + conn.nabla X Z₂ := conn.nabla_add_right X Z₁ Z₂
  rw [h3]
  have h4 : tensor_eval T ![Y, (conn.nabla X Z₁ + conn.nabla X Z₂)] ![] = tensor_eval T ![Y, (conn.nabla X Z₁)] ![] + tensor_eval T ![Y, (conn.nabla X Z₂)] ![] := tensor_eval_add_right T Y _ _
  rw [h4]
  have h5 : tensor_eval T ![(conn.nabla X Y), (Z₁ + Z₂)] ![] = tensor_eval T ![(conn.nabla X Y), Z₁] ![] + tensor_eval T ![(conn.nabla X Y), Z₂] ![] := tensor_eval_add_right T _ Z₁ Z₂
  rw [h5]
  ring

/-- Prove that the raw covariant derivative is linear with respect to scalar multiplication on the second vector field argument.
Input: (R, V, V)
Output: Prop -/
lemma rawCovDeriv_smul_right (a : R) (Y Z : V) :
  rawCovDeriv conn X T Y (a • Z) = a * rawCovDeriv conn X T Y Z := by
  dsimp [rawCovDeriv]
  have h1 : tensor_eval T ![Y, (a • Z)] ![] = a * tensor_eval T ![Y, Z] ![] := tensor_eval_smul_right T a Y Z
  rw [h1]
  have h2 : action X (a * tensor_eval T ![Y, Z] ![]) = action X a * tensor_eval T ![Y, Z] ![] + a * action X (tensor_eval T ![Y, Z] ![]) := DerivationRules.action_smul_right X a _
  rw [h2]
  have h3 : conn.nabla X (a • Z) = (action X a) • Z + a • (conn.nabla X Z) := conn.leibniz a X Z
  rw [h3]
  have h4 : tensor_eval T ![Y, ((action X a) • Z + a • (conn.nabla X Z))] ![] = tensor_eval T ![Y, ((action X a) • Z)] ![] + tensor_eval T ![Y, (a • (conn.nabla X Z))] ![] := tensor_eval_add_right T _ _ _
  rw [h4]
  have h5 : tensor_eval T ![Y, ((action X a) • Z)] ![] = action X a * tensor_eval T ![Y, Z] ![] := tensor_eval_smul_right T _ _ _
  have h6 : tensor_eval T ![Y, (a • (conn.nabla X Z))] ![] = a * tensor_eval T ![Y, (conn.nabla X Z)] ![] := tensor_eval_smul_right T _ _ _
  rw [h5, h6]
  have h7 : tensor_eval T ![(conn.nabla X Y), (a • Z)] ![] = a * tensor_eval T ![(conn.nabla X Y), Z] ![] := tensor_eval_smul_right T _ _ _
  rw [h7]
  ring

end Linearity

class BilinearFormExt (R V : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] where
  ext : ∀ (T₁ T₂ : AbstractBilinearForm R V), (∀ Y Z, tensor_eval T₁ ![Y, Z] ![] = tensor_eval T₂ ![Y, Z] ![]) → T₁ = T₂

variable (conn : AbstractAffineConnection R V) [DerivationRules R V] [AffineTensorCalculus conn]

/-- Covariant derivative of a (0,2)-tensor as an operator returning a new AbstractBilinearForm.
Input: (AbstractAffineConnection R V, V, AbstractBilinearForm R V)
Output: AbstractBilinearForm R V -/
def covDerivOp (X : V) (T : AbstractBilinearForm R V) : AbstractBilinearForm R V :=
  AffineTensorCalculus.nabla_tensor conn X T

lemma covDeriv_eval (X : V) (T : AbstractBilinearForm R V) (Y Z : V) :
  tensor_eval (covDerivOp conn X T) ![Y, Z] ![] = rawCovDeriv conn X T Y Z := by
  dsimp [covDerivOp, rawCovDeriv]
  have h_scalar : ∀ (A : AbstractTensor R V 2 2),
    ((TensorAlgebra.toData (AffineTensorCalculus.nabla_tensor conn X (contract (r:=0) (s:=0) (contract (r:=1) (s:=1) A)))) ![]) ![] =
    action X (((TensorAlgebra.toData (contract (r:=0) (s:=0) (contract (r:=1) (s:=1) A))) ![]) ![]) := by
    intro A
    have h_S : contract (r:=0) (s:=0) (contract (r:=1) (s:=1) A) = TensorAlgebra.fromData (scalarToData (((TensorAlgebra.toData (contract (r:=0) (s:=0) (contract (r:=1) (s:=1) A))) ![]) ![])) := by
      have h1 : TensorAlgebra.toData (contract (r:=0) (s:=0) (contract (r:=1) (s:=1) A)) = scalarToData (((TensorAlgebra.toData (contract (r:=0) (s:=0) (contract (r:=1) (s:=1) A))) ![]) ![]) := by
        ext m n
        dsimp [scalarToData, MultilinearMap.constOfIsEmpty]
        have hm : m = ![] := Subsingleton.elim _ _
        have hn : n = ![] := Subsingleton.elim _ _
        rw [hm, hn]
      rw [← h1]
      exact (TensorAlgebra.fromData_toData _).symm
    have h_rw : AffineTensorCalculus.nabla_tensor conn X (contract (r:=0) (s:=0) (contract (r:=1) (s:=1) A)) = AffineTensorCalculus.nabla_tensor conn X (TensorAlgebra.fromData (scalarToData (((TensorAlgebra.toData (contract (r:=0) (s:=0) (contract (r:=1) (s:=1) A))) ![]) ![]))) := congr_arg (AffineTensorCalculus.nabla_tensor conn X) h_S
    rw [h_rw]
    rw [AffineTensorCalculus.nabla_scalar X]
    rw [TensorAlgebra.toData_fromData]
    rfl
  let P_YZ := TensorAlgebra.tensor_prod (R:=R) (r1:=1) (s1:=0) (r2:=1) (s2:=0) (fromVector (R:=R) Z) (fromVector (R:=R) Y)
  let P_nYZ := TensorAlgebra.tensor_prod (R:=R) (r1:=1) (s1:=0) (r2:=1) (s2:=0) (fromVector (R:=R) Z) (fromVector (R:=R) (conn.nabla X Y))
  let P_YnZ := TensorAlgebra.tensor_prod (R:=R) (r1:=1) (s1:=0) (r2:=1) (s2:=0) (fromVector (R:=R) (conn.nabla X Z)) (fromVector (R:=R) Y)
  let TYZ := TensorAlgebra.tensor_prod (R:=R) (r1:=0) (s1:=2) (r2:=2) (s2:=0) T P_YZ
  let nTYZ := TensorAlgebra.tensor_prod (R:=R) (r1:=0) (s1:=2) (r2:=2) (s2:=0) (AffineTensorCalculus.nabla_tensor conn X T) P_YZ
  let TnYZ := TensorAlgebra.tensor_prod (R:=R) (r1:=0) (s1:=2) (r2:=2) (s2:=0) T P_nYZ
  let TYnZ := TensorAlgebra.tensor_prod (R:=R) (r1:=0) (s1:=2) (r2:=2) (s2:=0) T P_YnZ
  let CTYZ := contract (R:=R) (r:=0) (s:=0) (contract (R:=R) (r:=1) (s:=1) TYZ)
  let CnTYZ := contract (R:=R) (r:=0) (s:=0) (contract (R:=R) (r:=1) (s:=1) nTYZ)
  let CTnYZ := contract (R:=R) (r:=0) (s:=0) (contract (R:=R) (r:=1) (s:=1) TnYZ)
  let CTYnZ := contract (R:=R) (r:=0) (s:=0) (contract (R:=R) (r:=1) (s:=1) TYnZ)
  
  have h1 : action X (((TensorAlgebra.toData CTYZ) ![]) ![]) = ((TensorAlgebra.toData (AffineTensorCalculus.nabla_tensor conn X CTYZ)) ![]) ![] :=
    (h_scalar _).symm
  have h2 : AffineTensorCalculus.nabla_tensor conn X CTYZ = contract (R:=R) (r:=0) (s:=0) (contract (R:=R) (r:=1) (s:=1) (AffineTensorCalculus.nabla_tensor conn X TYZ)) := by
    dsimp [CTYZ]
    rw [AffineTensorCalculus.nabla_contract X, AffineTensorCalculus.nabla_contract X]
  have h3 : AffineTensorCalculus.nabla_tensor conn X TYZ = TensorAlgebra.add (R:=R) nTYZ (TensorAlgebra.tensor_prod (R:=R) (r1:=0) (s1:=2) (r2:=2) (s2:=0) T (AffineTensorCalculus.nabla_tensor conn X P_YZ)) := by
    dsimp [TYZ, nTYZ]
    rw [AffineTensorCalculus.nabla_tensor_prod (R:=R) X]
  have h4 : AffineTensorCalculus.nabla_tensor conn X P_YZ = TensorAlgebra.add (R:=R) P_nYZ P_YnZ := by
    dsimp [P_YZ, P_nYZ, P_YnZ]
    rw [AffineTensorCalculus.nabla_tensor_prod (R:=R) X]
    have h5 : AffineTensorCalculus.nabla_tensor conn X (fromVector (R:=R) Y) = fromVector (R:=R) (conn.nabla X Y) := by
      have hy : fromVector (R:=R) Y = TensorAlgebra.fromData (vectorToData Y) := rfl
      rw [hy, AffineTensorCalculus.nabla_vector (R:=R) X Y]; rfl
    have h6 : AffineTensorCalculus.nabla_tensor conn X (fromVector (R:=R) Z) = fromVector (R:=R) (conn.nabla X Z) := by
      have hz : fromVector (R:=R) Z = TensorAlgebra.fromData (vectorToData Z) := rfl
      rw [hz, AffineTensorCalculus.nabla_vector (R:=R) X Z]; rfl
    rw [h5, h6]
    -- nabla_tensor_prod gives add P_YnZ P_nYZ, but we need add P_nYZ P_YnZ
    -- Prove commutativity via toData
    have hadd_comm : TensorAlgebra.add P_YnZ P_nYZ = TensorAlgebra.add P_nYZ P_YnZ := by
      have h := TensorAlgebra.fromData_toData (TensorAlgebra.add P_YnZ P_nYZ)
      rw [TensorAlgebra.toData_add] at h
      have h' := TensorAlgebra.fromData_toData (TensorAlgebra.add P_nYZ P_YnZ)
      rw [TensorAlgebra.toData_add] at h'
      rw [← h, ← h']
      congr 1
      exact add_comm (TensorAlgebra.toData P_YnZ) (TensorAlgebra.toData P_nYZ)
    exact hadd_comm
  have h7 : TensorAlgebra.tensor_prod (R:=R) (r1:=0) (s1:=2) (r2:=2) (s2:=0) T (AffineTensorCalculus.nabla_tensor conn X P_YZ) = TensorAlgebra.add (R:=R) TnYZ TYnZ := by
    rw [h4]
    dsimp [TnYZ, TYnZ]
    rw [TensorAlgebra.tensor_prod_add_right (R:=R)]
  rw [h7] at h3
  have h8 : AffineTensorCalculus.nabla_tensor conn X CTYZ = TensorAlgebra.add (R:=R) CnTYZ (TensorAlgebra.add (R:=R) CTnYZ CTYnZ) := by
    rw [h2, h3]
    dsimp [CnTYZ, CTnYZ, CTYnZ]
    rw [TensorAlgebra.contract_add (R:=R), TensorAlgebra.contract_add (R:=R)]
    rw [TensorAlgebra.contract_add (R:=R), TensorAlgebra.contract_add (R:=R)]

  have he1 : ((TensorAlgebra.toData CTYZ) ![]) ![] = tensor_eval T ![Y, Z] ![] := (tensor_eval_isomorphism T Y Z).symm
  have he2 : ((TensorAlgebra.toData CnTYZ) ![]) ![] = tensor_eval (AffineTensorCalculus.nabla_tensor conn X T) ![Y, Z] ![] := (tensor_eval_isomorphism _ Y Z).symm
  have he3 : ((TensorAlgebra.toData CTnYZ) ![]) ![] = tensor_eval T ![(conn.nabla X Y), Z] ![] := (tensor_eval_isomorphism T _ Z).symm
  have he4 : ((TensorAlgebra.toData CTYnZ) ![]) ![] = tensor_eval T ![Y, (conn.nabla X Z)] ![] := (tensor_eval_isomorphism T Y _).symm

  have h_final : action X (tensor_eval T ![Y, Z] ![]) = tensor_eval (AffineTensorCalculus.nabla_tensor conn X T) ![Y, Z] ![] + tensor_eval T ![(conn.nabla X Y), Z] ![] + tensor_eval T ![Y, (conn.nabla X Z)] ![] := by
    rw [← he1, ← he2, ← he3, ← he4]
    rw [h1]
    rw [h8]
    erw [TensorAlgebra.toData_add, TensorAlgebra.toData_add]
    simp only [MultilinearMap.add_apply]
    ring
  rw [h_final]
  ring

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
  have h_eval : tensor_eval (covDerivOp conn X (metricToForm metric)) ![Y, Z] ![] = rawCovDeriv conn X (metricToForm metric) Y Z := covDeriv_eval conn X (metricToForm metric) Y Z
  rw [h_eval]
  dsimp [rawCovDeriv, metricToForm]
  have heval_Y_Z : tensor_eval metric.g_tensor ![Y, Z] ![] = metric.g Y Z := rfl
  have heval_nabla_Z : tensor_eval metric.g_tensor ![(conn.nabla X Y), Z] ![] = metric.g (conn.nabla X Y) Z := rfl
  have heval_Y_nabla : tensor_eval metric.g_tensor ![Y, (conn.nabla X Z)] ![] = metric.g Y (conn.nabla X Z) := rfl
  rw [heval_Y_Z, heval_nabla_Z, heval_Y_nabla]
  have h := MetricCompatible.compat (conn:=conn) (metric:=metric) X Y Z
  have r0 : tensor_eval (0 : AbstractBilinearForm R V) ![Y, Z] ![] = 0 := tensor_eval_zero Y Z
  calc action X (metric.g Y Z) - metric.g (conn.nabla X Y) Z - metric.g Y (conn.nabla X Z)
    _ = (metric.g (conn.nabla X Y) Z + metric.g Y (conn.nabla X Z)) - metric.g (conn.nabla X Y) Z - metric.g Y (conn.nabla X Z) := by rw [h]
    _ = 0 := by ring
    _ = tensor_eval 0 ![Y, Z] ![] := r0.symm

section GenericCovDeriv

/--
Universal covariant derivative of a tensor of rank (r, s),
mapping a vector field X and a tensor T to a tensor of the same rank.
-/
def genericCovDeriv {R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] [AbstractDerivationAction R V]
  (conn : AbstractAffineConnection R V) [AffineTensorCalculus conn]
  (X : V) {r s : ℕ} (T : AbstractTensor R V r s) : AbstractTensor R V r s :=
  AffineTensorCalculus.nabla_tensor conn X T

variable {R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] [AbstractDerivationAction R V]
  {conn : AbstractAffineConnection R V} [AffineTensorCalculus conn]

lemma genericCovDeriv_add (X : V) {r s : ℕ} (T1 T2 : AbstractTensor R V r s) :
  genericCovDeriv conn X (TensorAlgebra.add T1 T2) = TensorAlgebra.add (genericCovDeriv conn X T1) (genericCovDeriv conn X T2) := by
  dsimp [genericCovDeriv]
  rw [AffineTensorCalculus.nabla_add X T1 T2]

lemma genericCovDeriv_smul (X : V) (c : R) {r s : ℕ} (T : AbstractTensor R V r s) :
  genericCovDeriv conn X (TensorAlgebra.smul c T) = TensorAlgebra.add (TensorAlgebra.smul (AbstractDerivationAction.action X c) T) (TensorAlgebra.smul c (genericCovDeriv conn X T)) := by
  dsimp [genericCovDeriv]
  rw [AffineTensorCalculus.nabla_smul X c T]

lemma genericCovDeriv_tensor_prod (X : V) {r1 s1 r2 s2 : ℕ} (T1 : AbstractTensor R V r1 s1) (T2 : AbstractTensor R V r2 s2) :
  genericCovDeriv conn X (TensorAlgebra.tensor_prod T1 T2) = 
    TensorAlgebra.add (TensorAlgebra.tensor_prod (genericCovDeriv conn X T1) T2) (TensorAlgebra.tensor_prod T1 (genericCovDeriv conn X T2)) := by
  dsimp [genericCovDeriv]
  rw [AffineTensorCalculus.nabla_tensor_prod X T1 T2]

lemma genericCovDeriv_contract (X : V) {r s : ℕ} (T : AbstractTensor R V (r + 1) (s + 1)) :
  genericCovDeriv conn X (TensorAlgebra.contract T) = TensorAlgebra.contract (genericCovDeriv conn X T) := by
  dsimp [genericCovDeriv]
  rw [AffineTensorCalculus.nabla_contract X T]

end GenericCovDeriv

