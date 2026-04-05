import DifferentialGeometry.Bridge.Defs
import DifferentialGeometry.Algebra.VectorField
import DifferentialGeometry.Geometry.Connection

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

open DifferentialGeometry.Bridge
open TensorAlgebra
open AbstractDerivationAction

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
variable [TensorAlgebra R V] [AbstractDerivationAction R V]

def scalarToData (f : R) : TensorData R V 0 0 :=
  MultilinearMap.constOfIsEmpty R (fun _ : Fin 0 => V)
    (MultilinearMap.constOfIsEmpty R (fun _ : Fin 0 => (V →ₗ[R] R)) f)

def evalLinear (v : V) : (V →ₗ[R] R) →ₗ[R] R where
  toFun w := w v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def vectorToData (v : V) : TensorData R V 1 0 :=
  MultilinearMap.constOfIsEmpty R (fun _ : Fin 0 => V)
    (MultilinearMap.ofSubsingleton R (V →ₗ[R] R) R (0 : Fin 1) (evalLinear v))

/--
Layer 2: Affine Tensor Calculus
Extends an affine connection to the entire tensor algebra by defining a universal covariant derivative operator.
-/
class AffineTensorCalculus (conn : AbstractAffineConnection R V) where
  /-- The universal covariant derivative operator acting on any (r,s) tensor -/
  nabla_tensor (X : V) {r s : ℕ} : AbstractTensor R V r s → AbstractTensor R V r s

  /-- Axiom 1: Degenerates to directional derivative on scalars (0-0 tensors) -/
  nabla_scalar : ∀ (X : V) (f : R),
    nabla_tensor X (TensorAlgebra.fromData (scalarToData f)) = TensorAlgebra.fromData (scalarToData (action X f))

  /-- Axiom 2: Degenerates to the affine connection on vector fields (1-0 tensors) -/
  nabla_vector : ∀ (X Y : V),
    nabla_tensor X (TensorAlgebra.fromData (vectorToData Y)) = TensorAlgebra.fromData (vectorToData (conn.nabla X Y))

  /-- Axiom 3: Leibniz Rule for Tensor Products -/
  nabla_tensor_prod : ∀ (X : V) {r1 s1 r2 s2 : ℕ} (T1 : AbstractTensor R V r1 s1) (T2 : AbstractTensor R V r2 s2),
    nabla_tensor X (TensorAlgebra.tensor_prod T1 T2) =
      TensorAlgebra.add (TensorAlgebra.tensor_prod (nabla_tensor X T1) T2) (TensorAlgebra.tensor_prod T1 (nabla_tensor X T2))

  /-- Axiom 4: Commutes with intrinsic contraction -/
  nabla_contract : ∀ (X : V) {r s : ℕ} (T : AbstractTensor R V (r + 1) (s + 1)),
    nabla_tensor X (TensorAlgebra.contract T) = TensorAlgebra.contract (nabla_tensor X T)

  /-- Axiom 5: Linearity over R addition -/
  nabla_add : ∀ (X : V) {r s : ℕ} (T1 T2 : AbstractTensor R V r s),
    nabla_tensor X (TensorAlgebra.add T1 T2) = TensorAlgebra.add (nabla_tensor X T1) (nabla_tensor X T2)

  /-- Axiom 6: Extended Leibniz Rule for scalar multiplication -/
  nabla_smul : ∀ (X : V) (c : R) {r s : ℕ} (T : AbstractTensor R V r s),
    nabla_tensor X (TensorAlgebra.smul c T) =
      TensorAlgebra.add (TensorAlgebra.smul (action X c) T) (TensorAlgebra.smul c (nabla_tensor X T))

  /-- Axiom 7: Action on 0-2 tensors -/
  nabla_eval02 : ∀ (X Y Z : V) (T : AbstractTensor R V 0 2),
    (TensorAlgebra.toData (nabla_tensor X T)) ![Y, Z] ![] =
      action X ((TensorAlgebra.toData T) ![Y, Z] ![])
      - (TensorAlgebra.toData T) ![conn.nabla X Y, Z] ![]
      - (TensorAlgebra.toData T) ![Y, conn.nabla X Z] ![]
