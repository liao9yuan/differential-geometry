import DifferentialGeometry.Synthetic.Algebra.VectorField
import DifferentialGeometry.Bridge.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

open DifferentialGeometry.Bridge

/-!
# Smooth Bilinear Form
Algebraic formulation of a (0,2)-tensor.
-/

variable (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]

/-- Smooth Bilinear Form structure alias for `AbstractTensor R V 0 2`. -/
abbrev AbstractBilinearForm := TensorAlgebra.AbstractTensor R V 0 2

variable {R V}

/-- The unique zero tensor. -/
def zero_tensor {r s : ℕ} : TensorAlgebra.AbstractTensor R V r s := TensorAlgebra.fromData (0 : TensorData R V r s)

/-- Create a bilinear form from a linear map over linear maps -/
def TensorAlgebra.fromBilinear {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
  (B : V →ₗ[R] V →ₗ[R] R) : AbstractBilinearForm R V :=
  TensorAlgebra.fromData {
    toFun := fun X => MultilinearMap.constOfIsEmpty R _ (B (X 0) (X 1))
    map_update_add' := by
      intro instDec m i x y
      ext _
      fin_cases i
      · dsimp [Function.update]
        have hz : (1 : Fin 2) ≠ 0 := by clear instDec; decide
        simp [hz]
      · dsimp [Function.update]
        have hz : (0 : Fin 2) ≠ 1 := by clear instDec; decide
        simp [hz]
    map_update_smul' := by
      intro instDec m i c x
      ext _
      fin_cases i
      · dsimp [Function.update]
        have hz : (1 : Fin 2) ≠ 0 := by clear instDec; decide
        simp [hz]
      · dsimp [Function.update]
        have hz : (0 : Fin 2) ≠ 1 := by clear instDec; decide
        simp [hz]
  }

lemma TensorAlgebra.contract_fromBilinear {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
  (B : V →ₗ[R] V →ₗ[R] R) (X Y : V) :
  (TensorAlgebra.toData (TensorAlgebra.fromBilinear B)) ![X, Y] ![] = B X Y := by
  rw [TensorAlgebra.fromBilinear, TensorAlgebra.toData_fromData]
  rfl


/-- Zero typeclass instance for generic tensors -/
instance {r s : ℕ} : Zero (TensorAlgebra.AbstractTensor R V r s) where
  zero := zero_tensor

/-- Add typeclass instance for generic tensors -/
instance {r s : ℕ} : Add (TensorAlgebra.AbstractTensor R V r s) where
  add := TensorAlgebra.add

/-- SMul typeclass instance for generic tensors -/
instance {r s : ℕ} : SMul R (TensorAlgebra.AbstractTensor R V r s) where
  smul := TensorAlgebra.smul

/-- Sub typeclass instance for generic tensors -/
instance {r s : ℕ} : Sub (TensorAlgebra.AbstractTensor R V r s) where
  sub T₁ T₂ := TensorAlgebra.add T₁ (TensorAlgebra.smul (-1 : R) T₂)
