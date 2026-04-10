import DifferentialGeometry.Synthetic.Algebra.VectorField
import DifferentialGeometry.VectorField
import DifferentialGeometry.Synthetic.Algebra.TensorAlgebra
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

open DifferentialGeometry

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

lemma TensorAlgebra.tensor_eval_fromBilinear {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
  (B : V →ₗ[R] V →ₗ[R] R) (X Y : V) :
  tensor_eval (TensorAlgebra.fromBilinear B) ![X, Y] ![] = B X Y := by
  dsimp [tensor_eval]
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

lemma tensor_eval_zero (X Y : V) : tensor_eval (0 : AbstractBilinearForm R V) ![X, Y] ![] = (0:R) := by
  have hz : (0 : AbstractBilinearForm R V) = (0:R) • (0 : AbstractBilinearForm R V) := by
    have h1 : TensorAlgebra.toData (TensorAlgebra.smul (0:R) (0 : AbstractBilinearForm R V)) = (0:R) • TensorAlgebra.toData (0 : AbstractBilinearForm R V) := TensorAlgebra.toData_smul 0 0
    have h2 : (0:R) • TensorAlgebra.toData (0 : AbstractBilinearForm R V) = 0 := zero_smul R _
    rw [h2] at h1
    have h3 : TensorAlgebra.toData (0 : AbstractBilinearForm R V) = 0 := by
      have hzz : (0 : AbstractBilinearForm R V) = TensorAlgebra.fromData (0 : TensorData R V 0 2) := rfl
      rw [hzz, TensorAlgebra.toData_fromData]
    rw [← h3] at h1
    have h4 : TensorAlgebra.fromData (TensorAlgebra.toData (TensorAlgebra.smul (0:R) (0 : AbstractBilinearForm R V))) = TensorAlgebra.fromData (TensorAlgebra.toData (0 : AbstractBilinearForm R V)) := by rw [h1]
    rw [TensorAlgebra.fromData_toData, TensorAlgebra.fromData_toData] at h4
    exact h4.symm
  calc tensor_eval (0 : AbstractBilinearForm R V) ![X, Y] ![]
    _ = tensor_eval ((0:R) • (0 : AbstractBilinearForm R V)) ![X, Y] ![] := by nth_rw 1 [hz]
    _ = (0:R) * tensor_eval (0 : AbstractBilinearForm R V) ![X, Y] ![] := tensor_eval_smul 0 0 ![X, Y] ![]
    _ = (0:R) := MulZeroClass.zero_mul _

