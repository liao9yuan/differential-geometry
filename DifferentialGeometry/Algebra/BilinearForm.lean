import DifferentialGeometry.Algebra.VectorField
import DifferentialGeometry.Bridge.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false

open DifferentialGeometry.Bridge

/-!
# Smooth Bilinear Form
Algebraic formulation of a (0,2)-tensor.
-/

variable (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]

/-- Smooth Bilinear Form structure alias for `AbstractTensor R V 0 2`. -/
abbrev AbstractBilinearForm := TensorAlgebra.AbstractTensor R V 0 2

variable {R V}

/-- The zero tensor in `AbstractTensor R V r s`. Constructed carefully to avoid typeclass rewrites. -/
def zero_tensor : (r s : ℕ) → TensorAlgebra.AbstractTensor R V r s
| 0, 0 => TensorAlgebra.fromScalar (0 : R)
| r + 1, s => TensorAlgebra.tensor_prod (r1:=r) (s1:=s) (r2:=1) (s2:=0) (zero_tensor r s) (TensorAlgebra.fromVector (0 : V))
| 0, s + 1 => TensorAlgebra.tensor_prod (r1:=0) (s1:=s) (r2:=0) (s2:=1) (zero_tensor 0 s) (TensorAlgebra.fromCovector (0 : V →ₗ[R] R))

/-- Zero typeclass instance for generic tensors -/
instance {r s : ℕ} : Zero (TensorAlgebra.AbstractTensor R V r s) where
  zero := zero_tensor r s

lemma zero_tensor_0_2_step : (zero_tensor 0 2 : TensorAlgebra.AbstractTensor R V 0 2) =
  TensorAlgebra.tensor_prod (r1:=0) (s1:=1) (r2:=0) (s2:=1)
    (zero_tensor 0 1 : TensorAlgebra.AbstractTensor R V 0 1)
    (TensorAlgebra.fromCovector (0 : V →ₗ[R] R)) := by rw [zero_tensor]

/-- Add typeclass instance for generic tensors -/
instance {r s : ℕ} : Add (TensorAlgebra.AbstractTensor R V r s) where
  add := TensorAlgebra.add

/-- SMul typeclass instance for generic tensors -/
instance {r s : ℕ} : SMul R (TensorAlgebra.AbstractTensor R V r s) where
  smul := TensorAlgebra.smul

/-- Sub typeclass instance for generic tensors -/
instance {r s : ℕ} : Sub (TensorAlgebra.AbstractTensor R V r s) where
  sub T₁ T₂ := TensorAlgebra.add T₁ (TensorAlgebra.smul (-1 : R) T₂)
