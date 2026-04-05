import DifferentialGeometry.Geometry.Connection
import DifferentialGeometry.Geometry.Curvature
import DifferentialGeometry.Geometry.CurvatureTensor
import DifferentialGeometry.Algebra.BilinearForm
import DifferentialGeometry.Algebra.Trace
import DifferentialGeometry.Algebra.VectorField
import DifferentialGeometry.Bridge.Defs

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# Ricci Curvature Tensor
Rigorous construction of the Ricci curvature as a smooth bilinear form.
-/

open AbstractDerivationAction
open AbstractLieBracket
open DifferentialGeometry.Bridge TensorAlgebra

variable {R V : Type}
variable [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
variable [AbstractDerivationAction R V] [AbstractLieBracket V]

/-- Constructs the Ricci curvature as a rigorously proven AbstractBilinearForm. -/
def ricciForm (conn : AbstractAffineConnection R V) [DerivationRules R V] [LieDerivationRules R V] [TraceOperator R V] [TraceLinearityRules R V] : AbstractBilinearForm R V :=
  TensorAlgebra.fromBilinear {
    toFun := fun X => {
      toFun := fun Y => TraceOperator.trace (fun Z => Rm conn Z X Y)
      map_add' := fun Y₁ Y₂ => by
        have h_add : (fun Z => Rm conn Z X (Y₁ + Y₂)) = (fun Z => Rm conn Z X Y₁) + (fun Z => Rm conn Z X Y₂) := by
          ext Z
          exact Rm_add_Z conn Z X Y₁ Y₂
        rw [h_add]
        exact TraceLinearityRules.trace_add
      map_smul' := fun c Y => by
        have h_smul : (fun Z => Rm conn Z X (c • Y)) = c • (fun Z => Rm conn Z X Y) := by
          ext Z
          exact Rm_smul_Z conn c Z X Y
        rw [h_smul]
        exact TraceLinearityRules.trace_smul
    }
    map_add' := fun X₁ X₂ => by
      ext Y
      change (TraceOperator.trace (fun Z => Rm conn Z (X₁ + X₂) Y) : R) = TraceOperator.trace (fun Z => Rm conn Z X₁ Y) + TraceOperator.trace (fun Z => Rm conn Z X₂ Y)
      have h_add : (fun Z => Rm conn Z (X₁ + X₂) Y) = (fun Z => Rm conn Z X₁ Y) + (fun Z => Rm conn Z X₂ Y) := by
        ext Z
        exact Rm_add_Y conn Z X₁ X₂ Y
      rw [h_add]
      exact TraceLinearityRules.trace_add
    map_smul' := fun c X => by
      ext Y
      change (TraceOperator.trace (fun Z => Rm conn Z (c • X) Y) : R) = c * TraceOperator.trace (fun Z => Rm conn Z X Y)
      have h_smul : (fun Z => Rm conn Z (c • X) Y) = c • (fun Z => Rm conn Z X Y) := by
        ext Z
        exact Rm_smul_Y conn c Z X Y
      rw [h_smul]
      exact TraceLinearityRules.trace_smul
  }

lemma eval02_ricciForm (conn : AbstractAffineConnection R V) [DerivationRules R V] [LieDerivationRules R V] [TraceOperator R V] [TraceLinearityRules R V] (X Y : V) :
  eval02 (ricciForm conn) X Y = Rc conn X Y := by
  dsimp [ricciForm, Rc]
  rw [eval02_fromBilinear]
  rfl
