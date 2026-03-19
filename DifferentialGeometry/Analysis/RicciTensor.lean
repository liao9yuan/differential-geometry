import DifferentialGeometry.Geometry.Connection
import DifferentialGeometry.Geometry.Curvature
import DifferentialGeometry.Geometry.CurvatureTensor
import DifferentialGeometry.Algebra.BilinearForm
import DifferentialGeometry.Algebra.Trace
import DifferentialGeometry.Algebra.VectorField

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Ricci Curvature Tensor
Rigorous construction of the Ricci curvature as a smooth bilinear form.
-/

open AbstractDerivationAction
open AbstractLieBracket

variable {R V : Type}
variable [CommRing R] [AddCommGroup V] [Module R V]
variable [AbstractDerivationAction R V] [AbstractLieBracket V]

/-- Constructs the Ricci curvature as a rigorously proven SmoothBilinearForm. -/
def ricciForm (conn : AbstractAffineConnection R V) [DerivationRules R V] [LieDerivationRules R V] [TraceOperator R V] [TraceLinearityRules R V] : SmoothBilinearForm R V where
  val := fun X Y => Rc conn X Y
  add_left := fun X₁ X₂ Y => by
    unfold Rc
    have h : (fun Z => Rm conn Z (X₁ + X₂) Y) = (fun Z => Rm conn Z X₁ Y + Rm conn Z X₂ Y) := by
      funext Z
      rw [Rm_add_Y conn Z X₁ X₂ Y]
    rw [h]
    have eq_add : (fun Z => Rm conn Z X₁ Y + Rm conn Z X₂ Y) = (fun Z => Rm conn Z X₁ Y) + (fun Z => Rm conn Z X₂ Y) := rfl
    rw [eq_add]
    rw [TraceLinearityRules.trace_add]
  smul_left := fun c X Y => by
    unfold Rc
    have h : (fun Z => Rm conn Z (c • X) Y) = (fun Z => c • (Rm conn Z X Y)) := by
      funext Z
      rw [Rm_smul_Y conn c Z X Y]
    rw [h]
    rw [TraceLinearityRules.trace_smul]
  add_right := fun X Y₁ Y₂ => by
    unfold Rc
    have h : (fun Z => Rm conn Z X (Y₁ + Y₂)) = (fun Z => Rm conn Z X Y₁ + Rm conn Z X Y₂) := by
      funext Z
      rw [Rm_add_Z conn Z X Y₁ Y₂]
    rw [h]
    have eq_add : (fun Z => Rm conn Z X Y₁ + Rm conn Z X Y₂) = (fun Z => Rm conn Z X Y₁) + (fun Z => Rm conn Z X Y₂) := rfl
    rw [eq_add]
    rw [TraceLinearityRules.trace_add]
  smul_right := fun c X Y => by
    unfold Rc
    have h : (fun Z => Rm conn Z X (c • Y)) = (fun Z => c • (Rm conn Z X Y)) := by
      funext Z
      rw [Rm_smul_Z conn c Z X Y]
    rw [h]
    rw [TraceLinearityRules.trace_smul]
