import DifferentialGeometry.Geometry.Connection
import DifferentialGeometry.Geometry.Curvature
import DifferentialGeometry.Geometry.CurvatureTensor
import DifferentialGeometry.Algebra.BilinearForm
import DifferentialGeometry.Algebra.Trace
import DifferentialGeometry.Algebra.Basic

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Ricci Curvature Tensor
Rigorous construction of the Ricci curvature as a smooth bilinear form.
-/

open DerivationAction
open LieBracket

/-- Trace linearity rules mapping the general trace operator's linearity properties. -/
class TraceLinearityRules (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] [TraceOperator R V] where
  trace_add : ∀ (A B : V → V), (TraceOperator.trace (fun Z => A Z + B Z) : R) = TraceOperator.trace A + TraceOperator.trace B
  trace_smul : ∀ (c : R) (A : V → V), (TraceOperator.trace (fun Z => ScalarMul.smul c (A Z)) : R) = c * TraceOperator.trace A

variable {R V : Type}
variable [CommRing R] [AddCommGroup V] [Module R V]
variable [DerivationAction R V] [LieBracket V]

/-- Constructs the Ricci curvature as a rigorously proven SmoothBilinearForm. -/
def ricciForm (conn : AffineConnection R V) [DerivationRules R V] [LieDerivationRules R V] [TraceOperator R V] [TraceLinearityRules R V] : SmoothBilinearForm R V where
  val := fun X Y => Rc conn X Y
  add_left := fun X₁ X₂ Y => by
    unfold Rc
    have h : (fun Z => Rm conn Z (X₁ + X₂) Y) = (fun Z => Rm conn Z X₁ Y + Rm conn Z X₂ Y) := by
      funext Z
      rw [Rm_add_Y conn Z X₁ X₂ Y]
    rw [h]
    rw [TraceLinearityRules.trace_add]
  smul_left := fun c X Y => by
    unfold Rc
    simp only [← smul_eq_hSMul]
    have h : (fun Z => Rm conn Z (ScalarMul.smul c X) Y) = (fun Z => ScalarMul.smul c (Rm conn Z X Y)) := by
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
    rw [TraceLinearityRules.trace_add]
  smul_right := fun c X Y => by
    unfold Rc
    simp only [← smul_eq_hSMul]
    have h : (fun Z => Rm conn Z X (ScalarMul.smul c Y)) = (fun Z => ScalarMul.smul c (Rm conn Z X Y)) := by
      funext Z
      rw [Rm_smul_Z conn c Z X Y]
    rw [h]
    rw [TraceLinearityRules.trace_smul]
