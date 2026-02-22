import DifferentialGeometry.Geometry.Connection
import DifferentialGeometry.Geometry.Curvature
import DifferentialGeometry.Algebra.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Curvature Tensor Tensoriality
Proofs of the C-infinity linearity of the Riemann curvature tensor.
-/

open DerivationAction
open LieBracket

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] [DerivationAction R V] [LieBracket V]

/-- Axiomatizes the action of the Lie bracket on scalar functions. -/
class LieDerivationRules (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] [DerivationAction R V] [LieBracket V] where
  action_bracket : ∀ (X Y : V) (f : R), action (bracket X Y) f = action X (action Y f) - action Y (action X f)

lemma smul_eq_hSMul {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (c : R) (W : V) : ScalarMul.smul c W = HSMul.hSMul c W := rfl

/-- Proves that the Riemann curvature tensor is C-infinity linear with respect to its third vector field argument. -/
theorem Rm_smul_Z (conn : AffineConnection R V) [DerivationRules R V] [LieDerivationRules R V] (f : R) (X Y Z : V) :
  Rm conn X Y (ScalarMul.smul f Z) = ScalarMul.smul f (Rm conn X Y Z) := by
  -- Proof strategy:
  -- Rm conn X Y (fZ) = nabla X (nabla Y (fZ)) - nabla Y (nabla X (fZ)) - nabla [X,Y] (fZ)
  unfold Rm
  rw [conn.leibniz f Y Z]
  rw [conn.leibniz f X Z]
  rw [conn.leibniz f (bracket X Y) Z]
  rw [conn.nabla_add_right]
  rw [conn.nabla_add_right]
  rw [conn.leibniz (action Y f) X Z]
  rw [conn.leibniz (action X f) Y Z]
  rw [conn.leibniz f X (conn.nabla Y Z)]
  rw [conn.leibniz f Y (conn.nabla X Z)]
  rw [LieDerivationRules.action_bracket X Y f]
  simp only [smul_eq_hSMul]
  rw [sub_smul]
  rw [smul_sub, smul_sub]
  abel

omit [LieBracket V] in
lemma nabla_neg_left (conn : AffineConnection R V) (X Z : V) : conn.nabla (-X) Z = - conn.nabla X Z := by
  have h1 : conn.nabla (X + -X) Z = conn.nabla X Z + conn.nabla (-X) Z := conn.nabla_add_left X (-X) Z
  have h3 : conn.nabla (0 + 0) Z = conn.nabla 0 Z + conn.nabla 0 Z := conn.nabla_add_left 0 0 Z
  have h5 : conn.nabla 0 Z = 0 := by
    calc conn.nabla 0 Z = conn.nabla 0 Z + conn.nabla 0 Z - conn.nabla 0 Z := by abel
      _ = conn.nabla (0 + 0) Z - conn.nabla 0 Z := by rw [← h3]
      _ = conn.nabla 0 Z - conn.nabla 0 Z := by rw [add_zero]
      _ = 0 := by abel
  calc conn.nabla (-X) Z = conn.nabla X Z + conn.nabla (-X) Z - conn.nabla X Z := by abel
    _ = conn.nabla (X + -X) Z - conn.nabla X Z := by rw [← h1]
    _ = conn.nabla 0 Z - conn.nabla X Z := by rw [add_neg_cancel]
    _ = 0 - conn.nabla X Z := by rw [h5]
    _ = - conn.nabla X Z := by abel

omit [LieBracket V] in
lemma nabla_sub_left (conn : AffineConnection R V) (A B Z : V) : conn.nabla (A - B) Z = conn.nabla A Z - conn.nabla B Z := by
  calc conn.nabla (A - B) Z = conn.nabla (A + -B) Z := by rw [sub_eq_add_neg]
    _ = conn.nabla A Z + conn.nabla (-B) Z := conn.nabla_add_left A (-B) Z
    _ = conn.nabla A Z + - conn.nabla B Z := by rw [nabla_neg_left]
    _ = conn.nabla A Z - conn.nabla B Z := by rw [sub_eq_add_neg]

/-- Proves that the Riemann curvature tensor is C-infinity linear with respect to its first vector field argument. -/
theorem Rm_smul_X (conn : AffineConnection R V) [DerivationRules R V] [LieDerivationRules R V] (f : R) (X Y Z : V) :
  Rm conn (ScalarMul.smul f X) Y Z = ScalarMul.smul f (Rm conn X Y Z) := by
  unfold Rm
  rw [conn.nabla_smul_left f X (conn.nabla Y Z)]
  rw [conn.nabla_smul_left f X Z]
  rw [conn.leibniz f Y (conn.nabla X Z)]
  rw [DerivationRules.bracket_smul_left f X Y]
  rw [nabla_sub_left]
  rw [conn.nabla_smul_left f (bracket X Y) Z]
  rw [conn.nabla_smul_left (action Y f) X Z]
  simp only [smul_eq_hSMul]
  rw [smul_sub, smul_sub]
  abel
