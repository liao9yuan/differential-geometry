import DifferentialGeometry.Geometry.Connection
import DifferentialGeometry.Geometry.Curvature
import DifferentialGeometry.Algebra.VectorField
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Curvature Tensor Tensoriality
Proofs of the C-infinity linearity of the Riemann curvature tensor.
-/

open AbstractDerivationAction
open AbstractLieBracket

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] [AbstractDerivationAction R V] [AbstractLieBracket V]

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] [AbstractDerivationAction R V] [AbstractLieBracket V]


/-- Proves that the Riemann curvature tensor is C-infinity linear with respect to its third vector field argument. -/
theorem Rm_smul_Z (conn : AbstractAffineConnection R V) [DerivationRules R V] [LieDerivationRules R V] (f : R) (X Y Z : V) :
  Rm conn X Y (f • Z) = f • (Rm conn X Y Z) := by
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
  rw [sub_smul]
  rw [smul_sub, smul_sub]
  abel

omit [AbstractLieBracket V] in
lemma nabla_neg_left (conn : AbstractAffineConnection R V) (X Z : V) : conn.nabla (-X) Z = - conn.nabla X Z := by
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

omit [AbstractLieBracket V] in
lemma nabla_sub_left (conn : AbstractAffineConnection R V) (A B Z : V) : conn.nabla (A - B) Z = conn.nabla A Z - conn.nabla B Z := by
  calc conn.nabla (A - B) Z = conn.nabla (A + -B) Z := by rw [sub_eq_add_neg]
    _ = conn.nabla A Z + conn.nabla (-B) Z := conn.nabla_add_left A (-B) Z
    _ = conn.nabla A Z + - conn.nabla B Z := by rw [nabla_neg_left]
    _ = conn.nabla A Z - conn.nabla B Z := by rw [sub_eq_add_neg]

/-- Proves that Riemann curvature is additive in the first vector field argument. -/
lemma Rm_add_X (conn : AbstractAffineConnection R V) [DerivationRules R V] (X₁ X₂ Y Z : V) : Rm conn (X₁ + X₂) Y Z = Rm conn X₁ Y Z + Rm conn X₂ Y Z := by
  unfold Rm
  rw [conn.nabla_add_left X₁ X₂ (conn.nabla Y Z)]
  rw [conn.nabla_add_left X₁ X₂ Z]
  rw [DerivationRules.bracket_add_left R X₁ X₂ Y]
  rw [conn.nabla_add_left (bracket X₁ Y) (bracket X₂ Y) Z]
  rw [conn.nabla_add_right Y (conn.nabla X₁ Z) (conn.nabla X₂ Z)]
  abel

/-- Proves that Riemann curvature is additive in the third vector field argument. -/
lemma Rm_add_Z (conn : AbstractAffineConnection R V) (X Y Z₁ Z₂ : V) : Rm conn X Y (Z₁ + Z₂) = Rm conn X Y Z₁ + Rm conn X Y Z₂ := by
  unfold Rm
  rw [conn.nabla_add_right Y Z₁ Z₂]
  rw [conn.nabla_add_right X (conn.nabla Y Z₁) (conn.nabla Y Z₂)]
  rw [conn.nabla_add_right X Z₁ Z₂]
  rw [conn.nabla_add_right Y (conn.nabla X Z₁) (conn.nabla X Z₂)]
  rw [conn.nabla_add_right (bracket X Y) Z₁ Z₂]
  abel

/-- Proves that Riemann curvature is additive in the second vector field argument. -/
lemma Rm_add_Y (conn : AbstractAffineConnection R V) [DerivationRules R V] (X Y₁ Y₂ Z : V) : Rm conn X (Y₁ + Y₂) Z = Rm conn X Y₁ Z + Rm conn X Y₂ Z := by
  unfold Rm
  rw [conn.nabla_add_left Y₁ Y₂ Z]
  rw [conn.nabla_add_right X (conn.nabla Y₁ Z) (conn.nabla Y₂ Z)]
  rw [conn.nabla_add_left Y₁ Y₂ (conn.nabla X Z)]
  rw [DerivationRules.bracket_add_right R X Y₁ Y₂]
  rw [conn.nabla_add_left (bracket X Y₁) (bracket X Y₂) Z]
  abel

/-- Proves that the Riemann curvature tensor is C-infinity linear with respect to its second vector field argument. -/
theorem Rm_smul_Y (conn : AbstractAffineConnection R V) [DerivationRules R V] [LieDerivationRules R V] (f : R) (X Y Z : V) :
  Rm conn X (f • Y) Z = f • (Rm conn X Y Z) := by
  unfold Rm
  rw [conn.nabla_smul_left f Y Z]
  rw [conn.leibniz f X (conn.nabla Y Z)]
  rw [conn.nabla_smul_left f Y (conn.nabla X Z)]
  rw [DerivationRules.bracket_smul_right f X Y]
  rw [conn.nabla_add_left (f • (bracket X Y)) ((action X f) • Y) Z]
  rw [conn.nabla_smul_left f (bracket X Y) Z]
  rw [conn.nabla_smul_left (action X f) Y Z]
  rw [smul_sub, smul_sub]
  abel



/-- Proves that the Riemann curvature tensor is C-infinity linear with respect to its first vector field argument. -/
theorem Rm_smul_X (conn : AbstractAffineConnection R V) [DerivationRules R V] [LieDerivationRules R V] (f : R) (X Y Z : V) :
  Rm conn (f • X) Y Z = f • (Rm conn X Y Z) := by
  unfold Rm
  rw [conn.nabla_smul_left f X (conn.nabla Y Z)]
  rw [conn.nabla_smul_left f X Z]
  rw [conn.leibniz f Y (conn.nabla X Z)]
  rw [DerivationRules.bracket_smul_left f X Y]
  rw [nabla_sub_left]
  rw [conn.nabla_smul_left f (bracket X Y) Z]
  rw [conn.nabla_smul_left (action Y f) X Z]
  rw [smul_sub, smul_sub]
  abel
