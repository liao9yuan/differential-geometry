import DifferentialGeometry.Algebra.Basic
import DifferentialGeometry.Geometry.Connection
import DifferentialGeometry.Geometry.Curvature
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# First Bianchi Identity
Algebraic formulation and proof of the First Bianchi Identity.
-/

open DerivationAction
open LieBracket

variable {R V : Type}
variable [CommRing R] [AddCommGroup V] [Module R V]
variable [DerivationAction R V] [LieBracket V]

local notation "⁅" X ", " Y "⁆" => bracket X Y

/-- Jacobi identity for the Lie bracket of vector fields.
Input: (V)
Output: Prop -/
class JacobiIdentity (V : Type) [AddCommGroup V] [LieBracket V] where
  jacobi : ∀ X Y Z : V, ⁅X, ⁅Y, Z⁆⁆ + ⁅Y, ⁅Z, X⁆⁆ + ⁅Z, ⁅X, Y⁆⁆ = 0

/-- Negative homogeneity of the affine connection in the second argument.
Proof that ∇_X (-Y) = - ∇_X Y.
Input: (AffineConnection R V, V, V)
Output: Prop -/
lemma nabla_neg_right (conn : AffineConnection R V) (X Y : V) : conn.nabla X (-Y) = - conn.nabla X Y := by
  have h1 : conn.nabla X (Y + -Y) = conn.nabla X Y + conn.nabla X (-Y) := conn.nabla_add_right X Y (-Y)
  have h2 : Y + -Y = 0 := by abel
  rw [h2] at h1
  have h3 : conn.nabla X 0 = 0 := by
    have h_add : conn.nabla X 0 + conn.nabla X 0 = conn.nabla X 0 := by
      calc conn.nabla X 0 + conn.nabla X 0 = conn.nabla X (0 + 0) := (conn.nabla_add_right X 0 0).symm
        _ = conn.nabla X 0 := by rw [add_zero]
    calc conn.nabla X 0 = conn.nabla X 0 + conn.nabla X 0 - conn.nabla X 0 := by abel
      _ = conn.nabla X 0 - conn.nabla X 0 := by rw [h_add]
      _ = 0 := by abel
  rw [h3] at h1
  calc conn.nabla X (-Y) = - conn.nabla X Y + conn.nabla X Y + conn.nabla X (-Y) := by abel
    _ = - conn.nabla X Y + (conn.nabla X Y + conn.nabla X (-Y)) := by abel
    _ = - conn.nabla X Y + 0 := by rw [← h1]
    _ = - conn.nabla X Y := by abel

/-- Additive linearity of the affine connection over vector field subtraction.
Proof that ∇_X (Y - Z) = ∇_X Y - ∇_X Z.
Input: (AffineConnection R V, V, V, V)
Output: Prop -/
lemma nabla_sub_right (conn : AffineConnection R V) (X Y Z : V) : conn.nabla X (Y - Z) = conn.nabla X Y - conn.nabla X Z := by
  calc conn.nabla X (Y - Z) = conn.nabla X (Y + -Z) := by rw [sub_eq_add_neg]
    _ = conn.nabla X Y + conn.nabla X (-Z) := conn.nabla_add_right X Y (-Z)
    _ = conn.nabla X Y + - conn.nabla X Z := by rw [nabla_neg_right conn X Z]
    _ = conn.nabla X Y - conn.nabla X Z := by rw [sub_eq_add_neg]

/-- Regrouping of double covariant derivatives using the torsion-free property.
Proof that ∇_X (∇_Y Z) - ∇_X (∇_Z Y) = ∇_X ⁅Y, Z⁆.
Input: (AffineConnection R V, V, V, V)
Output: Prop -/
lemma nabla_torsion_group (conn : AffineConnection R V) [TorsionFree conn] (X Y Z : V) :
  conn.nabla X (conn.nabla Y Z) - conn.nabla X (conn.nabla Z Y) = conn.nabla X ⁅Y, Z⁆ := by
  rw [← nabla_sub_right conn X (conn.nabla Y Z) (conn.nabla Z Y)]
  have h1 : conn.nabla Y Z - conn.nabla Z Y = ⁅Y, Z⁆ := TorsionFree.torsion_zero Y Z
  rw [h1]

/-- First Bianchi Identity.
Proof that R(X,Y)Z + R(Y,Z)X + R(Z,X)Y = 0 for a torsion-free connection.
Input: (AffineConnection R V, V, V, V)
Output: Prop -/
theorem first_bianchi (conn : AffineConnection R V) [TorsionFree conn] [JacobiIdentity V] (X Y Z : V) :
  Rm conn X Y Z + Rm conn Y Z X + Rm conn Z X Y = 0 := by
  unfold Rm
  have h1 : Rm conn X Y Z = conn.nabla X (conn.nabla Y Z) - conn.nabla Y (conn.nabla X Z) - conn.nabla ⁅X, Y⁆ Z := rfl
  have h2 : Rm conn Y Z X = conn.nabla Y (conn.nabla Z X) - conn.nabla Z (conn.nabla Y X) - conn.nabla ⁅Y, Z⁆ X := rfl
  have h3 : Rm conn Z X Y = conn.nabla Z (conn.nabla X Y) - conn.nabla X (conn.nabla Z Y) - conn.nabla ⁅Z, X⁆ Y := rfl
  calc conn.nabla X (conn.nabla Y Z) - conn.nabla Y (conn.nabla X Z) - conn.nabla ⁅X, Y⁆ Z
    + (conn.nabla Y (conn.nabla Z X) - conn.nabla Z (conn.nabla Y X) - conn.nabla ⁅Y, Z⁆ X)
    + (conn.nabla Z (conn.nabla X Y) - conn.nabla X (conn.nabla Z Y) - conn.nabla ⁅Z, X⁆ Y)
      = (conn.nabla X (conn.nabla Y Z) - conn.nabla X (conn.nabla Z Y))
      + (conn.nabla Y (conn.nabla Z X) - conn.nabla Y (conn.nabla X Z))
      + (conn.nabla Z (conn.nabla X Y) - conn.nabla Z (conn.nabla Y X))
      - conn.nabla ⁅X, Y⁆ Z - conn.nabla ⁅Y, Z⁆ X - conn.nabla ⁅Z, X⁆ Y := by abel
    _ = conn.nabla X ⁅Y, Z⁆
      + conn.nabla Y ⁅Z, X⁆
      + conn.nabla Z ⁅X, Y⁆
      - conn.nabla ⁅X, Y⁆ Z - conn.nabla ⁅Y, Z⁆ X - conn.nabla ⁅Z, X⁆ Y := by
      rw [nabla_torsion_group conn X Y Z, nabla_torsion_group conn Y Z X, nabla_torsion_group conn Z X Y]
    _ = (conn.nabla X ⁅Y, Z⁆ - conn.nabla ⁅Y, Z⁆ X)
      + (conn.nabla Y ⁅Z, X⁆ - conn.nabla ⁅Z, X⁆ Y)
      + (conn.nabla Z ⁅X, Y⁆ - conn.nabla ⁅X, Y⁆ Z) := by abel
    _ = ⁅X, ⁅Y, Z⁆⁆ + ⁅Y, ⁅Z, X⁆⁆ + ⁅Z, ⁅X, Y⁆⁆ := by
      rw [TorsionFree.torsion_zero X ⁅Y, Z⁆]
      rw [TorsionFree.torsion_zero Y ⁅Z, X⁆]
      rw [TorsionFree.torsion_zero Z ⁅X, Y⁆]
    _ = 0 := JacobiIdentity.jacobi X Y Z
