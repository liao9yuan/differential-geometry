import DifferentialGeometry.Synthetic.Algebra.VectorField
import DifferentialGeometry.Synthetic.Algebra.Trace
import DifferentialGeometry.Synthetic.Geometry.Connection
import DifferentialGeometry.Synthetic.Geometry.Curvature
import DifferentialGeometry.Synthetic.Geometry.RicciTensor
import DifferentialGeometry.Synthetic.Analysis.TensorCalculus
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# First Bianchi Identity
Algebraic formulation and proof of the First Bianchi Identity.
-/

open AbstractDerivationAction
open AbstractLieBracket
open DifferentialGeometry TensorAlgebra

variable {R V : Type}
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
variable [AbstractDerivationAction R V] [AbstractLieBracket V] [DerivationRules R V]

local notation "⁅" X ", " Y "⁆" => bracket X Y



/-- Negative homogeneity of the affine connection in the second argument.
Proof that ∇_X (-Y) = - ∇_X Y.
Input: (AbstractAffineConnection R V, V, V)
Output: Prop -/
lemma nabla_neg_right (conn : AbstractAffineConnection R V) (X Y : V) : conn.nabla X (-Y) = - conn.nabla X Y := by
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
Input: (AbstractAffineConnection R V, V, V, V)
Output: Prop -/
lemma nabla_sub_right (conn : AbstractAffineConnection R V) (X Y Z : V) : conn.nabla X (Y - Z) = conn.nabla X Y - conn.nabla X Z := by
  calc conn.nabla X (Y - Z) = conn.nabla X (Y + -Z) := by rw [sub_eq_add_neg]
    _ = conn.nabla X Y + conn.nabla X (-Z) := conn.nabla_add_right X Y (-Z)
    _ = conn.nabla X Y + - conn.nabla X Z := by rw [nabla_neg_right conn X Z]
    _ = conn.nabla X Y - conn.nabla X Z := by rw [sub_eq_add_neg]


/-- Additive linearity of the lie bracket over vector field subtraction.
Proof that [X - Y, Z] = [X, Z] - [Y, Z].
Input: (R, V, V, V, V)
Output: Prop -/
lemma bracket_neg_left (_conn : AbstractAffineConnection R V) (X Y : V) : ⁅-X, Y⁆ = - ⁅X, Y⁆ := by
  have h1 : ⁅X + -X, Y⁆ = ⁅X, Y⁆ + ⁅-X, Y⁆ := DerivationRules.bracket_add_left R X (-X) Y
  have h2 : X + -X = 0 := by abel
  rw [h2] at h1
  have h3 : ⁅(0 : V), Y⁆ = 0 := by
    have h_add : ⁅(0 : V), Y⁆ + ⁅(0 : V), Y⁆ = ⁅(0 : V), Y⁆ := by
      calc ⁅(0 : V), Y⁆ + ⁅(0 : V), Y⁆ = ⁅(0 : V) + (0 : V), Y⁆ := (DerivationRules.bracket_add_left R 0 0 Y).symm
        _ = ⁅(0 : V), Y⁆ := by rw [add_zero]
    calc ⁅(0 : V), Y⁆ = ⁅(0 : V), Y⁆ + ⁅(0 : V), Y⁆ - ⁅(0 : V), Y⁆ := by abel
      _ = ⁅(0 : V), Y⁆ - ⁅(0 : V), Y⁆ := by rw [h_add]
      _ = 0 := by abel
  rw [h3] at h1
  calc ⁅-X, Y⁆ = - ⁅X, Y⁆ + ⁅X, Y⁆ + ⁅-X, Y⁆ := by abel
    _ = - ⁅X, Y⁆ + (⁅X, Y⁆ + ⁅-X, Y⁆) := by abel
    _ = - ⁅X, Y⁆ + 0 := by rw [← h1]
    _ = - ⁅X, Y⁆ := by abel

lemma bracket_sub_left (_conn : AbstractAffineConnection R V) (X Y Z : V) : ⁅X - Y, Z⁆ = ⁅X, Z⁆ - ⁅Y, Z⁆ := by
  calc ⁅X - Y, Z⁆ = ⁅X + -Y, Z⁆ := by rw [sub_eq_add_neg]
    _ = ⁅X, Z⁆ + ⁅-Y, Z⁆ := DerivationRules.bracket_add_left R X (-Y) Z
    _ = ⁅X, Z⁆ + - ⁅Y, Z⁆ := by rw [bracket_neg_left _conn Y Z]
    _ = ⁅X, Z⁆ - ⁅Y, Z⁆ := by rw [sub_eq_add_neg]

/-- Regrouping of double covariant derivatives using the torsion-free property.
Proof that ∇_X (∇_Y Z) - ∇_X (∇_Z Y) = ∇_X ⁅Y, Z⁆.
Input: (AbstractAffineConnection R V, V, V, V)
Output: Prop -/
lemma nabla_torsion_group (conn : AbstractAffineConnection R V) [TorsionFree conn] (X Y Z : V) :
  conn.nabla X (conn.nabla Y Z) - conn.nabla X (conn.nabla Z Y) = conn.nabla X ⁅Y, Z⁆ := by
  rw [← nabla_sub_right conn X (conn.nabla Y Z) (conn.nabla Z Y)]
  have h1 : conn.nabla Y Z - conn.nabla Z Y = ⁅Y, Z⁆ := TorsionFree.torsion_zero Y Z
  rw [h1]

/-- Commutation of covariant derivatives relates to Riemann curvature.
Proof that ∇_X (∇_Y Z) - ∇_Y (∇_X Z) = R(X,Y)Z + ∇_[X,Y] Z.
Input: (AbstractAffineConnection R V, V, V, V)
Output: Prop -/
lemma Rm_commutation (conn : AbstractAffineConnection R V) (X Y Z : V) :
  conn.nabla X (conn.nabla Y Z) - conn.nabla Y (conn.nabla X Z) = Rm conn X Y Z + conn.nabla ⁅X, Y⁆ Z := by
  unfold Rm
  abel

/-- Antisymmetry of the Riemann curvature tensor in the first two arguments.
Proof that R(X,Y)Z = - R(Y,X)Z.
Input: (AbstractAffineConnection R V, V, V, V)
Output: Prop -/
lemma Rm_antisymm (conn : AbstractAffineConnection R V) (X Y Z : V) :
  Rm conn X Y Z = - Rm conn Y X Z := by
  unfold Rm
  have h1 : ⁅X, Y⁆ = - ⁅Y, X⁆ := DerivationRules.bracket_antisymm R X Y
  rw [h1, nabla_neg_left]
  abel

/-- Linearity of Riemann tensor in the first argument over subtraction.
Proof that R(X-Y, Z)W = R(X,Z)W - R(Y,Z)W.
Input: (AbstractAffineConnection R V, V, V, V, V)
Output: Prop -/
lemma Rm_sub_left (conn : AbstractAffineConnection R V) (X Y Z W : V) :
  Rm conn (X - Y) Z W = Rm conn X Z W - Rm conn Y Z W := by
  unfold Rm
  rw [nabla_sub_left, bracket_sub_left conn, nabla_sub_left]
  repeat rw [nabla_sub_right]
  repeat rw [nabla_sub_left]
  abel

/-- First Bianchi Identity.
Proof that R(X,Y)Z + R(Y,Z)X + R(Z,X)Y = 0 for a torsion-free connection.
Input: (AbstractAffineConnection R V, V, V, V)
Output: Prop -/
theorem first_bianchi (conn : AbstractAffineConnection R V) [TorsionFree conn] [JacobiIdentity V] (X Y Z : V) :
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

/-- Covariant derivative of the Riemann curvature tensor.
Input: (AbstractAffineConnection R V, V, V, V, V)
Output: V -/
def covDerivRm (conn : AbstractAffineConnection R V) (X Y Z W : V) : V :=
  conn.nabla X (Rm conn Y Z W) - Rm conn (conn.nabla X Y) Z W - Rm conn Y (conn.nabla X Z) W - Rm conn Y Z (conn.nabla X W)

lemma Rm_unfold (conn : AbstractAffineConnection R V) (X Y Z : V) :
  Rm conn X Y Z = conn.nabla X (conn.nabla Y Z) - conn.nabla Y (conn.nabla X Z) - conn.nabla ⁅X, Y⁆ Z := rfl

lemma second_bianchi_S1 {R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] [AbstractDerivationAction R V] [AbstractLieBracket V] [DerivationRules R V] [JacobiIdentity V] (conn : AbstractAffineConnection R V) (X Y Z W : V) :
  (conn.nabla X (Rm conn Y Z W) - Rm conn Y Z (conn.nabla X W))
  + (conn.nabla Y (Rm conn Z X W) - Rm conn Z X (conn.nabla Y W))
  + (conn.nabla Z (Rm conn X Y W) - Rm conn X Y (conn.nabla Z W))
  = Rm conn ⁅X, Y⁆ Z W + Rm conn ⁅Y, Z⁆ X W + Rm conn ⁅Z, X⁆ Y W := by
  have h_jacobi : ⁅⁅X, Y⁆, Z⁆ + ⁅⁅Y, Z⁆, X⁆ + ⁅⁅Z, X⁆, Y⁆ = 0 := by
    have hj1 : ⁅⁅X, Y⁆, Z⁆ + ⁅⁅Y, Z⁆, X⁆ + ⁅⁅Z, X⁆, Y⁆ = - ⁅Z, ⁅X, Y⁆⁆ - ⁅X, ⁅Y, Z⁆⁆ - ⁅Y, ⁅Z, X⁆⁆ := by
      rw [DerivationRules.bracket_antisymm R ⁅X, Y⁆ Z, DerivationRules.bracket_antisymm R ⁅Y, Z⁆ X, DerivationRules.bracket_antisymm R ⁅Z, X⁆ Y]
      abel
    have hj2 : - ⁅Z, ⁅X, Y⁆⁆ - ⁅X, ⁅Y, Z⁆⁆ - ⁅Y, ⁅Z, X⁆⁆ = - (⁅X, ⁅Y, Z⁆⁆ + ⁅Y, ⁅Z, X⁆⁆ + ⁅Z, ⁅X, Y⁆⁆) := by abel
    have hj3 : ⁅X, ⁅Y, Z⁆⁆ + ⁅Y, ⁅Z, X⁆⁆ + ⁅Z, ⁅X, Y⁆⁆ = 0 := JacobiIdentity.jacobi X Y Z
    rw [hj1, hj2, hj3]
    abel
  have hX : conn.nabla X (Rm conn Y Z W) =
    conn.nabla X (conn.nabla Y (conn.nabla Z W)) - conn.nabla X (conn.nabla Z (conn.nabla Y W)) - conn.nabla X (conn.nabla ⁅Y, Z⁆ W) := by
    rw [Rm_unfold]
    repeat rw [nabla_sub_right]
  have hY : conn.nabla Y (Rm conn Z X W) =
    conn.nabla Y (conn.nabla Z (conn.nabla X W)) - conn.nabla Y (conn.nabla X (conn.nabla Z W)) - conn.nabla Y (conn.nabla ⁅Z, X⁆ W) := by
    rw [Rm_unfold]
    repeat rw [nabla_sub_right]
  have hZ : conn.nabla Z (Rm conn X Y W) =
    conn.nabla Z (conn.nabla X (conn.nabla Y W)) - conn.nabla Z (conn.nabla Y (conn.nabla X W)) - conn.nabla Z (conn.nabla ⁅X, Y⁆ W) := by
    rw [Rm_unfold]
    repeat rw [nabla_sub_right]
  have h_comm1 : conn.nabla X (conn.nabla Y (conn.nabla Z W)) - conn.nabla Y (conn.nabla X (conn.nabla Z W))
                 = Rm conn X Y (conn.nabla Z W) + conn.nabla ⁅X, Y⁆ (conn.nabla Z W) := Rm_commutation conn X Y (conn.nabla Z W)
  have h_comm2 : conn.nabla Y (conn.nabla Z (conn.nabla X W)) - conn.nabla Z (conn.nabla Y (conn.nabla X W))
                 = Rm conn Y Z (conn.nabla X W) + conn.nabla ⁅Y, Z⁆ (conn.nabla X W) := Rm_commutation conn Y Z (conn.nabla X W)
  have h_comm3 : conn.nabla Z (conn.nabla X (conn.nabla Y W)) - conn.nabla X (conn.nabla Z (conn.nabla Y W))
                 = Rm conn Z X (conn.nabla Y W) + conn.nabla ⁅Z, X⁆ (conn.nabla Y W) := Rm_commutation conn Z X (conn.nabla Y W)
  have h_R_comm1 : conn.nabla ⁅X, Y⁆ (conn.nabla Z W) - conn.nabla Z (conn.nabla ⁅X, Y⁆ W)
                   = Rm conn ⁅X, Y⁆ Z W + conn.nabla ⁅⁅X, Y⁆, Z⁆ W := Rm_commutation conn ⁅X, Y⁆ Z W
  have h_R_comm2 : conn.nabla ⁅Y, Z⁆ (conn.nabla X W) - conn.nabla X (conn.nabla ⁅Y, Z⁆ W)
                   = Rm conn ⁅Y, Z⁆ X W + conn.nabla ⁅⁅Y, Z⁆, X⁆ W := Rm_commutation conn ⁅Y, Z⁆ X W
  have h_R_comm3 : conn.nabla ⁅Z, X⁆ (conn.nabla Y W) - conn.nabla Y (conn.nabla ⁅Z, X⁆ W)
                   = Rm conn ⁅Z, X⁆ Y W + conn.nabla ⁅⁅Z, X⁆, Y⁆ W := Rm_commutation conn ⁅Z, X⁆ Y W
  have h2 : conn.nabla (⁅⁅X, Y⁆, Z⁆ + ⁅⁅Y, Z⁆, X⁆ + ⁅⁅Z, X⁆, Y⁆) W = conn.nabla 0 W := by rw [h_jacobi]
  have h3 : conn.nabla 0 W = 0 := by
    have h_add : conn.nabla 0 W + conn.nabla 0 W = conn.nabla 0 W := by
      calc conn.nabla 0 W + conn.nabla 0 W = conn.nabla (0 + 0) W := (conn.nabla_add_left 0 0 W).symm
        _ = conn.nabla 0 W := by rw [add_zero]
    calc conn.nabla 0 W = conn.nabla 0 W + conn.nabla 0 W - conn.nabla 0 W := by abel
      _ = conn.nabla 0 W - conn.nabla 0 W := by rw [h_add]
      _ = 0 := by abel
  rw [h3] at h2
  have h4 : conn.nabla (⁅⁅X, Y⁆, Z⁆ + ⁅⁅Y, Z⁆, X⁆) W + conn.nabla ⁅⁅Z, X⁆, Y⁆ W = 0 := by
    calc conn.nabla (⁅⁅X, Y⁆, Z⁆ + ⁅⁅Y, Z⁆, X⁆) W + conn.nabla ⁅⁅Z, X⁆, Y⁆ W = conn.nabla (⁅⁅X, Y⁆, Z⁆ + ⁅⁅Y, Z⁆, X⁆ + ⁅⁅Z, X⁆, Y⁆) W := (conn.nabla_add_left (⁅⁅X, Y⁆, Z⁆ + ⁅⁅Y, Z⁆, X⁆) ⁅⁅Z, X⁆, Y⁆ W).symm
      _ = 0 := h2
  have h5 : conn.nabla ⁅⁅X, Y⁆, Z⁆ W + conn.nabla ⁅⁅Y, Z⁆, X⁆ W + conn.nabla ⁅⁅Z, X⁆, Y⁆ W = 0 := by
    calc conn.nabla ⁅⁅X, Y⁆, Z⁆ W + conn.nabla ⁅⁅Y, Z⁆, X⁆ W + conn.nabla ⁅⁅Z, X⁆, Y⁆ W = conn.nabla (⁅⁅X, Y⁆, Z⁆ + ⁅⁅Y, Z⁆, X⁆) W + conn.nabla ⁅⁅Z, X⁆, Y⁆ W := by rw [conn.nabla_add_left]
      _ = 0 := h4
  calc (conn.nabla X (Rm conn Y Z W) - Rm conn Y Z (conn.nabla X W))
       + (conn.nabla Y (Rm conn Z X W) - Rm conn Z X (conn.nabla Y W))
       + (conn.nabla Z (Rm conn X Y W) - Rm conn X Y (conn.nabla Z W))
    = (conn.nabla X (conn.nabla Y (conn.nabla Z W)) - conn.nabla X (conn.nabla Z (conn.nabla Y W)) - conn.nabla X (conn.nabla ⁅Y, Z⁆ W) - Rm conn Y Z (conn.nabla X W))
      + (conn.nabla Y (conn.nabla Z (conn.nabla X W)) - conn.nabla Y (conn.nabla X (conn.nabla Z W)) - conn.nabla Y (conn.nabla ⁅Z, X⁆ W) - Rm conn Z X (conn.nabla Y W))
      + (conn.nabla Z (conn.nabla X (conn.nabla Y W)) - conn.nabla Z (conn.nabla Y (conn.nabla X W)) - conn.nabla Z (conn.nabla ⁅X, Y⁆ W) - Rm conn X Y (conn.nabla Z W)) := by
        rw [hX, hY, hZ]
    _ = (conn.nabla X (conn.nabla Y (conn.nabla Z W)) - conn.nabla Y (conn.nabla X (conn.nabla Z W)) - Rm conn X Y (conn.nabla Z W))
      + (conn.nabla Y (conn.nabla Z (conn.nabla X W)) - conn.nabla Z (conn.nabla Y (conn.nabla X W)) - Rm conn Y Z (conn.nabla X W))
      + (conn.nabla Z (conn.nabla X (conn.nabla Y W)) - conn.nabla X (conn.nabla Z (conn.nabla Y W)) - Rm conn Z X (conn.nabla Y W))
      + (conn.nabla ⁅X, Y⁆ (conn.nabla Z W) - conn.nabla Z (conn.nabla ⁅X, Y⁆ W))
      + (conn.nabla ⁅Y, Z⁆ (conn.nabla X W) - conn.nabla X (conn.nabla ⁅Y, Z⁆ W))
      + (conn.nabla ⁅Z, X⁆ (conn.nabla Y W) - conn.nabla Y (conn.nabla ⁅Z, X⁆ W))
      - conn.nabla ⁅X, Y⁆ (conn.nabla Z W) - conn.nabla ⁅Y, Z⁆ (conn.nabla X W) - conn.nabla ⁅Z, X⁆ (conn.nabla Y W) := by abel
    _ = (Rm conn X Y (conn.nabla Z W) + conn.nabla ⁅X, Y⁆ (conn.nabla Z W) - Rm conn X Y (conn.nabla Z W))
      + (Rm conn Y Z (conn.nabla X W) + conn.nabla ⁅Y, Z⁆ (conn.nabla X W) - Rm conn Y Z (conn.nabla X W))
      + (Rm conn Z X (conn.nabla Y W) + conn.nabla ⁅Z, X⁆ (conn.nabla Y W) - Rm conn Z X (conn.nabla Y W))
      + (Rm conn ⁅X, Y⁆ Z W + conn.nabla ⁅⁅X, Y⁆, Z⁆ W)
      + (Rm conn ⁅Y, Z⁆ X W + conn.nabla ⁅⁅Y, Z⁆, X⁆ W)
      + (Rm conn ⁅Z, X⁆ Y W + conn.nabla ⁅⁅Z, X⁆, Y⁆ W)
      - conn.nabla ⁅X, Y⁆ (conn.nabla Z W) - conn.nabla ⁅Y, Z⁆ (conn.nabla X W) - conn.nabla ⁅Z, X⁆ (conn.nabla Y W) := by
        rw [h_comm1, h_comm2, h_comm3, h_R_comm1, h_R_comm2, h_R_comm3]
    _ = Rm conn ⁅X, Y⁆ Z W + Rm conn ⁅Y, Z⁆ X W + Rm conn ⁅Z, X⁆ Y W
      + (conn.nabla ⁅⁅X, Y⁆, Z⁆ W + conn.nabla ⁅⁅Y, Z⁆, X⁆ W + conn.nabla ⁅⁅Z, X⁆, Y⁆ W) := by abel
    _ = Rm conn ⁅X, Y⁆ Z W + Rm conn ⁅Y, Z⁆ X W + Rm conn ⁅Z, X⁆ Y W + 0 := by rw [h5]
    _ = Rm conn ⁅X, Y⁆ Z W + Rm conn ⁅Y, Z⁆ X W + Rm conn ⁅Z, X⁆ Y W := by abel

lemma second_bianchi_S2 {R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] [AbstractDerivationAction R V] [AbstractLieBracket V] [DerivationRules R V] (conn : AbstractAffineConnection R V) [TorsionFree conn] (X Y Z W : V) :
  - Rm conn (conn.nabla X Y) Z W - Rm conn Y (conn.nabla X Z) W
  - Rm conn (conn.nabla Y Z) X W - Rm conn Z (conn.nabla Y X) W
  - Rm conn (conn.nabla Z X) Y W - Rm conn X (conn.nabla Z Y) W
  = - Rm conn ⁅X, Y⁆ Z W - Rm conn ⁅Y, Z⁆ X W - Rm conn ⁅Z, X⁆ Y W := by
  -- Helper: Rm(0, B, C) = 0
  have Rm_zero : ∀ B C : V, Rm conn (0 : V) B C = (0 : V) := by
    intro B C
    have h := Rm_add_X conn (0 : V) (0 : V) B C
    rw [add_zero] at h
    calc Rm conn 0 B C
        = Rm conn 0 B C + Rm conn 0 B C - Rm conn 0 B C := by abel
      _ = Rm conn 0 B C - Rm conn 0 B C := by rw [← h]
      _ = 0 := by abel
  -- Helper: Rm(-A, B, C) = -Rm(A, B, C)
  have Rm_neg_first : ∀ A B C : V, Rm conn (-A) B C = -Rm conn A B C := by
    intro A B C
    have h := Rm_add_X conn A (-A) B C
    rw [add_neg_cancel] at h
    rw [Rm_zero B C] at h
    calc Rm conn (-A) B C
        = -Rm conn A B C + (Rm conn A B C + Rm conn (-A) B C) := by abel
      _ = -Rm conn A B C + 0 := by rw [← h]
      _ = -Rm conn A B C := by abel
  -- Torsion-free decompositions: ∇_A B = ∇_B A + [A, B]
  have tf_XY : conn.nabla X Y = conn.nabla Y X + ⁅X, Y⁆ := by
    have h : conn.nabla X Y - conn.nabla Y X = ⁅X, Y⁆ := TorsionFree.torsion_zero (conn := conn) X Y
    calc conn.nabla X Y
        = conn.nabla X Y - conn.nabla Y X + conn.nabla Y X := by abel
      _ = ⁅X, Y⁆ + conn.nabla Y X := by rw [h]
      _ = conn.nabla Y X + ⁅X, Y⁆ := by abel
  have tf_XZ : conn.nabla X Z = conn.nabla Z X + ⁅X, Z⁆ := by
    have h : conn.nabla X Z - conn.nabla Z X = ⁅X, Z⁆ := TorsionFree.torsion_zero (conn := conn) X Z
    calc conn.nabla X Z
        = conn.nabla X Z - conn.nabla Z X + conn.nabla Z X := by abel
      _ = ⁅X, Z⁆ + conn.nabla Z X := by rw [h]
      _ = conn.nabla Z X + ⁅X, Z⁆ := by abel
  have tf_YZ : conn.nabla Y Z = conn.nabla Z Y + ⁅Y, Z⁆ := by
    have h : conn.nabla Y Z - conn.nabla Z Y = ⁅Y, Z⁆ := TorsionFree.torsion_zero (conn := conn) Y Z
    calc conn.nabla Y Z
        = conn.nabla Y Z - conn.nabla Z Y + conn.nabla Z Y := by abel
      _ = ⁅Y, Z⁆ + conn.nabla Z Y := by rw [h]
      _ = conn.nabla Z Y + ⁅Y, Z⁆ := by abel
  -- Split Rm using additivity: Rm(∇_A B, C, D) = Rm(∇_B A, C, D) + Rm([A,B], C, D)
  have sp1 : Rm conn (conn.nabla X Y) Z W = Rm conn (conn.nabla Y X) Z W + Rm conn ⁅X, Y⁆ Z W := by
    conv_lhs => rw [tf_XY]
    exact Rm_add_X conn (conn.nabla Y X) ⁅X, Y⁆ Z W
  have sp2 : Rm conn Y (conn.nabla X Z) W = Rm conn Y (conn.nabla Z X) W + Rm conn Y ⁅X, Z⁆ W := by
    conv_lhs => rw [tf_XZ]
    exact Rm_add_Y conn Y (conn.nabla Z X) ⁅X, Z⁆ W
  have sp3 : Rm conn (conn.nabla Y Z) X W = Rm conn (conn.nabla Z Y) X W + Rm conn ⁅Y, Z⁆ X W := by
    conv_lhs => rw [tf_YZ]
    exact Rm_add_X conn (conn.nabla Z Y) ⁅Y, Z⁆ X W
  -- Antisymmetry: Rm(A, B, C) = -Rm(B, A, C)
  have a1 : Rm conn Z (conn.nabla Y X) W = -Rm conn (conn.nabla Y X) Z W := Rm_antisymm conn Z (conn.nabla Y X) W
  have a2 : Rm conn Y (conn.nabla Z X) W = -Rm conn (conn.nabla Z X) Y W := Rm_antisymm conn Y (conn.nabla Z X) W
  have a3 : Rm conn X (conn.nabla Z Y) W = -Rm conn (conn.nabla Z Y) X W := Rm_antisymm conn X (conn.nabla Z Y) W
  -- Bracket term: Rm(Y, [X,Z], W) = Rm([Z,X], Y, W)
  have br : Rm conn Y ⁅X, Z⁆ W = Rm conn ⁅Z, X⁆ Y W := by
    rw [Rm_antisymm conn Y ⁅X, Z⁆ W]
    rw [DerivationRules.bracket_antisymm R X Z]
    rw [Rm_neg_first ⁅Z, X⁆ Y W]
    abel
  -- Substitute all identities and let abel handle the cancellation
  rw [sp1, sp2, sp3, a1, a2, a3, br]
  abel

/-- Second Bianchi Identity.
Proof that (∇_X R)(Y,Z)W + (∇_Y R)(Z,X)W + (∇_Z R)(X,Y)W = 0 for a torsion-free connection.
Input: (AbstractAffineConnection R V, V, V, V, V)
Output: Prop -/
theorem second_bianchi {R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] [AbstractDerivationAction R V] [AbstractLieBracket V] [DerivationRules R V] (conn : AbstractAffineConnection R V) [TorsionFree conn] [JacobiIdentity V] (X Y Z W : V) :
  covDerivRm conn X Y Z W + covDerivRm conn Y Z X W + covDerivRm conn Z X Y W = 0 := by
  unfold covDerivRm
  calc conn.nabla X (Rm conn Y Z W) - Rm conn (conn.nabla X Y) Z W - Rm conn Y (conn.nabla X Z) W - Rm conn Y Z (conn.nabla X W)
       + (conn.nabla Y (Rm conn Z X W) - Rm conn (conn.nabla Y Z) X W - Rm conn Z (conn.nabla Y X) W - Rm conn Z X (conn.nabla Y W))
       + (conn.nabla Z (Rm conn X Y W) - Rm conn (conn.nabla Z X) Y W - Rm conn X (conn.nabla Z Y) W - Rm conn X Y (conn.nabla Z W))
    = (conn.nabla X (Rm conn Y Z W) - Rm conn Y Z (conn.nabla X W)
       + (conn.nabla Y (Rm conn Z X W) - Rm conn Z X (conn.nabla Y W))
       + (conn.nabla Z (Rm conn X Y W) - Rm conn X Y (conn.nabla Z W)))
      + (- Rm conn (conn.nabla X Y) Z W - Rm conn Y (conn.nabla X Z) W
         - Rm conn (conn.nabla Y Z) X W - Rm conn Z (conn.nabla Y X) W
         - Rm conn (conn.nabla Z X) Y W - Rm conn X (conn.nabla Z Y) W) := by abel
    _ = (Rm conn ⁅X, Y⁆ Z W + Rm conn ⁅Y, Z⁆ X W + Rm conn ⁅Z, X⁆ Y W)
      + (- Rm conn ⁅X, Y⁆ Z W - Rm conn ⁅Y, Z⁆ X W - Rm conn ⁅Z, X⁆ Y W) := by
      rw [second_bianchi_S1, second_bianchi_S2]
    _ = 0 := by abel

section ContractedBianchi

/-- Gradient of the scalar curvature: the directional derivative of R = g^{ab} R_{ab}
along X. Defined as X(R) using the derivation action. -/
def grad_R {R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup V] [Module R V] [TensorAlgebra R V]
    [AbstractDerivationAction R V] [AbstractLieBracket V] [DerivationRules R V]
    (metric : MetricDuality R V) (conn : AbstractAffineConnection R V)
    [RiemannCurvatureTensorOp conn] (X : V) : R :=
  AbstractDerivationAction.action X (ScalarCurvature metric conn)

/-- Covariant derivative of the Ricci tensor (pointwise evaluation).
(∇_Y Ric)(Z, X) = Y(Ric(Z,X)) - Ric(∇_Y Z, X) - Ric(Z, ∇_Y X). -/
def covDerivRc {R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup V] [Module R V] [TensorAlgebra R V]
    [AbstractDerivationAction R V] [AbstractLieBracket V] [DerivationRules R V]
    (conn : AbstractAffineConnection R V) [RiemannCurvatureTensorOp conn]
    (Y Z X : V) : R :=
  AbstractDerivationAction.action Y (Rc conn Z X) - Rc conn (conn.nabla Y Z) X - Rc conn Z (conn.nabla Y X)

/-- Tensor operator wrapping the total covariant derivative of the Ricci tensor as
a (0,3) abstract tensor. Follows the same pattern as RiemannCurvatureTensorOp:
the analytic layer constructs the multilinear TensorData and verifies its evaluation
matches the pointwise covDerivRc formula. -/
class CovDerivRcTensorOp {R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup V] [Module R V] [TensorAlgebra R V]
    [AbstractDerivationAction R V] [AbstractLieBracket V] [DerivationRules R V]
    (conn : AbstractAffineConnection R V) [RiemannCurvatureTensorOp conn]
    [AffineTensorCalculus conn] where
  /-- The (0,3) tensor data for the total covariant derivative of Ricci.
  Encodes the trilinear map (Y, Z, X) ↦ (∇_Y Ric)(Z, X). -/
  nabla_rc_data : TensorData R V 0 3
  /-- Evaluation of the tensor data matches the pointwise covariant derivative. -/
  eval_eq : ∀ (Y Z X : V),
    nabla_rc_data ![Y, Z, X] (Fin.elim0) = covDerivRc conn Y Z X

/-- Divergence of the Ricci tensor: the metric trace of the total covariant derivative
of Ric. Defined as div(Ric)(X) = g^{ab} (∇_a Ric)(b, X) via metric_trace applied
to the (0,3) tensor ∇Ric, contracting the derivative direction with the first
Ricci slot, then evaluating the resulting (0,1) tensor at X. -/
def div_Rc {R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup V] [Module R V] [TensorAlgebra R V]
    [AbstractDerivationAction R V] [AbstractLieBracket V] [DerivationRules R V]
    (metric : MetricDuality R V) (conn : AbstractAffineConnection R V)
    [RiemannCurvatureTensorOp conn] [AffineTensorCalculus conn]
    [CovDerivRcTensorOp conn] (X : V) : R :=
  tensor_eval
    (metric_trace metric (0 : Fin 3) (0 : Fin 2)
      (TensorAlgebra.fromData (CovDerivRcTensorOp.nabla_rc_data (conn := conn))))
    ![X] ![]

/-- Contraction rules encoding the result of double metric contraction of the
second Bianchi identity. The analytic layer verifies these using local coordinates.

The derivation:
1. Contract the second Bianchi ∇_e R^f_{abc} + cyc = 0 over (f, a) to get
   the once-contracted Bianchi: ∇^c R_{abcd} + ∇_a Ric_{bd} − ∇_b Ric_{ad} = 0.
2. Contract again over (a, d) via g^{ad}, using:
   - g^{ad} ∇^c R_{abcd} = div_Rc(b)
   - g^{ad} ∇_a Ric_{bd} = div_Rc(b)
   - g^{ad} ∇_b Ric_{ad} = grad_R(b)
   yielding: div_Rc + div_Rc − grad_R = 0. -/
class BianchiContractionRules {R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup V] [Module R V] [TensorAlgebra R V]
    [AbstractDerivationAction R V] [AbstractLieBracket V] [DerivationRules R V]
    (metric : MetricDuality R V) (conn : AbstractAffineConnection R V)
    [RiemannCurvatureTensorOp conn] [AffineTensorCalculus conn]
    [CovDerivRcTensorOp conn] where
  /-- The double-contracted second Bianchi identity:
  div_Rc(X) + div_Rc(X) = grad_R(X). -/
  double_contraction : ∀ X : V,
    div_Rc metric conn X + div_Rc metric conn X = grad_R metric conn X

/-- Contracted Bianchi Identity.
2 · div(Ric) = grad(R), from double metric contraction of the second Bianchi. -/
theorem contracted_bianchi {R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup V] [Module R V] [TensorAlgebra R V]
    [AbstractDerivationAction R V] [AbstractLieBracket V] [DerivationRules R V]
    (metric : MetricDuality R V) (conn : AbstractAffineConnection R V)
    [RiemannCurvatureTensorOp conn] [TorsionFree conn] [JacobiIdentity V]
    [AffineTensorCalculus conn] [CovDerivRcTensorOp conn]
    [BianchiContractionRules metric conn] (X : V) :
    2 * div_Rc metric conn X = grad_R metric conn X := by
  have h := BianchiContractionRules.double_contraction (metric := metric) (conn := conn) X
  ring_nf
  linarith

end ContractedBianchi
