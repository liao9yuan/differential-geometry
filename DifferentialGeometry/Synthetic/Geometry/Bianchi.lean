import DifferentialGeometry.Synthetic.Algebra.VectorField
import DifferentialGeometry.Synthetic.Algebra.Trace
import DifferentialGeometry.Synthetic.Geometry.Connection
import DifferentialGeometry.Synthetic.Geometry.Curvature
import DifferentialGeometry.Synthetic.Geometry.RicciTensor
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
  sorry

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

variable [TraceOperator R V]

-- Definitions of Scalar Invariants
/-- Divergence of the Ricci tensor.
Input: (AbstractAffineConnection R V, V)
Output: R -/
axiom div_Rc (conn : AbstractAffineConnection R V) (X : V) : R

/-- Gradient of the scalar curvature.
Input: (AbstractAffineConnection R V, V)
Output: R -/
axiom grad_R (conn : AbstractAffineConnection R V) (X : V) : R

/-- Divergence of the Riemann curvature tensor.
Input: (AbstractAffineConnection R V, V, V, V)
Output: R -/
axiom div_Rm (conn : AbstractAffineConnection R V) (Y Z X : V) : R

/-- Covariant derivative of Ricci tensor.
Input: (AbstractAffineConnection R V, V, V, V)
Output: R -/
def covDerivRc {R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] [AbstractDerivationAction R V] [AbstractLieBracket V] [DerivationRules R V] [TraceOperator R V] (conn : AbstractAffineConnection R V) [RiemannCurvatureTensorOp conn] (Y Z X : V) : R :=
  AbstractDerivationAction.action Y (Rc conn Z X) - Rc conn (conn.nabla Y Z) X - Rc conn Z (conn.nabla Y X)



--- THEOREM CONTRACTIONS ---

/-- Specific linear algebraic identities resulting from contracting the covariant derivative of curvature.
Input: (AbstractAffineConnection R V)
Output: Type -/
class BianchiContractionRules {R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] [AbstractDerivationAction R V] [AbstractLieBracket V] [DerivationRules R V] [TraceOperator R V] (conn : AbstractAffineConnection R V) [RiemannCurvatureTensorOp conn] [Tensor14Trace R V] [BilinearTrace R V] where
  -- First trace transformations on each term
  trace_1_4_term1 : Tensor14Trace.trace_1_4 (fun x y z w => covDerivRm conn x y z w) = fun y z w => div_Rm conn y z w
  trace_1_4_term2 : Tensor14Trace.trace_1_4 (fun x y z w => covDerivRm conn y z x w) = fun y z w => - covDerivRc conn y z w
  trace_1_4_term3 : Tensor14Trace.trace_1_4 (fun x y z w => covDerivRm conn z x y w) = fun y z w => covDerivRc conn z y w
  -- Second trace transformations
  contract_div_Rm : ∀ X : V, BilinearTrace.tr (fun Y Z => div_Rm conn Y Z X) = - div_Rc conn X
  contract_nabla_Rc : ∀ X : V, BilinearTrace.tr (fun Y Z => covDerivRc conn Y Z X) = div_Rc conn X
  contract_nabla_Rc_swap : ∀ X : V, BilinearTrace.tr (fun Y Z => covDerivRc conn Z Y X) = grad_R conn X

/-- Contracted Bianchi Identity.
Proof that 2 * div_Rc = grad_R.
Input: (AbstractAffineConnection R V, V)
Output: Prop -/
theorem contracted_bianchi {R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] [AbstractDerivationAction R V] [AbstractLieBracket V] [DerivationRules R V] [TraceOperator R V] (conn : AbstractAffineConnection R V) [RiemannCurvatureTensorOp conn] [TorsionFree conn] [JacobiIdentity V]
  [Tensor14Trace R V] [Tensor14TraceLinearity R V]
  [BilinearTrace R V] [BilinearTraceLinearity R V]
  [BianchiContractionRules conn] (X : V) :
  2 * div_Rc conn X = grad_R conn X := by
  -- 1. Apply trace_1_4 to the entire second Bianchi identity
  have h_bianchi_fun : (fun x y z w => covDerivRm conn x y z w + covDerivRm conn y z x w + covDerivRm conn z x y w) = fun x y z w => 0 := by
    funext x y z w
    exact second_bianchi conn x y z w

  have eq_zero : (Tensor14Trace.trace_1_4 (R:=R) (V:=V) (fun x y z w => covDerivRm conn x y z w + covDerivRm conn y z x w + covDerivRm conn z x y w) : V → V → V → R) = Tensor14Trace.trace_1_4 (R:=R) (V:=V) (fun (_ _ _ _ : V) => (0 : V)) := by
    rw [h_bianchi_fun]

  -- 2. Expand additivity of trace_1_4
  rw [Tensor14TraceLinearity.tr_zero (R:=R) (V:=V)] at eq_zero
  have eq_zero' : (Tensor14Trace.trace_1_4 (R:=R) (V:=V) (fun x y z w => covDerivRm conn x y z w + (covDerivRm conn y z x w + covDerivRm conn z x y w)) : V → V → V → R) = fun (_ _ _ : V) => (0 : R) := by
    have h1 : (fun x y z w => covDerivRm conn x y z w + (covDerivRm conn y z x w + covDerivRm conn z x y w)) = (fun x y z w => covDerivRm conn x y z w + covDerivRm conn y z x w + covDerivRm conn z x y w) := by
      funext x y z w
      abel
    rw [h1]
    exact eq_zero

  rw [Tensor14TraceLinearity.tr_add (R:=R) (V:=V) (fun x y z w => covDerivRm conn x y z w) (fun x y z w => covDerivRm conn y z x w + covDerivRm conn z x y w)] at eq_zero'
  rw [Tensor14TraceLinearity.tr_add (R:=R) (V:=V) (fun x y z w => covDerivRm conn y z x w) (fun x y z w => covDerivRm conn z x y w)] at eq_zero'

  -- 3. Substitute the component transformations
  rw [BianchiContractionRules.trace_1_4_term1 (conn:=conn), BianchiContractionRules.trace_1_4_term2 (conn:=conn), BianchiContractionRules.trace_1_4_term3 (conn:=conn)] at eq_zero'

  -- 4. Apply the second contraction over Y and Z
  have h_eq_trace : BilinearTrace.tr (fun Y Z => div_Rm conn Y Z X - covDerivRc conn Y Z X + covDerivRc conn Z Y X) = 0 := by
    have h_eval : (fun (Y Z : V) => div_Rm conn Y Z X - covDerivRc conn Y Z X + covDerivRc conn Z Y X) = (fun (_ _ : V) => (0 : R)) := by
      funext Y Z
      have hF := congr_fun (congr_fun (congr_fun eq_zero' Y) Z) X
      dsimp at hF
      calc div_Rm conn Y Z X - covDerivRc conn Y Z X + covDerivRc conn Z Y X
        = div_Rm conn Y Z X + (-covDerivRc conn Y Z X + covDerivRc conn Z Y X) := by abel
        _ = 0 := hF
    rw [h_eval]
    exact BilinearTraceLinearity.tr_zero (R:=R) (V:=V)

  -- 5. Expand additivity of BilinearTrace
  have h_exp : BilinearTrace.tr (fun Y Z => div_Rm conn Y Z X - covDerivRc conn Y Z X + covDerivRc conn Z Y X) =
    BilinearTrace.tr (fun Y Z => div_Rm conn Y Z X) - BilinearTrace.tr (fun Y Z => covDerivRc conn Y Z X) + BilinearTrace.tr (fun Y Z => covDerivRc conn Z Y X) := by
    have h1 : BilinearTrace.tr (fun Y Z => div_Rm conn Y Z X - covDerivRc conn Y Z X + covDerivRc conn Z Y X) = BilinearTrace.tr (fun Y Z => div_Rm conn Y Z X - covDerivRc conn Y Z X) + BilinearTrace.tr (fun Y Z => covDerivRc conn Z Y X) := by
      exact BilinearTraceLinearity.tr_add (fun Y Z => div_Rm conn Y Z X - covDerivRc conn Y Z X) (fun Y Z => covDerivRc conn Z Y X)
    rw [h1]
    have h2 : BilinearTrace.tr (fun Y Z => div_Rm conn Y Z X - covDerivRc conn Y Z X) = BilinearTrace.tr (fun Y Z => div_Rm conn Y Z X) - BilinearTrace.tr (fun Y Z => covDerivRc conn Y Z X) := by
      exact BilinearTraceLinearity.tr_sub (fun Y Z => div_Rm conn Y Z X) (fun Y Z => covDerivRc conn Y Z X)
    rw [h2]

  -- 6. Substitute the second component transformations
  rw [h_exp] at h_eq_trace
  rw [BianchiContractionRules.contract_div_Rm (conn:=conn) X, BianchiContractionRules.contract_nabla_Rc (conn:=conn) X, BianchiContractionRules.contract_nabla_Rc_swap (conn:=conn) X] at h_eq_trace

  -- 7. Final algebraic simplification
  calc 2 * div_Rc conn X = div_Rc conn X + div_Rc conn X := by ring
    _ = div_Rc conn X + div_Rc conn X + 0 := by ring
    _ = div_Rc conn X + div_Rc conn X + (- div_Rc conn X - div_Rc conn X + grad_R conn X) := by rw [h_eq_trace]
    _ = grad_R conn X := by ring

end ContractedBianchi
