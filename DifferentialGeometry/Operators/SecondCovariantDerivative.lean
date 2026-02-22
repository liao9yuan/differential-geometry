import DifferentialGeometry.Geometry.Connection
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Algebra.Module.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

variable {R V : Type}
variable [CommRing R] [AddCommGroup V] [Module R V] [DerivationAction R V]

open DerivationAction

/-!
# Second Covariant Derivative
Defines the second covariant derivative operator for vector fields.
-/

/-- Helper lemma to distribute scalar multiplication over subtraction.
Input: (R, V, V)
Output: Prop -/
lemma h_smul_sub (a : R) (B C : V) : ScalarMul.smul a B - ScalarMul.smul a C = ScalarMul.smul a (B - C) := by
  exact (smul_sub a B C).symm

/-- Helper lemma for algebraic cancellation.
Input: (V, V, V)
Output: Prop -/
lemma h_cancel (A B C : V) : (A + B) - (A + C) = B - C := by
  abel

/-- Second covariant derivative: ∇²_{X,Y} Z = ∇_X (∇_Y Z) - ∇_{∇_X Y} Z
Input: (AffineConnection R V, V, V, V)
Output: V -/
def secondCovDeriv (conn : AffineConnection R V) (X Y Z : V) : V :=
  conn.nabla X (conn.nabla Y Z) - conn.nabla (conn.nabla X Y) Z

/-- Prove that the second covariant derivative is mathematically linear with respect to scalar multiplication on the first vector field argument X.
Input: (AffineConnection R V, R, V, V, V)
Output: Prop -/
lemma secondCovDeriv_smul_X (conn : AffineConnection R V) (a : R) (X Y Z : V) :
  secondCovDeriv conn (ScalarMul.smul a X) Y Z = ScalarMul.smul a (secondCovDeriv conn X Y Z) := by
  dsimp [secondCovDeriv]
  rw [conn.nabla_smul_left]
  rw [conn.nabla_smul_left]
  rw [conn.nabla_smul_left]
  rw [h_smul_sub]

/-- Prove that the second covariant derivative is mathematically linear with respect to scalar multiplication on the second vector field argument Y.
Input: (AffineConnection R V, R, V, V, V)
Output: Prop -/
lemma secondCovDeriv_smul_Y (conn : AffineConnection R V) (a : R) (X Y Z : V) :
  secondCovDeriv conn X (ScalarMul.smul a Y) Z = ScalarMul.smul a (secondCovDeriv conn X Y Z) := by
  dsimp [secondCovDeriv]
  have h1 : conn.nabla (ScalarMul.smul a Y) Z = ScalarMul.smul a (conn.nabla Y Z) := conn.nabla_smul_left a Y Z
  rw [h1]
  rw [conn.leibniz]
  have h2 : conn.nabla X (ScalarMul.smul a Y) = ScalarMul.smul (action X a) Y + ScalarMul.smul a (conn.nabla X Y) := conn.leibniz a X Y
  rw [h2]
  rw [conn.nabla_add_left]
  rw [conn.nabla_smul_left]
  rw [conn.nabla_smul_left]
  rw [h_cancel]
  rw [h_smul_sub]

/-- Commutator of the second covariant derivative.
Input: (AffineConnection R V, V, V, V)
Output: V -/
def secondCovDerivCommutator (conn : AffineConnection R V) (X Y Z : V) : V :=
  secondCovDeriv conn X Y Z - secondCovDeriv conn Y X Z
