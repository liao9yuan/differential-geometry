import DifferentialGeometry.Synthetic.Geometry.Connection
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Algebra.Module.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# Second Covariant Derivative
-/

section SecondCovDeriv

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- Second covariant derivative: ∇²_{X,Y} Z = ∇_X(∇_Y Z) - ∇_{∇_X Y} Z. -/
def secondCovDeriv (conn : V → V → V) (X Y Z : V) : V :=
  conn X (conn Y Z) - conn (conn X Y) Z

/-- The second covariant derivative is R-linear in X. -/
lemma secondCovDeriv_smul_X
    (conn : V → V → V)
    (conn_smul_left : ∀ (f : R) (X Z : V), conn (f • X) Z = f • conn X Z)
    (a : R) (X Y Z : V) :
    secondCovDeriv conn (a • X) Y Z = a • (secondCovDeriv conn X Y Z) := by
  dsimp [secondCovDeriv]
  rw [conn_smul_left, conn_smul_left, conn_smul_left]
  exact (smul_sub a _ _).symm

/-- The second covariant derivative is R-linear in Y. -/
lemma secondCovDeriv_smul_Y
    (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (conn_add_left : ∀ X Y Z : V, conn (X + Y) Z = conn X Z + conn Y Z)
    (conn_smul_left : ∀ (f : R) (X Z : V), conn (f • X) Z = f • conn X Z)
    (conn_leibniz : ∀ (f : R) (X Y : V), conn X (f • Y) = action emb X f • Y + f • conn X Y)
    (a : R) (X Y Z : V) :
    secondCovDeriv conn X (a • Y) Z = a • (secondCovDeriv conn X Y Z) := by
  dsimp [secondCovDeriv]
  rw [conn_smul_left a Y Z, conn_leibniz a X (conn Y Z),
      conn_leibniz a X Y, conn_add_left,
      conn_smul_left, conn_smul_left]
  simp only [smul_sub]; abel

-- `secondCovDerivCommutator` is defined in Connection.lean.

end SecondCovDeriv
