set_option autoImplicit false

/-!
# Base Algebraic Structures
Defines the algebraic interaction between the function ring R and the vector field module V.
-/

/-- Scalar multiplication action of R on V.
Input: (R, V)
Output: V -/
class ScalarMul (R : Type) (V : Type) where
  smul : R → V → V

infixr:73 " • " => ScalarMul.smul

variable (R V : Type)

/-- Derivation action of vector fields on functions.
Input: (V, R)
Output: R -/
class DerivationAction where
  action : V → R → R

/-- Lie bracket of two vector fields.
Input: (V, V)
Output: V -/
class LieBracket (V : Type) where
  bracket : V → V → V
