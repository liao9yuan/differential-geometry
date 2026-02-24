import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic

set_option autoImplicit false
set_option linter.style.longLine false

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
variable [CommRing R] [AddCommGroup V] [Module R V]

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

class LieDerivation (R V : Type) [CommRing R] [DerivationAction R V] [LieBracket V] where
  bracket_action : ∀ X Y : V, ∀ u : R,
    DerivationAction.action (LieBracket.bracket X Y) u =
    DerivationAction.action X (DerivationAction.action Y u) - DerivationAction.action Y (DerivationAction.action X u)

class ActionLinear (R V : Type) [CommRing R] [AddCommGroup V] [DerivationAction R V] where
  action_add : ∀ X Y : V, ∀ u : R,
    DerivationAction.action (X + Y) u = DerivationAction.action X u + DerivationAction.action Y u
