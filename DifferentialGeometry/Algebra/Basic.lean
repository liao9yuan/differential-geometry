import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Base Algebraic Structures
Defines the algebraic interaction between the function ring R and the vector field module V.
-/

variable (R V : Type*)
variable [CommRing R] [AddCommGroup V] [Module R V]

/-- Derivation action of vector fields on functions.
Input: (V, R)
Output: R -/
class AbstractDerivationAction where
  action : V → R → R

/-- Lie bracket of two vector fields.
Input: (V, V)
Output: V -/
class AbstractLieBracket (V : Type) where
  bracket : V → V → V
