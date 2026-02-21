set_option autoImplicit false

/-!
# Base Algebraic Structures
Completely self-contained. Defines the core algebraic interaction
between the ring of functions (R) and the module of vector fields (V).
-/

-- 1. Scalar Multiplication
class ScalarMul (R : Type) (V : Type) where
  smul : R → V → V

infixr:73 " • " => ScalarMul.smul

variable (R V : Type)

-- 2. Vector Fields as Derivations
class DerivationAction where
  action : V → R → R

-- 3. Lie Bracket of Vector Fields
class LieBracket (V : Type) where
  bracket : V → V → V
