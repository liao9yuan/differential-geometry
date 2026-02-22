set_option autoImplicit false

/-!
# Abstract Trace Operators
Algebraic definition of trace operators on endomorphisms.
-/

/-- Linear trace operator on vector field endomorphisms.
Input: (V → V)
Output: R -/
class TraceOperator (R V : Type) where
  trace : (V → V) → R
