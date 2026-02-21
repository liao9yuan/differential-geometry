set_option autoImplicit false

/-!
# Abstract Trace Operators
Provides algebraic hooks for tracing endomorphisms.
-/

-- Abstract Trace Operator (For future V* ⊗ V)
class TraceOperator (R V : Type) where
  trace : (V → V) → R
