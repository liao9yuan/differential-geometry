import Mathlib.Algebra.Module.Basic
import DifferentialGeometry.Algebra.Basic

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

/-- Trace linearity rules mapping the general trace operator's linearity properties. -/
class TraceLinearityRules (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] [ScalarMul R V]
  [TraceOperator R V] where
  trace_add : ∀ {A B : V → V}, (TraceOperator.trace (A + B) : R) =
    TraceOperator.trace A + TraceOperator.trace B
  trace_smul : ∀ {c : R} {A : V → V}, (TraceOperator.trace (fun X => ScalarMul.smul c (A X)) : R) =
    c * TraceOperator.trace A
  trace_comm : ∀ {A B : V → V}, (TraceOperator.trace (A ∘ B) : R) =
    TraceOperator.trace (B ∘ A)
