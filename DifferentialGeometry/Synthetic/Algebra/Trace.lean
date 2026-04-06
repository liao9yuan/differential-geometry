import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic
import DifferentialGeometry.Synthetic.Algebra.VectorField
import DifferentialGeometry.Synthetic.Algebra.BilinearForm
import DifferentialGeometry.Synthetic.Algebra.Metric

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# Abstract Trace Concepts
Abstract trace operations over tensors and bilinear forms.
-/

/-- Abstract Trace Operator mapping linear endomorphisms to R. -/
class TraceOperator (R V : Type) where
  trace : (V → V) → R

/-- Trace linearity rules mapping the general trace operator's linearity properties. -/
class TraceLinearityRules (R V : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TraceOperator R V] where
  trace_add : ∀ {A B : V → V}, (TraceOperator.trace (A + B) : R) = TraceOperator.trace A + TraceOperator.trace B
  trace_smul : ∀ {c : R} {A : V → V}, (TraceOperator.trace (fun X => c • (A X)) : R) = c * TraceOperator.trace A
  trace_comm : ∀ {A B : V → V}, (TraceOperator.trace (A ∘ B) : R) = TraceOperator.trace (B ∘ A)

--- TENSOR CONTRACTION 1 (Trace over 1st input and target slot) ---

/-- Abstract trace operator for a (1,4)-tensor mapping V^4 to V.
    Contracts the first argument (differentiation slot) and the fourth argument (target slot). -/
class Tensor14Trace (R V : Type) where
  trace_1_4 : (V → V → V → V → V) → (V → V → V → R)

/-- Linearity of trace_1_4. -/
class Tensor14TraceLinearity (R V : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Tensor14Trace R V] where
  tr_add : ∀ (T₁ T₂ : V → V → V → V → V), (Tensor14Trace.trace_1_4 (fun x y z w => T₁ x y z w + T₂ x y z w) : V → V → V → R) = fun y z w => Tensor14Trace.trace_1_4 T₁ y z w + Tensor14Trace.trace_1_4 T₂ y z w
  tr_zero : (Tensor14Trace.trace_1_4 (fun _ _ _ _ => (0 : V)) : V → V → V → R) = fun _ _ _ => (0 : R)

--- TENSOR CONTRACTION 2 (Bilinear trace over 2 inputs) ---

/-- Abstract trace operator for bilinear forms Mapping V x V to R. -/
class BilinearTrace (R V : Type) where
  tr : (V → V → R) → R

/-- Trace linearity rules mapping the general trace operator's linearity properties. -/
class BilinearTraceLinearity (R V : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [BilinearTrace R V] where
  tr_add : ∀ (T₁ T₂ : V → V → R), (BilinearTrace.tr (fun Y Z => T₁ Y Z + T₂ Y Z) : R) = BilinearTrace.tr T₁ + BilinearTrace.tr T₂
  tr_sub : ∀ (T₁ T₂ : V → V → R), (BilinearTrace.tr (fun Y Z => T₁ Y Z - T₂ Y Z) : R) = BilinearTrace.tr T₁ - BilinearTrace.tr T₂
  tr_zero : (BilinearTrace.tr (fun (_ _ : V) => (0 : R)) : R) = (0 : R)

open DifferentialGeometry TensorAlgebra

-- Axiomatic rules for the trace of rank-1 operators to support divergence product rule.
class MetricTraceRankOneRules (R V : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] (metric : AbstractMetricTensor R V) [MetricTraceOperator R V metric] where
  trace_rank_one : ∀ U W : V, MetricTraceOperator.metric_trace metric (fun Y Z => metric.g U Y * metric.g W Z) = metric.g U W
