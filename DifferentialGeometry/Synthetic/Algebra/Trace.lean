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



open DifferentialGeometry TensorAlgebra

/--
Universal abstract metric trace operator.
Traces an `AbstractTensor R V r (s+2)` over two covariant indices, yielding `AbstractTensor R V r s`.
It heavily leverages `raise_index` and `contract_general`.
-/
def metric_trace {R V : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
  (metric : MetricDuality R V) {r s : ℕ} (idx1 : Fin (s + 2)) (idx2 : Fin (s + 1)) (T : AbstractTensor R V r (s + 2)) : AbstractTensor R V r s :=
  TensorAlgebra.contract_general (r:=r) (s:=s) (0 : Fin (r + 1)) idx2 (raise_index metric idx1 T)

def contract4 {R V : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
    (T : AbstractTensor R V 4 4) : AbstractTensor R V 0 0 :=
  contract (r:=0) (s:=0) (contract (r:=1) (s:=1) (contract (r:=2) (s:=2) (contract (r:=3) (s:=3) T)))

def tensorInnerProduct {R V : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
    (metric : MetricDuality R V) (T S : AbstractBilinearForm R V) : R :=
  toScalar (
    contract4 (
      tensor_prod (r1:=4) (s1:=0) (r2:=0) (s2:=4)
        (tensor_prod (r1:=2) (s1:=0) (r2:=2) (s2:=0) metric.g_inv metric.g_inv)
        (tensor_prod (r1:=0) (s1:=2) (r2:=0) (s2:=2) T S)
    )
  )

/--
Axiomatizes the geometric definition of trace: the metric trace of a (0,2) abstract tensor
to a scalar is algebraically identically its tensor inner product against the metric's g_tensor:
tr_g(T) = ⟨g, T⟩.
-/
class MetricTraceEvaluationRules (R V : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] (metric : MetricDuality R V) where
  trace_eq_inner_product_g : ∀ (T : AbstractTensor R V 0 2),
    tensor_eval (metric_trace metric (0 : Fin 2) (0 : Fin 1) T) ![] ![] =
    tensorInnerProduct metric metric.toNonDegenerateMetric.toAbstractMetricTensor.g_tensor T

lemma metric_trace_add {R V : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
    (metric : MetricDuality R V) {r s : ℕ} (idx1 : Fin (s + 2)) (idx2 : Fin (s + 1)) (T1 T2 : AbstractTensor R V r (s + 2)) :
    metric_trace metric idx1 idx2 (TensorAlgebra.add T1 T2) = TensorAlgebra.add (metric_trace metric idx1 idx2 T1) (metric_trace metric idx1 idx2 T2) := by
  simp only [metric_trace]
  rw [raise_index_add, TensorAlgebra.contract_general_add (R:=R) (V:=V)]

lemma metric_trace_smul {R V : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
    (metric : MetricDuality R V) {r s : ℕ} (idx1 : Fin (s + 2)) (idx2 : Fin (s + 1)) (c : R) (T : AbstractTensor R V r (s + 2)) :
    metric_trace metric idx1 idx2 (TensorAlgebra.smul c T) = TensorAlgebra.smul c (metric_trace metric idx1 idx2 T) := by
  simp only [metric_trace]
  rw [raise_index_smul, TensorAlgebra.contract_general_smul (R:=R) (V:=V)]
