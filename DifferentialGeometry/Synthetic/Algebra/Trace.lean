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
