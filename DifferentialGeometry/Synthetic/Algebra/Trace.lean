import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Module.LinearMap.End
import DifferentialGeometry.Synthetic.Algebra.VectorField
import DifferentialGeometry.Synthetic.Algebra.BilinearForm
import DifferentialGeometry.Synthetic.Algebra.Metric
import DifferentialGeometry.Synthetic.Operator.CovariantDerivative

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# Abstract Trace Concepts

## The Algebraic `AbstractTrace`

We introduce a coordinate-free abstract trace for endomorphisms `(V →ₗ[R] V) → R`.
This is the foundational algebraic primitive from which all tensor contraction
evaluation ultimately derives. It avoids any dependence on frames or bases,
making it valid on non-parallelizable manifolds.

The class `AbstractTraceRules` axiomatizes:
- `tr`: a linear map `(V →ₗ[R] V) →ₗ[R] R`
- `trace_outer`: the outer product trace identity `tr(n.smulRight Y) = n(Y)`,
  which characterizes the trace of a rank-1 endomorphism `X ↦ n(X) • Y`
- `trace_comm`: cyclic commutativity `tr(A ∘ₗ B) = tr(B ∘ₗ A)`

## Metric Trace

The `metric_trace` operator contracts a (0, s+2) tensor over two covariant indices
by raising one index via the metric inverse and then applying `contract_general`.
-/

open DifferentialGeometry TensorAlgebra

/--
Abstract trace of an endomorphism, axiomatized coordinate-free.
`tr` is a linear functional on `End(V)` satisfying the outer product identity
and cyclic commutativity.
-/
class AbstractTraceRules (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] where
  /-- The abstract trace linear map `End(V) → R`. -/
  tr : (V →ₗ[R] V) →ₗ[R] R
  /-- Outer product trace: `tr(X ↦ n(X) • Y) = n(Y)`. -/
  trace_outer : ∀ (Y : V) (n : V →ₗ[R] R), tr (n.smulRight Y) = n Y
  /-- Cyclic commutativity: `tr(A ∘ B) = tr(B ∘ A)`. -/
  trace_comm : ∀ (A B : V →ₗ[R] V), tr (A ∘ₗ B) = tr (B ∘ₗ A)

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

/--
Axiomatizes the evaluation of an endomorphism matrix contraction pointwise without frames.
Contracting a raised (0,2) tensor against itself mathematically evaluates to the inner product
of the corresponding operator's output vectors.
-/
class EndomorphismContractionRules (R V : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] (metric : MetricDuality R V) where
  contract_raise_02_eval : ∀ (T : AbstractTensor R V 0 2) (Z_op : V → V),
    (∀ X Y, tensor_eval T ![X, Y] ![] = metric.g X (Z_op Y)) →
    ∀ X Y, tensor_eval (TensorAlgebra.contract (r:=0) (s:=2) (TensorAlgebra.tensor_prod (r1:=1) (s1:=1) (r2:=0) (s2:=2) (raise_index metric (0 : Fin 2) T) T)) ![X, Y] ![] = metric.g (Z_op X) (Z_op Y)

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

section NablaMetricTrace

/-!
## ∇ commutes with metric_trace

Helper lemmas and the main theorem showing the covariant derivative
algebraically commutes with the metric trace operator.
-/

open AbstractDerivationAction

private lemma smul_zero_eq_zero {R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup V] [Module R V] [TensorAlgebra R V]
    {r s : ℕ} (T : AbstractTensor R V r s) :
    TensorAlgebra.smul (0 : R) T = 0 := by
  rw [← TensorAlgebra.fromData_toData (TensorAlgebra.smul (0 : R) T),
      ← TensorAlgebra.fromData_toData (0 : AbstractTensor R V r s)]
  congr 1
  rw [TensorAlgebra.toData_smul, zero_smul]
  exact (TensorAlgebra.toData_fromData (0 : TensorData R V r s)).symm

private lemma tensor_prod_zero_left {R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup V] [Module R V] [TensorAlgebra R V]
    {r1 s1 r2 s2 : ℕ} (T : AbstractTensor R V r2 s2) :
    TensorAlgebra.tensor_prod (0 : AbstractTensor R V r1 s1) T = 0 := by
  have h1 : (0 : AbstractTensor R V r1 s1) = TensorAlgebra.smul (0 : R) (0 : AbstractTensor R V r1 s1) :=
    (smul_zero_eq_zero _).symm
  rw [h1, TensorAlgebra.tensor_prod_smul_left, smul_zero_eq_zero]

private lemma add_zero_left {R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup V] [Module R V] [TensorAlgebra R V]
    {r s : ℕ} (T : AbstractTensor R V r s) :
    TensorAlgebra.add (0 : AbstractTensor R V r s) T = T := by
  have h0 : TensorAlgebra.toData (0 : AbstractTensor R V r s) = 0 := by
    change TensorAlgebra.toData (TensorAlgebra.fromData (0 : TensorData R V r s)) = 0
    exact TensorAlgebra.toData_fromData 0
  have h1 : TensorAlgebra.toData (TensorAlgebra.add (0 : AbstractTensor R V r s) T) = TensorAlgebra.toData T := by
    rw [TensorAlgebra.toData_add, h0, zero_add]
  rw [← TensorAlgebra.fromData_toData (TensorAlgebra.add 0 T), h1, TensorAlgebra.fromData_toData]

private lemma genericCovDeriv_contract_general
    {R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup V] [Module R V] [TensorAlgebra R V] [AbstractDerivationAction R V]
    {conn : AbstractAffineConnection R V} [AffineTensorCalculus conn]
    (X : V) {r s : ℕ} (i : Fin (r + 1)) (j : Fin (s + 1))
    (T : AbstractTensor R V (r + 1) (s + 1)) :
    genericCovDeriv conn X (TensorAlgebra.contract_general i j T) =
    TensorAlgebra.contract_general i j (genericCovDeriv conn X T) := by
  simp only [TensorAlgebra.contract_general, genericCovDeriv]
  rw [AffineTensorCalculus.nabla_contract,
      AffineTensorCalculus.nabla_swap_covariant,
      AffineTensorCalculus.nabla_swap_contravariant]

-- If nabla A = B, then nabla (cast h A) = cast h B
private lemma nabla_cast_eq
    {R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup V] [Module R V] [TensorAlgebra R V] [AbstractDerivationAction R V]
    (conn : AbstractAffineConnection R V) [AffineTensorCalculus conn]
    (X : V) {r r' s s' : ℕ} (hr : r = r') (hs : s = s')
    (A B : AbstractTensor R V r s)
    (h_eq : AffineTensorCalculus.nabla_tensor conn X A = B)
    (h : AbstractTensor R V r s = AbstractTensor R V r' s') :
    AffineTensorCalculus.nabla_tensor conn X (cast h A) = cast h B := by
  subst hr; subst hs; exact h_eq

private lemma genericCovDeriv_raise_index
    {R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup V] [Module R V] [TensorAlgebra R V] [AbstractDerivationAction R V]
    (metric : MetricDuality R V)
    {conn : AbstractAffineConnection R V} [AffineTensorCalculus conn]
    (X : V) {r s : ℕ} (idx : Fin (s + 1))
    (T : AbstractTensor R V r (s + 1))
    (h_ginv : AffineTensorCalculus.nabla_tensor conn X metric.g_inv = 0) :
    genericCovDeriv conn X (raise_index metric idx T) =
    raise_index metric idx (genericCovDeriv conn X T) := by
  -- Key fact: nabla distributes through tensor_prod g_inv, with g_inv parallel
  have key : AffineTensorCalculus.nabla_tensor conn X (TensorAlgebra.tensor_prod metric.g_inv T) =
    TensorAlgebra.tensor_prod metric.g_inv (AffineTensorCalculus.nabla_tensor conn X T) := by
    rw [AffineTensorCalculus.nabla_tensor_prod, h_ginv, tensor_prod_zero_left, add_zero_left]
  -- Unfold raise_index and genericCovDeriv
  simp only [raise_index, genericCovDeriv]
  -- Pull nabla through the inner contract_general (using swap axioms)
  simp only [TensorAlgebra.contract_general]
  rw [AffineTensorCalculus.nabla_contract,
      AffineTensorCalculus.nabla_swap_covariant,
      AffineTensorCalculus.nabla_swap_contravariant]
  -- Now nabla is applied to the cast (tensor_prod g_inv T)
  -- Use nabla_cast_eq to push nabla through cast and apply key
  congr 1; congr 1; congr 1
  exact nabla_cast_eq conn X (by omega) (by omega) _ _ key _

lemma nabla_metric_trace
    {R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup V] [Module R V] [TensorAlgebra R V]
    [AbstractDerivationAction R V]
    (metric : MetricDuality R V)
    (conn : AbstractAffineConnection R V)
    [AffineTensorCalculus conn]
    [MetricCompatible conn metric.toNonDegenerateMetric.toAbstractMetricTensor]
    (X : V) {r s : ℕ} (idx1 : Fin (s + 2)) (idx2 : Fin (s + 1))
    (T : AbstractTensor R V r (s + 2))
    (h_ginv : AffineTensorCalculus.nabla_tensor conn X metric.g_inv = 0) :
    genericCovDeriv conn X (metric_trace metric idx1 idx2 T) =
    metric_trace metric idx1 idx2 (genericCovDeriv conn X T) := by
  -- Step 1: Unfold metric_trace
  simp only [metric_trace]
  -- Step 2: Pull genericCovDeriv through the outer contract_general
  rw [genericCovDeriv_contract_general]
  -- Step 3: Reduce to showing raise_index commutes with genericCovDeriv
  congr 1
  -- Step 4: Apply the raise_index commutativity lemma
  exact genericCovDeriv_raise_index metric X idx1 T h_ginv

end NablaMetricTrace
