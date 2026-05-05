import DifferentialGeometry.Synthetic.Algebra.Metric

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open SyntheticTensor

/-!
# Iterated Metric Traces

This file contains small, reusable wrappers for iterated metric traces. The
single metric trace is already implemented in `Algebra/Metric.lean` as
`metric_trace`, using `MetricDuality.g_inv`.

The wrappers here are deliberately concrete for `(0,4)` and `(0,5)` tensors,
which are the shapes needed for curvature and covariant curvature derivative
contractions. The Fubini/coherence predicates name the remaining abstract trace
law: two iterated metric traces should agree after the corresponding slot
transposition. For concrete traces this is a finite-index reindexing theorem;
for the current `AbstractTrace` interface it is an additional coherence rule,
not something forced by the existing single-contraction axioms alone.
-/

namespace SyntheticTensor

section DoubleMetricTrace

variable {R V : Type*}
variable [CommRing R] [AddCommGroup V] [Module R V]

/-- Iterated metric trace of a `(0,4)` tensor. The first trace removes two
covariant slots from the original tensor; the second trace removes the two
remaining covariant slots. -/
noncomputable def doubleMetricTrace04
    (met : MetricDuality R V) (atr : AbstractTrace R V)
    (first_hi : Fin 4) (first_lo : Fin 3)
    (second_hi : Fin 2) (second_lo : Fin 1)
    (T : TensorData R V 0 4) : R :=
  metric_trace met atr second_hi second_lo
    (metric_trace met atr first_hi first_lo T) ![] ![]

theorem doubleMetricTrace04_eval
    (met : MetricDuality R V) (atr : AbstractTrace R V)
    (first_hi : Fin 4) (first_lo : Fin 3)
    (second_hi : Fin 2) (second_lo : Fin 1)
    (T : TensorData R V 0 4) :
    doubleMetricTrace04 met atr first_hi first_lo second_hi second_lo T =
      metric_trace met atr second_hi second_lo
        (metric_trace met atr first_hi first_lo T) ![] ![] := by
  rfl

/-- Double metric trace of a `(0,4)` tensor is additive. -/
theorem doubleMetricTrace04_add
    (met : MetricDuality R V) (atr : AbstractTrace R V)
    (first_hi : Fin 4) (first_lo : Fin 3)
    (second_hi : Fin 2) (second_lo : Fin 1)
    (T₁ T₂ : TensorData R V 0 4) :
    doubleMetricTrace04 met atr first_hi first_lo second_hi second_lo (T₁ + T₂) =
      doubleMetricTrace04 met atr first_hi first_lo second_hi second_lo T₁ +
        doubleMetricTrace04 met atr first_hi first_lo second_hi second_lo T₂ := by
  simp [doubleMetricTrace04, metric_trace_add]

/-- Double metric trace of a `(0,4)` tensor commutes with scalar multiplication. -/
theorem doubleMetricTrace04_smul
    (met : MetricDuality R V) (atr : AbstractTrace R V)
    (first_hi : Fin 4) (first_lo : Fin 3)
    (second_hi : Fin 2) (second_lo : Fin 1)
    (c : R) (T : TensorData R V 0 4) :
    doubleMetricTrace04 met atr first_hi first_lo second_hi second_lo (c • T) =
      c * doubleMetricTrace04 met atr first_hi first_lo second_hi second_lo T := by
  simp [doubleMetricTrace04, metric_trace_smul, smul_eq_mul]

/-- Double metric trace of a `(0,4)` zero tensor is zero. -/
theorem doubleMetricTrace04_zero
    (met : MetricDuality R V) (atr : AbstractTrace R V)
    (first_hi : Fin 4) (first_lo : Fin 3)
    (second_hi : Fin 2) (second_lo : Fin 1) :
    doubleMetricTrace04 met atr first_hi first_lo second_hi second_lo
        (0 : TensorData R V 0 4) = 0 := by
  simp [doubleMetricTrace04, metric_trace_zero]

/-- Double metric trace of a `(0,4)` tensor commutes with negation. -/
theorem doubleMetricTrace04_neg
    (met : MetricDuality R V) (atr : AbstractTrace R V)
    (first_hi : Fin 4) (first_lo : Fin 3)
    (second_hi : Fin 2) (second_lo : Fin 1)
    (T : TensorData R V 0 4) :
    doubleMetricTrace04 met atr first_hi first_lo second_hi second_lo (-T) =
      - doubleMetricTrace04 met atr first_hi first_lo second_hi second_lo T := by
  rw [← neg_one_smul R T]
  rw [show -doubleMetricTrace04 met atr first_hi first_lo second_hi second_lo T =
      (-1 : R) * doubleMetricTrace04 met atr first_hi first_lo second_hi second_lo T by
    simp]
  exact doubleMetricTrace04_smul met atr first_hi first_lo second_hi second_lo (-1 : R) T

/-- Double metric trace of a `(0,4)` tensor commutes with subtraction. -/
theorem doubleMetricTrace04_sub
    (met : MetricDuality R V) (atr : AbstractTrace R V)
    (first_hi : Fin 4) (first_lo : Fin 3)
    (second_hi : Fin 2) (second_lo : Fin 1)
    (T₁ T₂ : TensorData R V 0 4) :
    doubleMetricTrace04 met atr first_hi first_lo second_hi second_lo (T₁ - T₂) =
      doubleMetricTrace04 met atr first_hi first_lo second_hi second_lo T₁ -
        doubleMetricTrace04 met atr first_hi first_lo second_hi second_lo T₂ := by
  rw [sub_eq_add_neg, sub_eq_add_neg, doubleMetricTrace04_add, doubleMetricTrace04_neg]

/-- Iterated metric trace of a `(0,5)` tensor, leaving one covariant slot. This
is the tensor shape needed for the contracted second Bianchi identity. -/
noncomputable def doubleMetricTrace05
    (met : MetricDuality R V) (atr : AbstractTrace R V)
    (first_hi : Fin 5) (first_lo : Fin 4)
    (second_hi : Fin 3) (second_lo : Fin 2)
    (T : TensorData R V 0 5) : TensorData R V 0 1 :=
  metric_trace met atr second_hi second_lo
    (metric_trace met atr first_hi first_lo T)

theorem doubleMetricTrace05_eval
    (met : MetricDuality R V) (atr : AbstractTrace R V)
    (first_hi : Fin 5) (first_lo : Fin 4)
    (second_hi : Fin 3) (second_lo : Fin 2)
    (T : TensorData R V 0 5) (X : V) :
    doubleMetricTrace05 met atr first_hi first_lo second_hi second_lo T ![X] ![] =
      metric_trace met atr second_hi second_lo
        (metric_trace met atr first_hi first_lo T) ![X] ![] := by
  rfl

/-- Double metric trace of a `(0,5)` tensor is additive. -/
theorem doubleMetricTrace05_add
    (met : MetricDuality R V) (atr : AbstractTrace R V)
    (first_hi : Fin 5) (first_lo : Fin 4)
    (second_hi : Fin 3) (second_lo : Fin 2)
    (T₁ T₂ : TensorData R V 0 5) :
    doubleMetricTrace05 met atr first_hi first_lo second_hi second_lo (T₁ + T₂) =
      doubleMetricTrace05 met atr first_hi first_lo second_hi second_lo T₁ +
        doubleMetricTrace05 met atr first_hi first_lo second_hi second_lo T₂ := by
  simp [doubleMetricTrace05, metric_trace_add]

/-- Double metric trace of a `(0,5)` tensor commutes with scalar multiplication. -/
theorem doubleMetricTrace05_smul
    (met : MetricDuality R V) (atr : AbstractTrace R V)
    (first_hi : Fin 5) (first_lo : Fin 4)
    (second_hi : Fin 3) (second_lo : Fin 2)
    (c : R) (T : TensorData R V 0 5) :
    doubleMetricTrace05 met atr first_hi first_lo second_hi second_lo (c • T) =
      c • doubleMetricTrace05 met atr first_hi first_lo second_hi second_lo T := by
  simp [doubleMetricTrace05, metric_trace_smul]

/-- Double metric trace of a `(0,5)` zero tensor is zero. -/
theorem doubleMetricTrace05_zero
    (met : MetricDuality R V) (atr : AbstractTrace R V)
    (first_hi : Fin 5) (first_lo : Fin 4)
    (second_hi : Fin 3) (second_lo : Fin 2) :
    doubleMetricTrace05 met atr first_hi first_lo second_hi second_lo
        (0 : TensorData R V 0 5) = 0 := by
  simp [doubleMetricTrace05, metric_trace_zero]

/-- Double metric trace of a `(0,5)` tensor commutes with negation. -/
theorem doubleMetricTrace05_neg
    (met : MetricDuality R V) (atr : AbstractTrace R V)
    (first_hi : Fin 5) (first_lo : Fin 4)
    (second_hi : Fin 3) (second_lo : Fin 2)
    (T : TensorData R V 0 5) :
    doubleMetricTrace05 met atr first_hi first_lo second_hi second_lo (-T) =
      - doubleMetricTrace05 met atr first_hi first_lo second_hi second_lo T := by
  rw [← neg_one_smul R T, ← neg_one_smul R
    (doubleMetricTrace05 met atr first_hi first_lo second_hi second_lo T)]
  exact doubleMetricTrace05_smul met atr first_hi first_lo second_hi second_lo (-1 : R) T

/-- Double metric trace of a `(0,5)` tensor commutes with subtraction. -/
theorem doubleMetricTrace05_sub
    (met : MetricDuality R V) (atr : AbstractTrace R V)
    (first_hi : Fin 5) (first_lo : Fin 4)
    (second_hi : Fin 3) (second_lo : Fin 2)
    (T₁ T₂ : TensorData R V 0 5) :
    doubleMetricTrace05 met atr first_hi first_lo second_hi second_lo (T₁ - T₂) =
      doubleMetricTrace05 met atr first_hi first_lo second_hi second_lo T₁ -
        doubleMetricTrace05 met atr first_hi first_lo second_hi second_lo T₂ := by
  rw [sub_eq_add_neg, sub_eq_add_neg, doubleMetricTrace05_add, doubleMetricTrace05_neg]

/-- Coherence predicate for two ways of double-tracing a `(0,4)` tensor.
Concrete realizations should prove instances of this from the coordinate
definition of `AbstractTrace.tensor_contract`. -/
def DoubleMetricTrace04Fubini
    (met : MetricDuality R V) (atr : AbstractTrace R V)
    (T : TensorData R V 0 4)
    (a_hi : Fin 4) (a_lo : Fin 3) (a_hi' : Fin 2) (a_lo' : Fin 1)
    (b_hi : Fin 4) (b_lo : Fin 3) (b_hi' : Fin 2) (b_lo' : Fin 1) : Prop :=
  doubleMetricTrace04 met atr a_hi a_lo a_hi' a_lo' T =
    doubleMetricTrace04 met atr b_hi b_lo b_hi' b_lo' T

/-- Coherence predicate for two ways of double-tracing a `(0,5)` tensor. This
is the Fubini/swap rule needed by the contracted-Bianchi contraction. -/
def DoubleMetricTrace05Fubini
    (met : MetricDuality R V) (atr : AbstractTrace R V)
    (T : TensorData R V 0 5)
    (a_hi : Fin 5) (a_lo : Fin 4) (a_hi' : Fin 3) (a_lo' : Fin 2)
    (b_hi : Fin 5) (b_lo : Fin 4) (b_hi' : Fin 3) (b_lo' : Fin 2) : Prop :=
  doubleMetricTrace05 met atr a_hi a_lo a_hi' a_lo' T =
    doubleMetricTrace05 met atr b_hi b_lo b_hi' b_lo' T

theorem doubleMetricTrace04_fubini_apply
    (met : MetricDuality R V) (atr : AbstractTrace R V)
    (T : TensorData R V 0 4)
    (a_hi : Fin 4) (a_lo : Fin 3) (a_hi' : Fin 2) (a_lo' : Fin 1)
    (b_hi : Fin 4) (b_lo : Fin 3) (b_hi' : Fin 2) (b_lo' : Fin 1)
    (h : DoubleMetricTrace04Fubini met atr T a_hi a_lo a_hi' a_lo'
      b_hi b_lo b_hi' b_lo') :
    doubleMetricTrace04 met atr a_hi a_lo a_hi' a_lo' T =
      doubleMetricTrace04 met atr b_hi b_lo b_hi' b_lo' T :=
  h

theorem doubleMetricTrace05_fubini_apply
    (met : MetricDuality R V) (atr : AbstractTrace R V)
    (T : TensorData R V 0 5)
    (a_hi : Fin 5) (a_lo : Fin 4) (a_hi' : Fin 3) (a_lo' : Fin 2)
    (b_hi : Fin 5) (b_lo : Fin 4) (b_hi' : Fin 3) (b_lo' : Fin 2)
    (h : DoubleMetricTrace05Fubini met atr T a_hi a_lo a_hi' a_lo'
      b_hi b_lo b_hi' b_lo') :
    doubleMetricTrace05 met atr a_hi a_lo a_hi' a_lo' T =
      doubleMetricTrace05 met atr b_hi b_lo b_hi' b_lo' T :=
  h

/-- The four index choices defining a double metric trace of a `(0,5)` tensor. -/
structure DoubleMetricTrace05Pattern where
  first_hi : Fin 5
  first_lo : Fin 4
  second_hi : Fin 3
  second_lo : Fin 2

namespace DoubleMetricTrace05Pattern

/-!
The contracted second Bianchi identity uses a lowered `(0,5)` tensor with slot
order

```text
T(A, X, Y, Z, W) = (∇_A Rm)(X, Y, Z, W).
```

The first divergence trace contracts original slots `(0, 3)` and `(1, 4)`,
leaving original slot `2`. The Fubini divergence pattern performs the same two
contractions in the opposite order. The scalar-gradient pattern contracts
original slots `(1, 3)` and `(2, 4)`, leaving original slot `0`.
-/

/-- Contract original slots `(0, 3)` and `(1, 4)` of a lowered `(0,5)`
curvature-derivative tensor, leaving original slot `2`. This is the first
divergence pattern in the contracted second Bianchi calculation. -/
def contractedBianchiDivPattern : DoubleMetricTrace05Pattern where
  first_hi := 3
  first_lo := 2
  second_hi := 2
  second_lo := 0

/-- The same double trace as `contractedBianchiDivPattern`, with the trace
order reversed.

The concrete `metric_trace` implementation first raises the selected covariant
slot and then contracts the new contravariant slot with a second covariant
slot. The indices below therefore encode the original-slot contractions
`(1, 4)` followed by `(0, 3)`, leaving original slot `2`. -/
def contractedBianchiDivFubiniPattern : DoubleMetricTrace05Pattern where
  first_hi := 4
  first_lo := 0
  second_hi := 2
  second_lo := 0

/-- Contract original slots `(1, 3)` and `(2, 4)` of a lowered `(0,5)`
curvature-derivative tensor, leaving original slot `0`. With the sign
convention used downstream, this is the scalar-gradient pattern in the
contracted second Bianchi calculation. -/
def contractedBianchiGradPattern : DoubleMetricTrace05Pattern where
  first_hi := 3
  first_lo := 0
  second_hi := 2
  second_lo := 1

/-- Apply a `(0,5)` double-trace pattern, leaving one vector slot. -/
noncomputable def tensor
    (p : DoubleMetricTrace05Pattern)
    (met : MetricDuality R V) (atr : AbstractTrace R V)
    (T : TensorData R V 0 5) : TensorData R V 0 1 :=
  doubleMetricTrace05 met atr p.first_hi p.first_lo p.second_hi p.second_lo T

/-- Apply a `(0,5)` double-trace pattern and evaluate the remaining slot. -/
noncomputable def apply
    (p : DoubleMetricTrace05Pattern)
    (met : MetricDuality R V) (atr : AbstractTrace R V)
    (T : TensorData R V 0 5) (X : V) : R :=
  p.tensor met atr T ![X] ![]

/-- Fubini/coherence between two `(0,5)` double-trace patterns on the same
tensor. -/
def Fubini
    (p q : DoubleMetricTrace05Pattern)
    (met : MetricDuality R V) (atr : AbstractTrace R V)
    (T : TensorData R V 0 5) : Prop :=
  DoubleMetricTrace05Fubini met atr T p.first_hi p.first_lo p.second_hi p.second_lo
    q.first_hi q.first_lo q.second_hi q.second_lo

theorem tensor_eq_of_fubini
    (p q : DoubleMetricTrace05Pattern)
    (met : MetricDuality R V) (atr : AbstractTrace R V)
    (T : TensorData R V 0 5)
    (h : p.Fubini q met atr T) :
    p.tensor met atr T = q.tensor met atr T :=
  h

theorem apply_eq_of_fubini
    (p q : DoubleMetricTrace05Pattern)
    (met : MetricDuality R V) (atr : AbstractTrace R V)
    (T : TensorData R V 0 5)
    (h : p.Fubini q met atr T) (X : V) :
    p.apply met atr T X = q.apply met atr T X := by
  exact congr_arg (fun S : TensorData R V 0 1 => S ![X] ![]) (p.tensor_eq_of_fubini q met atr T h)

/-- Patterned double metric trace is additive. -/
theorem tensor_add
    (p : DoubleMetricTrace05Pattern)
    (met : MetricDuality R V) (atr : AbstractTrace R V)
    (T₁ T₂ : TensorData R V 0 5) :
    p.tensor met atr (T₁ + T₂) = p.tensor met atr T₁ + p.tensor met atr T₂ := by
  exact doubleMetricTrace05_add met atr p.first_hi p.first_lo p.second_hi p.second_lo T₁ T₂

/-- Patterned double metric trace commutes with scalar multiplication. -/
theorem tensor_smul
    (p : DoubleMetricTrace05Pattern)
    (met : MetricDuality R V) (atr : AbstractTrace R V)
    (c : R) (T : TensorData R V 0 5) :
    p.tensor met atr (c • T) = c • p.tensor met atr T := by
  exact doubleMetricTrace05_smul met atr p.first_hi p.first_lo p.second_hi p.second_lo c T

/-- Patterned double metric trace sends the zero tensor to zero. -/
theorem tensor_zero
    (p : DoubleMetricTrace05Pattern)
    (met : MetricDuality R V) (atr : AbstractTrace R V) :
    p.tensor met atr (0 : TensorData R V 0 5) = 0 := by
  exact doubleMetricTrace05_zero met atr p.first_hi p.first_lo p.second_hi p.second_lo

/-- Patterned double metric trace commutes with negation. -/
theorem tensor_neg
    (p : DoubleMetricTrace05Pattern)
    (met : MetricDuality R V) (atr : AbstractTrace R V)
    (T : TensorData R V 0 5) :
    p.tensor met atr (-T) = -p.tensor met atr T := by
  exact doubleMetricTrace05_neg met atr p.first_hi p.first_lo p.second_hi p.second_lo T

/-- Patterned double metric trace commutes with subtraction. -/
theorem tensor_sub
    (p : DoubleMetricTrace05Pattern)
    (met : MetricDuality R V) (atr : AbstractTrace R V)
    (T₁ T₂ : TensorData R V 0 5) :
    p.tensor met atr (T₁ - T₂) = p.tensor met atr T₁ - p.tensor met atr T₂ := by
  exact doubleMetricTrace05_sub met atr p.first_hi p.first_lo p.second_hi p.second_lo T₁ T₂

/-- Evaluation of a patterned double metric trace is additive. -/
theorem apply_add
    (p : DoubleMetricTrace05Pattern)
    (met : MetricDuality R V) (atr : AbstractTrace R V)
    (T₁ T₂ : TensorData R V 0 5) (X : V) :
    p.apply met atr (T₁ + T₂) X =
      p.apply met atr T₁ X + p.apply met atr T₂ X := by
  unfold apply
  simpa only [Pi.add_apply, MultilinearMap.add_apply] using
    congr_arg (fun S : TensorData R V 0 1 => S ![X] ![]) (p.tensor_add met atr T₁ T₂)

/-- Evaluation of a patterned double metric trace commutes with scalar multiplication. -/
theorem apply_smul
    (p : DoubleMetricTrace05Pattern)
    (met : MetricDuality R V) (atr : AbstractTrace R V)
    (c : R) (T : TensorData R V 0 5) (X : V) :
    p.apply met atr (c • T) X = c * p.apply met atr T X := by
  unfold apply
  simpa only [MultilinearMap.smul_apply, smul_eq_mul] using
    congr_arg (fun S : TensorData R V 0 1 => S ![X] ![]) (p.tensor_smul met atr c T)

/-- Evaluation of a patterned double metric trace sends the zero tensor to zero. -/
theorem apply_zero
    (p : DoubleMetricTrace05Pattern)
    (met : MetricDuality R V) (atr : AbstractTrace R V) (X : V) :
    p.apply met atr (0 : TensorData R V 0 5) X = 0 := by
  unfold apply
  simpa using congr_arg (fun S : TensorData R V 0 1 => S ![X] ![]) (p.tensor_zero met atr)

/-- Evaluation of a patterned double metric trace commutes with negation. -/
theorem apply_neg
    (p : DoubleMetricTrace05Pattern)
    (met : MetricDuality R V) (atr : AbstractTrace R V)
    (T : TensorData R V 0 5) (X : V) :
    p.apply met atr (-T) X = -p.apply met atr T X := by
  rw [← neg_one_smul R T]
  rw [show -p.apply met atr T X = (-1 : R) * p.apply met atr T X by simp]
  exact p.apply_smul met atr (-1 : R) T X

/-- Evaluation of a patterned double metric trace commutes with subtraction. -/
theorem apply_sub
    (p : DoubleMetricTrace05Pattern)
    (met : MetricDuality R V) (atr : AbstractTrace R V)
    (T₁ T₂ : TensorData R V 0 5) (X : V) :
    p.apply met atr (T₁ - T₂) X =
      p.apply met atr T₁ X - p.apply met atr T₂ X := by
  rw [sub_eq_add_neg, sub_eq_add_neg, apply_add, apply_neg]

end DoubleMetricTrace05Pattern

/-- Low-level bridge class for metric double-trace Fubini.

The parent `HasTensorContractFubini atr` is the raw Fubini law for adjacent
`AbstractTrace.tensor_contract`s. The extra field records the corresponding
coherence after metric raising has inserted inverse-metric tensors and after
the selected slot permutations have been applied.

Concrete finite-dimensional trace realizations should instantiate this class
from their coordinate definition of `tensor_contract`, raw Fubini, and symmetry
of `MetricDuality.g_inv`. Synthetic curvature proofs should depend on this
bridge instead of carrying ad hoc per-theorem Fubini hypotheses. -/
class HasDoubleMetricTrace05PatternFubini
    (p q : DoubleMetricTrace05Pattern)
    (met : MetricDuality R V) (atr : AbstractTrace R V) : Prop
    extends HasTensorContractFubini atr where
  metric_trace_fubini : forall T : TensorData R V 0 5, p.Fubini q met atr T

/-- Extract the metric double-trace Fubini equality from the bridge class. -/
theorem doubleMetricTrace05Pattern_fubini
    (p q : DoubleMetricTrace05Pattern)
    (met : MetricDuality R V) (atr : AbstractTrace R V)
    [HasDoubleMetricTrace05PatternFubini p q met atr]
    (T : TensorData R V 0 5) :
    p.Fubini q met atr T :=
  HasDoubleMetricTrace05PatternFubini.metric_trace_fubini T

/-- Specialized bridge for the contracted-Bianchi divergence patterns. -/
theorem contractedBianchiDivMetricTraceFubini
    (met : MetricDuality R V) (atr : AbstractTrace R V)
    [HasDoubleMetricTrace05PatternFubini
      DoubleMetricTrace05Pattern.contractedBianchiDivFubiniPattern
      DoubleMetricTrace05Pattern.contractedBianchiDivPattern met atr]
    (T : TensorData R V 0 5) :
    DoubleMetricTrace05Pattern.contractedBianchiDivFubiniPattern.Fubini
      DoubleMetricTrace05Pattern.contractedBianchiDivPattern met atr T :=
  doubleMetricTrace05Pattern_fubini
    DoubleMetricTrace05Pattern.contractedBianchiDivFubiniPattern
    DoubleMetricTrace05Pattern.contractedBianchiDivPattern met atr T

end DoubleMetricTrace

end SyntheticTensor
