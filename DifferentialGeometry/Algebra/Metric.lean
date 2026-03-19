import DifferentialGeometry.Bridge.Defs
import DifferentialGeometry.Algebra.VectorField
import DifferentialGeometry.Algebra.BilinearForm
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option linter.style.longLine false

open DifferentialGeometry.Bridge
open TensorAlgebra

/-!
# Riemannian Metric
Algebraic formulation of the metric tensor and associated trace operations.
-/

/-- Metric tensor
Input: (V, V)
Output: R -/
structure AbstractMetricTensor (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] where
  /-- The true underlying generic metric tensor. -/
  g_tensor : AbstractTensor R V 0 2
  /-- Symmetry condition. (Now cleanly defined using the generic swap routing operation). -/
  symm_tensor : TensorAlgebra.swap_covariant (R:=R) (V:=V) 0 1 g_tensor = g_tensor

namespace AbstractMetricTensor

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]

/-- The classical geometric evaluation of the metric tensor on two vector fields. -/
def g (metric : AbstractMetricTensor R V) (X Y : V) : R :=
  toScalar (contract (r:=0) (s:=0) (contract (r:=1) (s:=1) (tensor_prod (r1:=0) (s1:=2) (r2:=2) (s2:=0) metric.g_tensor (tensor_prod (r1:=1) (s1:=0) (r2:=1) (s2:=0) (fromVector X) (fromVector Y)))))

lemma symm (metric : AbstractMetricTensor R V) (X Y : V) : metric.g X Y = metric.g Y X := by
  dsimp [g]
  have h := TensorAlgebra.contract_swap_covariant_eval X Y metric.g_tensor
  rw [metric.symm_tensor] at h
  rw [h]

lemma bilinear_add_left (metric : AbstractMetricTensor R V) (X Y Z : V) :
  metric.g (X + Y) Z = metric.g X Z + metric.g Y Z := by
  dsimp [g]
  rw [fromVector_add]
  rw [tensor_prod_add_left]
  rw [tensor_prod_add_right]
  rw [contract_add]
  rw [contract_add]
  rw [toScalar_add]

lemma bilinear_smul_left (metric : AbstractMetricTensor R V) (f : R) (X Y : V) :
  metric.g (f • X) Y = f * metric.g X Y := by
  dsimp [g]
  rw [fromVector_smul]
  rw [tensor_prod_smul_left]
  rw [tensor_prod_smul_right]
  rw [contract_smul]
  rw [contract_smul]
  rw [toScalar_smul]

end AbstractMetricTensor

lemma metric_neg_left {R V} [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] (metric : AbstractMetricTensor R V) (X Y : V) : metric.g (-X) Y = - metric.g X Y := by
  have h1 : metric.g (X + -X) Y = metric.g X Y + metric.g (-X) Y := metric.bilinear_add_left X (-X) Y
  have h3 : metric.g (0 + 0) Y = metric.g 0 Y + metric.g 0 Y := metric.bilinear_add_left 0 0 Y
  have h5 : metric.g 0 Y = 0 := by
    calc metric.g 0 Y = metric.g 0 Y + metric.g 0 Y - metric.g 0 Y := by ring
      _ = metric.g (0 + 0) Y - metric.g 0 Y := by rw [← h3]
      _ = metric.g 0 Y - metric.g 0 Y := by rw [add_zero]
      _ = 0 := by ring
  calc metric.g (-X) Y = metric.g X Y + metric.g (-X) Y - metric.g X Y := by ring
    _ = metric.g (X + -X) Y - metric.g X Y := by rw [← h1]
    _ = metric.g 0 Y - metric.g X Y := by rw [add_neg_cancel]
    _ = 0 - metric.g X Y := by rw [h5]
    _ = - metric.g X Y := by ring

lemma metric_sub_left {R V} [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] (metric : AbstractMetricTensor R V) (X Y Z : V) : metric.g (X - Y) Z = metric.g X Z - metric.g Y Z := by
  calc metric.g (X - Y) Z = metric.g (X + -Y) Z := by rw [sub_eq_add_neg]
    _ = metric.g X Z + metric.g (-Y) Z := metric.bilinear_add_left X (-Y) Z
    _ = metric.g X Z + - metric.g Y Z := by rw [metric_neg_left]
    _ = metric.g X Z - metric.g Y Z := by rw [sub_eq_add_neg]

/-- Trace operator associated with a specific metric tensor.
Input: (V → V → R)
Output: R -/
class MetricTraceOperator (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] (metric : AbstractMetricTensor R V) where
  metric_trace : (V → V → R) → R

/-- Axiomatic rules for the metric trace operator.
Input: (AbstractMetricTensor R V)
Output: Type -/
class MetricTraceRules (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
  (metric : AbstractMetricTensor R V) [MetricTraceOperator R V metric] where
  trace_add : ∀ (T₁ T₂ : V → V → R),
    MetricTraceOperator.metric_trace metric (fun X Y => T₁ X Y + T₂ X Y) =
    MetricTraceOperator.metric_trace metric T₁ + MetricTraceOperator.metric_trace metric T₂
  trace_smul : ∀ (a : R) (T : V → V → R),
    MetricTraceOperator.metric_trace metric (fun X Y => a * T X Y) =
    a * MetricTraceOperator.metric_trace metric T

/-- A metric tensor is non-degenerate if it implies equality of vector fields
when their inner products with all other vector fields are equal.
Input: (AbstractMetricTensor R V)
Output: Type -/
class NonDegenerateMetric (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] extends AbstractMetricTensor R V where
  eq_of_forall_g_eq : ∀ X Y : V, (∀ Z : V, AbstractMetricTensor.g toAbstractMetricTensor X Z = AbstractMetricTensor.g toAbstractMetricTensor Y Z) → X = Y

/-- Metric duality provides the musical isomorphism to convert bilinear forms to endomorphisms, and 1-forms to vector fields.
Input: (NonDegenerateMetric R V)
Output: Type -/
class MetricDuality (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] extends NonDegenerateMetric R V where
  raise : SmoothBilinearForm R V → (V → V)
  g_raise : ∀ (T : SmoothBilinearForm R V) (X Y : V), AbstractMetricTensor.g toAbstractMetricTensor (raise T X) Y = T X Y
  sharp : (V → R) → V
  flat : V → (V → R)
  sharp_add : ∀ f h : V → R, sharp (fun v => f v + h v) = sharp f + sharp h
  sharp_smul : ∀ (c : R) (f : V → R), sharp (fun v => c * f v) = c • (sharp f)
  sharp_g : ∀ Y : V, sharp (fun Z => AbstractMetricTensor.g toAbstractMetricTensor Y Z) = Y
  g_sharp : ∀ (f : V → R) (Z : V), AbstractMetricTensor.g toAbstractMetricTensor (sharp f) Z = f Z
  flat_def : ∀ (X Y : V), flat X Y = AbstractMetricTensor.g toAbstractMetricTensor X Y

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
variable (metric_duality : MetricDuality R V)

/-- Prove linearity of raise over addition. -/
lemma raise_add (T₁ T₂ : SmoothBilinearForm R V) (X : V) :
    metric_duality.raise (T₁ + T₂) X = metric_duality.raise T₁ X + metric_duality.raise T₂ X := by
  apply metric_duality.eq_of_forall_g_eq
  intro Z
  have h1 : AbstractMetricTensor.g metric_duality.toAbstractMetricTensor (metric_duality.raise (T₁ + T₂) X) Z = (T₁ + T₂) X Z := metric_duality.g_raise (T₁ + T₂) X Z
  have h2 : (T₁ + T₂) X Z = T₁ X Z + T₂ X Z := rfl
  have h3 : T₁ X Z = AbstractMetricTensor.g metric_duality.toAbstractMetricTensor (metric_duality.raise T₁ X) Z := by rw [metric_duality.g_raise T₁ X Z]
  have h4 : T₂ X Z = AbstractMetricTensor.g metric_duality.toAbstractMetricTensor (metric_duality.raise T₂ X) Z := by rw [metric_duality.g_raise T₂ X Z]
  have h5 : AbstractMetricTensor.g metric_duality.toAbstractMetricTensor (metric_duality.raise T₁ X + metric_duality.raise T₂ X) Z = AbstractMetricTensor.g metric_duality.toAbstractMetricTensor (metric_duality.raise T₁ X) Z + AbstractMetricTensor.g metric_duality.toAbstractMetricTensor (metric_duality.raise T₂ X) Z := metric_duality.toAbstractMetricTensor.bilinear_add_left _ _ _
  calc AbstractMetricTensor.g metric_duality.toAbstractMetricTensor (metric_duality.raise (T₁ + T₂) X) Z = T₁ X Z + T₂ X Z := by { rw [h1]; rfl }
    _ = AbstractMetricTensor.g metric_duality.toAbstractMetricTensor (metric_duality.raise T₁ X) Z + AbstractMetricTensor.g metric_duality.toAbstractMetricTensor (metric_duality.raise T₂ X) Z := by rw [h3, h4]
    _ = AbstractMetricTensor.g metric_duality.toAbstractMetricTensor (metric_duality.raise T₁ X + metric_duality.raise T₂ X) Z := by rw [h5]

/-- Prove linearity of raise over scalar multiplication. -/
lemma raise_smul (T : SmoothBilinearForm R V) (c : R) (X : V) :
    metric_duality.raise (c • T) X = c • metric_duality.raise T X := by
  apply metric_duality.eq_of_forall_g_eq
  intro Z
  have h1 : AbstractMetricTensor.g metric_duality.toAbstractMetricTensor (metric_duality.raise (c • T) X) Z = (c • T) X Z := metric_duality.g_raise (c • T) X Z
  -- (c • T) X Z = c * T X Z by definition
  have h3 : c * T X Z = c * AbstractMetricTensor.g metric_duality.toAbstractMetricTensor (metric_duality.raise T X) Z := by rw [metric_duality.g_raise T X Z]
  have h4 : AbstractMetricTensor.g metric_duality.toAbstractMetricTensor (c • metric_duality.raise T X) Z = c * AbstractMetricTensor.g metric_duality.toAbstractMetricTensor (metric_duality.raise T X) Z := metric_duality.toAbstractMetricTensor.bilinear_smul_left c _ Z
  calc AbstractMetricTensor.g metric_duality.toAbstractMetricTensor (metric_duality.raise (c • T) X) Z = c * T X Z := by { rw [h1]; rfl }
    _ = c * AbstractMetricTensor.g metric_duality.toAbstractMetricTensor (metric_duality.raise T X) Z := h3
    _ = AbstractMetricTensor.g metric_duality.toAbstractMetricTensor (c • metric_duality.raise T X) Z := by rw [h4]

