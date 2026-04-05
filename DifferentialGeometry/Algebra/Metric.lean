import DifferentialGeometry.Bridge.Defs
import DifferentialGeometry.Algebra.VectorField
import DifferentialGeometry.Algebra.BilinearForm
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

open DifferentialGeometry.Bridge
open TensorAlgebra

/-!
# Riemannian Metric
Algebraic formulation of the metric tensor and associated trace operations.
-/

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]

/-- Evaluate a 0-2 tensor on two vector fields. -/
def eval02 (T : AbstractTensor R V 0 2) (X Y : V) : R :=
  (toData T) ![X, Y] ![]

lemma eval02_zero (X Y : V) : eval02 (0 : AbstractBilinearForm R V) X Y = 0 := by
  have hz : (0 : AbstractBilinearForm R V) = fromData (0 : TensorData R V 0 2) := rfl
  rw [hz]
  dsimp [eval02]
  rw [TensorAlgebra.toData_fromData]
  rfl

lemma eval02_add_left (T : AbstractTensor R V 0 2) (X Y Z : V) :
  eval02 T (X + Y) Z = eval02 T X Z + eval02 T Y Z := by
  dsimp [eval02]
  have h := MultilinearMap.map_update_add (toData T) ![X, Z] 0 X Y
  have eq1 : Function.update ![X, Z] 0 (X + Y) = ![X + Y, Z] := by ext i; fin_cases i <;> rfl
  have eq2 : Function.update ![X, Z] 0 X = ![X, Z] := by ext i; fin_cases i <;> rfl
  have eq3 : Function.update ![X, Z] 0 Y = ![Y, Z] := by ext i; fin_cases i <;> rfl
  rw [eq1, eq2, eq3] at h
  rw [h]
  rfl

lemma eval02_smul_left (T : AbstractTensor R V 0 2) (f : R) (X Y : V) :
  eval02 T (f • X) Y = f * eval02 T X Y := by
  dsimp [eval02]
  have h := MultilinearMap.map_update_smul (toData T) ![X, Y] 0 f X
  have eq1 : Function.update ![X, Y] 0 (f • X) = ![f • X, Y] := by ext i; fin_cases i <;> rfl
  have eq2 : Function.update ![X, Y] 0 X = ![X, Y] := by ext i; fin_cases i <;> rfl
  rw [eq1, eq2] at h
  rw [h]
  rfl

lemma eval02_add_right (T : AbstractTensor R V 0 2) (X Y Z : V) :
  eval02 T X (Y + Z) = eval02 T X Y + eval02 T X Z := by
  dsimp [eval02]
  have h := MultilinearMap.map_update_add (toData T) ![X, Y] 1 Y Z
  have eq1 : Function.update ![X, Y] 1 (Y + Z) = ![X, Y + Z] := by ext i; fin_cases i <;> rfl
  have eq2 : Function.update ![X, Y] 1 Y = ![X, Y] := by ext i; fin_cases i <;> rfl
  have eq3 : Function.update ![X, Y] 1 Z = ![X, Z] := by ext i; fin_cases i <;> rfl
  rw [eq1, eq2, eq3] at h
  rw [h]
  rfl

lemma eval02_smul_right (T : AbstractTensor R V 0 2) (f : R) (X Y : V) :
  eval02 T X (f • Y) = f * eval02 T X Y := by
  dsimp [eval02]
  have h := MultilinearMap.map_update_smul (toData T) ![X, Y] 1 f Y
  have eq1 : Function.update ![X, Y] 1 (f • Y) = ![X, f • Y] := by ext i; fin_cases i <;> rfl
  have eq2 : Function.update ![X, Y] 1 Y = ![X, Y] := by ext i; fin_cases i <;> rfl
  rw [eq1, eq2] at h
  rw [h]
  rfl

lemma eval02_add (T₁ T₂ : AbstractTensor R V 0 2) (X Y : V) :
  eval02 (T₁ + T₂) X Y = eval02 T₁ X Y + eval02 T₂ X Y := by
  dsimp [eval02]
  have h_add : T₁ + T₂ = TensorAlgebra.add (r:=0) (s:=2) T₁ T₂ := rfl
  rw [h_add, toData_add]
  rfl

lemma eval02_smul (T : AbstractTensor R V 0 2) (c : R) (X Y : V) :
  eval02 (c • T) X Y = c * eval02 T X Y := by
  dsimp [eval02]
  have h_smul : c • T = TensorAlgebra.smul (r:=0) (s:=2) c T := rfl
  rw [h_smul, toData_smul]
  rfl

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
  eval02 metric.g_tensor X Y

/-- The symmetry condition of the metric. -/
lemma symm (metric : AbstractMetricTensor R V) (X Y : V) : metric.g X Y = metric.g Y X := by
  dsimp [g]
  have h_symm : eval02 metric.g_tensor X Y = eval02 (swap_covariant 0 1 metric.g_tensor) X Y := by rw [metric.symm_tensor]
  rw [h_symm]
  dsimp [eval02]
  rw [TensorAlgebra.toData_swap_covariant]
  have eq_swap : ![X, Y] ∘ Equiv.swap 0 1 = ![Y, X] := by ext i; fin_cases i <;> rfl
  rw [eq_swap]

lemma bilinear_add_left (metric : AbstractMetricTensor R V) (X Y Z : V) :
  metric.g (X + Y) Z = metric.g X Z + metric.g Y Z := by
  dsimp [g]
  exact eval02_add_left metric.g_tensor X Y Z

lemma bilinear_smul_left (metric : AbstractMetricTensor R V) (f : R) (X Y : V) :
  metric.g (f • X) Y = f * metric.g X Y := by
  dsimp [g]
  exact eval02_smul_left metric.g_tensor f X Y

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
  g_inv : AbstractTensor R V 2 0
  raise : AbstractBilinearForm R V → (V → V)
  g_raise : ∀ (T : AbstractBilinearForm R V) (X Y : V), AbstractMetricTensor.g toAbstractMetricTensor (raise T X) Y = eval02 T X Y
  sharp : (V → R) → V
  flat : V → (V → R)
  sharp_add : ∀ f h : V → R, sharp (fun v => f v + h v) = sharp f + sharp h
  sharp_smul : ∀ (c : R) (f : V → R), sharp (fun v => c * f v) = c • (sharp f)
  sharp_g : ∀ Y : V, sharp (fun Z => AbstractMetricTensor.g toAbstractMetricTensor Y Z) = Y
  g_sharp : ∀ (f : V → R) (Z : V), AbstractMetricTensor.g toAbstractMetricTensor (sharp f) Z = f Z
  flat_def : ∀ (X Y : V), flat X Y = AbstractMetricTensor.g toAbstractMetricTensor X Y

variable (metric_duality : MetricDuality R V)

/-- Prove linearity of raise over addition. -/
lemma raise_add (T₁ T₂ : AbstractBilinearForm R V) (X : V) :
    metric_duality.raise (T₁ + T₂) X = metric_duality.raise T₁ X + metric_duality.raise T₂ X := by
  apply metric_duality.eq_of_forall_g_eq
  intro Z
  have h5 : AbstractMetricTensor.g metric_duality.toAbstractMetricTensor (metric_duality.raise T₁ X + metric_duality.raise T₂ X) Z = AbstractMetricTensor.g metric_duality.toAbstractMetricTensor (metric_duality.raise T₁ X) Z + AbstractMetricTensor.g metric_duality.toAbstractMetricTensor (metric_duality.raise T₂ X) Z := metric_duality.toAbstractMetricTensor.bilinear_add_left _ _ _
  calc AbstractMetricTensor.g metric_duality.toAbstractMetricTensor (metric_duality.raise (T₁ + T₂) X) Z = eval02 (T₁ + T₂) X Z := metric_duality.g_raise (T₁ + T₂) X Z
    _ = eval02 T₁ X Z + eval02 T₂ X Z := eval02_add T₁ T₂ X Z
    _ = AbstractMetricTensor.g metric_duality.toAbstractMetricTensor (metric_duality.raise T₁ X) Z + AbstractMetricTensor.g metric_duality.toAbstractMetricTensor (metric_duality.raise T₂ X) Z := by rw [metric_duality.g_raise T₁ X Z, metric_duality.g_raise T₂ X Z]
    _ = AbstractMetricTensor.g metric_duality.toAbstractMetricTensor (metric_duality.raise T₁ X + metric_duality.raise T₂ X) Z := h5.symm

/-- Prove linearity of raise over scalar multiplication. -/
lemma raise_smul (T : AbstractBilinearForm R V) (c : R) (X : V) :
    metric_duality.raise (c • T) X = c • metric_duality.raise T X := by
  apply metric_duality.eq_of_forall_g_eq
  intro Z
  have h4 : AbstractMetricTensor.g metric_duality.toAbstractMetricTensor (c • metric_duality.raise T X) Z = c * AbstractMetricTensor.g metric_duality.toAbstractMetricTensor (metric_duality.raise T X) Z := metric_duality.toAbstractMetricTensor.bilinear_smul_left c _ Z
  calc AbstractMetricTensor.g metric_duality.toAbstractMetricTensor (metric_duality.raise (c • T) X) Z = eval02 (c • T) X Z := metric_duality.g_raise (c • T) X Z
    _ = c * eval02 T X Z := by
      exact eval02_smul T c X Z
    _ = c * AbstractMetricTensor.g metric_duality.toAbstractMetricTensor (metric_duality.raise T X) Z := by rw [metric_duality.g_raise T X Z]
    _ = AbstractMetricTensor.g metric_duality.toAbstractMetricTensor (c • metric_duality.raise T X) Z := h4.symm
