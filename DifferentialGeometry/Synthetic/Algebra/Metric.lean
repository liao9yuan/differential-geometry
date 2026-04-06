import DifferentialGeometry.VectorField
import DifferentialGeometry.Synthetic.Algebra.TensorAlgebra
import DifferentialGeometry.Synthetic.Algebra.VectorField
import DifferentialGeometry.Synthetic.Algebra.BilinearForm
import Mathlib.Tactic.Ring

open DifferentialGeometry
open TensorAlgebra

/-!
# Riemannian Metric
Algebraic formulation of the metric tensor and associated trace operations.
-/

variable {R V : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]



/-- Metric tensor
Input: (V, V)
Output: R -/
structure AbstractMetricTensor (R V : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] where
  /-- The true underlying generic metric tensor. -/
  g_tensor : AbstractTensor R V 0 2
  /-- Symmetry condition. (Now cleanly defined using the generic swap routing operation). -/
  symm_tensor : TensorAlgebra.swap_covariant (R:=R) (V:=V) 0 1 g_tensor = g_tensor
  /-- Positive definiteness. -/
  pos_def : ∀ X : V, X ≠ 0 → tensor_eval g_tensor ![X, X] ![] > 0

namespace AbstractMetricTensor

variable {R V : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]

/-- The classical geometric evaluation of the metric tensor on two vector fields. -/
def g (metric : AbstractMetricTensor R V) (X Y : V) : R :=
  tensor_eval metric.g_tensor ![X, Y] ![]

lemma symm (metric : AbstractMetricTensor R V) (X Y : V) : metric.g X Y = metric.g Y X := by
  dsimp [g, tensor_eval]
  have hz : TensorAlgebra.toData metric.g_tensor ![X, Y] ![] = TensorAlgebra.toData (TensorAlgebra.swap_covariant (R:=R) (V:=V) 0 1 metric.g_tensor) ![X, Y] ![] := by
    rw [metric.symm_tensor]
  rw [hz]
  rw [TensorAlgebra.toData_swap_covariant]
  have heq : ![X, Y] ∘ ⇑(Equiv.swap (0:Fin 2) (1:Fin 2)) = ![Y, X] := by
    ext i
    fin_cases i <;> rfl
  rw [heq]

lemma bilinear_add_left (metric : AbstractMetricTensor R V) (X Y Z : V) :
  metric.g (X + Y) Z = metric.g X Z + metric.g Y Z := by
  dsimp [g, tensor_eval]
  have hz : ![X + Y, Z] = Function.update ![X, Z] 0 (X + Y) := by
    ext i
    fin_cases i <;> rfl
  rw [hz]
  have h_add := MultilinearMap.map_update_add (TensorAlgebra.toData metric.g_tensor) ![X, Z] 0 X Y
  rw [h_add]
  have hz_x : Function.update ![X, Z] 0 X = ![X, Z] := by
    ext i
    fin_cases i <;> rfl
  have hz_y : Function.update ![X, Z] 0 Y = ![Y, Z] := by
    ext i
    fin_cases i <;> rfl
  rw [hz_x, hz_y]
  exact MultilinearMap.add_apply _ _ _

lemma bilinear_smul_left (metric : AbstractMetricTensor R V) (f : R) (X Y : V) :
  metric.g (f • X) Y = f * metric.g X Y := by
  dsimp [g, tensor_eval]
  have hz : ![f • X, Y] = Function.update ![X, Y] 0 (f • X) := by
    ext i
    fin_cases i <;> rfl
  rw [hz]
  have h_smul := MultilinearMap.map_update_smul (TensorAlgebra.toData metric.g_tensor) ![X, Y] 0 f X
  rw [h_smul]
  have hz_x : Function.update ![X, Y] 0 X = ![X, Y] := by
    ext i
    fin_cases i <;> rfl
  rw [hz_x]
  exact MultilinearMap.smul_apply _ _ _

end AbstractMetricTensor

lemma metric_neg_left {R V} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] (metric : AbstractMetricTensor R V) (X Y : V) : metric.g (-X) Y = - metric.g X Y := by
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

lemma metric_sub_left {R V} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] (metric : AbstractMetricTensor R V) (X Y Z : V) : metric.g (X - Y) Z = metric.g X Z - metric.g Y Z := by
  calc metric.g (X - Y) Z = metric.g (X + -Y) Z := by rw [sub_eq_add_neg]
    _ = metric.g X Z + metric.g (-Y) Z := metric.bilinear_add_left X (-Y) Z
    _ = metric.g X Z + - metric.g Y Z := by rw [metric_neg_left]
    _ = metric.g X Z - metric.g Y Z := by rw [sub_eq_add_neg]



/-- A metric tensor is non-degenerate if it implies equality of vector fields
when their inner products with all other vector fields are equal.
Input: (AbstractMetricTensor R V)
Output: Type -/
class NonDegenerateMetric (R V : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] extends AbstractMetricTensor R V where
  eq_of_forall_g_eq : ∀ X Y : V, (∀ Z : V, AbstractMetricTensor.g toAbstractMetricTensor X Z = AbstractMetricTensor.g toAbstractMetricTensor Y Z) → X = Y

/-- Metric duality provides the musical isomorphism to convert bilinear forms to endomorphisms, and 1-forms to vector fields.
Input: (NonDegenerateMetric R V)
Output: Type -/
class MetricDuality (R V : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] extends NonDegenerateMetric R V where
  g_inv : AbstractTensor R V 2 0
  raise : AbstractBilinearForm R V → (V → V)
  g_raise : ∀ (T : AbstractBilinearForm R V) (X Y : V), AbstractMetricTensor.g toAbstractMetricTensor (raise T X) Y = tensor_eval T ![X, Y] ![]
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
  calc AbstractMetricTensor.g metric_duality.toAbstractMetricTensor (metric_duality.raise (T₁ + T₂) X) Z = tensor_eval (T₁ + T₂) ![X, Z] ![] := metric_duality.g_raise (T₁ + T₂) X Z
    _ = tensor_eval T₁ ![X, Z] ![] + tensor_eval T₂ ![X, Z] ![] := by
      exact tensor_eval_add T₁ T₂ ![X, Z] ![]
    _ = AbstractMetricTensor.g metric_duality.toAbstractMetricTensor (metric_duality.raise T₁ X) Z + AbstractMetricTensor.g metric_duality.toAbstractMetricTensor (metric_duality.raise T₂ X) Z := by rw [metric_duality.g_raise T₁ X Z, metric_duality.g_raise T₂ X Z]
    _ = AbstractMetricTensor.g metric_duality.toAbstractMetricTensor (metric_duality.raise T₁ X + metric_duality.raise T₂ X) Z := h5.symm

/-- Prove linearity of raise over scalar multiplication. -/
lemma raise_smul (T : AbstractBilinearForm R V) (c : R) (X : V) :
    metric_duality.raise (c • T) X = c • metric_duality.raise T X := by
  apply metric_duality.eq_of_forall_g_eq
  intro Z
  have h4 : AbstractMetricTensor.g metric_duality.toAbstractMetricTensor (c • metric_duality.raise T X) Z = c * AbstractMetricTensor.g metric_duality.toAbstractMetricTensor (metric_duality.raise T X) Z := metric_duality.toAbstractMetricTensor.bilinear_smul_left c _ Z
  calc AbstractMetricTensor.g metric_duality.toAbstractMetricTensor (metric_duality.raise (c • T) X) Z = tensor_eval (c • T) ![X, Z] ![] := metric_duality.g_raise (c • T) X Z
    _ = c * tensor_eval T ![X, Z] ![] := by
      exact tensor_eval_smul c T ![X, Z] ![]
    _ = c * AbstractMetricTensor.g metric_duality.toAbstractMetricTensor (metric_duality.raise T X) Z := by rw [metric_duality.g_raise T X Z]
    _ = AbstractMetricTensor.g metric_duality.toAbstractMetricTensor (c • metric_duality.raise T X) Z := h4.symm

/--
Lowers the specified contravariant index `idx` of an arbitrary rank tensor into a covariant index.
Achieved algebraically by taking the tensor product with the metric and contracting.
-/
def lower_index {R V : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] (metric : AbstractMetricTensor R V) {r s : ℕ} (idx : Fin (r + 1)) (T : AbstractTensor R V (r + 1) s) : AbstractTensor R V r (s + 1) :=
  -- contract the contravariant idx of T with the 2nd covariant slot of g_tensor
  have h_eq : TensorAlgebra.AbstractTensor R V (0 + (r + 1)) (2 + s) = TensorAlgebra.AbstractTensor R V (r + 1) (s + 1 + 1) := by
    congr 1
    · omega
    · omega
  TensorAlgebra.contract_general (r:=r) (s:=s+1) idx (1 : Fin (s + 2)) (cast h_eq (TensorAlgebra.tensor_prod metric.g_tensor T))

/--
Raises the specified covariant index `idx` of an arbitrary rank tensor into a contravariant index.
Achieved algebraically by taking the tensor product with the inverse metric and contracting.
-/
def raise_index {R V : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] (metric : MetricDuality R V) {r s : ℕ} (idx : Fin (s + 1)) (T : AbstractTensor R V r (s + 1)) : AbstractTensor R V (r + 1) s :=
  -- contract the 2nd contravariant slot of g_inv with the covariant idx of T
  have h_eq : TensorAlgebra.AbstractTensor R V (2 + r) (0 + (s + 1)) = TensorAlgebra.AbstractTensor R V (r + 1 + 1) (s + 1) := by
    congr 1
    · omega
    · omega
  TensorAlgebra.contract_general (r:=r+1) (s:=s) (1 : Fin (r + 2)) idx (cast h_eq (TensorAlgebra.tensor_prod metric.g_inv T))
