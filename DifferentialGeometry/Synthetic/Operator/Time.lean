import DifferentialGeometry.Synthetic.Algebra.VectorField
import DifferentialGeometry.Synthetic.Algebra.Metric
import DifferentialGeometry.Synthetic.Geometry.Connection
import DifferentialGeometry.Synthetic.Operator.Gradient
import DifferentialGeometry.Synthetic.Operator.Laplacian
import DifferentialGeometry.Synthetic.Operator.Variation
import Mathlib.Algebra.Order.Ring.Defs

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false

/--
This axiomatizes the existence of 1/t, its derivative rule ∂_t (1/t) = -1/t^2, and its positivity.
-/
class TimeWeight (R : Type) [CommRing R] [PartialOrder R] (Time : Type) [TimeDerivative Time R] where
  inv_t : Time → R
  dt_inv_t : ∀ t, TimeDerivative.partial_t inv_t t = - (inv_t t)^2
  inv_t_nonneg : ∀ t, (0:R) ≤ inv_t t

/-- Single-variable calculus rules for scalar time derivatives. -/
class ScalarTimeDerivativeRules (R : Type) [CommRing R] (Time : Type) [TimeDerivative Time R] where
  /-- Product rule for addition: $\partial_t(f + g) = \partial_t f + \partial_t g$ -/
  dt_add : ∀ (f g : Time → R) t, TimeDerivative.partial_t (fun s => f s + g s) t = TimeDerivative.partial_t f t + TimeDerivative.partial_t g t
  /-- Product rule for subtraction: $\partial_t(f - g) = \partial_t f - \partial_t g$ -/
  dt_sub : ∀ (f g : Time → R) t, TimeDerivative.partial_t (fun s => f s - g s) t = TimeDerivative.partial_t f t - TimeDerivative.partial_t g t
  /-- Linearity for scalar multiplication: $\partial_t(cf) = c \partial_t f$ -/
  dt_smul : ∀ (c : R) (f : Time → R) t, TimeDerivative.partial_t (fun s => c * f s) t = c * TimeDerivative.partial_t f t
  /-- Product rule for multiplication: $\partial_t(fg) = (\partial_t f)g + f(\partial_t g)$ -/
  dt_mul : ∀ (f g : Time → R) t, TimeDerivative.partial_t (fun s => f s * g s) t = TimeDerivative.partial_t f t * g t + f t * TimeDerivative.partial_t g t


open DifferentialGeometry TensorAlgebra

variable {R V : Type}
variable [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] [AbstractDerivationAction R V]

class StaticMetricTimeRules
  (Time : Type)
  [TimeDerivative Time R]
  [TimeDerivative Time V]
  (metric : MetricDuality R V)
  [MetricTraceOperator R V metric.toNonDegenerateMetric.toAbstractMetricTensor]
  (conn : AbstractAffineConnection R V) where
  dt_laplacian : ∀ (f : Time → R) t,
    TimeDerivative.partial_t (fun s => laplacian metric.toNonDegenerateMetric.toAbstractMetricTensor conn (f s)) t =
    laplacian metric.toNonDegenerateMetric.toAbstractMetricTensor conn (TimeDerivative.partial_t f t)
  dt_grad : ∀ (f : Time → R) t,
    TimeDerivative.partial_t (fun s => grad metric (f s)) t = grad metric (TimeDerivative.partial_t f t)
  dt_metric_g : ∀ (X : Time → V) t,
    TimeDerivative.partial_t (fun s => metric.g (X s) (X s)) t =
    (2:R) * metric.g (X t) (TimeDerivative.partial_t X t)

/--
Generic time derivative operator acting directly on abstract tensors.
-/
class TensorTimeCalculus (Time R V : Type) [CommRing R] [AddCommGroup V] [Module R V]
    [TensorAlgebra R V] [TimeDerivative Time R] [TimeDerivative Time V] where
  partial_t_tensor (t : Time) {r s : ℕ} : (Time → AbstractTensor R V r s) → AbstractTensor R V r s

  -- Basic evaluations
  t_scalar : ∀ (f : Time → R) (t : Time),
    partial_t_tensor t (fun x => TensorAlgebra.fromData (scalarToData (f x))) = TensorAlgebra.fromData (scalarToData (TimeDerivative.partial_t f t))

  t_vector : ∀ (X : Time → V) (t : Time),
    partial_t_tensor t (fun x => TensorAlgebra.fromData (vectorToData (X x))) = TensorAlgebra.fromData (vectorToData (TimeDerivative.partial_t X t))

  -- Additivity
  t_add : ∀ {r s : ℕ} (T1 T2 : Time → AbstractTensor R V r s) (t : Time),
    partial_t_tensor t (fun x => TensorAlgebra.add (T1 x) (T2 x)) = TensorAlgebra.add (partial_t_tensor t T1) (partial_t_tensor t T2)

  -- Extended Leibniz Rule for scalar multiplication
  t_smul : ∀ {r s : ℕ} (c : Time → R) (T : Time → AbstractTensor R V r s) (t : Time),
    partial_t_tensor t (fun x => TensorAlgebra.smul (c x) (T x)) =
      TensorAlgebra.add (TensorAlgebra.smul (TimeDerivative.partial_t c t) (T t)) (TensorAlgebra.smul (c t) (partial_t_tensor t T))

  -- Leibniz Rule for Tensor Products
  t_tensor_prod : ∀ {r1 s1 r2 s2 : ℕ} (T1 : Time → AbstractTensor R V r1 s1) (T2 : Time → AbstractTensor R V r2 s2) (t : Time),
    partial_t_tensor t (fun x => TensorAlgebra.tensor_prod (T1 x) (T2 x)) =
      TensorAlgebra.add (TensorAlgebra.tensor_prod (partial_t_tensor t T1) (T2 t)) (TensorAlgebra.tensor_prod (T1 t) (partial_t_tensor t T2))

  -- Commutativity with contraction
  t_contract : ∀ {r s : ℕ} (T : Time → AbstractTensor R V (r + 1) (s + 1)) (t : Time),
    partial_t_tensor t (fun x => TensorAlgebra.contract (T x)) = TensorAlgebra.contract (partial_t_tensor t T)
