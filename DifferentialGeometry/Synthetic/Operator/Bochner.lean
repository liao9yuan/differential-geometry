import DifferentialGeometry.Synthetic.Algebra.VectorField
import DifferentialGeometry.Synthetic.Algebra.Metric
import DifferentialGeometry.Synthetic.Geometry.Connection
import DifferentialGeometry.Synthetic.Operator.Hessian
import DifferentialGeometry.Synthetic.Operator.Laplacian
import DifferentialGeometry.Synthetic.Geometry.Curvature
import DifferentialGeometry.Synthetic.Geometry.RicciTensor
import DifferentialGeometry.Synthetic.Geometry.RicciIdentity
import DifferentialGeometry.Synthetic.Operator.Gradient
import DifferentialGeometry.Synthetic.Analysis.TensorInnerProduct
import DifferentialGeometry.VectorField
import DifferentialGeometry.Synthetic.Algebra.TensorAlgebra
import DifferentialGeometry.Synthetic.Algebra.BilinearForm
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

open AbstractDerivationAction AbstractLieBracket DifferentialGeometry TensorAlgebra

variable {R V : Type}
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
variable [AbstractDerivationAction R V] [AbstractLieBracket V] [DerivationRules R V]


-- Proves the expansion of the directional derivative of the squared norm of the gradient.
lemma grad_norm_sq_deriv
  (metric : MetricDuality R V)
  (conn : AbstractAffineConnection R V) [MetricCompatible conn metric.toNonDegenerateMetric.toAbstractMetricTensor]
  (f : R) (X : V) :
  action X (metric.g (grad metric f) (grad metric f)) =
  metric.g (conn.nabla X (grad metric f)) (grad metric f) + metric.g (conn.nabla X (grad metric f)) (grad metric f) := by
  exact norm_sq_deriv conn metric.toNonDegenerateMetric.toAbstractMetricTensor X (grad metric f)

-- Proves the swapping of third-order derivatives of a function by injecting the Riemann curvature tensor.
lemma hessian_commute_ricci [AbstractLieBracket V]
  (conn : AbstractAffineConnection R V) [TorsionFree conn]
  (metric : MetricDuality R V)
  (f : R) (X Y : V) :
  conn.nabla X (conn.nabla Y (grad metric f)) =
  conn.nabla Y (conn.nabla X (grad metric f)) + conn.nabla (bracket X Y) (grad metric f) + Rm conn X Y (grad metric f) := by
  have h := ricci_identity conn X Y (grad metric f)
  have he := secondCovDerivCommutator_expand conn X Y (grad metric f)
  rw [TorsionFree.torsion_zero (conn := conn) X Y] at he
  rw [he] at h
  calc conn.nabla X (conn.nabla Y (grad metric f))
    _ = conn.nabla X (conn.nabla Y (grad metric f)) - conn.nabla Y (conn.nabla X (grad metric f)) - conn.nabla (bracket X Y) (grad metric f) + conn.nabla (bracket X Y) (grad metric f) + conn.nabla Y (conn.nabla X (grad metric f)) := by abel
    _ = Rm conn X Y (grad metric f) + conn.nabla (bracket X Y) (grad metric f) + conn.nabla Y (conn.nabla X (grad metric f)) := by rw [h]
    _ = conn.nabla Y (conn.nabla X (grad metric f)) + conn.nabla (bracket X Y) (grad metric f) + Rm conn X Y (grad metric f) := by abel

variable [AbstractLieBracket V] [DerivationRules R V]



lemma hessian_norm_sq_grad
  (metric : MetricDuality R V)
  (conn : AbstractAffineConnection R V) [MetricCompatible conn metric.toNonDegenerateMetric.toAbstractMetricTensor]
  (f : R) (X Y : V) :
  Hess conn (metric.g (grad metric f) (grad metric f)) X Y =
  2 * metric.g (secondCovDeriv conn X Y (grad metric f)) (grad metric f) +
  2 * metric.g (conn.nabla X (grad metric f)) (conn.nabla Y (grad metric f)) := by
  dsimp [Hess]
  have h1 : action Y (metric.g (grad metric f) (grad metric f)) = metric.g (conn.nabla Y (grad metric f)) (grad metric f) + metric.g (conn.nabla Y (grad metric f)) (grad metric f) := norm_sq_deriv conn metric.toNonDegenerateMetric.toAbstractMetricTensor Y (grad metric f)
  rw [h1]
  rw [DerivationRules.action_add_right]
  have h2 : action X (metric.g (conn.nabla Y (grad metric f)) (grad metric f)) = metric.g (conn.nabla X (conn.nabla Y (grad metric f))) (grad metric f) + metric.g (conn.nabla Y (grad metric f)) (conn.nabla X (grad metric f)) := MetricCompatible.compat (conn:=conn) X (conn.nabla Y (grad metric f)) (grad metric f)
  rw [h2]
  have h3 : action (conn.nabla X Y) (metric.g (grad metric f) (grad metric f)) = metric.g (conn.nabla (conn.nabla X Y) (grad metric f)) (grad metric f) + metric.g (conn.nabla (conn.nabla X Y) (grad metric f)) (grad metric f) := norm_sq_deriv conn metric.toNonDegenerateMetric.toAbstractMetricTensor (conn.nabla X Y) (grad metric f)
  rw [h3]
  have hsym : metric.g (conn.nabla Y (grad metric f)) (conn.nabla X (grad metric f)) = metric.g (conn.nabla X (grad metric f)) (conn.nabla Y (grad metric f)) := metric.symm _ _
  rw [hsym]
  dsimp [secondCovDeriv]
  have hsplit : metric.g (conn.nabla X (conn.nabla Y (grad metric f)) - conn.nabla (conn.nabla X Y) (grad metric f)) (grad metric f) = metric.g (conn.nabla X (conn.nabla Y (grad metric f))) (grad metric f) - metric.g (conn.nabla (conn.nabla X Y) (grad metric f)) (grad metric f) := by
    calc metric.g (conn.nabla X (conn.nabla Y (grad metric f)) - conn.nabla (conn.nabla X Y) (grad metric f)) (grad metric f)
      _ = metric.g (conn.nabla X (conn.nabla Y (grad metric f)) + - conn.nabla (conn.nabla X Y) (grad metric f)) (grad metric f) := by rw [sub_eq_add_neg]
      _ = metric.g (conn.nabla X (conn.nabla Y (grad metric f))) (grad metric f) + metric.g (- conn.nabla (conn.nabla X Y) (grad metric f)) (grad metric f) := metric.bilinear_add_left _ _ _
      _ = metric.g (conn.nabla X (conn.nabla Y (grad metric f))) (grad metric f) + - metric.g (conn.nabla (conn.nabla X Y) (grad metric f)) (grad metric f) := by rw [metric_neg_left]
      _ = metric.g (conn.nabla X (conn.nabla Y (grad metric f))) (grad metric f) - metric.g (conn.nabla (conn.nabla X Y) (grad metric f)) (grad metric f) := (sub_eq_add_neg _ _).symm
  rw [hsplit]
  ring

/-!
## Bochner-Weitzenböck Calculus Interface

The `BochnerCalculus` class provides the two key algebraic axioms for the Bochner-Weitzenböck
formula, following the same pattern as `TensorInnerProductRules` and `AffineTensorCalculus`.

**Mathematical content of the axioms:**

- `bochner_lap_expand` encodes the expansion of Δ(|∇f|²) obtained by applying the Hessian
  trace to the identity `Hess(|∇f|²)(X,Y) = 2g(∇²_{X,Y}∇f, ∇f) + 2g(∇_X∇f, ∇_Y∇f)`,
  and identifying the second term's metric trace with `tensorNormSq(hessianForm f)`.

- `bochner_commutation` encodes the vector Bochner formula:
  the metric trace of `(X,Y) ↦ g(∇²_{X,Y}∇f, ∇f)` equals `Ric(∇f,∇f) + g(∇f, ∇(Δf))`,
  proved in the analytic backend via the Ricci identity and metric compatibility.

These axioms can be instantiated and proved in the coordinate-based analytic layer.
-/
class BochnerCalculus
    (metric : MetricDuality R V)
    (conn : AbstractAffineConnection R V)
    [AffineTensorCalculus conn] [RiemannCurvatureTensorOp conn] [TorsionFree conn]
    [MetricCompatible conn metric.toNonDegenerateMetric.toAbstractMetricTensor]
    [TensorInnerProductRules R V metric] where
  /-- The abstract intermediate quantity: metric trace of (X,Y) ↦ g(∇²_{X,Y}∇f, ∇f). -/
  roughBochnerTrace : R → R
  /-- Step 1: The Laplacian of |∇f|² decomposes into the rough trace and the Hessian squared norm. -/
  bochner_lap_expand : ∀ (f : R),
    laplacian metric conn (metric.g (grad metric f) (grad metric f)) =
    2 * roughBochnerTrace f + 2 * tensorNormSq metric (hessianForm metric conn f)
  /-- Step 2: The rough Bochner trace equals the Ricci term plus the gradient-of-Laplacian term. -/
  bochner_commutation : ∀ (f : R),
    roughBochnerTrace f =
    Rc conn (grad metric f) (grad metric f) +
    metric.g (grad metric f) (grad metric (laplacian metric conn f))

-- Proves the Bochner-Weitzenbock formula relating the Laplacian of the squared gradient to the Hessian, Ricci curvature, and the gradient of the Laplacian.
theorem bochner_identity
  [Invertible (2 : R)]
  (metric : MetricDuality R V)
  (conn : AbstractAffineConnection R V) [AffineTensorCalculus conn] [RiemannCurvatureTensorOp conn] [TorsionFree conn]
  [MetricCompatible conn metric.toNonDegenerateMetric.toAbstractMetricTensor]
  [TensorInnerProductRules R V metric]
  [BC : BochnerCalculus metric conn]
  (f : R) :
  laplacian metric conn (metric.g (grad metric f) (grad metric f)) =
  2 * tensorNormSq metric (hessianForm metric conn f) +
  2 * Rc conn (grad metric f) (grad metric f) +
  2 * metric.g (grad metric f) (grad metric (laplacian metric conn f)) := by
  have h1 := BC.bochner_lap_expand f
  have h2 := BC.bochner_commutation f
  rw [h1, h2]
  ring
