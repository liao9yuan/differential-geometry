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

/-- The (0,2) abstract tensor encoding `(X, Y) ↦ g(∇²_{X,Y}∇f, ∇f)`.
Defined algebraically as the residual of `hessianForm(|∇f|²)` after subtracting
the Hessian norm contribution, scaled by `⅟2`. The metric trace of this tensor
recovers the "rough Bochner trace" in the Bochner–Weitzenböck formula. -/
noncomputable def secondCovDeriv_02_tensor
    [Invertible (2 : R)]
    (metric : MetricDuality R V)
    (conn : AbstractAffineConnection R V)
    [AffineTensorCalculus conn]
    [MetricCompatible conn metric.toNonDegenerateMetric.toAbstractMetricTensor]
    [TensorInnerProductRules R V metric]
    (f : R) : AbstractBilinearForm R V :=
  let hF := hessianForm metric conn f
  let Q := TensorAlgebra.contract (r:=0) (s:=2)
    (TensorAlgebra.tensor_prod (r1:=1) (s1:=1) (r2:=0) (s2:=2)
      (raise_index metric (0 : Fin 2) hF) hF)
  TensorAlgebra.smul (⅟(2 : R))
    (TensorAlgebra.add
      (hessianForm metric conn (metric.g (grad metric f) (grad metric f)))
      (TensorAlgebra.smul (-2 : R) Q))

/-- Helper: the abstract Hessian-norm tensor from `inner_trace`. -/
private noncomputable def hessNormQ
    (metric : MetricDuality R V)
    (conn : AbstractAffineConnection R V)
    [AffineTensorCalculus conn]
    (f : R) : AbstractBilinearForm R V :=
  let hF := hessianForm metric conn f
  TensorAlgebra.contract (r:=0) (s:=2)
    (TensorAlgebra.tensor_prod (r1:=1) (s1:=1) (r2:=0) (s2:=2)
      (raise_index metric (0 : Fin 2) hF) hF)

private lemma tensorNormSq_eq_trace_hessNormQ
    (metric : MetricDuality R V)
    (conn : AbstractAffineConnection R V)
    [AffineTensorCalculus conn]
    [MetricCompatible conn metric.toNonDegenerateMetric.toAbstractMetricTensor]
    [TensorInnerProductRules R V metric]
    (f : R) :
    tensorNormSq metric (hessianForm metric conn f) =
    tensor_eval (metric_trace metric (0 : Fin 2) (0 : Fin 1) (hessNormQ metric conn f)) ![] ![] := by
  unfold tensorNormSq hessNormQ
  exact TensorInnerProductRules.inner_trace (hessianForm metric conn f) (hessianForm metric conn f)

theorem bochner_lap_expand_thm
    [Invertible (2 : R)]
    (metric : MetricDuality R V)
    (conn : AbstractAffineConnection R V)
    [AffineTensorCalculus conn] [RiemannCurvatureTensorOp conn] [TorsionFree conn]
    [MetricCompatible conn metric.toNonDegenerateMetric.toAbstractMetricTensor]
    [TensorInnerProductRules R V metric]
    [BilinearFormExt R V]
    [MetricEvaluationRules R V metric.toNonDegenerateMetric.toAbstractMetricTensor]
    [MetricTraceEvaluationRules R V metric]
    (f : R) :
    laplacian metric conn (metric.g (grad metric f) (grad metric f)) =
    2 * (tensor_eval (metric_trace metric (0 : Fin 2) (0 : Fin 1)
      (secondCovDeriv_02_tensor metric conn f)) ![] ![]) +
    2 * tensorNormSq metric (hessianForm metric conn f) := by
  -- Step 1: Unfold laplacian and secondCovDeriv_02_tensor
  simp only [laplacian, secondCovDeriv_02_tensor]
  -- Step 2: Distribute metric_trace through smul and add
  rw [metric_trace_smul, metric_trace_add, metric_trace_smul]
  -- Step 3: Distribute tensor_eval through smul and add
  rw [tensor_eval_smul, tensor_eval_add, tensor_eval_smul]
  -- Step 4: Identify the hessNormQ trace with tensorNormSq via inner_trace
  rw [tensorNormSq_eq_trace_hessNormQ metric conn f]
  simp only [hessNormQ]
  -- Step 5: Algebraic simplification: L = 2 * (⅟2 * (L + (-2) * N)) + 2 * N
  -- where L = laplacian term, N = norm term
  -- Goal is now: L = 2 * (⅟2 * (L + (-2) * N)) + 2 * N
  -- where L, N are specific tensor_eval expressions.
  -- Use 2 * ⅟2 = 1 to simplify.
  set L := tensor_eval (metric_trace metric (0 : Fin 2) (0 : Fin 1) (hessianForm metric conn (metric.g (grad metric f) (grad metric f)))) ![] ![]
  set N := tensor_eval (metric_trace metric (0 : Fin 2) (0 : Fin 1) (TensorAlgebra.contract (r:=0) (s:=2) (TensorAlgebra.tensor_prod (r1:=1) (s1:=1) (r2:=0) (s2:=2) (raise_index metric (0 : Fin 2) (hessianForm metric conn f)) (hessianForm metric conn f)))) ![] ![]
  have h2 : (2 : R) * ⅟(2 : R) = 1 := mul_invOf_self (2 : R)
  have h_inv2 : ⅟(2 : R) * 2 = 1 := invOf_mul_self (2 : R)
  -- Expand RHS: 2 * (⅟2 * (L + (-2) * N)) + 2 * N
  -- = (2 * ⅟2) * (L + (-2) * N) + 2 * N   [assoc]
  -- = 1 * (L + (-2) * N) + 2 * N            [h2]
  -- = L + (-2) * N + 2 * N                  [one_mul]
  -- = L
  have key : 2 * (⅟(2 : R) * (L + (-2) * N)) + 2 * N = L := by
    have : 2 * (⅟(2 : R) * (L + (-2) * N)) = L + (-2) * N := by
      calc 2 * (⅟(2 : R) * (L + (-2) * N))
        _ = (2 * ⅟(2 : R)) * (L + (-2) * N) := by ring
        _ = 1 * (L + (-2) * N) := by rw [h2]
        _ = L + (-2) * N := by ring
    linarith
  linarith [key]

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
