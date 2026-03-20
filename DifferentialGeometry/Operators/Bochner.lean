import DifferentialGeometry.Algebra.VectorField
import DifferentialGeometry.Algebra.Metric
import DifferentialGeometry.Geometry.Connection
import DifferentialGeometry.Operators.Hessian
import DifferentialGeometry.Operators.Laplacian
import DifferentialGeometry.Geometry.Curvature
import DifferentialGeometry.Geometry.RicciIdentity
import DifferentialGeometry.Operators.Gradient
import DifferentialGeometry.Analysis.TensorInnerProduct
import DifferentialGeometry.Bridge.Defs
import DifferentialGeometry.Algebra.BilinearForm
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open AbstractDerivationAction AbstractLieBracket DifferentialGeometry.Bridge TensorAlgebra

variable {R V : Type}
variable [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
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

-- Define the Hessian as a SmoothBilinearForm so we can take its tensor norm squared.
def hessianForm (metric : MetricDuality R V) (conn : AbstractAffineConnection R V) [MetricCompatible conn metric.toNonDegenerateMetric.toAbstractMetricTensor] (f : R) : AbstractBilinearForm R V :=
  fromBilinear
    { toFun := fun X =>
        { toFun := fun Y => metric.g (conn.nabla X (grad metric f)) Y
          map_add' := fun Y1 Y2 => by
            rw [metric.symm _ (Y1 + Y2), metric.bilinear_add_left Y1 Y2 _, metric.symm _ Y1, metric.symm _ Y2]
          map_smul' := fun c Y => by
            change metric.g (conn.nabla X (grad metric f)) (c • Y) = c • metric.g (conn.nabla X (grad metric f)) Y
            rw [metric.symm _ (c • Y), metric.bilinear_smul_left c Y _, metric.symm _ Y]
            rfl }
      map_add' := fun X1 X2 => LinearMap.ext fun Y => by
        change metric.g (conn.nabla (X1 + X2) (grad metric f)) Y = metric.g (conn.nabla X1 (grad metric f)) Y + metric.g (conn.nabla X2 (grad metric f)) Y
        rw [conn.nabla_add_left, metric.bilinear_add_left]
      map_smul' := fun c X => LinearMap.ext fun Y => by
        change metric.g (conn.nabla (c • X) (grad metric f)) Y = c • metric.g (conn.nabla X (grad metric f)) Y
        rw [conn.nabla_smul_left, metric.bilinear_smul_left]
        rfl }


omit [AbstractLieBracket V] [DerivationRules R V] in
lemma hessian_eq_g_nabla_grad
  (metric : MetricDuality R V)
  (conn : AbstractAffineConnection R V) [MetricCompatible conn metric.toNonDegenerateMetric.toAbstractMetricTensor]
  (f : R) (X Y : V) :
  Hess conn f X Y = metric.g (conn.nabla X (grad metric f)) Y := by
  dsimp [Hess]
  have h1 : action Y f = metric.g (grad metric f) Y := (g_grad metric f Y).symm
  rw [h1]
  rw [MetricCompatible.compat (conn := conn) X (grad metric f) Y]
  have sx : metric.g (grad metric f) (conn.nabla X Y) = metric.g (conn.nabla X Y) (grad metric f) := metric.symm _ _
  rw [sx]
  have g_grad_nabla : metric.g (conn.nabla X Y) (grad metric f) = action (conn.nabla X Y) f := by
    rw [metric.symm (conn.nabla X Y) (grad metric f)]
    exact g_grad metric f (conn.nabla X Y)
  rw [g_grad_nabla]
  abel

lemma eval02_hessianForm
  (metric : MetricDuality R V)
  (conn : AbstractAffineConnection R V) [MetricCompatible conn metric.toNonDegenerateMetric.toAbstractMetricTensor]
  (f : R) (X Y : V) :
  eval02 (hessianForm metric conn f) X Y = Hess conn f X Y := by
  dsimp [hessianForm, eval02]
  rw [TensorAlgebra.contract_fromBilinear]
  dsimp
  exact (hessian_eq_g_nabla_grad metric conn f X Y).symm

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

class BochnerTraceRules (metric : MetricDuality R V) [MetricTraceOperator R V metric.toNonDegenerateMetric.toAbstractMetricTensor]
  (conn : AbstractAffineConnection R V) [TraceOperator R V] [MetricCompatible conn metric.toNonDegenerateMetric.toAbstractMetricTensor] where
  trace_second_cov_deriv : ∀ f : R,
    MetricTraceOperator.metric_trace metric.toNonDegenerateMetric.toAbstractMetricTensor (fun X Y => metric.g (secondCovDeriv conn X Y (grad metric f)) (grad metric f)) =
    Rc conn (grad metric f) (grad metric f) + metric.g (grad metric f) (grad metric (laplacian metric.toNonDegenerateMetric.toAbstractMetricTensor conn f))
  trace_norm_sq : ∀ f : R,
    MetricTraceOperator.metric_trace metric.toNonDegenerateMetric.toAbstractMetricTensor (fun X Y => metric.g (conn.nabla X (grad metric f)) (conn.nabla Y (grad metric f))) =
    tensorNormSq metric (hessianForm metric conn f)

-- Proves the Bochner-Weitzenbock formula relating the Laplacian of the squared gradient to the Hessian, Ricci curvature, and the gradient of the Laplacian.
theorem bochner_identity
  [Invertible (2 : R)] [TraceOperator R V]
  (metric : MetricDuality R V)
  [MetricTraceOperator R V metric.toNonDegenerateMetric.toAbstractMetricTensor] [MetricTraceRules R V metric.toNonDegenerateMetric.toAbstractMetricTensor]
  (conn : AbstractAffineConnection R V) [MetricCompatible conn metric.toNonDegenerateMetric.toAbstractMetricTensor] [TorsionFree conn]
  [bochner_rules : BochnerTraceRules metric conn]
  (f : R) :
  laplacian metric.toNonDegenerateMetric.toAbstractMetricTensor conn (metric.g (grad metric f) (grad metric f)) =
  2 * tensorNormSq metric (hessianForm metric conn f) +
  2 * Rc conn (grad metric f) (grad metric f) +
  2 * metric.g (grad metric f) (grad metric (laplacian metric.toNonDegenerateMetric.toAbstractMetricTensor conn f)) := by
  have hl : laplacian metric.toNonDegenerateMetric.toAbstractMetricTensor conn (metric.g (grad metric f) (grad metric f)) = MetricTraceOperator.metric_trace metric.toNonDegenerateMetric.toAbstractMetricTensor (Hess conn (metric.g (grad metric f) (grad metric f))) := rfl
  rw [hl]
  have h1 : MetricTraceOperator.metric_trace metric.toNonDegenerateMetric.toAbstractMetricTensor (Hess conn (metric.g (grad metric f) (grad metric f))) =
            MetricTraceOperator.metric_trace metric.toNonDegenerateMetric.toAbstractMetricTensor (fun X Y => 2 * metric.g (secondCovDeriv conn X Y (grad metric f)) (grad metric f) + 2 * metric.g (conn.nabla X (grad metric f)) (conn.nabla Y (grad metric f))) := by
    have h_hess : Hess conn (metric.g (grad metric f) (grad metric f)) = fun X Y => 2 * metric.g (secondCovDeriv conn X Y (grad metric f)) (grad metric f) + 2 * metric.g (conn.nabla X (grad metric f)) (conn.nabla Y (grad metric f)) := by
      funext X Y
      exact hessian_norm_sq_grad metric conn f X Y
    rw [h_hess]
  rw [h1]
  rw [MetricTraceRules.trace_add]
  have h_smul1 : MetricTraceOperator.metric_trace metric.toNonDegenerateMetric.toAbstractMetricTensor (fun X Y => 2 * metric.g (secondCovDeriv conn X Y (grad metric f)) (grad metric f)) = 2 * MetricTraceOperator.metric_trace metric.toNonDegenerateMetric.toAbstractMetricTensor (fun X Y => metric.g (secondCovDeriv conn X Y (grad metric f)) (grad metric f)) := MetricTraceRules.trace_smul 2 _
  have h_smul2 : MetricTraceOperator.metric_trace metric.toNonDegenerateMetric.toAbstractMetricTensor (fun X Y => 2 * metric.g (conn.nabla X (grad metric f)) (conn.nabla Y (grad metric f))) = 2 * MetricTraceOperator.metric_trace metric.toNonDegenerateMetric.toAbstractMetricTensor (fun X Y => metric.g (conn.nabla X (grad metric f)) (conn.nabla Y (grad metric f))) := MetricTraceRules.trace_smul 2 _
  rw [h_smul1, h_smul2]
  have h_sq : MetricTraceOperator.metric_trace metric.toNonDegenerateMetric.toAbstractMetricTensor (fun X Y => metric.g (conn.nabla X (grad metric f)) (conn.nabla Y (grad metric f))) = tensorNormSq metric (hessianForm metric conn f) := bochner_rules.trace_norm_sq f
  rw [h_sq]
  have h_sec : MetricTraceOperator.metric_trace metric.toNonDegenerateMetric.toAbstractMetricTensor (fun X Y => metric.g (secondCovDeriv conn X Y (grad metric f)) (grad metric f)) = Rc conn (grad metric f) (grad metric f) + metric.g (grad metric f) (grad metric (laplacian metric.toNonDegenerateMetric.toAbstractMetricTensor conn f)) := bochner_rules.trace_second_cov_deriv f
  rw [h_sec]
  ring
