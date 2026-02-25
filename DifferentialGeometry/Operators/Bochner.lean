import DifferentialGeometry.Algebra.Basic
import DifferentialGeometry.Algebra.Metric
import DifferentialGeometry.Geometry.Connection
import DifferentialGeometry.Operators.Hessian
import DifferentialGeometry.Operators.Laplacian
import DifferentialGeometry.Geometry.Curvature
import DifferentialGeometry.Geometry.RicciIdentity
import DifferentialGeometry.Operators.Gradient
import DifferentialGeometry.Analysis.TensorInnerProduct
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false

open DerivationAction
open LieBracket

variable {R V : Type}
variable [CommRing R] [AddCommGroup V] [Module R V]
variable [DerivationAction R V]

class MusicalIsomorphismRules (metric : MetricTensor R V) [iso : MusicalIsomorphism R V metric] where
  g_grad : ∀ (f : R) (X : V), metric.g (grad metric f) X = action X f

-- Proves the expansion of the directional derivative of the squared norm of the gradient.
lemma grad_norm_sq_deriv
  (metric : MetricTensor R V) [iso : MusicalIsomorphism R V metric]
  (conn : AffineConnection R V) [MetricCompatible conn metric]
  (f : R) (X : V) :
  action X (metric.g (grad metric f) (grad metric f)) =
  metric.g (conn.nabla X (grad metric f)) (grad metric f) + metric.g (conn.nabla X (grad metric f)) (grad metric f) := by
  exact norm_sq_deriv conn metric X (grad metric f)

-- Proves the swapping of third-order derivatives of a function by injecting the Riemann curvature tensor.
lemma hessian_commute_ricci [LieBracket V]
  (conn : AffineConnection R V) [TorsionFree conn]
  (metric : MetricTensor R V) [iso : MusicalIsomorphism R V metric]
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

variable [LieBracket V] [DerivationRules R V]

-- Define the Hessian as a SmoothBilinearForm so we can take its tensor norm squared.
def hessianForm (conn : AffineConnection R V) (f : R) : SmoothBilinearForm R V where
  val := Hess conn f
  add_left := fun X1 X2 Y => by
    dsimp [Hess]
    rw [DerivationRules.action_add_left X1 X2 (action Y f)]
    rw [conn.nabla_add_left X1 X2 Y]
    rw [DerivationRules.action_add_left (conn.nabla X1 Y) (conn.nabla X2 Y) f]
    abel
  smul_left := fun c X Y => by
    change action (ScalarMul.smul c X) (action Y f) - action (conn.nabla (ScalarMul.smul c X) Y) f = c * (action X (action Y f) - action (conn.nabla X Y) f)
    rw [DerivationRules.action_smul_left c X (action Y f)]
    rw [conn.nabla_smul_left c X Y]
    rw [DerivationRules.action_smul_left c (conn.nabla X Y) f]
    ring
  add_right := fun X Y1 Y2 => by
    dsimp [Hess]
    rw [DerivationRules.action_add_left Y1 Y2 f]
    rw [DerivationRules.action_add_right X (action Y1 f) (action Y2 f)]
    rw [conn.nabla_add_right X Y1 Y2]
    rw [DerivationRules.action_add_left (conn.nabla X Y1) (conn.nabla X Y2) f]
    abel
  smul_right := fun c X Y => by
    change action X (action (ScalarMul.smul c Y) f) - action (conn.nabla X (ScalarMul.smul c Y)) f = c * (action X (action Y f) - action (conn.nabla X Y) f)
    rw [DerivationRules.action_smul_left c Y f]
    rw [DerivationRules.action_smul_right X c (action Y f)]
    rw [conn.leibniz c X Y]
    rw [DerivationRules.action_add_left (ScalarMul.smul (action X c) Y) (ScalarMul.smul c (conn.nabla X Y)) f]
    rw [DerivationRules.action_smul_left (action X c) Y f]
    rw [DerivationRules.action_smul_left c (conn.nabla X Y) f]
    ring

omit [LieBracket V] [DerivationRules R V] in
lemma hessian_eq_g_nabla_grad
  (metric : MetricTensor R V) [iso : MusicalIsomorphism R V metric]
  [iso_rules : MusicalIsomorphismRules metric]
  (conn : AffineConnection R V) [MetricCompatible conn metric]
  (f : R) (X Y : V) :
  Hess conn f X Y = metric.g (conn.nabla X (grad metric f)) Y := by
  dsimp [Hess]
  have h1 : action Y f = metric.g (grad metric f) Y := (MusicalIsomorphismRules.g_grad f Y).symm
  rw [h1]
  rw [MetricCompatible.compat (conn := conn) X (grad metric f) Y]
  have sx : metric.g (grad metric f) (conn.nabla X Y) = metric.g (conn.nabla X Y) (grad metric f) := metric.symm _ _
  rw [sx]
  have g_grad_nabla : metric.g (conn.nabla X Y) (grad metric f) = action (conn.nabla X Y) f := by
    rw [metric.symm (conn.nabla X Y) (grad metric f)]
    exact (MusicalIsomorphismRules.g_grad f (conn.nabla X Y))
  rw [g_grad_nabla]
  abel

lemma hessian_norm_sq_grad
  (metric : MetricTensor R V) [iso : MusicalIsomorphism R V metric]
  [MusicalIsomorphismRules metric]
  (conn : AffineConnection R V) [MetricCompatible conn metric]
  (f : R) (X Y : V) :
  Hess conn (metric.g (grad metric f) (grad metric f)) X Y =
  2 * metric.g (secondCovDeriv conn X Y (grad metric f)) (grad metric f) +
  2 * metric.g (conn.nabla X (grad metric f)) (conn.nabla Y (grad metric f)) := by
  dsimp [Hess]
  have h1 : action Y (metric.g (grad metric f) (grad metric f)) = metric.g (conn.nabla Y (grad metric f)) (grad metric f) + metric.g (conn.nabla Y (grad metric f)) (grad metric f) := norm_sq_deriv conn metric Y (grad metric f)
  rw [h1]
  rw [DerivationRules.action_add_right]
  have h2 : action X (metric.g (conn.nabla Y (grad metric f)) (grad metric f)) = metric.g (conn.nabla X (conn.nabla Y (grad metric f))) (grad metric f) + metric.g (conn.nabla Y (grad metric f)) (conn.nabla X (grad metric f)) := MetricCompatible.compat (conn:=conn) X (conn.nabla Y (grad metric f)) (grad metric f)
  rw [h2]
  have h3 : action (conn.nabla X Y) (metric.g (grad metric f) (grad metric f)) = metric.g (conn.nabla (conn.nabla X Y) (grad metric f)) (grad metric f) + metric.g (conn.nabla (conn.nabla X Y) (grad metric f)) (grad metric f) := norm_sq_deriv conn metric (conn.nabla X Y) (grad metric f)
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

class BochnerTraceRules (metric : MetricTensor R V) [iso : MusicalIsomorphism R V metric] [MetricTraceOperator R V metric]
  (conn : AffineConnection R V) [TraceOperator R V] where
  trace_second_cov_deriv : ∀ f : R,
    MetricTraceOperator.metric_trace metric (fun X Y => metric.g (secondCovDeriv conn X Y (grad metric f)) (grad metric f)) =
    Rc conn (grad metric f) (grad metric f) + metric.g (grad metric f) (grad metric (laplacian metric conn f))
  trace_norm_sq : ∀ f : R,
    MetricTraceOperator.metric_trace metric (fun X Y => metric.g (conn.nabla X (grad metric f)) (conn.nabla Y (grad metric f))) =
    tensorNormSq metric (hessianForm conn f)

-- Proves the Bochner-Weitzenbock formula relating the Laplacian of the squared gradient to the Hessian, Ricci curvature, and the gradient of the Laplacian.
theorem bochner_identity
  [Invertible (2 : R)] [TraceOperator R V]
  (metric : MetricTensor R V) [iso : MusicalIsomorphism R V metric]
  [MusicalIsomorphismRules metric]
  [MetricTraceOperator R V metric] [MetricTraceRules R V metric]
  (conn : AffineConnection R V) [MetricCompatible conn metric] [TorsionFree conn]
  [bochner_rules : BochnerTraceRules metric conn]
  (f : R) :
  laplacian metric conn (metric.g (grad metric f) (grad metric f)) =
  2 * tensorNormSq metric (hessianForm conn f) +
  2 * Rc conn (grad metric f) (grad metric f) +
  2 * metric.g (grad metric f) (grad metric (laplacian metric conn f)) := by
  have hl : laplacian metric conn (metric.g (grad metric f) (grad metric f)) = MetricTraceOperator.metric_trace metric (Hess conn (metric.g (grad metric f) (grad metric f))) := rfl
  rw [hl]
  have h1 : MetricTraceOperator.metric_trace metric (Hess conn (metric.g (grad metric f) (grad metric f))) =
            MetricTraceOperator.metric_trace metric (fun X Y => 2 * metric.g (secondCovDeriv conn X Y (grad metric f)) (grad metric f) + 2 * metric.g (conn.nabla X (grad metric f)) (conn.nabla Y (grad metric f))) := by
    have h_hess : Hess conn (metric.g (grad metric f) (grad metric f)) = fun X Y => 2 * metric.g (secondCovDeriv conn X Y (grad metric f)) (grad metric f) + 2 * metric.g (conn.nabla X (grad metric f)) (conn.nabla Y (grad metric f)) := by
      funext X Y
      exact hessian_norm_sq_grad metric conn f X Y
    rw [h_hess]
  rw [h1]
  rw [MetricTraceRules.trace_add]
  have h_smul1 : MetricTraceOperator.metric_trace metric (fun X Y => 2 * metric.g (secondCovDeriv conn X Y (grad metric f)) (grad metric f)) = 2 * MetricTraceOperator.metric_trace metric (fun X Y => metric.g (secondCovDeriv conn X Y (grad metric f)) (grad metric f)) := MetricTraceRules.trace_smul 2 _
  have h_smul2 : MetricTraceOperator.metric_trace metric (fun X Y => 2 * metric.g (conn.nabla X (grad metric f)) (conn.nabla Y (grad metric f))) = 2 * MetricTraceOperator.metric_trace metric (fun X Y => metric.g (conn.nabla X (grad metric f)) (conn.nabla Y (grad metric f))) := MetricTraceRules.trace_smul 2 _
  rw [h_smul1, h_smul2]
  have h_sq : MetricTraceOperator.metric_trace metric (fun X Y => metric.g (conn.nabla X (grad metric f)) (conn.nabla Y (grad metric f))) = tensorNormSq metric (hessianForm conn f) := bochner_rules.trace_norm_sq f
  rw [h_sq]
  have h_sec : MetricTraceOperator.metric_trace metric (fun X Y => metric.g (secondCovDeriv conn X Y (grad metric f)) (grad metric f)) = Rc conn (grad metric f) (grad metric f) + metric.g (grad metric f) (grad metric (laplacian metric conn f)) := bochner_rules.trace_second_cov_deriv f
  rw [h_sec]
  ring
