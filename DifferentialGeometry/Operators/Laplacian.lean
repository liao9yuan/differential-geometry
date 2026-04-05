import DifferentialGeometry.Algebra.VectorField
import DifferentialGeometry.Algebra.Metric
import DifferentialGeometry.Operators.Hessian
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Abel
import DifferentialGeometry.Geometry.Connection
import DifferentialGeometry.Operators.CovariantDerivative

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

open AbstractDerivationAction DifferentialGeometry.Bridge TensorAlgebra

variable {R V : Type}
variable [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
variable [AbstractDerivationAction R V]

/-- Laplacian of a function defined as the metric trace of its Hessian: `Δu = tr_g(∇²u)`.
Input: (AbstractMetricTensor R V, AbstractAffineConnection R V, R)
Output: R -/
def laplacian (metric : AbstractMetricTensor R V) [MetricTraceOperator R V metric]
    (conn : AbstractAffineConnection R V) (u : R) : R :=
  MetricTraceOperator.metric_trace metric (Hess conn u)

/-- $\Delta(f+g) = \Delta f + \Delta g$ -/
lemma laplacian_add (metric : AbstractMetricTensor R V) [MetricTraceOperator R V metric]
  [MetricTraceRules R V metric] (conn : AbstractAffineConnection R V) [AbstractLieBracket V] [DerivationRules R V] (f g : R) :
  laplacian metric conn (f + g) = laplacian metric conn f + laplacian metric conn g := by
  dsimp [laplacian]
  have hessian_add : Hess conn (f + g) = (fun X Y => Hess conn f X Y + Hess conn g X Y) := by
    funext X Y
    dsimp [Hess]
    have h1 : action Y (f + g) = action Y f + action Y g := DerivationRules.action_add_right Y f g
    rw [h1]
    have h2 : action X (action Y f + action Y g) = action X (action Y f) + action X (action Y g) := DerivationRules.action_add_right X (action Y f) (action Y g)
    rw [h2]
    have h3 : action (conn.nabla X Y) (f + g) = action (conn.nabla X Y) f + action (conn.nabla X Y) g := DerivationRules.action_add_right (conn.nabla X Y) f g
    rw [h3]
    ring
  rw [hessian_add]
  exact MetricTraceRules.trace_add (metric := metric) (fun X Y => Hess conn f X Y) (fun X Y => Hess conn g X Y)

/-- $\Delta(f-g) = \Delta f - \Delta g$ -/
lemma laplacian_sub (metric : AbstractMetricTensor R V) [MetricTraceOperator R V metric]
  [MetricTraceRules R V metric] (conn : AbstractAffineConnection R V) [AbstractLieBracket V] [DerivationRules R V] (f g : R) :
  laplacian metric conn (f - g) = laplacian metric conn f - laplacian metric conn g := by
  dsimp [laplacian]
  have action_sub : ∀ (X : V) (f g : R), action X (f - g) = action X f - action X g := by
    intro X f g
    have hz : f - g = f + -g := sub_eq_add_neg f g
    rw [hz]
    have h1 : action X (f + -g) = action X f + action X (-g) := DerivationRules.action_add_right X f (-g)
    rw [h1]
    have hneg : action X (-g) = - action X g := action_neg X g
    rw [hneg]
    exact (sub_eq_add_neg (action X f) (action X g)).symm
  have hessian_sub : Hess conn (f - g) = (fun X Y => Hess conn f X Y - Hess conn g X Y) := by
    funext X Y
    dsimp [Hess]
    have h1 : action Y (f - g) = action Y f - action Y g := action_sub Y f g
    rw [h1]
    have h2 : action X (action Y f - action Y g) = action X (action Y f) - action X (action Y g) := action_sub X (action Y f) (action Y g)
    rw [h2]
    have h3 : action (conn.nabla X Y) (f - g) = action (conn.nabla X Y) f - action (conn.nabla X Y) g := action_sub (conn.nabla X Y) f g
    rw [h3]
    ring
  rw [hessian_sub]
  have h_sub : (fun X Y => Hess conn f X Y - Hess conn g X Y) = ((fun X Y => Hess conn f X Y) + (fun X Y => (-1:R) * Hess conn g X Y)) := by
    funext X Y
    calc Hess conn f X Y - Hess conn g X Y = Hess conn f X Y - 1 * Hess conn g X Y := by ring
      _ = Hess conn f X Y + (-1:R) * Hess conn g X Y := by ring
  rw [h_sub]
  have t1 : MetricTraceOperator.metric_trace metric ((fun X Y => Hess conn f X Y) + (fun X Y => (-1:R) * Hess conn g X Y)) = MetricTraceOperator.metric_trace metric (fun X Y => Hess conn f X Y) + MetricTraceOperator.metric_trace metric (fun X Y => (-1:R) * Hess conn g X Y) := MetricTraceRules.trace_add (metric := metric) (fun X Y => Hess conn f X Y) (fun X Y => (-1:R) * Hess conn g X Y)
  rw [t1]
  have t2 : MetricTraceOperator.metric_trace metric (fun X Y => (-1:R) * Hess conn g X Y) = (-1:R) * MetricTraceOperator.metric_trace metric (fun X Y => Hess conn g X Y) := MetricTraceRules.trace_smul (metric := metric) (-1:R) (fun X Y => Hess conn g X Y)
  rw [t2]
  ring

section GenericLaplacian

/-- 
Operator mapping a generic V → V → Tensor form into its metric trace. 
Used for constructing the generic Laplacian from the second covariant derivative.
-/
class MetricTensorTraceOperator {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
    (metric : AbstractMetricTensor R V) {r s : ℕ} where
  metric_trace_tensor : (V → V → AbstractTensor R V r s) → AbstractTensor R V r s

/-- 
Requirements for trace linearity on the generalized trace operator. 
-/
class MetricTensorTraceRules {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
    (metric : AbstractMetricTensor R V) {r s : ℕ} [MetricTensorTraceOperator metric (r := r) (s := s)] where
  trace_add : ∀ (A B : V → V → AbstractTensor R V r s),
    MetricTensorTraceOperator.metric_trace_tensor metric (fun X Y => TensorAlgebra.add (A X Y) (B X Y)) =
    TensorAlgebra.add (MetricTensorTraceOperator.metric_trace_tensor metric A) (MetricTensorTraceOperator.metric_trace_tensor metric B)
  trace_smul : ∀ (c : R) (A : V → V → AbstractTensor R V r s),
    MetricTensorTraceOperator.metric_trace_tensor metric (fun X Y => TensorAlgebra.smul c (A X Y)) =
    TensorAlgebra.smul c (MetricTensorTraceOperator.metric_trace_tensor metric A)

/-- 
The second covariant derivative $\nabla^2_{X,Y} T$ for an arbitrary tensor.
Defined as $\nabla_X (\nabla_Y T) - \nabla_{\nabla_X Y} T$.
-/
def SecondCovDerivTensor {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] [AbstractDerivationAction R V]
    (conn : AbstractAffineConnection R V) [AffineTensorCalculus conn]
    {r s : ℕ} (T : AbstractTensor R V r s) (X Y : V) : AbstractTensor R V r s :=
  let nXY_T := genericCovDeriv conn (conn.nabla X Y) T
  let nY_T := genericCovDeriv conn Y T
  let nX_nY_T := genericCovDeriv conn X nY_T
  TensorAlgebra.add nX_nY_T (TensorAlgebra.smul (-1:R) nXY_T)

/--
The generic rough tensor Laplacian $\Delta T$.
Constructed as $\text{tr}_g(\nabla^2 T)$.
-/
def genericLaplacian {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] [AbstractDerivationAction R V]
    (metric : AbstractMetricTensor R V) {r s : ℕ} [MetricTensorTraceOperator metric (r := r) (s := s)]
    (conn : AbstractAffineConnection R V) [AffineTensorCalculus conn]
    (T : AbstractTensor R V r s) : AbstractTensor R V r s :=
  MetricTensorTraceOperator.metric_trace_tensor metric (SecondCovDerivTensor conn T)

end GenericLaplacian

