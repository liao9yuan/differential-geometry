import DifferentialGeometry.Synthetic.Algebra.VectorField
import DifferentialGeometry.Synthetic.Algebra.Trace
import DifferentialGeometry.Synthetic.Algebra.Metric
import DifferentialGeometry.Synthetic.Geometry.Connection
import DifferentialGeometry.Synthetic.Operator.Gradient
import DifferentialGeometry.Synthetic.Algebra.Trace
import DifferentialGeometry.Synthetic.Operator.Bochner
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

open DifferentialGeometry.Bridge TensorAlgebra

variable {R V : Type}
variable [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
variable [AbstractDerivationAction R V]

open AbstractDerivationAction

/-!
# Divergence Operator
Algebraic definition of the divergence of a vector field.
-/

/-- Divergence operator defined as the trace of the covariant derivative. -/
def divergence (metric : AbstractMetricTensor R V) [MetricTraceOperator R V metric] (conn : AbstractAffineConnection R V) (X : V) : R :=
  MetricTraceOperator.metric_trace metric (fun Y Z => metric.g (conn.nabla Y X) Z)

-- Proves the Leibniz rule for the divergence of a scalar-multiplied vector field.
lemma divergence_smul (metric : MetricDuality R V) [MetricTraceOperator R V metric.toNonDegenerateMetric.toAbstractMetricTensor] [MetricTraceRules R V metric.toNonDegenerateMetric.toAbstractMetricTensor] [MetricTraceRankOneRules R V metric.toNonDegenerateMetric.toAbstractMetricTensor] (conn : AbstractAffineConnection R V) (f : R) (X : V) :
    divergence metric.toNonDegenerateMetric.toAbstractMetricTensor conn (f • X) = f * divergence metric.toNonDegenerateMetric.toAbstractMetricTensor conn X + action X f := by
  dsimp [divergence]
  have h1 : (fun Y Z => metric.g (conn.nabla Y (f • X)) Z) =
            (fun Y Z => metric.g ((action Y f) • X + f • (conn.nabla Y X)) Z) := by
    funext Y Z
    rw [conn.leibniz]
  rw [h1]
  have h2 : (fun Y Z => metric.g ((action Y f) • X + f • (conn.nabla Y X)) Z) =
            (fun Y Z => action Y f * metric.g X Z + f * metric.g (conn.nabla Y X) Z) := by
    funext Y Z
    rw [metric.bilinear_add_left, metric.bilinear_smul_left, metric.bilinear_smul_left]
  rw [h2]
  rw [MetricTraceRules.trace_add]
  rw [MetricTraceRules.trace_smul]
  -- Isolate the rank-1 term
  have h_rank_one : (fun Y Z => action Y f * metric.g X Z) = (fun Y Z => metric.g (grad metric f) Y * metric.g X Z) := by
    funext Y Z
    have h_grad := g_grad metric f Y
    rw [← h_grad]
  rw [h_rank_one]
  -- Apply the fundamental linear algebra rule
  rw [MetricTraceRankOneRules.trace_rank_one (metric := metric.toNonDegenerateMetric.toAbstractMetricTensor) (grad metric f) X]
  -- Convert the gradient inner product back to the derivation action
  have h_grad_X := g_grad metric f X
  rw [h_grad_X]
  ring

/-!
# Integration and Divergence Theorem
Axiomatization of the global integral to establish integration by parts.
-/

/-- Abstract global integration operator. -/
class IntegralOperator (R : Type) [CommRing R] where
  integral : R → R
  integral_add : ∀ f g : R, integral (f + g) = integral f + integral g
  integral_smul : ∀ (c f : R), integral (c * f) = c * integral f

/-- The Divergence Theorem as an axiom (integral of divergence vanishes). -/
class DivergenceTheorem (metric : AbstractMetricTensor R V) [MetricTraceOperator R V metric] (conn : AbstractAffineConnection R V) [IntegralOperator R] where
  integral_div_zero : ∀ X : V, IntegralOperator.integral (divergence metric conn X) = 0

-- Proves Green's first identity (Integration by parts) for a vector field and a scalar function.
theorem integration_by_parts (metric : MetricDuality R V) [MetricTraceOperator R V metric.toNonDegenerateMetric.toAbstractMetricTensor]
    [MetricTraceRules R V metric.toNonDegenerateMetric.toAbstractMetricTensor] [MetricTraceRankOneRules R V metric.toNonDegenerateMetric.toAbstractMetricTensor] (conn : AbstractAffineConnection R V)
    [IntegralOperator R] [DivergenceTheorem metric.toNonDegenerateMetric.toAbstractMetricTensor conn] (f : R) (X : V) :
    IntegralOperator.integral (f * divergence metric.toNonDegenerateMetric.toAbstractMetricTensor conn X) + IntegralOperator.integral (action X f) = 0 := by
  have h_div_smul : divergence metric.toNonDegenerateMetric.toAbstractMetricTensor conn (f • X) = f * divergence metric.toNonDegenerateMetric.toAbstractMetricTensor conn X + action X f :=
    divergence_smul metric conn f X
  have h_int_eq : IntegralOperator.integral (divergence metric.toNonDegenerateMetric.toAbstractMetricTensor conn (f • X)) =
                  IntegralOperator.integral (f * divergence metric.toNonDegenerateMetric.toAbstractMetricTensor conn X + action X f) := by
    rw [h_div_smul]
  rw [IntegralOperator.integral_add] at h_int_eq
  have h_zero : IntegralOperator.integral (divergence metric.toNonDegenerateMetric.toAbstractMetricTensor conn (f • X)) = 0 :=
    DivergenceTheorem.integral_div_zero (X := f • X)
  rw [h_zero] at h_int_eq
  exact h_int_eq.symm
