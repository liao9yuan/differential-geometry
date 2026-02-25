import DifferentialGeometry.Algebra.Basic
import DifferentialGeometry.Algebra.Trace
import DifferentialGeometry.Algebra.Metric
import DifferentialGeometry.Geometry.Connection
import DifferentialGeometry.Operators.Gradient
import DifferentialGeometry.Analysis.TraceRankOne
import DifferentialGeometry.Operators.Bochner
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false

variable {R V : Type}
variable [CommRing R] [AddCommGroup V] [Module R V]
variable [DerivationAction R V]

open DerivationAction

/-!
# Divergence Operator
Algebraic definition of the divergence of a vector field.
-/

/-- Divergence operator defined as the trace of the covariant derivative. -/
def divergence (metric : MetricTensor R V) [MetricTraceOperator R V metric] (conn : AffineConnection R V) (X : V) : R :=
  MetricTraceOperator.metric_trace metric (fun Y Z => metric.g (conn.nabla Y X) Z)

-- Proves the Leibniz rule for the divergence of a scalar-multiplied vector field.
lemma divergence_smul (metric : MetricTensor R V) [MetricTraceOperator R V metric] [MetricTraceRules R V metric] [MetricTraceRankOneRules R V metric] [MusicalIsomorphism R V metric] [MusicalIsomorphismRules metric] (conn : AffineConnection R V) (f : R) (X : V) :
    divergence metric conn (ScalarMul.smul f X) = f * divergence metric conn X + action X f := by
  dsimp [divergence]
  have h1 : (fun Y Z => metric.g (conn.nabla Y (ScalarMul.smul f X)) Z) =
            (fun Y Z => metric.g (ScalarMul.smul (action Y f) X + ScalarMul.smul f (conn.nabla Y X)) Z) := by
    funext Y Z
    rw [conn.leibniz]
  rw [h1]
  have h2 : (fun Y Z => metric.g (ScalarMul.smul (action Y f) X + ScalarMul.smul f (conn.nabla Y X)) Z) =
            (fun Y Z => action Y f * metric.g X Z + f * metric.g (conn.nabla Y X) Z) := by
    funext Y Z
    rw [metric.bilinear_add_left, metric.bilinear_smul_left, metric.bilinear_smul_left]
  rw [h2]
  rw [MetricTraceRules.trace_add]
  rw [MetricTraceRules.trace_smul]
  -- Isolate the rank-1 term
  have h_rank_one : (fun Y Z => action Y f * metric.g X Z) = (fun Y Z => metric.g (grad metric f) Y * metric.g X Z) := by
    funext Y Z
    have h_grad := MusicalIsomorphismRules.g_grad (metric := metric) f Y
    rw [← h_grad]
  rw [h_rank_one]
  -- Apply the fundamental linear algebra rule
  rw [MetricTraceRankOneRules.trace_rank_one (metric := metric) (grad metric f) X]
  -- Convert the gradient inner product back to the derivation action
  have h_grad_X := MusicalIsomorphismRules.g_grad (metric := metric) f X
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
class DivergenceTheorem (metric : MetricTensor R V) [MetricTraceOperator R V metric] (conn : AffineConnection R V) [IntegralOperator R] where
  integral_div_zero : ∀ X : V, IntegralOperator.integral (divergence metric conn X) = 0

-- Proves Green's first identity (Integration by parts) for a vector field and a scalar function.
theorem integration_by_parts (metric : MetricTensor R V) [MetricTraceOperator R V metric]
    [MetricTraceRules R V metric] [MetricTraceRankOneRules R V metric] [MusicalIsomorphism R V metric] [MusicalIsomorphismRules metric] (conn : AffineConnection R V)
    [IntegralOperator R] [DivergenceTheorem metric conn] (f : R) (X : V) :
    IntegralOperator.integral (f * divergence metric conn X) + IntegralOperator.integral (action X f) = 0 := by
  have h_div_smul : divergence metric conn (ScalarMul.smul f X) = f * divergence metric conn X + action X f :=
    divergence_smul metric conn f X
  have h_int_eq : IntegralOperator.integral (divergence metric conn (ScalarMul.smul f X)) =
                  IntegralOperator.integral (f * divergence metric conn X + action X f) := by
    rw [h_div_smul]
  rw [IntegralOperator.integral_add] at h_int_eq
  have h_zero : IntegralOperator.integral (divergence metric conn (ScalarMul.smul f X)) = 0 :=
    DivergenceTheorem.integral_div_zero (X := ScalarMul.smul f X)
  rw [h_zero] at h_int_eq
  exact h_int_eq.symm
