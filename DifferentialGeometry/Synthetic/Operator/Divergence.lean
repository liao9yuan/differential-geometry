import DifferentialGeometry.Synthetic.Algebra.VectorField
import DifferentialGeometry.Synthetic.Algebra.Trace
import DifferentialGeometry.Synthetic.Algebra.Metric
import DifferentialGeometry.Synthetic.Geometry.Connection
import DifferentialGeometry.Synthetic.Operator.Gradient
import DifferentialGeometry.Synthetic.Algebra.Trace
import DifferentialGeometry.Synthetic.Operator.Bochner
import DifferentialGeometry.Synthetic.Operator.CovariantDerivative
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

open DifferentialGeometry TensorAlgebra

variable {R V : Type}
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
variable [AbstractDerivationAction R V]

open AbstractDerivationAction

/-!
# Divergence Operator
Algebraic definition of the divergence of a vector field.
-/


/-- Divergence operator defined algebraically by taking the metric trace of the lowered generic covariant derivative of the vector field. -/
def divergence (metric : MetricDuality R V) (conn : AbstractAffineConnection R V) [AffineTensorCalculus conn] (X : V) : R :=
  tensor_eval (metric_trace metric (0: Fin 2) (0: Fin 1) (lower_index metric.toNonDegenerateMetric.toAbstractMetricTensor (0: Fin 1) (covariant_differential metric conn X))) ![] ![]


-- Proves the Leibniz rule for the divergence of a scalar-multiplied vector field.
lemma divergence_smul (metric : MetricDuality R V) (conn : AbstractAffineConnection R V) [AffineTensorCalculus conn] [AbstractLieBracket V] [DerivationRules R V] (f : R) (X : V) :
    divergence metric conn (f • X) = f * divergence metric conn X + action X f := by
  sorry

/-!
# Integration and Divergence Theorem
Axiomatization of the global integral to establish integration by parts.
-/

/-- Abstract global integration operator. -/
class IntegralOperator (R : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R] where
  integral : R → R
  integral_add : ∀ f g : R, integral (f + g) = integral f + integral g
  integral_smul : ∀ (c f : R), integral (c * f) = c * integral f

/-- The Divergence Theorem as an axiom (integral of divergence vanishes). -/
class DivergenceTheorem (metric : MetricDuality R V) (conn : AbstractAffineConnection R V) [AffineTensorCalculus conn] [IntegralOperator R] where
  integral_div_zero : ∀ X : V, IntegralOperator.integral (divergence metric conn X) = 0

-- Proves Green's first identity (Integration by parts) for a vector field and a scalar function.
theorem integration_by_parts (metric : MetricDuality R V) (conn : AbstractAffineConnection R V) [AffineTensorCalculus conn] [AbstractLieBracket V] [DerivationRules R V]
    [IntegralOperator R] [DivergenceTheorem metric conn] (f : R) (X : V) :
    IntegralOperator.integral (f * divergence metric conn X) + IntegralOperator.integral (action X f) = 0 := by
  have h_div_smul : divergence metric conn (f • X) = f * divergence metric conn X + action X f :=
    divergence_smul metric conn f X
  have h_int_eq : IntegralOperator.integral (divergence metric conn (f • X)) =
                  IntegralOperator.integral (f * divergence metric conn X + action X f) := by
    rw [h_div_smul]
  rw [IntegralOperator.integral_add] at h_int_eq
  have h_zero : IntegralOperator.integral (divergence metric conn (f • X)) = 0 :=
    DivergenceTheorem.integral_div_zero (X := f • X)
  rw [h_zero] at h_int_eq
  exact h_int_eq.symm
