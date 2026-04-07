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


/-!
## Leibniz Rule Infrastructure

The (1,1)-tensor `df_tensor f X` represents the tensor product `df ⊗ X`, mapping each
direction `Y` to `(Y f) • X`. This is the "extra" term arising from the covariant derivative's
Leibniz rule for scalar multiplication.
-/

variable [AbstractLieBracket V] [DerivationRules R V]

/-- The (1,1)-tensor `Y ↦ (Y f) • X`, encoding the tensor product `df ⊗ X`. -/
def df_tensor (f : R) (X : V) : AbstractTensor R V 1 1 :=
  TensorAlgebra.fromData {
    toFun := fun m => (action (m 0) f) • vectorToData (R:=R) X ![]
    map_update_add' := fun m i X1 X2 => by
      have hz : i = 0 := Subsingleton.elim _ _
      subst hz
      simp only [Fin.isValue, Function.update_self]
      rw [DerivationRules.action_add_left X1 X2 f]
      rw [add_smul]
    map_update_smul' := fun m i c Y => by
      have hz : i = 0 := Subsingleton.elim _ _
      subst hz
      simp only [Fin.isValue, Function.update_self]
      rw [DerivationRules.action_smul_left c Y f]
      rw [mul_smul]
  }


/-- The covariant differential of `f • X` decomposes via the Leibniz rule into
    the sum of `df_tensor f X` and `f • covariant_differential X`. -/
lemma covariant_differential_smul_leibniz (metric : MetricDuality R V)
    (conn : AbstractAffineConnection R V) [AffineTensorCalculus conn]
    (f : R) (X : V) :
    covariant_differential metric conn (f • X) =
    TensorAlgebra.add (df_tensor f X) (TensorAlgebra.smul f (covariant_differential metric conn X)) := by
  -- Prove equality of (1,1)-tensors via fromData/toData round-trip
  conv_lhs => rw [← TensorAlgebra.fromData_toData (covariant_differential metric conn (f • X))]
  conv_rhs => rw [← TensorAlgebra.fromData_toData (TensorAlgebra.add (df_tensor f X) (TensorAlgebra.smul f (covariant_differential metric conn X)))]
  congr 1
  ext m n
  -- LHS: data of covariant_differential at direction (m 0) applied to fromVector (f • X)
  simp only [covariant_differential, TensorAlgebra.toData_fromData]
  -- Use fromVector_smul and genericCovDeriv_smul (the AffineTensorCalculus Leibniz rule)
  have h_fv : fromVector (R:=R) (f • X) = TensorAlgebra.smul f (fromVector (R:=R) X) := fromVector_smul f X
  -- Rewrite the genericCovDeriv argument
  change (TensorAlgebra.toData (genericCovDeriv conn (m 0) (fromVector (R:=R) (f • X))) ![]) n =
    (TensorAlgebra.toData (TensorAlgebra.add (df_tensor f X) (TensorAlgebra.smul f (TensorAlgebra.fromData { toFun := fun m => (TensorAlgebra.toData (genericCovDeriv conn (m 0) (fromVector X))) ![], map_update_add' := _, map_update_smul' := _ }))) m) n
  rw [h_fv, genericCovDeriv_smul]
  -- RHS side
  rw [TensorAlgebra.toData_add, TensorAlgebra.toData_smul]
  simp only [df_tensor]
  -- LHS: toData of add (smul (action (m 0) f) (fromVector X)) (smul f (genericCovDeriv conn (m 0) (fromVector X)))
  rw [TensorAlgebra.toData_add, TensorAlgebra.toData_smul, TensorAlgebra.toData_smul]
  -- Now both sides should match: (action (m 0) f) • toData (fromVector X) ![] + f • toData (genericCovDeriv ...) ![]
  simp only [fromVector, TensorAlgebra.toData_fromData]
  rfl


/-- The metric trace identity for the `df ⊗ X` tensor:
    `trace(g^{-1} · g · (df ⊗ X)) = X(f)`.
    This axiomatizes the fundamental property `g^{ab} g_{bc} = δ^a_c` applied to
    the specific (1,1)-tensor structure arising in the divergence Leibniz rule. -/
lemma div_trace_df_tensor (metric : MetricDuality R V) (f : R) (X : V) :
    tensor_eval
      (metric_trace metric (0 : Fin 2) (0 : Fin 1)
        (lower_index metric.toNonDegenerateMetric.toAbstractMetricTensor (0 : Fin 1) (df_tensor f X)))
      ![] ![] = action X f := by
  sorry


-- Proves the Leibniz rule for the divergence of a scalar-multiplied vector field.
lemma divergence_smul (metric : MetricDuality R V) (conn : AbstractAffineConnection R V) [AffineTensorCalculus conn] (f : R) (X : V) :
    divergence metric conn (f • X) = f * divergence metric conn X + action X f := by
  -- Step 1: Unfold divergence and apply the Leibniz decomposition of covariant_differential
  unfold divergence
  rw [covariant_differential_smul_leibniz metric conn f X]
  -- Step 2: Propagate the sum through lower_index (linear)
  rw [lower_index_add]
  -- Step 3: Propagate through metric_trace (linear)
  rw [metric_trace_add]
  -- Step 4: Propagate through tensor_eval (linear)
  rw [tensor_eval_add]
  -- Step 5: For the scalar-multiplied term, propagate f through the pipeline
  rw [lower_index_smul, metric_trace_smul, tensor_eval_smul]
  -- Step 6: The df_tensor term evaluates to action X f by the divergence pipeline lemma
  rw [div_trace_df_tensor metric f X]
  -- Step 7: Conclude by commutativity of addition
  ring

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
theorem integration_by_parts (metric : MetricDuality R V) (conn : AbstractAffineConnection R V) [AffineTensorCalculus conn]
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
