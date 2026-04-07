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

/-- Formal derivation of the 1-form df functionally acting on vectors. -/
def df_covector (f : R) : V →ₗ[R] R where
  toFun := fun X => action X f
  map_add' := fun X1 X2 => DerivationRules.action_add_left X1 X2 f
  map_smul' := fun c X => DerivationRules.action_smul_left c X f

/-- The covariant differential of `f • X` decomposes via the Leibniz rule formally
    into the sum of the algebraic outer product and `f • covariant_differential X`. -/
lemma covariant_differential_smul_leibniz (metric : MetricDuality R V)
    (conn : AbstractAffineConnection R V) [AffineTensorCalculus conn]
    (f : R) (X : V) :
    covariant_differential metric conn (f • X) =
    TensorAlgebra.add (TensorAlgebra.outerProduct X (df_covector f)) (TensorAlgebra.smul f (covariant_differential metric conn X)) := by
  conv_lhs => rw [← TensorAlgebra.fromData_toData (covariant_differential metric conn (f • X))]
  conv_rhs => rw [← TensorAlgebra.fromData_toData (TensorAlgebra.add (TensorAlgebra.outerProduct X (df_covector f)) (TensorAlgebra.smul f (covariant_differential metric conn X)))]
  congr 1
  ext m n
  -- LHS
  simp only [covariant_differential, TensorAlgebra.toData_fromData]
  have h_fv : fromVector (R:=R) (f • X) = TensorAlgebra.smul f (fromVector (R:=R) X) := fromVector_smul f X
  change (TensorAlgebra.toData (genericCovDeriv conn (m 0) (fromVector (R:=R) (f • X))) ![]) n =
    (TensorAlgebra.toData (TensorAlgebra.add (TensorAlgebra.outerProduct X (df_covector f)) (TensorAlgebra.smul f (TensorAlgebra.fromData { toFun := fun m => (TensorAlgebra.toData (genericCovDeriv conn (m 0) (fromVector X))) ![], map_update_add' := _, map_update_smul' := _ }))) m) n
  rw [h_fv, genericCovDeriv_smul]
  -- LHS side sum
  rw [TensorAlgebra.toData_add, TensorAlgebra.toData_smul, TensorAlgebra.toData_smul]
  simp only [MultilinearMap.add_apply, MultilinearMap.smul_apply]
  -- RHS side
  rw [TensorAlgebra.toData_add, TensorAlgebra.toData_smul]
  simp only [MultilinearMap.add_apply, MultilinearMap.smul_apply]
  rw [TensorAlgebra.toData_outerProduct]
  simp only [df_covector, LinearMap.coe_mk, AddHom.coe_mk, fromVector, TensorAlgebra.toData_fromData]
  rfl

-- Proves the Leibniz rule for the divergence of a scalar-multiplied vector field natively.
lemma divergence_smul (metric : MetricDuality R V) (conn : AbstractAffineConnection R V) [AffineTensorCalculus conn] [MetricInverse R V metric] (f : R) (X : V) :
    divergence metric conn (f • X) = f * divergence metric conn X + action X f := by
  -- Step 1: Unfold divergence and apply the Leibniz decomposition functionally
  unfold divergence
  rw [covariant_differential_smul_leibniz metric conn f X]
  -- Step 2: Propagate the sum
  rw [lower_index_add, metric_trace_add, tensor_eval_add]
  -- Step 3: Propagate through the scalar multiplicative pipeline
  rw [lower_index_smul, metric_trace_smul, tensor_eval_smul]
  -- Step 4: Structurally collapse the inner trace term `metric_trace ∘ lower_index` into `contract`
  -- First expand metric_trace which uses `contract_general ... (raise_index)`
  unfold metric_trace
  -- Substitute the MetricInverse identity `raise_lower_id`
  rw [MetricInverse.raise_lower_id (TensorAlgebra.outerProduct X (df_covector f))]
  -- The expression evaluates to `tensor_eval (contract ...) ![] ![]`
  -- `contract_general` acting on (1,1) is exactly `contract` because index swaps of 0 for length 1 is eq.
  -- Wait, I should just use `contract_outerProduct` -- let's look at `contract_general_0_0` or natively.
  -- metric_trace uses `contract_general 0 0`.
  have h_c : TensorAlgebra.contract_general (R:=R) (V:=V) (r:=0) (s:=0) 0 0 (TensorAlgebra.outerProduct X (df_covector f)) = TensorAlgebra.contract (TensorAlgebra.outerProduct X (df_covector f)) := by
    rw [TensorAlgebra.contract_general_0_0]
  rw [h_c]
  -- Step 5: Native trace evaluation of the outer product provides `α X`.
  have h_val : tensor_eval (TensorAlgebra.contract (TensorAlgebra.outerProduct X (df_covector f))) ![] ![] = TensorAlgebra.toScalar (TensorAlgebra.contract (TensorAlgebra.outerProduct X (df_covector f))) := by
    dsimp [tensor_eval]
    exact (TensorAlgebra.toScalar_eq_toData _).symm
  rw [h_val]
  rw [TensorAlgebra.contract_outerProduct X (df_covector f)]
  -- Clean up
  have h_df : (df_covector f) X = action X f := rfl
  rw [h_df]
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
    [IntegralOperator R] [DivergenceTheorem metric conn] [MetricInverse R V metric] (f : R) (X : V) :
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
