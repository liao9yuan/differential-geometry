import DifferentialGeometry.Synthetic.Algebra.VectorField
import DifferentialGeometry.Synthetic.Geometry.Connection
import DifferentialGeometry.Synthetic.Operator.Gradient
import DifferentialGeometry.Synthetic.Operator.CovariantDerivative
import DifferentialGeometry.Synthetic.Algebra.Metric
import DifferentialGeometry.Synthetic.Algebra.TensorAlgebra
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

open DifferentialGeometry TensorAlgebra

variable {R V : Type}
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
variable [AbstractDerivationAction R V] [AbstractLieBracket V] [DerivationRules R V]

open AbstractDerivationAction

/-- Hessian of a function: `∇²u(X, Y) = X(Y(u)) - (∇_X Y)(u)`.
Input: (AbstractAffineConnection R V, R, V, V)
Output: R -/
def Hess (conn : AbstractAffineConnection R V) (u : R) (X Y : V) : R :=
  action X (action Y u) - action (conn.nabla X Y) u

open AbstractLieBracket

theorem hessian_symm [AbstractLieBracket V] [LieDerivation R V] [ActionLinear R V]
    (conn : AbstractAffineConnection R V) [TorsionFree conn] (u : R) (X Y : V) :
    Hess conn u X Y = Hess conn u Y X := by
  have t1 : conn.nabla X Y = conn.nabla Y X + bracket X Y := by
    calc conn.nabla X Y = conn.nabla X Y - conn.nabla Y X + conn.nabla Y X := by abel
      _ = bracket X Y + conn.nabla Y X := by rw [TorsionFree.torsion_zero (conn := conn)]
      _ = conn.nabla Y X + bracket X Y := by abel
  calc Hess conn u X Y
    _ = action X (action Y u) - action (conn.nabla X Y) u := rfl
    _ = action X (action Y u) - action (conn.nabla Y X + bracket X Y) u := by rw [t1]
    _ = action X (action Y u) - (action (conn.nabla Y X) u + action (bracket X Y) u) := by rw [ActionLinear.action_add]
    _ = action X (action Y u) - (action (conn.nabla Y X) u + (action X (action Y u) - action Y (action X u))) := by rw [LieDerivation.bracket_action]
    _ = action Y (action X u) - action (conn.nabla Y X) u := by ring
    _ = Hess conn u Y X := rfl



/-- Rigorous `(1,1)` tensor mapping representing the full generic covariant derivative `∇Z`. -/
def covariant_differential (_metric : MetricDuality R V) (conn : AbstractAffineConnection R V) [AffineTensorCalculus conn] (Z : V) : AbstractTensor R V 1 1 :=
  TensorAlgebra.fromData {
    toFun := fun m => (TensorAlgebra.toData (genericCovDeriv conn (m 0) (fromVector Z))) ![]
    map_update_add' := fun m i X1 X2 => by
      have hz : i = 0 := Subsingleton.elim _ _
      subst hz
      dsimp [genericCovDeriv, fromVector]
      rw [AffineTensorCalculus.nabla_vector]
      rw [AffineTensorCalculus.nabla_vector]
      rw [AffineTensorCalculus.nabla_vector]
      simp only [Fin.isValue, Function.update_self]
      rw [conn.nabla_add_left X1 X2 Z]
      rw [TensorAlgebra.toData_fromData]
      rw [TensorAlgebra.toData_fromData]
      rw [TensorAlgebra.toData_fromData]
      rw [vectorToData_add]
      rfl
    map_update_smul' := fun m i c X => by
      have hz : i = 0 := Subsingleton.elim _ _
      subst hz
      dsimp [genericCovDeriv, fromVector]
      rw [AffineTensorCalculus.nabla_vector]
      rw [AffineTensorCalculus.nabla_vector]
      simp only [Fin.isValue, Function.update_self]
      rw [conn.nabla_smul_left c X Z]
      rw [TensorAlgebra.toData_fromData]
      rw [TensorAlgebra.toData_fromData]
      rw [vectorToData_smul]
      rfl
  }

/-- Systematic definition: hessianForm as an AbstractTensor R V 0 2.
    Computed by lowering the contravariant index of the generic covariant derivative of the gradient. -/
def hessianForm (metric : MetricDuality R V) (conn : AbstractAffineConnection R V) [AffineTensorCalculus conn] (u : R) : AbstractTensor R V 0 2 :=
  lower_index metric.toNonDegenerateMetric.toAbstractMetricTensor (0: Fin 1) (covariant_differential metric conn (grad metric u))

-- Linearity of covariant_differential in its vector argument
lemma covariant_differential_add_vec (metric : MetricDuality R V) (conn : AbstractAffineConnection R V) [AffineTensorCalculus conn]
    (Z1 Z2 : V) :
    covariant_differential metric conn (Z1 + Z2) = TensorAlgebra.add (covariant_differential metric conn Z1) (covariant_differential metric conn Z2) := by
  conv_lhs => rw [← TensorAlgebra.fromData_toData (covariant_differential metric conn (Z1 + Z2))]
  conv_rhs => rw [← TensorAlgebra.fromData_toData (TensorAlgebra.add (covariant_differential metric conn Z1) (covariant_differential metric conn Z2))]
  congr 1
  rw [TensorAlgebra.toData_add]
  simp only [covariant_differential, TensorAlgebra.toData_fromData]
  ext m
  simp only [MultilinearMap.add_apply, fromVector_add, genericCovDeriv_add, TensorAlgebra.toData_add]
  rfl

-- Linearity of hessianForm in the scalar argument
lemma hessianForm_add (metric : MetricDuality R V) (conn : AbstractAffineConnection R V) [AffineTensorCalculus conn]
    (f g : R) :
    hessianForm metric conn (f + g) = TensorAlgebra.add (hessianForm metric conn f) (hessianForm metric conn g) := by
  unfold hessianForm
  rw [grad_add, covariant_differential_add_vec, lower_index_add]

-- Linearity of covariant_differential in its vector argument (scalar multiplication)
lemma covariant_differential_smul_vec (metric : MetricDuality R V) (conn : AbstractAffineConnection R V) [AffineTensorCalculus conn]
    (c : R) (Z : V) (hc : ∀ X : V, action X c = 0) :
    covariant_differential metric conn (c • Z) = TensorAlgebra.smul c (covariant_differential metric conn Z) := by
  conv_lhs => rw [← TensorAlgebra.fromData_toData (covariant_differential metric conn (c • Z))]
  conv_rhs => rw [← TensorAlgebra.fromData_toData (TensorAlgebra.smul c (covariant_differential metric conn Z))]
  congr 1
  rw [TensorAlgebra.toData_smul]
  simp only [covariant_differential, TensorAlgebra.toData_fromData]
  ext m i
  simp only [MultilinearMap.coe_mk, fromVector_smul, genericCovDeriv_smul, TensorAlgebra.toData_add, TensorAlgebra.toData_smul, MultilinearMap.add_apply, MultilinearMap.smul_apply]
  have hz : action (m 0) c = 0 := hc (m 0)
  rw [hz, zero_smul, zero_add]

lemma grad_smul_const (metric : MetricDuality R V) (c f : R) (hc : ∀ X : V, action X c = 0) :
    grad metric (c * f) = c • grad metric f := by
  apply metric.toNonDegenerateMetric.eq_of_forall_g_eq
  intro X
  have h1 : metric.g (grad metric (c * f)) X = action X (c * f) := g_grad metric (c * f) X
  have h2 : action X (c * f) = c * action X f := action_mul_const X c f (hc X)
  have h3 : metric.g (c • grad metric f) X = c * metric.g (grad metric f) X := metric.toNonDegenerateMetric.toAbstractMetricTensor.bilinear_smul_left _ _ _
  have h4 : metric.g (grad metric f) X = action X f := g_grad metric f X
  have h5 : metric.g (c • grad metric f) X = c * action X f := by rw [h3, h4]
  rw [h1, h2, ← h5]

-- Linearity of hessianForm in the scalar argument
lemma hessianForm_smul (metric : MetricDuality R V) (conn : AbstractAffineConnection R V) [AffineTensorCalculus conn]
    (c f : R) (hc : ∀ X : V, action X c = 0) :
    hessianForm metric conn (c * f) = TensorAlgebra.smul c (hessianForm metric conn f) := by
  unfold hessianForm
  rw [grad_smul_const metric c f hc, covariant_differential_smul_vec metric conn c (grad metric f) hc, lower_index_smul]

/-- Evaluating `hessianForm metric conn u` at vectors `(X, Y)` exactly matches `Hess conn u X Y`.
This connects the abstract tensor formulation to the pointwise definition. -/
lemma hessianForm_eval (metric : MetricDuality R V)
    (conn : AbstractAffineConnection R V) [AffineTensorCalculus conn]
    [MetricEvaluationRules R V metric.toNonDegenerateMetric.toAbstractMetricTensor]
    [MetricCompatible conn metric.toNonDegenerateMetric.toAbstractMetricTensor]
    [TorsionFree conn] [LieDerivation R V] [ActionLinear R V]
    (u : R) (X Y : V) :
    tensor_eval (hessianForm metric conn u) ![X, Y] ![] =
    Hess conn u X Y := by
  -- Step 1: Unfold hessianForm to lower_index of covariant_differential
  unfold hessianForm
  -- Step 2: Prove that covariant_differential evaluates as T(Y', n) = n(∇_{Y'} grad u)
  have h_cov_eval : ∀ (Y' : V) (n : V →ₗ[R] R),
      tensor_eval (covariant_differential metric conn (grad metric u)) ![Y'] ![n] =
      n (conn.nabla Y' (grad metric u)) := by
    intro Y' n
    simp only [tensor_eval, covariant_differential, TensorAlgebra.toData_fromData]
    dsimp only [MultilinearMap.coe_mk]
    -- Reduce ![Y'] 0 to Y' via definitional equality
    change ((TensorAlgebra.toData (genericCovDeriv conn Y' (fromVector (grad metric u)))) ![]) (![n]) =
      n (conn.nabla Y' (grad metric u))
    have h_nabla : genericCovDeriv conn Y' (fromVector (R:=R) (grad metric u)) =
        fromVector (R:=R) (conn.nabla Y' (grad metric u)) := by
      simp only [genericCovDeriv, fromVector]
      exact AffineTensorCalculus.nabla_vector Y' (grad metric u)
    rw [h_nabla]
    simp only [fromVector, TensorAlgebra.toData_fromData]
    dsimp [vectorToData, MultilinearMap.constOfIsEmpty, MultilinearMap.ofSubsingleton, evalLinear]
  -- Step 3: Apply MetricEvaluationRules.lower_index_1_1_eval
  have h_lower := MetricEvaluationRules.lower_index_1_1_eval
    (metric := metric.toNonDegenerateMetric.toAbstractMetricTensor)
    (covariant_differential metric conn (grad metric u))
    (fun Y' => conn.nabla Y' (grad metric u))
    h_cov_eval X Y
  rw [h_lower]
  -- Goal: metric.g X (∇_Y grad u) = Hess conn u X Y
  -- Step 4: Use metric compatibility to show g(X, ∇_Y grad u) = Hess u Y X
  have h_compat := MetricCompatible.compat (conn:=conn)
    (metric:=metric.toNonDegenerateMetric.toAbstractMetricTensor) Y X (grad metric u)
  -- h_compat : action Y (g X (grad u)) = g(∇_Y X, grad u) + g(X, ∇_Y grad u)
  have h1 : metric.g X (grad metric u) = action X u := by
    rw [metric.toNonDegenerateMetric.toAbstractMetricTensor.symm X (grad metric u)]
    exact g_grad metric u X
  have h2 : metric.g (conn.nabla Y X) (grad metric u) = action (conn.nabla Y X) u := by
    rw [metric.toNonDegenerateMetric.toAbstractMetricTensor.symm (conn.nabla Y X) (grad metric u)]
    exact g_grad metric u (conn.nabla Y X)
  rw [h1, h2] at h_compat
  -- h_compat : action Y (action X u) = action (∇_Y X) u + g(X, ∇_Y grad u)
  -- So g(X, ∇_Y grad u) = action Y (action X u) - action (∇_Y X) u = Hess u Y X
  have h3 : metric.g X (conn.nabla Y (grad metric u)) =
      action Y (action X u) - action (conn.nabla Y X) u := by linarith
  rw [h3]
  -- Goal: Hess conn u Y X = Hess conn u X Y (definitionally)
  exact hessian_symm conn u Y X

