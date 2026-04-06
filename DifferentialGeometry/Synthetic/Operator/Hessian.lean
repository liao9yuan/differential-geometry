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
