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

open TensorAlgebra DifferentialGeometry

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

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



open AbstractDerivationAction

/-- Helper `(0,2)` tensor for the covariant derivative of a vector field Z. -/
def covDeriv_02 (metric : MetricDuality R V) (conn : AbstractAffineConnection R V) (Z : V) : AbstractBilinearForm R V :=
  TensorAlgebra.fromBilinear {
    toFun := fun X => {
      toFun := fun Y => metric.g (conn.nabla X Z) Y
      map_add' := fun Y₁ Y₂ => by sorry
      map_smul' := fun c Y => by sorry
    }
    map_add' := fun X₁ X₂ => by sorry
    map_smul' := fun c X => by sorry
  }

/-- Rigorous `(1,1)` tensor mapping representing the full generic covariant derivative `∇Z`. -/
def covariant_differential (metric : MetricDuality R V) (conn : AbstractAffineConnection R V) (Z : V) : TensorAlgebra.AbstractTensor R V 1 1 :=
  raise_index metric (0: Fin 2) (covDeriv_02 metric conn Z)

/-- Systematic definition: hessianForm as an AbstractTensor R V 0 2.
    Computed by lowering the contravariant index of the generic covariant derivative of the gradient. -/
def hessianForm (metric : MetricDuality R V) (conn : AbstractAffineConnection R V) [AffineTensorCalculus conn] (u : R) : TensorAlgebra.AbstractTensor R V 0 2 :=
  lower_index metric.toNonDegenerateMetric.toAbstractMetricTensor (0: Fin 1) (covariant_differential metric conn (grad metric u))


