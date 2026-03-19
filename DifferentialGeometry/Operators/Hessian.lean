import DifferentialGeometry.Algebra.VectorField
import DifferentialGeometry.Geometry.Connection
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option linter.style.longLine false

variable {R V : Type}
variable [CommRing R] [AddCommGroup V] [Module R V]
variable [AbstractDerivationAction R V]

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
