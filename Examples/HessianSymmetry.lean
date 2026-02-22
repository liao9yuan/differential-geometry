import DifferentialGeometry.Algebra.Basic
import DifferentialGeometry.Geometry.Connection
import DifferentialGeometry.Operators.Hessian
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic

/-!
# Hessian Symmetry
Proof that the Hessian is symmetric for any torsion-free affine connection.
-/

set_option autoImplicit false
set_option linter.style.longLine false

class LieDerivation (R V : Type) [CommRing R] [DerivationAction R V] [LieBracket V] where
  bracket_action : ∀ X Y : V, ∀ u : R,
    DerivationAction.action (LieBracket.bracket X Y) u =
    DerivationAction.action X (DerivationAction.action Y u) - DerivationAction.action Y (DerivationAction.action X u)

class ActionLinear (R V : Type) [CommRing R] [AddCommGroup V] [DerivationAction R V] where
  action_add : ∀ X Y : V, ∀ u : R,
    DerivationAction.action (X + Y) u = DerivationAction.action X u + DerivationAction.action Y u

variable {R V : Type}
  [CommRing R] [AddCommGroup V] [Module R V]
  [DerivationAction R V] [LieBracket V]
  [LieDerivation R V] [ActionLinear R V]

variable (conn : AffineConnection R V) [TorsionFree conn]

open DerivationAction
open LieBracket

theorem hessian_symm (u : R) (X Y : V) : Hess conn u X Y = Hess conn u Y X := by
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


#check hessian_symm
