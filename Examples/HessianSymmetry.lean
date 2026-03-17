import DifferentialGeometry.Algebra.Basic
import DifferentialGeometry.Geometry.Connection
import DifferentialGeometry.Operators.Hessian
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic

/-!
# Hessian Symmetry
Proof that the Hessian is symmetric for any torsion-free affine connection.


# ----------------------------------------------------------------
# NOTE:
# This proof is already done in DifferentialGeometry.Operators.Hessian.
# This is just a sample of proof using DifferentialGeometry library.
# That is why the variable names are weired.
# ----------------------------------------------------------------

-/

set_option autoImplicit false
set_option linter.style.longLine false

class LieDerivation_example (R V : Type) [CommRing R] [AbstractDerivationAction R V] [AbstractLieBracket V] where
  bracket_action : ∀ X Y : V, ∀ u : R,
    AbstractDerivationAction.action (AbstractLieBracket.bracket X Y) u =
    AbstractDerivationAction.action X (AbstractDerivationAction.action Y u) - AbstractDerivationAction.action Y (AbstractDerivationAction.action X u)

class ActionLinear_example (R V : Type) [CommRing R] [AddCommGroup V] [AbstractDerivationAction R V] where
  action_add : ∀ X Y : V, ∀ u : R,
    AbstractDerivationAction.action (X + Y) u = AbstractDerivationAction.action X u + AbstractDerivationAction.action Y u

variable {R V : Type}
  [CommRing R] [AddCommGroup V] [Module R V]
  [AbstractDerivationAction R V] [AbstractLieBracket V]
  [LieDerivation_example R V] [ActionLinear_example R V]

variable (conn : AbstractAffineConnection R V) [TorsionFree conn]

open AbstractDerivationAction
open AbstractLieBracket

theorem hessian_symm_example (u : R) (X Y : V) : Hess conn u X Y = Hess conn u Y X := by
  have t1 : conn.nabla X Y = conn.nabla Y X + bracket X Y := by
    calc conn.nabla X Y = conn.nabla X Y - conn.nabla Y X + conn.nabla Y X := by abel
      _ = bracket X Y + conn.nabla Y X := by rw [TorsionFree.torsion_zero (conn := conn)]
      _ = conn.nabla Y X + bracket X Y := by abel
  calc Hess conn u X Y
    _ = action X (action Y u) - action (conn.nabla X Y) u := rfl
    _ = action X (action Y u) - action (conn.nabla Y X + bracket X Y) u := by rw [t1]
    _ = action X (action Y u) - (action (conn.nabla Y X) u + action (bracket X Y) u) := by rw [ActionLinear_example.action_add]
    _ = action X (action Y u) - (action (conn.nabla Y X) u + (action X (action Y u) - action Y (action X u))) := by rw [LieDerivation_example.bracket_action]
    _ = action Y (action X u) - action (conn.nabla Y X) u := by ring
    _ = Hess conn u Y X := rfl


#check hessian_symm_example
