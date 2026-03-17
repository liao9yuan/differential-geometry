import DifferentialGeometry.Algebra.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Lie Algebra Foundations
Algebraic foundations for Lie brackets and derivations on vector fields.
-/

open AbstractDerivationAction
open AbstractLieBracket

class LieDerivation (R V : Type) [CommRing R] [AbstractDerivationAction R V] [AbstractLieBracket V] where
  bracket_action : ∀ X Y : V, ∀ u : R,
    AbstractDerivationAction.action (AbstractLieBracket.bracket X Y) u =
    AbstractDerivationAction.action X (AbstractDerivationAction.action Y u) - AbstractDerivationAction.action Y (AbstractDerivationAction.action X u)

class ActionLinear (R V : Type) [CommRing R] [AddCommGroup V] [AbstractDerivationAction R V] where
  action_add : ∀ X Y : V, ∀ u : R,
    AbstractDerivationAction.action (X + Y) u = AbstractDerivationAction.action X u + AbstractDerivationAction.action Y u

-- Defines the foundational rule that vector fields are distinguishable by their action on functions.
/-- Vector field non-degeneracy axiom class. -/
class VectorFieldNonDegenerate (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] [AbstractDerivationAction R V] where
  eq_of_action_eq : ∀ X Y : V, (∀ f : R, action X f = action Y f) → X = Y

-- Formalizes the behavior of the Lie bracket on functions as the commutator of derivations.
/-- Lie derivation rules including bracket commutator and derivation linearity. -/
class LieDerivationRules (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] [AbstractDerivationAction R V] [AbstractLieBracket V] where
  action_bracket : ∀ (X Y : V) (f : R), action (bracket X Y) f = action X (action Y f) - action Y (action X f)
  action_add : ∀ (X Y : V) (f : R), action (X + Y) f = action X f + action Y f
  action_sub : ∀ (X : V) (f g : R), action X (f - g) = action X f - action X g
  action_zero : ∀ (f : R), action (0 : V) f = 0

-- Proves the Jacobi Identity (The Critical Test).
/-- Proof of the Jacobi identity over vector fields. -/
theorem jacobi_identity_proof {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] [AbstractDerivationAction R V] [AbstractLieBracket V] [VectorFieldNonDegenerate R V] [LieDerivationRules R V] (X Y Z : V) : bracket X (bracket Y Z) + bracket Y (bracket Z X) + bracket Z (bracket X Y) = 0 := by
  apply VectorFieldNonDegenerate.eq_of_action_eq (R := R)
  intro f
  simp only [LieDerivationRules.action_add, LieDerivationRules.action_zero, LieDerivationRules.action_bracket, LieDerivationRules.action_sub]
  abel
