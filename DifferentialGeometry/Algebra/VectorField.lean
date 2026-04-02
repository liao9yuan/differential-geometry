import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# Vector Field Concepts
Algebraic foundations for vector fields, derivations, and Lie brackets.
-/

variable (R V : Type*)
variable [CommRing R] [AddCommGroup V] [Module R V]

/-- Derivation action of vector fields on functions.
Input: (V, R)
Output: R -/
class AbstractDerivationAction where
  action : V → R → R

/-- Lie bracket of two vector fields.
Input: (V, V)
Output: V -/
class AbstractLieBracket (V : Type*) where
  bracket : V → V → V

open AbstractDerivationAction
open AbstractLieBracket

class LieDerivation (R V : Type*) [CommRing R] [AbstractDerivationAction R V] [AbstractLieBracket V] where
  bracket_action : ∀ X Y : V, ∀ u : R,
    AbstractDerivationAction.action (AbstractLieBracket.bracket X Y) u =
    AbstractDerivationAction.action X (AbstractDerivationAction.action Y u) - AbstractDerivationAction.action Y (AbstractDerivationAction.action X u)

class ActionLinear (R V : Type*) [CommRing R] [AddCommGroup V] [AbstractDerivationAction R V] where
  action_add : ∀ X Y : V, ∀ u : R,
    AbstractDerivationAction.action (X + Y) u = AbstractDerivationAction.action X u + AbstractDerivationAction.action Y u

-- Defines the foundational rule that vector fields are distinguishable by their action on functions.
/-- Vector field non-degeneracy axiom class. -/
class VectorFieldNonDegenerate (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] [AbstractDerivationAction R V] where
  eq_of_action_eq : ∀ X Y : V, (∀ f : R, action X f = action Y f) → X = Y

-- Formalizes the behavior of the Lie bracket on functions as the commutator of derivations.
/-- Lie derivation rules including bracket commutator and derivation linearity. -/
class LieDerivationRules (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] [AbstractDerivationAction R V] [AbstractLieBracket V] where
  action_bracket : ∀ (X Y : V) (f : R), action (bracket X Y) f = action X (action Y f) - action Y (action X f)
  action_add : ∀ (X Y : V) (f : R), action (X + Y) f = action X f + action Y f
  action_sub : ∀ (X : V) (f g : R), action X (f - g) = action X f - action X g
  action_zero : ∀ (f : R), action (0 : V) f = 0

/-- Leibniz rule and Jacobi identity for derivation action and Lie bracket.
Input: (R, V)
Output: Type -/
class DerivationRules (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] [AbstractDerivationAction R V] [AbstractLieBracket V] where
  action_add_left : ∀ X Y : V, ∀ f : R, action (X + Y) f = action X f + action Y f
  action_add_right : ∀ X : V, ∀ f g : R, action X (f + g) = action X f + action X g
  action_smul_left : ∀ (c : R) (X : V) (f : R), action (c • X) f = c * action X f
  action_smul_right : ∀ X : V, ∀ (c f : R), action X (c * f) = action X c * f + c * action X f
  bracket_add_left : ∀ X Y Z : V, bracket (X + Y) Z = bracket X Z + bracket Y Z
  bracket_add_right : ∀ X Y Z : V, bracket X (Y + Z) = bracket X Y + bracket X Z
  bracket_smul_left : ∀ (c : R) (X Y : V), bracket (c • X) Y = c • (bracket X Y) - (action Y c) • X
  bracket_smul_right : ∀ (c : R) (X Y : V), bracket X (c • Y) = c • (bracket X Y) + (action X c) • Y
  bracket_antisymm : ∀ X Y : V, bracket X Y = - bracket Y X

variable [AbstractDerivationAction R V] [AbstractLieBracket V]
variable [DerivationRules R V]

/-- $X(0) = 0$ -/
lemma action_zero {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] [AbstractDerivationAction R V] [AbstractLieBracket V] [DerivationRules R V] (X : V) : action X (0:R) = 0 := by
  have h := DerivationRules.action_add_right X (0:R) (0:R)
  rw [add_zero] at h
  calc action X (0:R) = action X (0:R) + action X (0:R) - action X (0:R) := by abel
    _ = action X (0:R) - action X (0:R) := by rw [← h]
    _ = 0 := by abel

/-- $X(-g) = -X(g)$ -/
lemma action_neg {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] [AbstractDerivationAction R V] [AbstractLieBracket V] [DerivationRules R V] (X : V) (g : R) : action X (- g) = - action X g := by
  have h : action X (g + -g) = action X g + action X (-g) := DerivationRules.action_add_right X g (-g)
  have hz : g + -g = 0 := by abel
  rw [hz, action_zero X] at h
  calc action X (-g) = action X g + action X (-g) - action X g := by abel
    _ = 0 - action X g := by rw [← h]
    _ = - action X g := by abel

/-- Proves that the derivation action on the constant 1 is zero: $X(1) = 0$. -/
lemma action_one {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] [AbstractDerivationAction R V] [AbstractLieBracket V] [DerivationRules R V] (X : V) : action X (1:R) = 0 := by
  have h1 : action X ((1:R) * (1:R)) = action X (1:R) * (1:R) + (1:R) * action X (1:R) := DerivationRules.action_smul_right X (1:R) (1:R)
  have h2 : (1:R) * (1:R) = (1:R) := by ring
  rw [h2] at h1
  have h3 : action X (1:R) * (1:R) = action X (1:R) := by ring
  have h4 : (1:R) * action X (1:R) = action X (1:R) := by ring
  rw [h3, h4] at h1
  calc action X (1:R) = action X (1:R) + action X (1:R) - action X (1:R) := by abel
    _ = action X (1:R) - action X (1:R) := by rw [← h1]
    _ = 0 := by abel

/-- Proves that if the derivation action on a constant $c$ is zero, then $X(c + c) = 0$. -/
lemma action_add_self {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] [AbstractDerivationAction R V] [AbstractLieBracket V] [DerivationRules R V] (X : V) (c : R) (hc : action X c = 0) : action X (c + c) = 0 := by
  have h : action X (c + c) = action X c + action X c := DerivationRules.action_add_right X c c
  rw [hc, add_zero] at h
  exact h

/-- Proves that the derivation action on the constant 2 is zero: $X(2) = 0$. -/
lemma action_two {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] [AbstractDerivationAction R V] [AbstractLieBracket V] [DerivationRules R V] (X : V) : action X (2:R) = 0 := by
  have h_two : (2:R) = (1:R) + (1:R) := by ring
  rw [h_two]
  exact action_add_self X (1:R) (action_one X)

/-- Proves that the derivation action on the constant -2 is zero: $X(-2) = 0$. -/
lemma action_neg_two {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] [AbstractDerivationAction R V] [AbstractLieBracket V] [DerivationRules R V] (X : V) : action X (- (2:R)) = 0 := by
  rw [action_neg X (2:R), action_two X, neg_zero]

/-- Proves that the constant factor $c$ commutes with the derivation action: $X(c * f) = c * X(f)$. -/
lemma action_mul_const {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] [AbstractDerivationAction R V] [AbstractLieBracket V] [DerivationRules R V] (X : V) (c f : R) (hc : action X c = 0) : action X (c * f) = c * action X f := by
  rw [DerivationRules.action_smul_right X c f, hc, zero_mul, zero_add]

-- Proves the Jacobi Identity (The Critical Test).
/-- Proof of the Jacobi identity over vector fields. -/
theorem jacobi_identity_proof {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] [AbstractDerivationAction R V] [AbstractLieBracket V] [VectorFieldNonDegenerate R V] [LieDerivationRules R V] (X Y Z : V) : bracket X (bracket Y Z) + bracket Y (bracket Z X) + bracket Z (bracket X Y) = 0 := by
  apply VectorFieldNonDegenerate.eq_of_action_eq (R := R)
  intro f
  simp only [LieDerivationRules.action_add, LieDerivationRules.action_zero, LieDerivationRules.action_bracket, LieDerivationRules.action_sub]
  abel

/-- Jacobi identity for the Lie bracket of vector fields.
Input: (V)
Output: Prop -/
class JacobiIdentity (V : Type*) [AddCommGroup V] [AbstractLieBracket V] where
  jacobi : ∀ X Y Z : V, bracket X (bracket Y Z) + bracket Y (bracket Z X) + bracket Z (bracket X Y) = 0
