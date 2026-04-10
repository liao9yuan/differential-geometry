import DifferentialGeometry.Synthetic.Operator.SecondCovariantDerivative
import DifferentialGeometry.Synthetic.Geometry.Connection
import DifferentialGeometry.Synthetic.Geometry.Curvature
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Algebra.Module.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# Ricci Identity
Proofs of the algebraic expansion of the second covariant derivative commutator and the Ricci identity.
-/

open AbstractDerivationAction
open AbstractLieBracket

variable {R V : Type}
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [AbstractDerivationAction R V]

/-- Distributes the covariant derivative over subtraction of vector fields in the first argument. -/
lemma nabla_sub_left (conn : AbstractAffineConnection R V) (X Y Z : V) : conn.nabla (X - Y) Z = conn.nabla X Z - conn.nabla Y Z := by
  have h1 : X - Y + Y = X := by abel
  have h2 : conn.nabla (X - Y + Y) Z = conn.nabla (X - Y) Z + conn.nabla Y Z := conn.nabla_add_left (X - Y) Y Z
  rw [h1] at h2
  exact eq_sub_of_add_eq h2.symm

/-- Expands the commutator of the second covariant derivative algebraically. -/
lemma secondCovDerivCommutator_expand (conn : AbstractAffineConnection R V) (X Y Z : V) :
  secondCovDerivCommutator conn X Y Z = conn.nabla X (conn.nabla Y Z) - conn.nabla Y (conn.nabla X Z) - conn.nabla (conn.nabla X Y - conn.nabla Y X) Z := by
  dsimp [secondCovDerivCommutator, secondCovDeriv]
  rw [nabla_sub_left]
  abel

variable [AbstractLieBracket V]

/-- The commutator of the second covariant derivative equals the Riemann curvature tensor for a torsion-free connection. -/
theorem ricci_identity (conn : AbstractAffineConnection R V) [TorsionFree conn] (X Y Z : V) :
  secondCovDerivCommutator conn X Y Z = Rm conn X Y Z := by
  rw [secondCovDerivCommutator_expand]
  rw [TorsionFree.torsion_zero (conn := conn) X Y]
  rfl
