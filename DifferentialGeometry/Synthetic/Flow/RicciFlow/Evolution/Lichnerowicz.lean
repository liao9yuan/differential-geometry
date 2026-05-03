import DifferentialGeometry.Synthetic.Flow.RicciFlow.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# Lichnerowicz Laplacian Interface

This file introduces a named interface for the `(0,2)` Lichnerowicz layer used
by the Ricci evolution formula. The concrete curvature-reaction expansion is a
later algebraic target; the current API records the intended decomposition into
rough Laplacian plus curvature reaction.
-/

open SyntheticTensor

section Lichnerowicz02

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- A curvature reaction term for a `(0,2)` tensor. -/
abbrev CurvatureReaction02 (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] :=
  TensorData R V 0 2

/-- The Lichnerowicz Laplacian, exposed as rough Laplacian plus reaction. -/
noncomputable def lichnerowicz_laplacian_02
    (rough reaction : TensorData R V 0 2) : TensorData R V 0 2 :=
  rough + reaction

theorem lichnerowicz_laplacian_02_eval
    (rough reaction : TensorData R V 0 2) (X Y : V) :
    lichnerowicz_laplacian_02 rough reaction ![X, Y] ![] =
    rough ![X, Y] ![] + reaction ![X, Y] ![] := by
  rfl

/-- Interface for any operator claimed to be the `(0,2)` Lichnerowicz Laplacian. -/
def IsLichnerowiczLaplacian02
    (L rough reaction : TensorData R V 0 2 -> TensorData R V 0 2) : Prop :=
  forall T, L T = rough T + reaction T

theorem lichnerowicz_laplacian_from_interface
    (L rough reaction : TensorData R V 0 2 -> TensorData R V 0 2)
    (hL : IsLichnerowiczLaplacian02 L rough reaction) (T : TensorData R V 0 2) :
    L T = rough T + reaction T :=
  hL T

end Lichnerowicz02

