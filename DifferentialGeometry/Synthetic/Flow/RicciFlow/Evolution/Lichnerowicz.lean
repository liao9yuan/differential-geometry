import DifferentialGeometry.Synthetic.Flow.RicciFlow.Basic
import Mathlib.Tactic.Ring

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

/-- Lichnerowicz reaction specialized to the Ricci tensor in the convention of
`RicciFlow/main.tex`, Lemma 6.3:

`reaction = 2 * (Riemann contracted with Ricci) - 2 * Ricci^2`.

The two inputs are still abstract `(0,2)` tensors. The realization layer is
responsible for identifying them with
`R_{ikj\ell} Ric^{k\ell}` and `Ric_i{}^k Ric_{kj}`. -/
noncomputable def ricci_lichnerowicz_reaction_02
    (riemannRicci ricciSquare : TensorData R V 0 2) :
    TensorData R V 0 2 :=
  (2 : R) • riemannRicci - (2 : R) • ricciSquare

theorem ricci_lichnerowicz_reaction_02_eval
    (riemannRicci ricciSquare : TensorData R V 0 2) (X Y : V) :
    ricci_lichnerowicz_reaction_02 riemannRicci ricciSquare ![X, Y] ![] =
      2 * riemannRicci ![X, Y] ![] -
        2 * ricciSquare ![X, Y] ![] := by
  simp [ricci_lichnerowicz_reaction_02, smul_eq_mul]

/-- Ricci-specialized Lichnerowicz RHS:

`Delta Ric + 2 Rm * Ric - 2 Ric^2`.

This is the tensor-level RHS in Lemma 6.3 after naming the rough Laplacian,
Riemann-Ricci contraction, and Ricci-square tensors separately. -/
noncomputable def ricci_lichnerowicz_laplacian_rhs
    (rough riemannRicci ricciSquare : TensorData R V 0 2) :
    TensorData R V 0 2 :=
  lichnerowicz_laplacian_02 rough
    (ricci_lichnerowicz_reaction_02 riemannRicci ricciSquare)

theorem ricci_lichnerowicz_laplacian_rhs_eval
    (rough riemannRicci ricciSquare : TensorData R V 0 2) (X Y : V) :
    ricci_lichnerowicz_laplacian_rhs rough riemannRicci ricciSquare ![X, Y] ![] =
      rough ![X, Y] ![] +
        2 * riemannRicci ![X, Y] ![] -
          2 * ricciSquare ![X, Y] ![] := by
  simp [ricci_lichnerowicz_laplacian_rhs, lichnerowicz_laplacian_02_eval,
    ricci_lichnerowicz_reaction_02_eval]
  ring

end Lichnerowicz02
