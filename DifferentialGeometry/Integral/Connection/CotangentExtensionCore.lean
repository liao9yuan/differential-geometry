import DifferentialGeometry.Integral.Connection.CurvatureCore
import DifferentialGeometry.Synthetic.Realization.TensorNabla
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Cotangent Extension Core

This file exposes the cotangent connection under the upstream-style names used
by the integral-connection Ricci identity files.  The construction itself is the
already checked `dualCovariantDerivative`; no second cotangent bundle structure
is introduced.
-/

noncomputable section

namespace DifferentialGeometry
namespace Integral
namespace Connection

open Bundle CovariantDerivative
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

/-- Smooth cotangent sections in the upstream-style bridge. -/
abbrev CotangentSection :=
  ContMDiffSection I (E →L[Real] Real) (∞ : WithTop ℕ∞)
    (Bundle.dual Real (TangentSpace I : M -> Type _))

/-- The cotangent connection induced by a tangent-bundle connection. -/
noncomputable abbrev cotangentCov
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _)) :
    CovariantDerivative I (E →L[Real] Real)
      (Bundle.dual Real (TangentSpace I : M -> Type _)) :=
  dualCovariantDerivative I M cov

@[simp]
theorem cotangentCov_eq_dualCovariantDerivative
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _)) :
    cotangentCov (I := I) (M := M) cov = dualCovariantDerivative I M cov :=
  rfl

instance cotangentCov_contMDiff
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    [ContMDiffCovariantDerivative cov ∞] :
    ContMDiffCovariantDerivative (cotangentCov (I := I) (M := M) cov) ∞ := by
  dsimp [cotangentCov]
  infer_instance

/-- Product-rule characterization of the induced cotangent connection. -/
theorem cotangentCov_dualPairing
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (α : CotangentSection (I := I) (M := M))
    (Y : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) (v : TangentSpace I x) :
    extDerivFun (I := I) (fun y : M => α y (Y y)) x v =
      ((cotangentCov (I := I) (M := M) cov) α x v) (Y x) +
        α x ((cov (fun y : M => Y y) x) v) := by
  have h :=
    dualCovariantDerivative_apply (I := I) (M := M) cov α Y x v
  rw [h]
  ring

end Connection
end Integral
end DifferentialGeometry
