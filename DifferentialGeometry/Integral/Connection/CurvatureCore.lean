import RicciFlower.Realized.Curvature

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Core Connection Curvature Notation

This file gives the small upstream-style names used by the integral-connection
Ricci identity bridge.  It deliberately does not construct Levi-Civita
connections or introduce metric-Christoffel definitions.
-/

noncomputable section

namespace DifferentialGeometry
namespace Integral
namespace Connection

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Upstream-style application of a connection to a section along a tangent field. -/
def covApply
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X Z : (p : M) -> TangentSpace I p) :
    (p : M) -> TangentSpace I p :=
  fun p => (cov Z p) (X p)

/-- Upstream-style curvature section:
`∇_X∇_Y Z - ∇_Y∇_X Z - ∇_[X,Y] Z`. -/
def riemannSec
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X Y Z : (p : M) -> TangentSpace I p) :
    (p : M) -> TangentSpace I p :=
  fun p =>
    (cov (covApply (I := I) cov Y Z) p) (X p) -
      (cov (covApply (I := I) cov X Z) p) (Y p) -
        (cov Z p) (VectorField.mlieBracket I X Y p)

@[simp]
theorem covApply_apply
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X Z : (p : M) -> TangentSpace I p) (p : M) :
    covApply (I := I) cov X Z p = (cov Z p) (X p) :=
  rfl

@[simp]
theorem riemannSec_def
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X Y Z : (p : M) -> TangentSpace I p) (p : M) :
    riemannSec (I := I) cov X Y Z p =
      (cov (covApply (I := I) cov Y Z) p) (X p) -
        (cov (covApply (I := I) cov X Z) p) (Y p) -
          (cov Z p) (VectorField.mlieBracket I X Y p) :=
  rfl

/-- The borrowed curvature notation agrees definitionally with RicciFlower's
realized curvature operator. -/
theorem riemannSec_eq_connectionRiemannCurvatureField
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X Y Z : (p : M) -> TangentSpace I p) :
    riemannSec (I := I) cov X Y Z =
      RicciFlower.Realized.connectionRiemannCurvatureField (I := I) cov X Y Z :=
  rfl

end Connection
end Integral
end DifferentialGeometry

