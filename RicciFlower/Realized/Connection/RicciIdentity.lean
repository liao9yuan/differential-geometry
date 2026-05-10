import DifferentialGeometry.Integral.Connection.RicciIdentityCore
import RicciFlower.Realized.CurvatureComponents

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Ricci Identity Bridge for Realized Connections

This file exposes the RicciFlower-facing one-form Ricci identity without
importing the upstream Levi-Civita construction.  The borrowed algebraic core
lives in `DifferentialGeometry.Integral.Connection.RicciIdentityCore`; the
public RicciFlower endpoint stays the realized tensor predicate
`OneFormThirdCovDerivCommAt`.
-/

noncomputable section

namespace RicciFlower
namespace Realized
namespace Connection

open Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [Module.Finite Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((⊤ : WithTop ℕ∞) + 1) M]

/-- Connection-generic one-form Ricci identity in RicciFlower's public tensor
interface.

The proof currently routes through the coordinate Christoffel curvature layer:
`hcoord` is the local coordinate calculation for the one-form commutator, while
`hcurv` identifies the coordinate curvature coefficients with the realized
connection curvature.  This theorem is deliberately independent of any
primitive metric-Christoffel or upstream `LeviCivita g` definition. -/
theorem oneFormRicciIdentity_of_connection
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (x : M)
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hRm : Rm13RealizesConnection (I := I) cov Rm13)
    (hcurv : ConnectionCurvatureCoordAt (I := I) cov x)
    (hcoord : OneFormThirdCommChristoffelCoordAt (I := I) cov x alpha nabla2Alpha) :
    OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha :=
  one_form_third_comm_coord_of_christoffelCurv (I := I) cov Rm13 x alpha
    nabla2Alpha hRm hcurv hcoord

/-- Evaluation form of `oneFormRicciIdentity_of_connection`. -/
theorem oneFormRicciIdentity_of_connection_apply
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (x : M)
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hRm : Rm13RealizesConnection (I := I) cov Rm13)
    (hcurv : ConnectionCurvatureCoordAt (I := I) cov x)
    (hcoord : OneFormThirdCommChristoffelCoordAt (I := I) cov x alpha nabla2Alpha)
    (X Y Z : TangentSpace I x) :
    nabla2Alpha (vec3 X Y Z) - nabla2Alpha (vec3 Y X Z) =
      -Rm13 x alpha (vec3 X Y Z) :=
  one_form_third_covDeriv_comm (I := I) Rm13 alpha nabla2Alpha
    (oneFormRicciIdentity_of_connection (I := I) cov Rm13 x alpha nabla2Alpha
      hRm hcurv hcoord) X Y Z

end Connection
end Realized
end RicciFlower
