import DifferentialGeometry.Integral.Connection.RicciIdentityCore
import DifferentialGeometry.Synthetic.Realization.Connection
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
namespace Connection

open Tensor0SBundle
open SyntheticTensor
open Realized
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [Module.Finite Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((⊤ : WithTop ℕ∞) + 1) M]

/-- Smooth-section form of the algebraic one-form Ricci identity for a concrete
Mathlib covariant derivative and an abstract smooth-section functional.

This is the direct RicciFlower access point to
`DifferentialGeometry.Integral.Connection.ricci_identity_oneForm`: it lives at
the level of global smooth tangent sections.  The separate bridge to
`OneFormThirdCovDerivCommAt` must still identify a smooth one-form tensor field
with the corresponding `C^∞(M)`-linear functional, identify
`Nabla2OneFormRealizesAt` with this iterated `nabla_dual` expression, and then
use torsion-freeness to remove the bracket correction. -/
theorem oneFormRicciIdentity_smoothFunctional_apply
    [SigmaCompactSpace M] [T2Space M] [CompleteSpace E]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯)
    (alpha :
      Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯
        →ₗ[C^∞⟮I, M; Real⟯] C^∞⟮I, M; Real⟯)
    (x : M) :
    ((nabla_dual
        (concreteDerivationEmbedding I M)
        (concreteConn I M cov)
        (concreteConn_add_right I M cov)
        (concreteConn_leibniz I M cov)
        X
        (nabla_dual
          (concreteDerivationEmbedding I M)
          (concreteConn I M cov)
          (concreteConn_add_right I M cov)
          (concreteConn_leibniz I M cov)
          Y
          alpha)) Z) x -
      ((nabla_dual
        (concreteDerivationEmbedding I M)
        (concreteConn I M cov)
        (concreteConn_add_right I M cov)
        (concreteConn_leibniz I M cov)
        Y
        (nabla_dual
          (concreteDerivationEmbedding I M)
          (concreteConn I M cov)
          (concreteConn_add_right I M cov)
          (concreteConn_leibniz I M cov)
          X
          alpha)) Z) x -
      ((nabla_dual
        (concreteDerivationEmbedding I M)
        (concreteConn I M cov)
        (concreteConn_add_right I M cov)
        (concreteConn_leibniz I M cov)
        (bracket
          (concreteDerivationEmbedding I M)
          X Y)
        alpha) Z) x =
      -(alpha
        (Rm
          (concreteDerivationEmbedding I M)
          (concreteConn I M cov)
          X Y Z)) x := by
  let emb :=
    concreteDerivationEmbedding I M
  let conn := concreteConn I M cov
  let ha := concreteConn_add_right I M cov
  let hl := concreteConn_leibniz I M cov
  have h :=
    DifferentialGeometry.Integral.Connection.ricci_identity_oneForm
      emb conn ha hl X Y Z alpha
  exact congrArg (fun f : C^∞⟮I, M; Real⟯ => f x) h

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

/-- Smooth-connection version of `oneFormRicciIdentity_of_connection`.

The coordinate curvature hypothesis is now produced in the general
connection-curvature layer.  The one-form coordinate commutator is intentionally
left explicit until the higher-order covariant-derivative API is settled. -/
theorem oneFormRicciIdentity_of_smooth_connection
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (x : M)
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hRm : Rm13RealizesConnection (I := I) cov Rm13)
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (hcoord : OneFormThirdCommChristoffelCoordAt (I := I) cov x alpha nabla2Alpha) :
    OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha :=
  oneFormRicciIdentity_of_connection (I := I) cov Rm13 x alpha nabla2Alpha
    hRm (connection_curvature_coord_of_christoffel (I := I) cov hcov x) hcoord

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

/-- Evaluation form of `oneFormRicciIdentity_of_smooth_connection`. -/
theorem oneFormRicciIdentity_of_smooth_connection_apply
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (x : M)
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hRm : Rm13RealizesConnection (I := I) cov Rm13)
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (hcoord : OneFormThirdCommChristoffelCoordAt (I := I) cov x alpha nabla2Alpha)
    (X Y Z : TangentSpace I x) :
    nabla2Alpha (vec3 X Y Z) - nabla2Alpha (vec3 Y X Z) =
      -Rm13 x alpha (vec3 X Y Z) :=
  one_form_third_covDeriv_comm (I := I) Rm13 alpha nabla2Alpha
    (oneFormRicciIdentity_of_smooth_connection (I := I) cov Rm13 x alpha
      nabla2Alpha hRm hcov hcoord) X Y Z

end Connection
end RicciFlower
