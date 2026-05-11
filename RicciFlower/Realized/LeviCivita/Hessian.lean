import RicciFlower.Realized.ScalarBochner
import RicciFlower.Realized.LeviCivita.Torsion
import RicciFlower.Coordinates.NablaComponents.OneForm
import RicciFlower.Coordinates.NablaComponents.TwoTensor

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Levi-Civita Hessian symmetry

This file proves the Levi-Civita Hessian symmetry endpoint used by the
Levi-Civita scalar-Bochner wrapper.  The intended route is direct: use the
realized `∇ du` and `∇ (∇ du)` interfaces, the scalar bracket formula for
`du`, and torsion-freeness of `leviCivitaConnectionOfMetric`.
-/

noncomputable section

namespace RicciFlower
namespace Realized
namespace LeviCivita

open Bundle Tensor0SBundle
open Coordinates
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
variable [IsManifold I ((⊤ : WithTop ℕ∞) + 1) M]

/-- Coordinate-frame component symmetry of the Hessian section `∇ du`.

This is the mathematical core of Hessian symmetry:
`(∇_X du)(Y) - (∇_Y du)(X) = du([X,Y] - (∇_X Y - ∇_Y X))`, and the right-hand
side vanishes for the Levi-Civita connection by the scalar bracket formula and
torsion-freeness.
-/
private theorem leviCivita_nablaDuSec_coordFrame_symm
    [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M) (u : M -> Real)
    (hu : ContMDiff I 𝓘(Real, Real) ∞ u)
    (duSec : OneFormSection (I := I) (M := M))
    (nablaDuSec : TwoTensorSection (I := I) (M := M))
    (hnabla : NablaOneFormSectionRealizes (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) duSec nablaDuSec)
    (hdu : DuFieldRealizes (I := I) u duSec)
    (x : M) (i j : CoordinateIdx (𝕜 := Real) E) :
    nablaDuSec x (vec2
        (coordinateFrameAt_toBasis (I := I) x i)
        (coordinateFrameAt_toBasis (I := I) x j)) =
      nablaDuSec x (vec2
        (coordinateFrameAt_toBasis (I := I) x j)
        (coordinateFrameAt_toBasis (I := I) x i)) := by
  -- TODO: finish the direct coordinate proof.  The exact remaining lemma is a
  -- smooth-section extension/congruence bridge:
  --
  --   If global smooth sections `Xi`, `Xj` agree near `x` with the local
  --   coordinate-frame fields, then `hnabla x Xi (Xj x)` may be rewritten with
  --   the moving-slot formula, and `vderiv_mlieBracket` plus
  --   `torsion_free_apply` cancels the two sides.
  --
  -- This is the actual Hessian proof obligation, not an adapter hypothesis.
  sorry

/-- Pointwise symmetry of the realized Levi-Civita Hessian section, obtained
from the coordinate-frame Hessian symmetry by tensor extensionality. -/
private theorem leviCivita_nablaDuSec_pointwise_symm
    [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M) (u : M -> Real)
    (hu : ContMDiff I 𝓘(Real, Real) ∞ u)
    (duSec : OneFormSection (I := I) (M := M))
    (nablaDuSec : TwoTensorSection (I := I) (M := M))
    (hnabla : NablaOneFormSectionRealizes (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) duSec nablaDuSec)
    (hdu : DuFieldRealizes (I := I) u duSec)
    (x : M) :
    ∀ U V : TangentSpace I x,
      nablaDuSec x (vec2 U V) = nablaDuSec x (vec2 V U) := by
  intro U V
  have hsymm := Coordinates.tensor0S_two_symm_of_coordFrame
    (I := I) (coordinateFrameAt_toBasis (I := I) x) (nablaDuSec x) ?_
  · exact hsymm U V
  intro i j
  simpa [vec2] using
    leviCivita_nablaDuSec_coordFrame_symm
      (I := I) g u hu duSec nablaDuSec hnabla hdu x i j

/-- Levi-Civita Hessian symmetry for a function, expressed as trailing-slot
symmetry of the second covariant derivative of `du`. -/
theorem oneFormLastTwoSymmAt_of_leviCivita_du
    [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M) (u : M -> Real)
    (hu : ContMDiff I 𝓘(Real, Real) ∞ u)
    (duSec : OneFormSection (I := I) (M := M))
    (nablaDuSec : TwoTensorSection (I := I) (M := M))
    {x : M}
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hdu : DuFieldRealizes (I := I) u duSec)
    (hnabla2 : Nabla2OneFormRealizesAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) duSec nablaDuSec x nabla2Du) :
    OneFormLastTwoSymmAt (I := I) nabla2Du := by
  classical
  have hnabla := nabla2OneFormRealizesAt_first
    (I := I) (leviCivitaConnectionOfMetric (I := I) g)
    duSec nablaDuSec x nabla2Du hnabla2
  have hsymm : ∀ y : M, ∀ U V : TangentSpace I y,
      nablaDuSec y (vec2 (I := I) U V) =
        nablaDuSec y (vec2 (I := I) V U) :=
    fun y U V =>
      leviCivita_nablaDuSec_pointwise_symm
        (I := I) g u hu duSec nablaDuSec hnabla hdu y U V
  -- The remaining proof is the correct direct endpoint: a realized `∇ Hess u`
  -- inherits the already-proved pointwise symmetry of `Hess u`.
  --
  -- Do not use the bump-section theorem here.  It only supplies `C^∞`
  -- sections, while the current `Nabla2OneFormRealizesAt` / `nabla0SFun` API
  -- asks for `C^⊤` sections.  The clean fix is to lower or parameterize that
  -- core API to smooth order, then apply the proved coordinate theorem
  -- `Coordinates.nabla0SFun_two_symm_of_symm`.
  sorry

end LeviCivita
end Realized
end RicciFlower
