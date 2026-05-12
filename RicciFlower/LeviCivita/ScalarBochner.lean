import RicciFlower.Realized.ScalarBochner
import RicciFlower.LeviCivita.Curvature
import RicciFlower.LeviCivita.Hessian

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Levi-Civita scalar Bochner endpoints

This file packages the Levi-Civita geometric inputs for the generic scalar
Bochner assembly in `RicciFlower.Realized.ScalarBochner`.
-/

noncomputable section

namespace RicciFlower
namespace LeviCivita

open Bundle Tensor0SBundle
open Realized
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I (∞ : WithTop ℕ∞) M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

/-- Levi-Civita specialization of the bridge from two total covariant
derivative realization steps to the existing pointwise second-one-form
realization predicate. -/
theorem nabla2OneFormRealizesAt_of_totalNabla_leviCivita
    [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (alpha : OneFormSection (I := I) (M := M))
    (nablaAlpha : TwoTensorSection (I := I) (M := M))
    (nabla2AlphaSec :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 3)
    (h1 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 1 (leviCivitaConnectionOfMetric (I := I) g)
      alpha nablaAlpha)
    (h2 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 (leviCivitaConnectionOfMetric (I := I) g)
      nablaAlpha nabla2AlphaSec)
    (x : M) :
    Nabla2OneFormRealizesAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) alpha nablaAlpha x
      (nabla2AlphaSec x) :=
  nabla2OneFormRealizesAt_of_totalNabla (I := I)
    (leviCivitaConnectionOfMetric (I := I) g) alpha nablaAlpha
    nabla2AlphaSec h1 h2 x

private theorem traceNablaHessianRealizesDLapAt_of_leviCivita_higherOrder_frontier
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M) (u : M -> Real)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (duSec : OneFormSection (I := I) (M := M))
    (nablaDuSec : TwoTensorSection (I := I) (M := M))
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (hdu : DuFieldRealizes (I := I) u duSec)
    (hnabla2 : Nabla2OneFormRealizesAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) duSec nablaDuSec x nabla2Du) :
    TraceNablaHessianRealizesDLapAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) g basis gInv u nabla2Du := by
  -- Frontier: trace the higher-order Hessian derivative and identify it with
  -- the differential of the scalar Laplacian.  This should be proved after the
  -- total covariant derivative API supplies the Hessian trace derivative.
  sorry

/-- The trace of the Levi-Civita third covariant derivative of `du` realizes
`d (Delta u)`. -/
theorem traceNablaHessianRealizesDLapAt_of_leviCivita
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M) (u : M -> Real)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (duSec : OneFormSection (I := I) (M := M))
    (nablaDuSec : TwoTensorSection (I := I) (M := M))
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (hdu : DuFieldRealizes (I := I) u duSec)
    (hnabla2 : Nabla2OneFormRealizesAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) duSec nablaDuSec x nabla2Du) :
    TraceNablaHessianRealizesDLapAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) g basis gInv u nabla2Du :=
  traceNablaHessianRealizesDLapAt_of_leviCivita_higherOrder_frontier
    (I := I) g u basis gInv duSec nablaDuSec nabla2Du hinv hdu hnabla2

/-- Levi-Civita-facing scalar Bochner formula with the geometric LC inputs
produced internally. -/
theorem fundamental_bochner_of_leviCivita_terms
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (leviCivitaConnectionOfMetric (I := I) g) (1 : WithTop ℕ∞))
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInvFrame : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hRm13 : Rm13RealizesConnection (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) Rm13)
    (hRm04 : Rm04RealizesConnection (I := I) g
      (leviCivitaConnectionOfMetric (I := I) g) Rm04)
    (hRic13 : RicciTensorRealizesRm13Trace (I := I) Ric Rm13)
    (hRic04 : RicciTensorRealizesRm04TraceInFrame (I := I) Ric Rm04 gInvFrame frame)
    (u : M -> Real)
    (hu : ContMDiff I 𝓘(Real, Real) ∞ u)
    (Hess nablaDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (roughDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInvAt : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInvAt)
    (X : Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (duSec : OneFormSection (I := I) (M := M))
    (nablaDuSec : TwoTensorSection (I := I) (M := M))
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (normSecond :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (hfields : SmoothBasisFieldsAt (I := I) basis X)
    (hHess : HessianRealizesNablaDuAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) duSec Hess x)
    (hdu : DuFieldRealizes (I := I) u duSec)
    (hnabla : NablaOneFormRealizesAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) duSec nablaDu x)
    (hnabla2 : Nabla2OneFormRealizesAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) duSec nablaDuSec x nabla2Du)
    (hlapTrace :
      laplacian (I := I)
        (leviCivitaConnectionOfMetric (I := I) g) g
        (fun y : M =>
          inner0S (I := I) g y 1
            (differential1FormFun (I := I) u y)
            (differential1FormFun (I := I) u y)) x =
        metricTrace0S2InBasis (I := I) basis gInvAt normSecond Fin.elim0)
    (hsecond : OneFormNormSecondProductInBasis (I := I) basis gInvAt
      (differential1FormFun (I := I) u x) (nablaDu x) nabla2Du normSecond)
    (hrough : RoughLap0SRealizesMetricTrace (I := I) basis gInvAt
      (s := 1) (roughDu x) nabla2Du) :
    (1 / 2 : Real) * laplacian (I := I)
        (leviCivitaConnectionOfMetric (I := I) g) g
        (gradNormSq (I := I) g u) x =
      g.inner x
          (gradientFun (I := I) g
            (laplacian (I := I)
              (leviCivitaConnectionOfMetric (I := I) g) g u) x)
          (gradientFun (I := I) g u x) +
        hessianNormSq (I := I) g Hess x +
          ricciGradGrad (I := I) Ric g u x := by
  refine fundamental_bochner_of_lc_terms (I := I) g Ric Rm13 Rm04
    gInvFrame frame hRm13 hRic13 hRic04 u Hess nablaDu roughDu
    basis gInvAt hinv X duSec nablaDuSec nabla2Du normSecond
    hfields hHess hdu hnabla hnabla2 hlapTrace hsecond hrough ?_ ?_ ?_ ?_
  · exact traceNablaHessianRealizesDLapAt_of_leviCivita (I := I)
      g u basis gInvAt duSec nablaDuSec nabla2Du hinv hdu hnabla2
  · exact oneFormLastTwoSymmAt_of_leviCivita_du (I := I)
      g u hu duSec nablaDuSec nabla2Du hdu hnabla2
  · exact oneFormThirdCovDerivCommAt_of_leviCivita (I := I)
      g Rm13 duSec nablaDuSec (differential1FormFun (I := I) u x)
      nabla2Du hRm13 (by simpa [duField] using hdu x) hnabla2
  · exact rm13MetricSkewAt_of_leviCivita_realizes (I := I)
      g hcov Rm13 Rm04 hRm13 hRm04

/-- Levi-Civita scalar Bochner formula where the scalar Laplacian trace of
`|du|^2` is produced from the operator-level Hessian trace theorem. -/
theorem fundamental_bochner_of_leviCivita_terms_of_normSecond_realizes
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (leviCivitaConnectionOfMetric (I := I) g) (1 : WithTop ℕ∞))
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInvFrame : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hRm13 : Rm13RealizesConnection (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) Rm13)
    (hRm04 : Rm04RealizesConnection (I := I) g
      (leviCivitaConnectionOfMetric (I := I) g) Rm04)
    (hRic13 : RicciTensorRealizesRm13Trace (I := I) Ric Rm13)
    (hRic04 : RicciTensorRealizesRm04TraceInFrame (I := I) Ric Rm04 gInvFrame frame)
    (u : M -> Real)
    (hu : ContMDiff I 𝓘(Real, Real) ∞ u)
    (Hess nablaDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (roughDu : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInvAt : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInvAt)
    (X : Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (duSec normDuSec : OneFormSection (I := I) (M := M))
    (nablaDuSec : TwoTensorSection (I := I) (M := M))
    (nabla2Du :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (normSecond :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (normSecondSec : (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (hfields : SmoothBasisFieldsAt (I := I) basis X)
    (hHess : HessianRealizesNablaDuAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) duSec Hess x)
    (hdu : DuFieldRealizes (I := I) u duSec)
    (hnabla : NablaOneFormRealizesAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) duSec nablaDu x)
    (hnabla2 : Nabla2OneFormRealizesAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) duSec nablaDuSec x nabla2Du)
    (hnormSecond : normSecondSec x = normSecond)
    (hnormDu : DuFieldRealizes (I := I)
      (fun y : M =>
        inner0S (I := I) g y 1
          (differential1FormFun (I := I) u y)
          (differential1FormFun (I := I) u y)) normDuSec)
    (hnormHess : HessianRealizesNablaDuAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) normDuSec normSecondSec x)
    (hnormGrad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) g
        (fun z : M =>
          inner0S (I := I) g z 1
            (differential1FormFun (I := I) u z)
            (differential1FormFun (I := I) u z)) y) x)
    (hsecond : OneFormNormSecondProductInBasis (I := I) basis gInvAt
      (differential1FormFun (I := I) u x) (nablaDu x) nabla2Du normSecond)
    (hrough : RoughLap0SRealizesMetricTrace (I := I) basis gInvAt
      (s := 1) (roughDu x) nabla2Du) :
    (1 / 2 : Real) * laplacian (I := I)
        (leviCivitaConnectionOfMetric (I := I) g) g
        (gradNormSq (I := I) g u) x =
      g.inner x
          (gradientFun (I := I) g
            (laplacian (I := I)
              (leviCivitaConnectionOfMetric (I := I) g) g u) x)
          (gradientFun (I := I) g u x) +
        hessianNormSq (I := I) g Hess x +
          ricciGradGrad (I := I) Ric g u x := by
  refine fundamental_bochner_of_lc_terms_of_normSecond_realizes (I := I)
    g Ric Rm13 Rm04 gInvFrame frame hRm13 hRic13 hRic04
    u Hess nablaDu roughDu basis gInvAt hinv X duSec normDuSec
    nablaDuSec nabla2Du normSecond normSecondSec hfields hHess hdu
    hnabla hnabla2 hnormSecond hnormDu hnormHess hnormGrad hsecond hrough
    ?_ ?_ ?_ ?_
  · exact traceNablaHessianRealizesDLapAt_of_leviCivita (I := I)
      g u basis gInvAt duSec nablaDuSec nabla2Du hinv hdu hnabla2
  · exact oneFormLastTwoSymmAt_of_leviCivita_du (I := I)
      g u hu duSec nablaDuSec nabla2Du hdu hnabla2
  · exact oneFormThirdCovDerivCommAt_of_leviCivita (I := I)
      g Rm13 duSec nablaDuSec (differential1FormFun (I := I) u x)
      nabla2Du hRm13 (by simpa [duField] using hdu x) hnabla2
  · exact rm13MetricSkewAt_of_leviCivita_realizes (I := I)
      g hcov Rm13 Rm04 hRm13 hRm04

end LeviCivita
end RicciFlower
