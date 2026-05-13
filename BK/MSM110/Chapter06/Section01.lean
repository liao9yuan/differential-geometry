/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RicciFlower contributors
-/

import RicciFlower.RicciFlow.Evolution.Connection
import RicciFlower.RicciFlow.Evolution.Metric
import RicciFlower.RicciFlow.Evolution.Ricci
import RicciFlower.RicciFlow.Evolution.Scalar
import RicciFlower.RicciFlow.Evolution.Volume

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

/-!
# MSM110 Chapter 6.1

Minimal book companion for the curvature evolution section.  The canonical
proofs remain in `RicciFlower.RicciFlow.Evolution.*`; this module only gives
book-label aliases for the checked fixed-frame/integrated interfaces.
-/

namespace BK
namespace MSM110
namespace Chapter06
namespace Section01

noncomputable section

open Bundle RicciFlower.RicciFlow
open RicciFlower.Coordinates
open MeasureTheory
open RicciFlower.Analysis.Volume
open RicciFlower.Analysis.VolumeVariation
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {u : Set M}

/-- MSM110 Chapter 6.1, Ricci-flow specialization of inverse-metric evolution. -/
theorem eq_inverse_metric_ricci_flow
    {D : RicciFlower.Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (gInv : Real -> RicciFlower.Realized.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hreg :
      MetricFrameTimeRegularityInFrameOnLocal
        (I := I) S gInv gInvDt frame u)
    (t : RicciFlower.Realized.RealTimeInterval.RegularTime D)
    (x : M) (i j : Idx) :
    HasDerivWithinAt
      (fun s : Real => gInv s x i j)
      (2 * raisedRicciCompInFrame (I := I) S gInv frame (t : Real) x i j)
      D.carrier
      (t : Real) :=
  RicciFlower.RicciFlow.evol_inverse_metric_inFrame
    (I := I) S hS gInv gInvDt frame hreg t x i j

/-- MSM110 Chapter 6.1, equation `eq:christoffel_symbols_ricci_flow`. -/
theorem eq_christoffel_symbols_ricci_flow
    {D : RicciFlower.Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (gInv : Real -> RicciFlower.Realized.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (hreg :
      MetricFrameSpacetimeRegularityInFrameOnLocal
        (I := I) S gInv gInvDt frame u)
    (hnabla :
      NablaRicciComponentsByConnectionInFrameOn
        (I := I) S frame u nablaRic)
    (t : RicciFlower.Realized.RealTimeInterval.RegularTime D)
    (x : M) (hx : x ∈ u)
    (i j k : Idx) :
    HasDerivWithinAt
      (fun s : Real =>
        RicciFlower.Coordinates.christoffelSymbolInFrame
          (S.family.connection s) frame hframe x i j k)
      (RicciFlower.Coordinates.ricciFlowChristoffelEvolutionRHSInFrame
        (nablaRicLastRaisedInFrame (M := M) gInv nablaRic)
        (nablaRicDirectionRaisedInFrame (M := M) gInv nablaRic)
        (t : Real) x i j k)
      D.carrier
      (t : Real) :=
  RicciFlower.RicciFlow.evol_christoffel_inFrame
    (I := I) S hS gInv gInvDt frame hframe hu nablaRic hreg hnabla t x hx i j k

/-- MSM110 Chapter 6.1, local coordinate-frame form of
`eq:riemann_curvature_three_one_ricci_flow_one`. -/
theorem eq_riemann_curvature_three_one_ricci_flow_one_local
    {D : RicciFlower.Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm13 : Real -> RicciFlower.Realized.Tensor13Section (I := I) (M := M))
    (gInv : Real -> RicciFlower.Realized.InverseMetricComponents M (CoordinateIdx (𝕜 := Real) E))
    (nablaRic :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (x₀ : M)
    (hRm : ∀ t : Real,
      RicciFlower.Realized.Rm13RealizesConnection
        (I := I) (S.family.connection t) (Rm13 t))
    (hcov : ∀ t : Real,
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (S.family.connection t) (∞ : WithTop ℕ∞))
    (htf : ∀ t : RicciFlower.Realized.RealTimeInterval.RegularTime D,
      RicciFlower.LeviCivita.IsTorsionFree (I := I) (S.family.connection (t : Real)))
    (hEvol : ChristoffelEvolutionEquationInFrameOn
      (I := I) S gInv (RicciFlower.Coordinates.coordinateFrameAt (I := I) x₀)
      (RicciFlower.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x₀)
      nablaRic)
    (hmixed : RicciFlower.RicciFlow.ChristoffelCoordMixedDerivativeInFrameOn
      (I := I) S gInv nablaRic x₀ D.carrier ({x₀} : Set M)) :
    Riemann13VariationFormulaInFrameOnLocal
      (I := I) (D := D) Rm13
      (RicciFlower.Coordinates.coordinateFrameAt (I := I) x₀)
      (RicciFlower.RicciFlow.coordinateFrameAt_isLocalFrame_singleton (I := I) x₀)
      (fun τ x d out l₁ l₂ =>
        christoffelVariationCovDerivCoordAt (I := I)
          (S.family.connection τ)
          (christoffelEvolutionRHSInFrame (M := M) gInv nablaRic)
          τ x d out l₁ l₂) :=
  RicciFlower.RicciFlow.riemann13VariationFormulaInFrameOnLocal_of_christoffelEvolution
    (I := I) S Rm13 gInv nablaRic x₀ hRm hcov htf hEvol hmixed

/-- MSM110 Chapter 6.1, local coordinate-frame Ricci variation obtained from
Christoffel evolution and the local Riemann trace. -/
theorem eq_ricci_tensor_ricci_flow_one_local_from_christoffel
    {D : RicciFlower.Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm13 : Real -> RicciFlower.Realized.Tensor13Section (I := I) (M := M))
    (gInv : Real -> RicciFlower.Realized.InverseMetricComponents M (CoordinateIdx (𝕜 := Real) E))
    (nablaRic :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (x₀ : M)
    (htrace : ∀ t : Real,
      RicciFlower.Realized.RicciTensorRealizesRm13Trace
        (I := I) (S.ricci t) (Rm13 t))
    (hRm : ∀ t : Real,
      RicciFlower.Realized.Rm13RealizesConnection
        (I := I) (S.family.connection t) (Rm13 t))
    (hcov : ∀ t : Real,
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (S.family.connection t) (∞ : WithTop ℕ∞))
    (htf : ∀ t : RicciFlower.Realized.RealTimeInterval.RegularTime D,
      RicciFlower.LeviCivita.IsTorsionFree (I := I) (S.family.connection (t : Real)))
    (hEvol : ChristoffelEvolutionEquationInFrameOn
      (I := I) S gInv (RicciFlower.Coordinates.coordinateFrameAt (I := I) x₀)
      (RicciFlower.Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) x₀)
      nablaRic)
    (hmixed : RicciFlower.RicciFlow.ChristoffelCoordMixedDerivativeInFrameOn
      (I := I) S gInv nablaRic x₀ D.carrier ({x₀} : Set M)) :
    RicciVariationFormulaInFrameOnLocal
      (I := I) S (RicciFlower.Coordinates.coordinateFrameAt (I := I) x₀)
      ({x₀} : Set M)
      (fun τ x d out l₁ l₂ =>
        christoffelVariationCovDerivCoordAt (I := I)
          (S.family.connection τ)
          (christoffelEvolutionRHSInFrame (M := M) gInv nablaRic)
          τ x d out l₁ l₂) :=
  RicciFlower.RicciFlow.ricciVariationFormulaInCoordFrameAt_of_christoffelEvolution
    (I := I) S Rm13 gInv nablaRic x₀ htrace hRm hcov htf hEvol hmixed

/-- MSM110 Chapter 6.1, local fixed-frame Ricci evolution from local variation
and the contracted commutator package. -/
theorem eq_ricci_tensor_ricci_flow_two_local
    {D : RicciFlower.Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> RicciFlower.Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> RicciFlower.Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (hInv : SymmetricInverseMetricComponentsInFrameOn gInv)
    (h_var : RicciVariationFormulaInFrameOnLocal (I := I) S frame u
      (nablaGammaDtFromNabla2RicInFrame (M := M) gInv nabla2Ric))
    (hcomm : RicciContractedCommutatorsInFrame
      (I := I) S Rm04 gInv frame nabla2Ric) :
    RicciEvolutionEquationInFrameOnLocal
      (I := I) S Rm04 gInv frame u
      (roughLapRicInFrame (M := M) gInv nabla2Ric) :=
  RicciFlower.RicciFlow.ricciEvolutionEquationInFrameOnLocal_of_variation_commutators
    (I := I) S Rm04 gInv frame u nabla2Ric hInv h_var hcomm

/-- MSM110 Chapter 6.1, equation `eq:ricci_tensor_ricci_flow_two`. -/
theorem eq_ricci_tensor_ricci_flow_two
    {D : RicciFlower.Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> RicciFlower.Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> RicciFlower.Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (hInv : SymmetricInverseMetricComponentsInFrameOn gInv)
    (h_var : RicciVariationFormulaInFrameOn (I := I) S frame
      (nablaGammaDtFromNabla2RicInFrame (M := M) gInv nabla2Ric))
    (hcomm : RicciContractedCommutatorsInFrame
      (I := I) S Rm04 gInv frame nabla2Ric)
    (t : RicciFlower.Realized.RealTimeInterval.RegularTime D)
    (x : M) (i j : Idx) :
    HasDerivWithinAt
      (fun s : Real => ricciCompInFrame (I := I) S frame s x i j)
      (roughLapRicInFrame (M := M) gInv nabla2Ric (t : Real) x i j +
        2 * rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame
          (t : Real) x i j -
        2 * ricciQuadraticCompInFrame (I := I) S gInv frame
          (t : Real) x i j)
      D.carrier
      (t : Real) :=
  RicciFlower.RicciFlow.evol_ricci_inFrame_of_variation_commutators
    (I := I) S Rm04 gInv frame nabla2Ric hInv h_var hcomm t x i j

/-- MSM110 Chapter 6.1, scalar contracted-Bianchi algebra bridge. -/
theorem scalar_contracted_bianchi_reduction
    {D : RicciFlower.Realized.RealTimeInterval}
    (scalarLap contractedRicciHessian : Real -> M -> Real)
    (hbianchi : ScalarSecondDerivativeContractedBianchiOn (D := D)
      scalarLap contractedRicciHessian) :
    ScalarContractedBianchiReductionOn (D := D)
      scalarLap contractedRicciHessian :=
  RicciFlower.RicciFlow.scalarContractedBianchiReductionOn_of_secondDerivativeContractedBianchi
    (M := M) scalarLap contractedRicciHessian hbianchi

/-- MSM110 Chapter 6.1, equation `eq:scalar_curv_evolu`. -/
theorem eq_scalar_curv_evolu
    {D : RicciFlower.Realized.RealTimeInterval}
    (scalar scalarLap contractedRicciHessian ricciNormSq : Real -> M -> Real)
    (hpre : ScalarPreBianchiEvolutionEquationOn (D := D)
      scalar scalarLap contractedRicciHessian ricciNormSq)
    (hbianchi : ScalarContractedBianchiReductionOn (D := D)
      scalarLap contractedRicciHessian) :
    ScalarEvolutionEquationOn (D := D) scalar scalarLap ricciNormSq :=
  RicciFlower.RicciFlow.msm110_ch6_1_scalar_curvature_evolution
    (M := M) scalar scalarLap contractedRicciHessian ricciNormSq hpre hbianchi

/-- MSM110 Chapter 6.1, equation `eq:evolution_of_volume_element`, in the
integrated moving-measure form used by the current volume API. -/
theorem eq_evolution_of_volume_element_integrated
    [CompactSpace M]
    (G : RicciFlower.Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (Ric : RicciFlower.Realized.RicciTensorField (I := I) (M := M) Real)
    {f : Real -> M -> Real} {t₀ : Real}
    (hEq : RicciFlower.Realized.MetricVariationEquationDerivAt (I := I) G Ric t₀)
    (hg : MetricFamilyRegularAt (I := I)
      (metricFamilyForMeasure (I := I) (M := M) G) t₀)
    (hf : FunctionRegularAt f t₀) :
    HasDerivAt
      (fun s : Real => ∫ x, f s x ∂(volumeMeasureFamily (I := I) (M := M) G s))
      (∫ x, (deriv (fun s : Real => f s x) t₀ -
            RicciFlower.RicciFlow.Evolution.Volume.scalarCurvatureFromRicciInVolumeFrame
              (I := I) (M := M) G Ric t₀ x * f t₀ x)
          ∂(volumeMeasureFamily (I := I) (M := M) G t₀))
      t₀ :=
  RicciFlower.RicciFlow.Evolution.Volume.volume_variation_ricciFlow_at_of_metricDeriv_canonicalScalar
    (I := I) (M := M) G Ric (f := f) hEq hg hf

/-- MSM110 Chapter 6.1, total-volume specialization of
`eq:evolution_of_volume_element`. -/
theorem total_volume_evolution_ricci_flow
    [CompactSpace M]
    (G : RicciFlower.Realized.RealizedMetricFamily (I := I) (M := M) Real)
    (Ric : RicciFlower.Realized.RicciTensorField (I := I) (M := M) Real)
    {t₀ : Real}
    (hEq : RicciFlower.Realized.MetricVariationEquationDerivAt (I := I) G Ric t₀)
    (hg : MetricFamilyRegularAt (I := I)
      (metricFamilyForMeasure (I := I) (M := M) G) t₀) :
    HasDerivAt
      (fun s : Real => ∫ _x, (1 : Real) ∂(volumeMeasureFamily (I := I) (M := M) G s))
      (∫ x, -
          RicciFlower.RicciFlow.Evolution.Volume.scalarCurvatureFromRicciInVolumeFrame
            (I := I) (M := M) G Ric t₀ x
          ∂(volumeMeasureFamily (I := I) (M := M) G t₀))
      t₀ :=
  RicciFlower.RicciFlow.Evolution.Volume.total_volume_variation_ricciFlow_at_of_metricDeriv
    (I := I) (M := M) G Ric hEq hg

end

end Section01
end Chapter06
end MSM110
end BK
