import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Retag
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.CovDivergenceRoughLaplacianCommutation
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricTraceRetag
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SharpFlatEndoField
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.ConnDiffCovGradBridge

/-!
# Scalar nonautonomous tame coefficients

This file packages the moving-cometric principal coefficient over a fixed
background metric.  The coefficient is kept as an intrinsic operator field;
evaluation lemmas are scalarized before unfolding the Hom-bundle model.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Tensor0SBundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- The moving cometric double-trace field, retagged over a fixed background
metric without changing its underlying section. -/
noncomputable def traceCast
    (q h : SmoothRiemannianMetric I M) : SmoothCcTensor q 2 0 :=
  SmoothCcTensor.retagEquiv h q 2 0
    (cometricDoubleTraceField (I := I) h 0)

/-- The retagged moving trace factors through the fixed trace after retagging
one covariant slot by `q♭ ∘ h♯`. -/
theorem trace_retag_eq
    (q h : SmoothRiemannianMetric I M) :
    traceCast (I := I) q h =
      appCcRS (I := I) (M := M) q 2 2 0
        (cometricDoubleTraceField (I := I) q 0)
        (slotExtend (I := I) (M := M) q 1 1
          (sharpFlatEndoCc (I := I) q h)) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [traceCast, SmoothCcTensor.retag_toSection,
    appCcRS_toSection, cometricDoubleTraceField_toSection,
    slotExtend_toSection, sharpFlatEndoCc_toSection,
    ContinuousLinearMap.comp_apply]
  exact trace_slot_flat (I := I) q h x D

/-- Retagging the fixed trace over its own metric leaves it unchanged. -/
theorem traceCast_self (q : SmoothRiemannianMetric I M) :
    traceCast (I := I) q q = cometricDoubleTraceField (I := I) q 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [traceCast, SmoothCcTensor.retag_toSection]

/-- The covector endomorphism measuring the moving inverse-cometric
difference relative to the fixed background metric. -/
noncomputable def scalarFluxCoeff
    (q h : SmoothRiemannianMetric I M) : SmoothCcTensor q 1 1 :=
  sharpFlatEndoCc (I := I) q h - sharpFlatEndoCc (I := I) q q

/-- The principal coefficient in the scalar moving-minus-fixed Laplacian. -/
noncomputable def scalarTraceCoeff
    (q h : SmoothRiemannianMetric I M) : SmoothCcTensor q 2 0 :=
  traceCast (I := I) q h - cometricDoubleTraceField (I := I) q 0

/-- The scalar principal coefficient is the fixed cometric trace of the
slot-extended inverse-cometric difference. -/
theorem scalar_trace_factor
    (q h : SmoothRiemannianMetric I M) :
    scalarTraceCoeff (I := I) q h =
      appCcRS (I := I) (M := M) q 2 2 0
        (cometricDoubleTraceField (I := I) q 0)
        (slotExtend (I := I) (M := M) q 1 1
          (scalarFluxCoeff (I := I) q h)) := by
  rw [scalarTraceCoeff, scalarFluxCoeff, slotExtend_sub, appCcRS_sub_right]
  rw [← trace_retag_eq (I := I) (M := M) q h,
    ← trace_retag_eq (I := I) (M := M) q q, traceCast_self]

/-- The scalar principal Hessian arm is a divergence-form flux minus the
coefficient-derivative lower-order arm. -/
theorem scalar_flux_split
    (q h : SmoothRiemannianMetric I M) (U : SmoothCcTensor q 0 0) :
    appCc (I := I) (M := M) q 2 0 (scalarTraceCoeff (I := I) q h)
        (iteratedCovGrad (I := I) q 0 0 2 U) =
      covDivergence (I := I) (M := M) q 0
          (appCc (I := I) (M := M) q 1 1
            (scalarFluxCoeff (I := I) q h)
            (iteratedCovGrad (I := I) q 0 0 1 U)) -
        appCc (I := I) (M := M) q 1 0
          (appCcRS (I := I) (M := M) q 1 2 0
            (cometricDoubleTraceField (I := I) q 0)
            (covGrad (I := I) (M := M) q 1 1
              (scalarFluxCoeff (I := I) q h)))
          (iteratedCovGrad (I := I) q 0 0 1 U) := by
  have htwo :
      covGrad (I := I) (M := M) q 0 1
          (iteratedCovGrad (I := I) q 0 0 1 U) =
        iteratedCovGrad (I := I) q 0 0 2 U := by
    rw [iteratedCovGrad_succ]
  have hdiv := covDiv_appCc (I := I) (M := M) q
    (scalarFluxCoeff (I := I) q h)
    (iteratedCovGrad (I := I) q 0 0 1 U)
  rw [htwo] at hdiv
  rw [scalar_trace_factor, hdiv]
  abel

/-- The first-order coefficient obtained by tracing the connection difference
with the moving cometric, represented over the fixed background metric. -/
noncomputable def connTraceCoeff
    (q h : SmoothRiemannianMetric I M) : SmoothCcTensor q 1 0 :=
  appCcRS (I := I) (M := M) q 1 2 0 (traceCast (I := I) q h)
    (connDiffSection (I := I) h q)

/-- The scalar moving-minus-fixed Laplacian coefficient expression over the
fixed background: moving trace on the fixed Hessian, minus the traced
connection-difference correction on the fixed gradient. -/
noncomputable def scalarLapDiffCc
    (q h : SmoothRiemannianMetric I M) (U : SmoothCcTensor q 0 0) :
    SmoothCcTensor q 0 0 :=
  appCc (I := I) (M := M) q 2 0 (scalarTraceCoeff (I := I) q h)
      (iteratedCovGrad (I := I) q 0 0 2 U) -
    appCc (I := I) (M := M) q 1 0 (connTraceCoeff (I := I) q h)
      (iteratedCovGrad (I := I) q 0 0 1 U)

/-- Fully applied scalar normal form for the retagged moving trace. -/
theorem traceCast_apply
    (q h : SmoothRiemannianMetric I M) (W : SmoothCcTensor q 0 2) (x : M) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 0 I x from
            (appCc (I := I) (M := M) q 2 0
              (traceCast (I := I) q h) W).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (fun i => Fin.elim0 i) =
      Tensor0SSpace.toModel
          (cometricDoubleTraceFib (I := I) h 0 x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
                W.toSection x)
              (unitZeroSec (I := I) (M := M) x)))
        (fun i => Fin.elim0 i) := by
  rw [appCc_toSection, traceCast,
    SmoothCcTensor.retag_toSection, cometricDoubleTraceField_toSection]
  rfl

/-- Fully applied scalar normal form for the moving-minus-fixed principal
coefficient. -/
theorem scalarTrace_apply
    (q h : SmoothRiemannianMetric I M) (W : SmoothCcTensor q 0 2) (x : M) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 0 I x from
            (appCc (I := I) (M := M) q 2 0
              (scalarTraceCoeff (I := I) q h) W).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (fun i => Fin.elim0 i) =
      Tensor0SSpace.toModel
          (cometricDoubleTraceFib (I := I) h 0 x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
                W.toSection x)
              (unitZeroSec (I := I) (M := M) x)))
          (fun i => Fin.elim0 i) -
        Tensor0SSpace.toModel
          (cometricDoubleTraceFib (I := I) q 0 x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
                W.toSection x)
              (unitZeroSec (I := I) (M := M) x)))
          (fun i => Fin.elim0 i) := by
  rw [scalarTraceCoeff, appCc_sub_left]
  have h_sec :
      (appCc (I := I) (M := M) q 2 0 (traceCast (I := I) q h) W -
          appCc (I := I) (M := M) q 2 0
            (cometricDoubleTraceField (I := I) q 0) W).toSection x =
        (appCc (I := I) (M := M) q 2 0 (traceCast (I := I) q h) W).toSection x -
          (appCc (I := I) (M := M) q 2 0
            (cometricDoubleTraceField (I := I) q 0) W).toSection x := rfl
  rw [h_sec]
  rw [ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub,
    ContinuousMultilinearMap.sub_apply]
  rw [traceCast_apply (I := I) (M := M) q h W x]
  rw [appCc_toSection, cometricDoubleTraceField_toSection]
  rfl

/-- Fully applied scalar normal form for the traced connection-difference
coefficient. -/
theorem connTrace_apply
    (q h : SmoothRiemannianMetric I M) (W : SmoothCcTensor q 0 1) (x : M) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 0 I x from
            (appCc (I := I) (M := M) q 1 0
              (connTraceCoeff (I := I) q h) W).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (fun i => Fin.elim0 i) =
      Tensor0SSpace.toModel
          (cometricDoubleTraceFib (I := I) h 0 x
            ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
                connDiffFib (I := I) h q x)
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
                  W.toSection x)
                (unitZeroSec (I := I) (M := M) x))))
        (fun i => Fin.elim0 i) := by
  rw [connTraceCoeff, appCc_toSection, appCcRS_toSection, traceCast,
    SmoothCcTensor.retag_toSection, cometricDoubleTraceField_toSection,
    connDiffSection_toSection]
  rfl

/-- Fully applied scalar decomposition of the moving-minus-fixed Laplacian
coefficient expression. -/
theorem scalarLapDiff_apply
    (q h : SmoothRiemannianMetric I M) (U : SmoothCcTensor q 0 0) (x : M) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 0 I x from
            (scalarLapDiffCc (I := I) q h U).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (fun i => Fin.elim0 i) =
      (Tensor0SSpace.toModel
          (cometricDoubleTraceFib (I := I) h 0 x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
                (iteratedCovGrad (I := I) q 0 0 2 U).toSection x)
              (unitZeroSec (I := I) (M := M) x)))
          (fun i => Fin.elim0 i) -
        Tensor0SSpace.toModel
          (cometricDoubleTraceFib (I := I) q 0 x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
                (iteratedCovGrad (I := I) q 0 0 2 U).toSection x)
              (unitZeroSec (I := I) (M := M) x)))
          (fun i => Fin.elim0 i)) -
        Tensor0SSpace.toModel
          (cometricDoubleTraceFib (I := I) h 0 x
            ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
                connDiffFib (I := I) h q x)
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
                  (iteratedCovGrad (I := I) q 0 0 1 U).toSection x)
                (unitZeroSec (I := I) (M := M) x))))
          (fun i => Fin.elim0 i) := by
  rw [scalarLapDiffCc]
  have h_sec :
      (appCc (I := I) (M := M) q 2 0 (scalarTraceCoeff (I := I) q h)
            (iteratedCovGrad (I := I) q 0 0 2 U) -
          appCc (I := I) (M := M) q 1 0 (connTraceCoeff (I := I) q h)
            (iteratedCovGrad (I := I) q 0 0 1 U)).toSection x =
        (appCc (I := I) (M := M) q 2 0 (scalarTraceCoeff (I := I) q h)
            (iteratedCovGrad (I := I) q 0 0 2 U)).toSection x -
          (appCc (I := I) (M := M) q 1 0 (connTraceCoeff (I := I) q h)
            (iteratedCovGrad (I := I) q 0 0 1 U)).toSection x := rfl
  rw [h_sec, ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub,
    ContinuousMultilinearMap.sub_apply]
  rw [scalarTrace_apply (I := I) (M := M) q h
      (iteratedCovGrad (I := I) q 0 0 2 U) x,
    connTrace_apply (I := I) (M := M) q h
      (iteratedCovGrad (I := I) q 0 0 1 U) x]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
