import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.LieCorr0CoeffL2JetBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.LieCorr0AMixRefold

/-!
# Low-regularity normal form for the `lc0VB` correction

This module exposes the nested operator-field factorization already proved by
`lc0VB_eq_app` and `vbSplit`.  It keeps the exact Ricci--DeTurck contraction
visible to low-regularity estimates without importing the unfinished
`LieCorr0LowJet` module.
-/

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open LieCorr0Core

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
  [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- At the base background, `wXi` is the `g₀`-lowered connection difference. -/
theorem wXi_self_eq (g₀ g₁ : SmoothRiemannianMetric I M) :
    wXi (I := I) (M := M) g₀ g₁ g₀ =
      connDiffLoweredCc (I := I) g₀ g₁ := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  apply ContinuousMultilinearMap.ext
  intro m
  rw [wXi_unitModel_apply, connDiffLoweredCc_unitModel_apply']

/-- On a covariant passenger, the moving cometric trace is represented by
`lc0TraceRF` without identifying the ambient mixed-tensor bundles. -/
theorem trace_app_refold (g₀ g₁ : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g₀ 0 3) :
    appCcRS (I := I) (M := M) g₀ 0 3 1
        (cometricCastG0 (I := I) g₀ g₁) W =
      appCcRS (I := I) (M := M) g₀ 0 3 1
        (lc0TraceRF (I := I) (M := M) g₀ g₁ 1 (Equiv.refl _)) W := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  simp only [unitModel, appCcRS_toSection, ContinuousLinearMap.comp_apply]
  let Z : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      W.toSection x) (unitTensor (I := I) (M := M) x)
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 1 I x from
        (cometricCastG0 (I := I) g₀ g₁).toSection x) Z) =
    Tensor0SSpace.toModel
      ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 1 I x from
        (lc0TraceRF (I := I) (M := M) g₀ g₁ 1 (Equiv.refl _)).toSection x) Z)
  rw [show
    (show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 1 I x from
      (lc0TraceRF (I := I) (M := M) g₀ g₁ 1 (Equiv.refl _)).toSection x) Z =
        lieCorr0TraceStep (I := I) g₁ 1 (Equiv.refl _) x Z from
      congrFun (congrArg DFunLike.coe
        (lc0TraceRF_fiber (I := I) (M := M) g₀ g₁ 1 (Equiv.refl _) x)) Z]
  rfl

/-- The base-background DeTurck covector as a rank-one trace applied to the
`g₀`-lowered connection difference. -/
theorem wOmega_refold (g₀ g₁ : SmoothRiemannianMetric I M) :
    wOmega (I := I) (M := M) g₀ g₁ g₀ =
      appCcRS (I := I) (M := M) g₀ 0 3 1
        (lc0TraceRF (I := I) (M := M) g₀ g₁ 1 (Equiv.refl _))
        (connDiffLoweredCc (I := I) g₀ g₁) := by
  unfold wOmega
  rw [wXi_self_eq, ← appCcRS_zero_eq_appCc]
  exact trace_app_refold (I := I) (M := M) g₀ g₁ _

/-- Changing the fixed DeTurck background cancels the common moving
connection difference before the moving trace is estimated. -/
theorem wOmega_sub_refold (g₀ g₁ gA gB : SmoothRiemannianMetric I M) :
    wOmega (I := I) (M := M) g₀ g₁ gA -
        wOmega (I := I) (M := M) g₀ g₁ gB =
      appCcRS (I := I) (M := M) g₀ 0 3 1
        (lc0TraceRF (I := I) (M := M) g₀ g₁ 1 (Equiv.refl _))
        (connDiffLoweredCc (I := I) g₀ gB -
          connDiffLoweredCc (I := I) g₀ gA) := by
  unfold wOmega
  rw [← appCcRS_zero_eq_appCc, ← appCcRS_zero_eq_appCc,
    ← appCcRS_sub_right]
  rw [show
    wXi (I := I) (M := M) g₀ g₁ gA -
        wXi (I := I) (M := M) g₀ g₁ gB =
      connDiffLoweredCc (I := I) g₀ gB -
        connDiffLoweredCc (I := I) g₀ gA by
    unfold wXi
    abel]
  exact trace_app_refold (I := I) (M := M) g₀ g₁ _

/-- The nested RicciFlower operator form of the vector--bilinear correction. -/
noncomputable def lc0VBFormRF (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 :=
  (2 : ℝ) • appCcRS (I := I) (M := M) g₀ 2 4 2
    (lc0RiemLive (I := I) (M := M) g₀ g₁)
    (appCcRS (I := I) (M := M) g₀ 2 1 4
      (vbMcdArm (I := I) (M := M) g₀ g₁)
      (ipLowCc (I := I) (M := M) g₀
        (wOmega (I := I) (M := M) g₀ g₁ g₀)))

/-- The vector--bilinear correction equals its nested RicciFlower operator form. -/
theorem vb_refold_rf (g₀ g₁ : SmoothRiemannianMetric I M) :
    lc0VB (I := I) (M := M) g₀ g₁ =
      lc0VBFormRF (I := I) (M := M) g₀ g₁ := by
  rw [lc0VB_eq_app, vbSplit]
  rfl

end DifferentialGeometry.Integral.Connection
