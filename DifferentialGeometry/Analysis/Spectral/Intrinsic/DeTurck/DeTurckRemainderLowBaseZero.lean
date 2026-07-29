import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderLowBasePair

/-!
# Low-base zero-path action

This module isolates the exact action-level consequence of the public
Ricci--DeTurck zero-arm refold.  It introduces no high-Sobolev ball or
supercritical differentiability hypothesis.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Tensor0SBundle
open scoped BigOperators Manifold ContDiff

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-! ## Exact zero-path split -/

/-- The small second-order action created by the exact zero-arm refold. -/
def zeroA2Act
    (g : SmoothRiemannianMetric I M) (T U : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ) :
    SmoothCcTensor g 0 2 :=
  appCc (I := I) (M := M) g 4 2
    (rhsRefold2Int (I := I) (M := M) g T hδ_lt hδ hδZ)
    (iteratedCovGrad (I := I) g 0 2 2 U)

/-- The algebraic lower action left after the zero-arm refold.

This is not yet the final `A1` action: its zero-order coefficient still has to
be given an action-level top-head extraction before low-base estimates apply.
-/
def zeroLowAct
    (g : SmoothRiemannianMetric I M) (T U : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ) :
    SmoothCcTensor g 0 2 :=
  appCc (I := I) (M := M) g 2 2
      (rhsRefold0Int (I := I) (M := M) g g T hδ_lt hδ hδZ) U +
    appCc (I := I) (M := M) g 3 2
      (rhsLow1PathIntegral (I := I) (M := M) g g T 0
        hδ_lt hδ hδ_lt hδZ)
      (iteratedCovGrad (I := I) g 0 2 1 U)

/-- On the diagonal, the original zero- and one-order path actions split
exactly into the refolded second-order action and the algebraic lower action. -/
theorem zeroPath_split
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g T x v w =
        ccTensorBilin (I := I) g T x w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ) :
    appCc (I := I) (M := M) g 2 2
          (rhsLow0PathIntegral (I := I) (M := M) g g T 0
            hδ_lt hδ hδ_lt hδZ)
          (iteratedCovGrad (I := I) g 0 2 0 T) +
        appCc (I := I) (M := M) g 3 2
          (rhsLow1PathIntegral (I := I) (M := M) g g T 0
            hδ_lt hδ hδ_lt hδZ)
          (iteratedCovGrad (I := I) g 0 2 1 T) =
      zeroA2Act (I := I) (M := M) g T T hδ_lt hδ hδZ +
        zeroLowAct (I := I) (M := M) g T T hδ_lt hδ hδZ := by
  have hzero : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g (0 : SmoothCcTensor g 0 2) x v w =
        ccTensorBilin (I := I) g (0 : SmoothCcTensor g 0 2) x w v := by
    intro x v w
    have h0 : (0 : SmoothCcTensor g 0 2) =
        (0 : ℝ) • (0 : SmoothCcTensor g 0 2) := (zero_smul ℝ _).symm
    rw [h0]
    simp only [ccTensorBilin_apply, ccTensorModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul, zero_mul]
  have hraw := rhsArm_sub_eq_paths (I := I) (M := M) g g T 0
    hTsymm hzero hδ_lt hδ hδ_lt hδZ
  simp only [sub_zero] at hraw
  have href := rhs_sub_zero_refold (I := I) (M := M)
    g g T hTsymm hδ_lt hδ hδZ
  rw [refoldTopInt_eq (I := I) (M := M) g g T hδ_lt hδ hδZ,
    appCc_add_left] at href
  simp only [zeroA2Act, zeroLowAct]
  calc
    _ = (realizedRHSArm (I := I) g g T hδ_lt hδ -
          realizedRHSArm (I := I) g g 0 hδ_lt hδZ) -
        appCc (I := I) (M := M) g 4 2
          (rhsTopPathIntegral (I := I) (M := M) g g T 0
            hδ_lt hδ hδ_lt hδZ)
          (iteratedCovGrad (I := I) g 0 2 2 T) := by
      rw [hraw]
      abel
    _ = _ := by
      rw [href]
      abel

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
