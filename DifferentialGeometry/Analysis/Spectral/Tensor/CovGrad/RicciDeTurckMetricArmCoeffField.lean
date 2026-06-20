import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricContractionTowerGrid
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricInverseDifferenceMultiplier

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization (gFibreOpBound)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

set_option backward.isDefEq.respectTransparency false in

def gInvDiffSlotCoeff (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M => TensorRSSpace.ofCLM (gInvDiffSlotEndo (I := I) g₀ g₁ x)
      contMDiff_toFun := gInvDiffSlotEndo_contMDiff (I := I) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in

def gInvDiffMetricArmCoeffField (g₀ g₁ : SmoothRiemannianMetric I M) :
    ∀ r : ℕ, SmoothCcTensor g₀ (r + 0) (r + 0) :=
  fun r => match r with
    | 2 => gInvDiffSlotCoeff (I := I) g₀ g₁
    | _ => 0

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in

theorem gInvDiffMetricArm_iteratedCovGrad_singleSum_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (x₀ : M) (W : SmoothCcTensor g₀ 0 2) (a : ℕ) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x₀
        ((iteratedCovGrad g₀ 0 2 a
          ((fixedCoeffDiffOp (I := I) (M := M) g₀
            (gInvDiffMetricArmCoeffField (I := I) g₀ g₁)).op 0 2 W)).toSection x₀) ≤
      ((4 : ℝ) ^ a * gridWindowSum
          (fixedCoeffDiffOp (I := I) (M := M) g₀
            (gInvDiffMetricArmCoeffField (I := I) g₀ g₁)).kappa 0 2 a) *
        ∑ q ∈ Finset.range (a + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x₀
            ((iteratedCovGrad g₀ 0 2 q W).toSection x₀) :=
  fixedCoeffDiffOp_iteratedCovGrad_singleSum_le (I := I) (M := M) g₀
    (gInvDiffMetricArmCoeffField (I := I) g₀ g₁) x₀ 2 W a

set_option linter.unusedSectionVars false in

theorem exists_gInvDiffMetricArm_neumannFibreBound (g₀ : SmoothRiemannianMetric I M) :
    ∃ Cnorm : ℝ, 0 ≤ Cnorm ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ),
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + h y v w) →
        ∀ {δ : ℝ}, δ < 1 / 2 → 0 ≤ δ → gFibreOpBound (I := I) g₀ h δ →
        ∀ (x : M) (v : TensorRSSpace 0 2 I x),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
              (gInvDiffFibreEndo (I := I) g₀ g₁ x v) ≤
            (Cnorm * δ) ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x v :=
  exists_gInvDiffFibreEndo_neumannFibreBound (I := I) g₀

end Connection
end Integral
end DifferentialGeometry

end
