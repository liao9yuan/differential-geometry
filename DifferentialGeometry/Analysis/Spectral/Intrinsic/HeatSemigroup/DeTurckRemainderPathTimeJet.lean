import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralEigenSeriesJointGram
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralPointwiseFlowDeriv
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckChartRegularityFromJoint
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators NNReal
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

theorem deTurckRemainder_path_coeff_timeJet_withMass
    (g₀ g_bg : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (F : ℝ → SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (F t)) δ)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (F t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i) :
    ∃ Rjet : ℕ → ℝ → SmoothCcTensor g₀ 0 2,
      (∀ i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
          ContDiff ℝ ∞ (fun t => tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
              (deTurckSmoothRemainder (I := I) g₀ g_bg (F t) hδ_lt (hδ t))) i)) ∧
        (∀ (j : ℕ) (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2),
          ∀ t ∈ Set.Icc (0 : ℝ) T,
            iteratedDeriv j (fun s => tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
                (deTurckSmoothRemainder (I := I) g₀ g_bg (F s) hδ_lt (hδ s))) i) t =
              tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Rjet j t)) i) ∧
        (∀ (j : ℕ) (σ : ℝ), 0 ≤ σ →
          ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
            ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
              tensorSobolevWeight (I := I) (M := M) i σ *
                  (tensorL2Coeff (I := I) (M := M)
                    (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                    (SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Rjet j t)) i) ^ 2 ≤ B i) :=
  sorry

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
