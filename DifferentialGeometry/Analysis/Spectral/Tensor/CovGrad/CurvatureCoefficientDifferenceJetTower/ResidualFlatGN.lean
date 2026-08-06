import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.InverseMetricRaisedEndomorphismJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.JetProductIntegral
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RecoveryEndomorphismJetBound
import DifferentialGeometry.Tensor.Multilinear.Basis
import DifferentialGeometry.Tensor.Mixed.Field
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqSmoothCcUniformBound
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FiberNormSubadditivity
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenbergLpFiberNorm
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderHigherOrderTame
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RaisedKoszulCovariantJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RaisedKoszulParallelRaiseJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceArmRfnsBound
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnDiffPalatini
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.AppCcDropIteratedGrid
import DifferentialGeometry.Analysis.Sobolev.BoundedFactorProductGrid
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fin.Tuple.NatAntidiagonal

/-!
# Gagliardo–Nirenberg interpolation input for the capped-top-layer flat integral

The `hGNv` proof block extracted from
`boundedFactorGrid_cappedTopLayer_integral_flat` (`ResidualFlat.lean`) so that it
elaborates in its own Lean process; a memory refactor only, the hog theorem's
statement is unchanged.

The interpolation constant is passed in as a function `Cgn` together with the
single identification `hCgn_ch` naming it as the chosen witness of the
Gagliardo–Nirenberg existential, so that the `Exists.choose` bookkeeping happens
once, in the consumer.

Chunk map: `../CurvatureCoefficientDifferenceJetTower.md`.
-/

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
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization (gFibreOpBound ccTensorBilinSymm ccTensorBilin ccTensorBilin_apply ccTensorModel ccTensorMultilinear ccTensorBilinSymm_contMDiff ccTensorBilinSymm_apply ccTensorBilinSymm_symm)
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

namespace CurvatureCoefficientDifferenceJetTower

/-- Gagliardo–Nirenberg interpolation for the intermediate jets of `∇²P`, with
the interpolation constant supplied as `Cgn i₀` through the identification
`hCgn_ch`, and the top jet written as a `SmoothCcTensor` norm. -/
theorem jetGNInterp (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {Cgn : ℕ → ℝ}
    (hCgn_ch : ∀ (k : ℕ) (hk : 1 ≤ k),
      (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 (2 + 2) k hk).choose = Cgn k)
    {Lam : ℝ} (hLam_nn : 0 ≤ Lam)
    (hΛsup_v2 : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 2) x
        ((iteratedCovGrad (I := I) g₀ 0 2 2 P).toSection x) ≤ Lam ^ 2)
    (i₀ : ℕ) (hi₀ : 1 ≤ i₀) (j : ℕ) (hj0 : 0 < j) (hji : j < i₀) :
    (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + j) x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + 2) j
              (iteratedCovGrad (I := I) g₀ 0 2 2 P)).toSection x)) ^ ((i₀ : ℝ) / (j : ℝ))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((j : ℝ) / (i₀ : ℝ)) ≤
      Cgn i₀ * Lam ^ (2 * (1 - (j : ℝ) / (i₀ : ℝ))) *
        ‖iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
          (iteratedCovGrad (I := I) g₀ 0 2 2 P)‖ ^ (2 * (j : ℝ) / (i₀ : ℝ)) := by
  have hGNspec := (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
    (I := I) (M := M) g₀ 0 (2 + 2) i₀ hi₀).choose_spec.2
  have hb := hGNspec (iteratedCovGrad (I := I) g₀ 0 2 2 P) Lam hLam_nn hΛsup_v2 j hj0 hji
  rw [hCgn_ch i₀ hi₀] at hb
  have hnorm : Integral.L2.tensorL2Norm (I := I) g₀ 0 ((2 + 2) + i₀)
      (iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
        (iteratedCovGrad (I := I) g₀ 0 2 2 P)).toFun =
      ‖iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀ (iteratedCovGrad (I := I) g₀ 0 2 2 P)‖ :=
    (SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
      (iteratedCovGrad (I := I) g₀ 0 2 2 P))).symm
  rw [hnorm] at hb
  exact hb

end CurvatureCoefficientDifferenceJetTower

end Connection
end Integral
end DifferentialGeometry

end
