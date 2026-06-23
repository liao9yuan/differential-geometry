import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckMetricArmCoeffField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceFibreBound
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingReverseHebeyToHs
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCmOrderDropping
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.PointwiseToL2Packaging

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
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization (gFibreOpBound ccTensorBilinSymm)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option linter.unusedSectionVars false in
theorem tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) :
    tensorL2Norm (I := I) (M := M) g r s S.toFun ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  have hfun : S.toFun = fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
      (r := r) (s := s) (x := x) (S.toSection x) := rfl
  rw [hfun]
  exact tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g r s _

set_option linter.unusedSectionVars false in
theorem norm_le_of_pointwise_fiberNormSq_bound_rs
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (C : SmoothCcTensor g r s) (B : ℝ)
    (hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g r s x (C.toSection x) ≤ B) :
    ‖C‖ ^ 2 ≤ B * (riemannianVolumeMeasure (I := I) (M := M) g Set.univ).toReal := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  rw [SmoothCcTensor.norm_def (I := I) (M := M) C,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g r s C]
  have hint : MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g r s x (C.toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g r s C
  calc ∫ x, riemannianFiberNormSq (I := I) (M := M) g r s x (C.toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)
      ≤ ∫ _x, B ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
        refine MeasureTheory.integral_mono hint (MeasureTheory.integrable_const B)
          (fun x => hpt x)
    _ = B * (riemannianVolumeMeasure (I := I) (M := M) g Set.univ).toReal := by
        rw [MeasureTheory.integral_const, smul_eq_mul,
          MeasureTheory.measureReal_def, mul_comm]

set_option linter.unusedSectionVars false in
theorem riemannianFiberNormSq_gInvDiffSlotCoeff_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : δ < 1 / 2) (hδ0 : 0 ≤ δ)
    (h : ∀ y v w, g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm g₀ T y v w)
    (hbound : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm g₀ T) δ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((gInvDiffSlotCoeff (I := I) g₀ g₁).toSection x) ≤
      ((Module.finrank ℝ E : ℝ)) ^ 2 := by
  have hδ1 : δ < 1 := by linarith
  have hbase := riemannianFiberNormSq_gInvDiffSlotEndo_le (I := I) (M := M) g₀ g₁
    (ccTensorBilinSymm g₀ T) (fun y v w => h y v w) hδ1 hδ0 hbound x
  have hcoeff : (0 : ℝ) < 1 - δ := by linarith
  have hratio : δ / (1 - δ) ≤ 1 := by
    rw [div_le_one hcoeff]; linarith
  have hratio0 : 0 ≤ δ / (1 - δ) := div_nonneg hδ0 (by linarith)
  have hfr0 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  have hmono : ((Module.finrank ℝ E : ℝ) * (δ / (1 - δ))) ^ 2 ≤
      ((Module.finrank ℝ E : ℝ)) ^ 2 := by
    have : (Module.finrank ℝ E : ℝ) * (δ / (1 - δ)) ≤ (Module.finrank ℝ E : ℝ) := by
      calc (Module.finrank ℝ E : ℝ) * (δ / (1 - δ))
          ≤ (Module.finrank ℝ E : ℝ) * 1 := by
            exact mul_le_mul_of_nonneg_left hratio hfr0
        _ = (Module.finrank ℝ E : ℝ) := by rw [mul_one]
    nlinarith [mul_nonneg hfr0 hratio0]
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          ((gInvDiffSlotCoeff (I := I) g₀ g₁).toSection x)
      = riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          (show TensorRSSpace 2 2 I x from
            TensorRSSpace.ofCLM (gInvDiffSlotEndo (I := I) g₀ g₁ x)) := by rfl
    _ ≤ ((Module.finrank ℝ E : ℝ) * (δ / (1 - δ))) ^ 2 := hbase
    _ ≤ ((Module.finrank ℝ E : ℝ)) ^ 2 := hmono

end Connection
end Integral
end DifferentialGeometry

end
