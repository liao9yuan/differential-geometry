import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceJetTower
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCm
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciDifferenceMeanValue
import DifferentialGeometry.Geometry.Connection.SingleSlotOperatorFiberNormBound

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Geometry
namespace Curvature

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option linter.unusedSectionVars false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem exists_rfns_curvCoeff_realizedFam_le_of_jetEnvelope
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (B : ℝ)
    (hB : 0 ≤ B)
    (coeff : SmoothRiemannianMetric I M → SmoothCcTensor g₀ 2 2)
    (hcoeff_curvature : coeff = (fun g₁ => ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁) ∨
      coeff = (fun g₁ => ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁)) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
        (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (x : M),
        (∑ j ∈ Finset.range 3,
            (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
            ‖(iteratedCovGrad (I := I) g₀ 0 2 j
                (convexPerturbation (I := I) g₀ T T' s)).toSection x‖)) ≤ B →
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
              ((coeff (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) ≤ Λ :=
  sorry

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem exists_rfns_riemannBiContrFib_realizedFam_le_of_jetEnvelope
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (B : ℝ)
    (hB : 0 ≤ B) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
        (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (x : M),
        (∑ j ∈ Finset.range 3,
            (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
            ‖(iteratedCovGrad (I := I) g₀ 0 2 j
                (convexPerturbation (I := I) g₀ T T' s)).toSection x‖)) ≤ B →
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
              (show TensorRSSpace 2 2 I x from
                TensorRSSpace.ofCLM (riemannBiContrFib (I := I)
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) x)) ≤ Λ := by
  classical
  obtain ⟨Λ, hΛ_nn, hΛ⟩ :=
    exists_rfns_curvCoeff_realizedFam_le_of_jetEnvelope (I := I) (M := M) g₀ hδ₀ B hB
      (fun g₁ => ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁) (Or.inl rfl)
  refine ⟨Λ, hΛ_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' s hs x henv
  have h := hΛ T T' hδ_le hδ hδ'_le hδ' s hs x henv
  rwa [ricciArmOrder0RiemannCoeff_toSection] at h

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem exists_rfns_ricciArmOrder0CurvCoeffFib_realizedFam_le_of_jetEnvelope
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (B : ℝ)
    (hB : 0 ≤ B) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
        (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (x : M),
        (∑ j ∈ Finset.range 3,
            (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
            ‖(iteratedCovGrad (I := I) g₀ 0 2 j
                (convexPerturbation (I := I) g₀ T T' s)).toSection x‖)) ≤ B →
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
              (show TensorRSSpace 2 2 I x from
                TensorRSSpace.ofCLM (ricciArmOrder0CurvCoeffFib (I := I)
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) x)) ≤ Λ := by
  classical
  obtain ⟨Λ, hΛ_nn, hΛ⟩ :=
    exists_rfns_curvCoeff_realizedFam_le_of_jetEnvelope (I := I) (M := M) g₀ hδ₀ B hB
      (fun g₁ => ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) (Or.inr rfl)
  refine ⟨Λ, hΛ_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' s hs x henv
  have h := hΛ T T' hδ_le hδ hδ'_le hδ' s hs x henv
  rwa [ricciArmOrder0CurvCoeff_toSection] at h

end Curvature
end Geometry
end DifferentialGeometry

end
