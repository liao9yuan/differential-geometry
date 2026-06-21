import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciDifferenceMeanValue

noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1600000

open Set Function MeasureTheory intervalIntegral Bundle Tensor0SBundle
open scoped Topology Manifold BigOperators ContDiff Matrix

namespace DifferentialGeometry
namespace PDE
namespace DeTurck
namespace RicciLinearization

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem riemannianFiberNormSq_ricciArmOrder0RiemannCoeff_realizedFam_ballUniform_le
    [BoundarylessManifold I M] [CompleteSpace E]
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ ΛR : ℝ, 0 ≤ ΛR ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
              ((ricciArmOrder0RiemannCoeff (I := I) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) ≤ ΛR ^ 2 :=
  sorry

theorem riemannianFiberNormSq_ricciArmPrincipalCoeffPure_realizedFam_ballUniform_le
    [BoundarylessManifold I M] [CompleteSpace E]
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ ΛR : ℝ, 0 ≤ ΛR ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
              ((ricciArmPrincipalCoeffPure (I := I) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) ≤ ΛR ^ 2 :=
  sorry

theorem riemannianFiberNormSq_ricciArmOrder0CurvCoeff_realizedFam_ballUniform_le
    [BoundarylessManifold I M] [CompleteSpace E]
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ ΛR : ℝ, 0 ≤ ΛR ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
              ((ricciArmOrder0CurvCoeff (I := I) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) ≤ ΛR ^ 2 :=
  sorry

set_option linter.unusedVariables false in
theorem exists_realizedFam_curvatureCoeff_ballUniform_bound
    [BoundarylessManifold I M] [CompleteSpace E]
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ ΛR : ℝ, 0 ≤ ΛR ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
              ((ricciArmOrder0RiemannCoeff (I := I) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) ≤ ΛR ^ 2 ∧
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
              ((ricciArmPrincipalCoeffPure (I := I) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) ≤ ΛR ^ 2 ∧
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
              ((ricciArmOrder0CurvCoeff (I := I) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) ≤ ΛR ^ 2 := by
  classical
  obtain ⟨Λ₀, hΛ₀_nn, hb₀⟩ :=
    riemannianFiberNormSq_ricciArmOrder0RiemannCoeff_realizedFam_ballUniform_le
      (I := I) g₀ a ha_super hR hδ₀
  obtain ⟨Λ₁, hΛ₁_nn, hb₁⟩ :=
    riemannianFiberNormSq_ricciArmPrincipalCoeffPure_realizedFam_ballUniform_le
      (I := I) g₀ a ha_super hR hδ₀
  obtain ⟨Λ₂, hΛ₂_nn, hb₂⟩ :=
    riemannianFiberNormSq_ricciArmOrder0CurvCoeff_realizedFam_ballUniform_le
      (I := I) g₀ a ha_super hR hδ₀
  refine ⟨max Λ₀ (max Λ₁ Λ₂), le_trans hΛ₀_nn (le_max_left _ _), ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs x
  have hΛ₀_le : Λ₀ ≤ max Λ₀ (max Λ₁ Λ₂) := le_max_left _ _
  have hΛ₁_le : Λ₁ ≤ max Λ₀ (max Λ₁ Λ₂) :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hΛ₂_le : Λ₂ ≤ max Λ₀ (max Λ₁ Λ₂) :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hM_nn : 0 ≤ max Λ₀ (max Λ₁ Λ₂) := le_trans hΛ₀_nn hΛ₀_le
  refine ⟨?_, ?_, ?_⟩
  · refine le_trans (hb₀ T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x) ?_
    exact pow_le_pow_left₀ hΛ₀_nn hΛ₀_le 2
  · refine le_trans (hb₁ T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x) ?_
    exact pow_le_pow_left₀ hΛ₁_nn hΛ₁_le 2
  · refine le_trans (hb₂ T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x) ?_
    exact pow_le_pow_left₀ hΛ₂_nn hΛ₂_le 2

end RicciLinearization
end DeTurck
end PDE
end DifferentialGeometry

end
