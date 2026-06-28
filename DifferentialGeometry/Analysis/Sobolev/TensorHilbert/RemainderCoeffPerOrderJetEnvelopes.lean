import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciDeTurckArmCoeffPerOrderJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceJetTower

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (ricciArmOrder0RiemannCoeff raisedKoszul)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (realizedFam)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option linter.unusedVariables false in
theorem gInvDiffSlotCoeff_realizedFam_perOrder_rfns_pointwise_singleOrder
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_le : δ ≤ δ₀)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (hTball : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R)
    (hT'ball : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R)
    (i : ℕ) (hi : i ≤ a) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (gInvDiffSlotCoeff (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s))).toSection x) ≤
      coeffPerOrderJetBound (E := E) R δ₀ 2 i :=
  sorry

set_option linter.unusedVariables false in
theorem gInvDiffSlotCoeff_realizedFam_perOrder_rfns_pointwise_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 2 2 i
                (gInvDiffSlotCoeff (I := I) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s))).toSection x) ≤ K i := by
  refine ⟨coeffPerOrderJetBound (E := E) R δ₀ 2,
    fun i => coeffPerOrderJetBound_nonneg R δ₀ hR hδ₀ 2 i, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i hi s hs x
  exact gInvDiffSlotCoeff_realizedFam_perOrder_rfns_pointwise_singleOrder
    (I := I) g₀ a ha_super hR hδ₀ T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i hi s hs x

set_option linter.unusedVariables false in
theorem ricciArmOrder0RiemannCoeff_realizedFam_perOrder_rfns_pointwise_singleOrder
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_le : δ ≤ δ₀)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (hTball : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R)
    (hT'ball : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R)
    (i : ℕ) (hi : i ≤ a) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0RiemannCoeff (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s))).toSection x) ≤
      coeffPerOrderJetBound (E := E) R δ₀ 2 i :=
  sorry

set_option linter.unusedVariables false in
theorem ricciArmOrder0RiemannCoeff_realizedFam_perOrder_rfns_pointwise_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s))).toSection x) ≤ K i := by
  refine ⟨coeffPerOrderJetBound (E := E) R δ₀ 2,
    fun i => coeffPerOrderJetBound_nonneg R δ₀ hR hδ₀ 2 i, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i hi s hs x
  exact ricciArmOrder0RiemannCoeff_realizedFam_perOrder_rfns_pointwise_singleOrder
    (I := I) g₀ a ha_super hR hδ₀ T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i hi s hs x

set_option linter.unusedVariables false in
theorem raisedKoszul_realizedFam_perOrder_rfns_pointwise_singleOrder
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_le : δ ≤ δ₀)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (hTball : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R)
    (hT'ball : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R)
    (i : ℕ) (hi : i ≤ a) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 2 i
          (raisedKoszul (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s))).toSection x) ≤
      coeffPerOrderJetBound (E := E) R δ₀ 1 i :=
  sorry

set_option linter.unusedVariables false in
theorem raisedKoszul_realizedFam_perOrder_rfns_pointwise_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 1 2 i
                (raisedKoszul (I := I) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s))).toSection x) ≤ K i := by
  refine ⟨coeffPerOrderJetBound (E := E) R δ₀ 1,
    fun i => coeffPerOrderJetBound_nonneg R δ₀ hR hδ₀ 1 i, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i hi s hs x
  exact raisedKoszul_realizedFam_perOrder_rfns_pointwise_singleOrder
    (I := I) g₀ a ha_super hR hδ₀ T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i hi s hs x

end DifferentialGeometry.Integral.Connection

end
