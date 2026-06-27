import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmAppCc
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (linearizedRicciArm0BaseCoeff linearizedRicciArm1BaseCoeff ricciArmPrincipalCoeff
    traceHessianCoeff)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (realizedFam)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

noncomputable def coeffPerOrderJetBound (R δ₀ : ℝ) (curvWeight : ℕ) (i : ℕ) : ℝ :=
  (Module.finrank ℝ E : ℝ) ^ (curvWeight + 2) * (1 + R) ^ (2 * i + 6) *
    (1 / (1 - δ₀)) ^ (4 * i + 12)

theorem coeffPerOrderJetBound_nonneg (R δ₀ : ℝ) (hR : 0 ≤ R) (hδ₀ : δ₀ < 1)
    (curvWeight i : ℕ) : 0 ≤ coeffPerOrderJetBound (E := E) R δ₀ curvWeight i := by
  have hpos : 0 < 1 - δ₀ := by linarith
  have hinv_nn : 0 ≤ 1 / (1 - δ₀) := by positivity
  simp only [coeffPerOrderJetBound]
  refine mul_nonneg (mul_nonneg ?_ ?_) ?_
  · exact pow_nonneg (Nat.cast_nonneg _) _
  · exact pow_nonneg (by linarith) _
  · exact pow_nonneg hinv_nn _

set_option linter.unusedVariables false in
theorem linearizedRicciArm0BaseCoeff_perOrder_rfns_pointwise_singleOrder
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
          (linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s)).toSection x) ≤
      coeffPerOrderJetBound (E := E) R δ₀ 2 i :=
  sorry

set_option linter.unusedVariables false in
theorem linearizedRicciArm1BaseCoeff_perOrder_rfns_pointwise_singleOrder
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
    riemannianFiberNormSq (I := I) (M := M) g₀ 3 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 3 2 i
          (linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s)).toSection x) ≤
      coeffPerOrderJetBound (E := E) R δ₀ 3 i :=
  sorry

set_option linter.unusedVariables false in
theorem ricciArmPrincipalCoeff_realizedFam_perOrder_rfns_pointwise_singleOrder
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
    riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 4 2 i
          (ricciArmPrincipalCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s))).toSection x) ≤
      coeffPerOrderJetBound (E := E) R δ₀ 4 i :=
  sorry

set_option linter.unusedVariables false in
theorem traceHessianCoeff_realizedFam_perOrder_rfns_pointwise_singleOrder
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
    riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 4 2 i
          (traceHessianCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s))).toSection x) ≤
      coeffPerOrderJetBound (E := E) R δ₀ 4 i :=
  sorry

set_option linter.unusedVariables false in
theorem linearizedRicciArm0BaseCoeff_realizedFam_perOrder_rfns_pointwise_ballUniform
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
                (linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s)).toSection x) ≤ K i := by
  refine ⟨coeffPerOrderJetBound (E := E) R δ₀ 2,
    fun i => coeffPerOrderJetBound_nonneg R δ₀ hR hδ₀ 2 i, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i hi s hs x
  exact linearizedRicciArm0BaseCoeff_perOrder_rfns_pointwise_singleOrder
    (I := I) g₀ a ha_super hR hδ₀ T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i hi s hs x

set_option linter.unusedVariables false in
theorem linearizedRicciArm1BaseCoeff_realizedFam_perOrder_rfns_pointwise_ballUniform
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
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 3 2 i
                (linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s)).toSection x) ≤ K i := by
  refine ⟨coeffPerOrderJetBound (E := E) R δ₀ 3,
    fun i => coeffPerOrderJetBound_nonneg R δ₀ hR hδ₀ 3 i, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i hi s hs x
  exact linearizedRicciArm1BaseCoeff_perOrder_rfns_pointwise_singleOrder
    (I := I) g₀ a ha_super hR hδ₀ T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i hi s hs x

set_option linter.unusedVariables false in
theorem ricciArmPrincipalCoeff_realizedFam_perOrder_rfns_pointwise_ballUniform
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
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 4 2 i
                (ricciArmPrincipalCoeff (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s))).toSection x) ≤ K i := by
  refine ⟨coeffPerOrderJetBound (E := E) R δ₀ 4,
    fun i => coeffPerOrderJetBound_nonneg R δ₀ hR hδ₀ 4 i, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i hi s hs x
  exact ricciArmPrincipalCoeff_realizedFam_perOrder_rfns_pointwise_singleOrder
    (I := I) g₀ a ha_super hR hδ₀ T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i hi s hs x

set_option linter.unusedVariables false in
theorem traceHessianCoeff_realizedFam_perOrder_rfns_pointwise_ballUniform
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
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 4 2 i
                (traceHessianCoeff (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s))).toSection x) ≤ K i := by
  refine ⟨coeffPerOrderJetBound (E := E) R δ₀ 4,
    fun i => coeffPerOrderJetBound_nonneg R δ₀ hR hδ₀ 4 i, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i hi s hs x
  exact traceHessianCoeff_realizedFam_perOrder_rfns_pointwise_singleOrder
    (I := I) g₀ a ha_super hR hδ₀ T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i hi s hs x

theorem l2_of_pointwise_rfns_iteratedCovGrad_perOrder
    (g₀ : SmoothRiemannianMetric I M) (r i : ℕ)
    (C : SmoothCcTensor g₀ r 2) (Ki : ℝ)
    (hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ r (2 + i) x
          ((iteratedCovGrad (I := I) g₀ r 2 i C).toSection x) ≤ Ki) :
    ‖iteratedCovGrad (I := I) g₀ r 2 i C‖ ^ 2 ≤
      Ki * (riemannianVolumeMeasure (I := I) (M := M) g₀ Set.univ).toReal :=
  norm_le_of_pointwise_fiberNormSq_bound_rs (I := I) (M := M) g₀ r (2 + i)
    (iteratedCovGrad (I := I) g₀ r 2 i C) Ki hpt

end DifferentialGeometry.Integral.Connection

end
