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

theorem linearizedRicciArm0BaseCoeff_realizedFam_jetL2_perOrder_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s)‖ ^ 2 ≤ P i :=
  sorry

theorem linearizedRicciArm1BaseCoeff_realizedFam_jetL2_perOrder_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s)‖ ^ 2 ≤ P i :=
  sorry

theorem ricciArmPrincipalCoeff_realizedFam_jetL2_perOrder_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (ricciArmPrincipalCoeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 ≤ P i :=
  sorry

theorem traceHessianCoeff_realizedFam_jetL2_perOrder_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (traceHessianCoeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 ≤ P i :=
  sorry

end DifferentialGeometry.Integral.Connection

end
