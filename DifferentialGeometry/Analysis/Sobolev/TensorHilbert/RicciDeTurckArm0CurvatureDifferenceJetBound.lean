import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RemainderCoeffPerOrderJetEnvelopes
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear

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
  (ricciArmOrder0RiemannCoeff ricciArmOrder0CurvCoeff)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option linter.unusedVariables false in
theorem ricciArmOrder0RiemannCoeff_sub_background_perOrder_l2_ballUniform_generic
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁
              - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤ C i :=
  sorry

set_option linter.unusedVariables false in
theorem ricciArmOrder0CurvCoeff_sub_background_perOrder_l2_ballUniform_generic
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁
              - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤ C i :=
  sorry

set_option linter.unusedVariables false in
set_option maxHeartbeats 1600000 in
theorem ricciArmOrder0BaseCoeff_perOrder_l2_ballUniform_generic
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁
              - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤ K i := by
  obtain ⟨CR, hCR_nn, hCR⟩ :=
    ricciArmOrder0RiemannCoeff_sub_background_perOrder_l2_ballUniform_generic
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨CC, hCC_nn, hCC⟩ :=
    ricciArmOrder0CurvCoeff_sub_background_perOrder_l2_ballUniform_generic
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨fun i => 3 * (CR i + CC i +
      ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀
          - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2), ?_, ?_⟩
  · intro i
    have h1 := hCR_nn i
    have h2 := hCC_nn i
    have h3 : (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀
          - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 := sq_nonneg _
    change (0 : ℝ) ≤ 3 * (CR i + CC i +
      ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀
          - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2)
    linarith
  · intro g₁ P δ hδ_le hδ htie hPball i hi
    have hR2 := hCR g₁ P hδ_le hδ htie hPball i hi
    have hC2 := hCC g₁ P hδ_le hδ htie hPball i hi
    change ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁
          - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
      3 * (CR i + CC i +
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀
            - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2)
    have hsplit : (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁
          - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁)
        = ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁
              - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)
            - (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁
              - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀))
          + (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀
              - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) := by abel
    have e1 := iteratedCovGrad_add (I := I) g₀ 2 2 i
      ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁
          - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)
        - (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁
          - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀))
      (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀
        - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)
    have e2 := iteratedCovGrad_sub (I := I) g₀ 2 2 i
      (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁
        - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)
      (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁
        - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)
    rw [hsplit, e1, e2]
    set u := iteratedCovGrad (I := I) g₀ 2 2 i
      (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁
        - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) with hu
    set v := iteratedCovGrad (I := I) g₀ 2 2 i
      (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁
        - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) with hv
    set w := iteratedCovGrad (I := I) g₀ 2 2 i
      (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀
        - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) with hw
    clear_value u v w
    have habc : ∀ (t a b c cr cc : ℝ), 0 ≤ a → 0 ≤ b → 0 ≤ c → 0 ≤ t →
        t ≤ a + b + c → a ^ 2 ≤ cr → b ^ 2 ≤ cc →
        t ^ 2 ≤ 3 * (cr + cc + c ^ 2) := by
      intro t a b c cr cc ha hb hc ht hsum hcr hcc
      have hsabc : 0 ≤ a + b + c := by linarith
      nlinarith [mul_le_mul hsum hsum ht hsabc, sq_nonneg (a - b), sq_nonneg (b - c),
        sq_nonneg (a - c), hcr, hcc, ha, hb, hc]
    have htri : ‖(u - v) + w‖ ≤ ‖u‖ + ‖v‖ + ‖w‖ := by
      calc ‖(u - v) + w‖ ≤ ‖u - v‖ + ‖w‖ := norm_add_le _ _
        _ ≤ (‖u‖ + ‖v‖) + ‖w‖ := add_le_add (norm_sub_le u v) le_rfl
    exact habc ‖(u - v) + w‖ ‖u‖ ‖v‖ ‖w‖ (CR i) (CC i)
      (norm_nonneg u) (norm_nonneg v) (norm_nonneg w) (norm_nonneg _) htri hR2 hC2

end DifferentialGeometry.Integral.Connection

end
