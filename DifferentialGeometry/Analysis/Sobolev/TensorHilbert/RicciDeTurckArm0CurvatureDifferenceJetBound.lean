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

private theorem sq_le_two_add (t u v c1 c2 : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (htri : t ≤ u + v) (h1 : u ^ 2 ≤ c1) (h2 : v ^ 2 ≤ c2) : t ^ 2 ≤ 2 * (c1 + c2) := by
  have huv : 0 ≤ u + v := by linarith
  nlinarith [mul_le_mul htri htri ht huv, sq_nonneg (u - v), h1, h2, hu, hv]

theorem exists_coeffMixedRm_pinned (g₀ g₁ : SmoothRiemannianMetric I M) :
    ∃ mixed : SmoothCcTensor g₀ 2 2,
      ∀ (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x),
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 2 2 mixed W) x v =
          2 * ∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
            g₁.inner x (riemannOp (LeviCivita (I := I) g₀) x (v 0)
                (smoothOrthoFrame (I := I) g₁ x a' x)
                (smoothOrthoFrame (I := I) g₁ x b' x)) (v 1) *
              DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel
                (I := I) (M := M) g₀ 2 W x
                (fun j => if j = 0 then smoothOrthoFrame (I := I) g₁ x a' x
                  else smoothOrthoFrame (I := I) g₁ x b' x) :=
  sorry

noncomputable def coeffMixedRm (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 2 2 :=
  Classical.choose (exists_coeffMixedRm_pinned (I := I) (M := M) g₀ g₁)

theorem coeffMixedRm_appCc_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2 (coeffMixedRm (I := I) (M := M) g₀ g₁) W) x v =
      2 * ∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
        g₁.inner x (riemannOp (LeviCivita (I := I) g₀) x (v 0)
            (smoothOrthoFrame (I := I) g₁ x a' x)
            (smoothOrthoFrame (I := I) g₁ x b' x)) (v 1) *
          DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel
            (I := I) (M := M) g₀ 2 W x
            (fun j => if j = 0 then smoothOrthoFrame (I := I) g₁ x a' x
              else smoothOrthoFrame (I := I) g₁ x b' x) :=
  Classical.choose_spec (exists_coeffMixedRm_pinned (I := I) (M := M) g₀ g₁) W x v

theorem exists_coeffMixedCurv_pinned (g₀ g₁ : SmoothRiemannianMetric I M) :
    ∃ mixed : SmoothCcTensor g₀ 2 2,
      ∀ (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x),
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 2 2 mixed W) x v =
          DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel
              (I := I) (M := M) g₀ 2 W x
              (Function.update v 0
                (DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₁ x
                  (ricciTensor (I := I) g₀ x (v 0)).toLinearMap)) +
            DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel
              (I := I) (M := M) g₀ 2 W x
              (Function.update v 1
                (DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₁ x
                  (ricciTensor (I := I) g₀ x (v 1)).toLinearMap)) :=
  sorry

noncomputable def coeffMixedCurv (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 2 2 :=
  Classical.choose (exists_coeffMixedCurv_pinned (I := I) (M := M) g₀ g₁)

theorem coeffMixedCurv_appCc_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2 (coeffMixedCurv (I := I) (M := M) g₀ g₁) W) x v =
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel
          (I := I) (M := M) g₀ 2 W x
          (Function.update v 0
            (DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₁ x
              (ricciTensor (I := I) g₀ x (v 0)).toLinearMap)) +
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel
          (I := I) (M := M) g₀ 2 W x
          (Function.update v 1
            (DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₁ x
              (ricciTensor (I := I) g₀ x (v 1)).toLinearMap)) :=
  Classical.choose_spec (exists_coeffMixedCurv_pinned (I := I) (M := M) g₀ g₁) W x v

set_option linter.unusedVariables false in
theorem coeffMixedRm_sub_g1coeff_perOrder_l2_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C1 : ℕ → ℝ, (∀ i, 0 ≤ C1 i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁
              - coeffMixedRm (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤ C1 i :=
  sorry

set_option linter.unusedVariables false in
theorem coeffMixedRm_sub_g0coeff_perOrder_l2_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C2 : ℕ → ℝ, (∀ i, 0 ≤ C2 i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (coeffMixedRm (I := I) (M := M) g₀ g₁
              - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤ C2 i :=
  sorry

set_option linter.unusedVariables false in
theorem coeffMixedCurv_sub_g1coeff_perOrder_l2_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C1 : ℕ → ℝ, (∀ i, 0 ≤ C1 i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁
              - coeffMixedCurv (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤ C1 i :=
  sorry

set_option linter.unusedVariables false in
theorem coeffMixedCurv_sub_g0coeff_perOrder_l2_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C2 : ℕ → ℝ, (∀ i, 0 ≤ C2 i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (coeffMixedCurv (I := I) (M := M) g₀ g₁
              - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤ C2 i :=
  sorry

set_option linter.unusedVariables false in
theorem ricciArmOrder0RiemannCoeff_frameSplit_perOrder_l2_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C1 C2 : ℕ → ℝ, (∀ i, 0 ≤ C1 i) ∧ (∀ i, 0 ≤ C2 i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∃ mixed : SmoothCcTensor g₀ 2 2,
          (∀ (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x),
            DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ 2
                (appCc (I := I) (M := M) g₀ 2 2 mixed W) x v =
              2 * ∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
                g₁.inner x (riemannOp (LeviCivita (I := I) g₀) x (v 0)
                    (smoothOrthoFrame (I := I) g₁ x a' x)
                    (smoothOrthoFrame (I := I) g₁ x b' x)) (v 1) *
                  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel
                    (I := I) (M := M) g₀ 2 W x
                    (fun j => if j = 0 then smoothOrthoFrame (I := I) g₁ x a' x
                      else smoothOrthoFrame (I := I) g₁ x b' x)) ∧
          ∀ (i : ℕ), i ≤ a →
            ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ - mixed)‖ ^ 2 ≤ C1 i ∧
            ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (mixed - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤ C2 i := by
  obtain ⟨C1, hC1nn, hb1⟩ :=
    coeffMixedRm_sub_g1coeff_perOrder_l2_ballUniform (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨C2, hC2nn, hb2⟩ :=
    coeffMixedRm_sub_g0coeff_perOrder_l2_ballUniform (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨C1, C2, hC1nn, hC2nn, ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball
  refine ⟨coeffMixedRm (I := I) (M := M) g₀ g₁,
    coeffMixedRm_appCc_eq (I := I) (M := M) g₀ g₁, ?_⟩
  intro i hi
  exact ⟨hb1 g₁ P hδ_le hδ htie hPball i hi, hb2 g₁ P hδ_le hδ htie hPball i hi⟩

set_option linter.unusedVariables false in
theorem ricciArmOrder0CurvCoeff_frameSplit_perOrder_l2_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C1 C2 : ℕ → ℝ, (∀ i, 0 ≤ C1 i) ∧ (∀ i, 0 ≤ C2 i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∃ mixed : SmoothCcTensor g₀ 2 2,
          (∀ (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x),
            DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ 2
                (appCc (I := I) (M := M) g₀ 2 2 mixed W) x v =
              DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel
                  (I := I) (M := M) g₀ 2 W x
                  (Function.update v 0
                    (DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₁ x
                      (ricciTensor (I := I) g₀ x (v 0)).toLinearMap)) +
                DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel
                  (I := I) (M := M) g₀ 2 W x
                  (Function.update v 1
                    (DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₁ x
                      (ricciTensor (I := I) g₀ x (v 1)).toLinearMap))) ∧
          ∀ (i : ℕ), i ≤ a →
            ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ - mixed)‖ ^ 2 ≤ C1 i ∧
            ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (mixed - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤ C2 i := by
  obtain ⟨C1, hC1nn, hb1⟩ :=
    coeffMixedCurv_sub_g1coeff_perOrder_l2_ballUniform (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨C2, hC2nn, hb2⟩ :=
    coeffMixedCurv_sub_g0coeff_perOrder_l2_ballUniform (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨C1, C2, hC1nn, hC2nn, ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball
  refine ⟨coeffMixedCurv (I := I) (M := M) g₀ g₁,
    coeffMixedCurv_appCc_eq (I := I) (M := M) g₀ g₁, ?_⟩
  intro i hi
  exact ⟨hb1 g₁ P hδ_le hδ htie hPball i hi, hb2 g₁ P hδ_le hδ htie hPball i hi⟩

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
              - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤ C i := by
  obtain ⟨C1, C2, hC1nn, hC2nn, hbd⟩ :=
    ricciArmOrder0RiemannCoeff_frameSplit_perOrder_l2_ballUniform
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨fun i => 2 * (C1 i + C2 i),
    fun i => by have h1 := hC1nn i; have h2 := hC2nn i; linarith, ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i hi
  obtain ⟨mixed, _hpin, hpieces⟩ := hbd g₁ P hδ_le hδ htie hPball
  obtain ⟨hp1, hp2⟩ := hpieces i hi
  have hsplit : (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁
        - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)
      = (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ - mixed)
        + (mixed - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) := by abel
  have e1 := iteratedCovGrad_add (I := I) g₀ 2 2 i
    (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ - mixed)
    (mixed - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)
  rw [hsplit, e1]
  set u := iteratedCovGrad (I := I) g₀ 2 2 i
    (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ - mixed) with hu
  set v := iteratedCovGrad (I := I) g₀ 2 2 i
    (mixed - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) with hv
  clear_value u v
  exact sq_le_two_add ‖u + v‖ ‖u‖ ‖v‖ (C1 i) (C2 i)
    (norm_nonneg _) (norm_nonneg u) (norm_nonneg v) (norm_add_le u v) hp1 hp2

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
              - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤ C i := by
  obtain ⟨C1, C2, hC1nn, hC2nn, hbd⟩ :=
    ricciArmOrder0CurvCoeff_frameSplit_perOrder_l2_ballUniform
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨fun i => 2 * (C1 i + C2 i),
    fun i => by have h1 := hC1nn i; have h2 := hC2nn i; linarith, ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i hi
  obtain ⟨mixed, _hpin, hpieces⟩ := hbd g₁ P hδ_le hδ htie hPball
  obtain ⟨hp1, hp2⟩ := hpieces i hi
  have hsplit : (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁
        - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)
      = (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ - mixed)
        + (mixed - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) := by abel
  have e1 := iteratedCovGrad_add (I := I) g₀ 2 2 i
    (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ - mixed)
    (mixed - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)
  rw [hsplit, e1]
  set u := iteratedCovGrad (I := I) g₀ 2 2 i
    (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ - mixed) with hu
  set v := iteratedCovGrad (I := I) g₀ 2 2 i
    (mixed - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) with hv
  clear_value u v
  exact sq_le_two_add ‖u + v‖ ‖u‖ ‖v‖ (C1 i) (C2 i)
    (norm_nonneg _) (norm_nonneg u) (norm_nonneg v) (norm_add_le u v) hp1 hp2

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
