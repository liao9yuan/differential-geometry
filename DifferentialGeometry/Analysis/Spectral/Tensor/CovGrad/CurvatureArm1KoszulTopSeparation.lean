import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RemainderCoeffPerOrderJetEnvelopes
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmAppCc

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (ricciArmOrder1KoszulCoeff raisedKoszul)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private lemma arm1NormSq_eq_integral (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (C : SmoothCcTensor g r s) :
    ‖C‖ ^ 2 = ∫ x, riemannianFiberNormSq (I := I) (M := M) g r s x (C.toSection x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [SmoothCcTensor.norm_def (I := I) (M := M) C,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g r s C]

set_option linter.unusedVariables false in
theorem ricciArmOrder1KoszulCoeff_topSeparatedResidual_jetL2_flat_leak_allOrders
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧ ∃ Kleak : ℝ, 0 ≤ Kleak ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ),
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
                (ricciArmOrder1KoszulCoeff (I := I) (M := M) g₀ g₁) -
              appCcRS (I := I) (M := M) g₀ 3 1 (2 + i)
                (iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁))
                (cometricCastG0 (I := I) g₀ g₁)‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) +
              Kleak * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P‖ ^ 2 := by
  sorry

set_option linter.unusedVariables false in
theorem ricciArmOrder1KoszulCoeff_perOrder_l2_topSeparated_generic_allOrders
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧ ∃ Kleak : ℝ, 0 ≤ Kleak ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ),
          ∃ Hd : SmoothCcTensor g₀ 3 (2 + i),
            (∀ x : M,
              riemannianFiberNormSq (I := I) (M := M) g₀ 3 (2 + i) x (Hd.toSection x) ≤
                Ktop * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P).toSection x)) ∧
            ‖Hd‖ ^ 2 ≤ Ktop * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P‖ ^ 2 ∧
            ‖iteratedCovGrad (I := I) g₀ 3 2 i
                (ricciArmOrder1KoszulCoeff (I := I) (M := M) g₀ g₁) - Hd‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) +
                Kleak * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P‖ ^ 2 := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨ΛB, _, hΛB_nn, _, hBfeed⟩ :=
    cometricDoubleTraceField_order0sup_jetL2_ballUniform_generic
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨Kc, hKc_nn, Kleak, hKleak_nn, hleaf⟩ :=
    ricciArmOrder1KoszulCoeff_topSeparatedResidual_jetL2_flat_leak_allOrders
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨10 * ΛB ^ 2, by positivity, Kc, hKc_nn, Kleak, hKleak_nn, ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i
  obtain ⟨hBsup, _⟩ := hBfeed g₁ P hδ_le hδ htie hPball
  have hheadpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (2 + i) x
          ((appCcRS (I := I) (M := M) g₀ 3 1 (2 + i)
            (iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁))
            (cometricCastG0 (I := I) g₀ g₁)).toSection x) ≤
        10 * ΛB ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P).toSection x) := by
    intro x
    rw [appCcRS_toSection (I := I) (M := M) g₀ 3 1 (2 + i)
      (iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁))
      (cometricCastG0 (I := I) g₀ g₁) x]
    refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 3 1
      (2 + i) x _ _) ?_
    have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) ≤
        10 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P).toSection x) :=
      rfns_iteratedCovGrad_raisedKoszul_pointwise_le (I := I) (M := M) g₀ g₁ P htie i x
    have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 3 1 x
        ((cometricCastG0 (I := I) g₀ g₁).toSection x) ≤ ΛB ^ 2 := hBsup x
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 1 x
          ((cometricCastG0 (I := I) g₀ g₁).toSection x)
        ≤ (10 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P).toSection x)) * ΛB ^ 2 := by
          refine mul_le_mul h1 h2
            (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 3 1 x _) ?_
          have := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P).toSection x)
          positivity
      _ = 10 * ΛB ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P).toSection x) := by ring
  refine ⟨appCcRS (I := I) (M := M) g₀ 3 1 (2 + i)
      (iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁))
      (cometricCastG0 (I := I) g₀ g₁), hheadpt, ?_, ?_⟩
  · have hF_int : MeasureTheory.Integrable
        (fun x => 10 * ΛB ^ 2 *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
      (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (2 + (i + 1))
        (iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P)).const_mul _
    have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M)
      g₀ 3 (2 + i)
      (appCcRS (I := I) (M := M) g₀ 3 1 (2 + i)
        (iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁))
        (cometricCastG0 (I := I) g₀ g₁))
      _ hF_int hheadpt
    refine le_trans key ?_
    rw [MeasureTheory.integral_const_mul]
    rw [← arm1NormSq_eq_integral (I := I) (M := M) g₀ 0 (2 + (i + 1))
      (iteratedCovGrad (I := I) g₀ 0 2 (i + 1) P)]
  · exact hleaf g₁ P hδ_le hδ htie hPball i

end DifferentialGeometry.Integral.Connection

end
