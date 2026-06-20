import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckRealizedSolutionFamily

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

theorem deTurckRemainder_iteratedCovGradSum_ballBound
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) (d : ℕ) (hda : a ≤ d) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀_nn : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ),
        (∀ j : ℕ, j ≤ d + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∑ q ∈ Finset.range (d + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 q
              (deTurckSmoothRemainder (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ)‖ ^ 2) ≤
          C * (1 + ∑ i ∈ Finset.range (d + 2 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i T‖ ^ 2) := by
  classical
  
  
  obtain ⟨Cdiff, hCdiff_nn, hCdiff⟩ :=
    deTurckRemainderDiff_iteratedCovGradSum_ballBound_order (I := I) (M := M) g₀ g_bg a ha_super d
      hda hR hδ₀
  
  have hδ0_lt : (0 : ℝ) < 1 := by norm_num
  have hδ0_le : (0 : ℝ) ≤ δ₀ := hδ₀_nn
  have hδ0 : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) 0 :=
    gFibreOpBound_ccTensorBilinSymm_zero (I := I) (M := M) g₀
  
  have hjet_zero : ∀ j : ℕ,
      iteratedCovGrad (I := I) g₀ 0 2 j (0 : SmoothCcTensor g₀ 0 2) = 0 := by
    intro j
    have h := iteratedCovGrad_sub (I := I) g₀ 0 2 j (0 : SmoothCcTensor g₀ 0 2) 0
    rw [sub_self] at h
    rw [h, sub_self]
  
  set N0 : SmoothCcTensor g₀ 0 2 :=
    deTurckSmoothRemainder (I := I) g₀ g_bg (0 : SmoothCcTensor g₀ 0 2) hδ0_lt hδ0 with hN0_def
  set K0 : ℝ := ∑ q ∈ Finset.range (d + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 q N0‖ ^ 2 with hK0_def
  have hK0_nn : 0 ≤ K0 := Finset.sum_nonneg fun q _ => sq_nonneg _
  refine ⟨2 * Cdiff + 2 * K0, by positivity, ?_⟩
  intro T δ hδ_le hδ hTball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  
  set Scol : ℝ := ∑ i ∈ Finset.range (d + 2 + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i T‖ ^ 2 with hScol_def
  have hScol_nn : 0 ≤ Scol := Finset.sum_nonneg fun i _ => sq_nonneg _
  
  have hT'ball : ∀ j : ℕ, j ≤ d + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (0 : SmoothCcTensor g₀ 0 2)‖ ≤ R := by
    intro j _
    rw [hjet_zero j, norm_zero]; exact hR
  
  set D : SmoothCcTensor g₀ 0 2 :=
    deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ - N0 with hD_def
  
  have hdiff := hCdiff T (0 : SmoothCcTensor g₀ 0 2) hδ_le hδ hδ0_le hδ0 hTball hT'ball
  
  have hdiff' : (∑ q ∈ Finset.range (d + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ ^ 2) ≤ Cdiff * Scol := by
    rw [hD_def, hN0_def, hScol_def]
    simpa only [sub_zero] using hdiff
  
  have hper : ∀ q ∈ Finset.range (d + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 q
          (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ)‖ ^ 2 ≤
        2 * ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ ^ 2 +
          2 * ‖iteratedCovGrad (I := I) g₀ 0 2 q N0‖ ^ 2 := by
    intro q _
    have hsplit : iteratedCovGrad (I := I) g₀ 0 2 q
        (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ) =
          iteratedCovGrad (I := I) g₀ 0 2 q D +
            iteratedCovGrad (I := I) g₀ 0 2 q N0 := by
      rw [hD_def, iteratedCovGrad_sub, sub_add_cancel]
    rw [hsplit]
    have htri := norm_add_le (iteratedCovGrad (I := I) g₀ 0 2 q D)
      (iteratedCovGrad (I := I) g₀ 0 2 q N0)
    have hsumnn : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ +
        ‖iteratedCovGrad (I := I) g₀ 0 2 q N0‖ :=
      add_nonneg (norm_nonneg _) (norm_nonneg _)
    have hsq : ‖iteratedCovGrad (I := I) g₀ 0 2 q D +
        iteratedCovGrad (I := I) g₀ 0 2 q N0‖ ^ 2 ≤
          (‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ +
            ‖iteratedCovGrad (I := I) g₀ 0 2 q N0‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htri 2
    refine hsq.trans ?_
    nlinarith [sq_nonneg (‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ -
      ‖iteratedCovGrad (I := I) g₀ 0 2 q N0‖)]
  
  calc (∑ q ∈ Finset.range (d + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 q
            (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ)‖ ^ 2)
      ≤ ∑ q ∈ Finset.range (d + 1),
          (2 * ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ ^ 2 +
            2 * ‖iteratedCovGrad (I := I) g₀ 0 2 q N0‖ ^ 2) := Finset.sum_le_sum hper
    _ = 2 * (∑ q ∈ Finset.range (d + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ ^ 2) +
          2 * K0 := by
        rw [hK0_def, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 * (Cdiff * Scol) + 2 * K0 := by
        have := hdiff'
        linarith
    _ ≤ (2 * Cdiff + 2 * K0) * (1 + Scol) := by
        have hCS_nn : 0 ≤ Cdiff * Scol := mul_nonneg hCdiff_nn hScol_nn
        nlinarith [hCdiff_nn, hK0_nn, hScol_nn, mul_nonneg hK0_nn hScol_nn]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
