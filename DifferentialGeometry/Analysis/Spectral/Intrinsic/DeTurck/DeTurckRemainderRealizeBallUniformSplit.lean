import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderPrincipalArmOpNorm

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

theorem deTurckPrincipalCometricArm_realize_ballUniform_Hs_norm_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ Clower : ℕ → ℝ, (∀ k, 0 ≤ Clower k) ∧
      ∀ (k : ℕ) (T₀ : SmoothCcTensor g₀ 0 2)
        (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀
              (tensorSectionRealizeMetric (I := I) g₀ T₀
                (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                (hδ_fibre T₀ hball)) T₀)‖ ≤
          (δ / (1 - δ)) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ +
            Clower k * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) T₀‖ :=
  sorry

theorem deTurckPrincipalCometricArm_realize_ballUniform_Hs_inner_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ Clower : ℕ → ℝ, (∀ k, 0 ≤ Clower k) ∧
      ∀ (k : ℕ) (φ T₀ : SmoothCcTensor g₀ 0 2)
        (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        (inner ℝ (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1) φ)
            (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
              (deTurckPrincipalCometricArm (I := I) (M := M) g₀
                (tensorSectionRealizeMetric (I := I) g₀ T₀
                  (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                  (hδ_fibre T₀ hball)) T₀)) : ℝ) ≤
          (δ / (1 - δ)) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖
              * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1) φ‖ +
            Clower k * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) T₀‖
              * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1) φ‖ := by
  obtain ⟨Clower, hCl, hnorm⟩ :=
    deTurckPrincipalCometricArm_realize_ballUniform_Hs_norm_le (I := I) (M := M)
      g₀ a ha_super hR₀ hδ_le hδ_fibre
  refine ⟨Clower, hCl, fun k φ T₀ hball => ?_⟩
  have hnb := hnorm k T₀ hball
  have hφ_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1) φ‖ :=
    norm_nonneg _
  calc (inner ℝ (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1) φ)
          (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀
              (tensorSectionRealizeMetric (I := I) g₀ T₀
                (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                (hδ_fibre T₀ hball)) T₀)) : ℝ)
      ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1) φ‖ *
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀
              (tensorSectionRealizeMetric (I := I) g₀ T₀
                (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                (hδ_fibre T₀ hball)) T₀)‖ := real_inner_le_norm _ _
    _ ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1) φ‖ *
          ((δ / (1 - δ)) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
                (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ +
            Clower k * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) T₀‖) :=
        mul_le_mul_of_nonneg_left hnb hφ_nn
    _ = (δ / (1 - δ)) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
              (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖
            * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1) φ‖ +
          Clower k * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) T₀‖
            * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1) φ‖ := by ring

theorem deTurckPrincipalCometricArm_realize_ballUniform_spectralShift_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ Clower : ℕ → ℝ, (∀ k, 0 ≤ Clower k) ∧
      ∀ (k : ℕ) (T₀ : SmoothCcTensor g₀ 0 2)
        (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀
              (tensorSectionRealizeMetric (I := I) g₀ T₀
                (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                (hδ_fibre T₀ hball)) T₀)‖ ≤
          (1 / 2 : ℝ) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) + 1) T₀‖ +
            Clower k * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) T₀‖ := by
  obtain ⟨Clower, hCl, hpair⟩ :=
    deTurckPrincipalCometricArm_realize_ballUniform_Hs_inner_le (I := I) (M := M)
      g₀ a ha_super hR₀ hδ_le hδ_fibre
  refine ⟨Clower, hCl, fun k T₀ hball => ?_⟩
  have hpair' := hpair k
    (deTurckPrincipalCometricArm (I := I) (M := M) g₀
      (tensorSectionRealizeMetric (I := I) g₀ T₀
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)) T₀)
    T₀ hball
  rw [real_inner_self_eq_norm_sq] at hpair'
  set NA : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
      (deTurckPrincipalCometricArm (I := I) (M := M) g₀
        (tensorSectionRealizeMetric (I := I) g₀ T₀
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)) T₀)‖
    with hNA_def
  set R : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
      (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ with hR_def
  set L : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) T₀‖ with hL_def
  set B : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) + 1) T₀‖ with hB_def
  change NA ≤ (1 / 2 : ℝ) * B + Clower k * L
  have h1δ : (0 : ℝ) < 1 - δ := by
    have := lt_of_le_of_lt hδ_le (show (1 : ℝ) / 3 < 1 by norm_num); linarith
  have hhalf : δ / (1 - δ) ≤ 1 / 2 := by
    rw [div_le_iff₀ h1δ]; linarith
  have hshift : R ≤ B := by
    rw [hR_def, hB_def]
    refine le_trans
      (smoothCcToTensorHs_rawTensorConnLapSmooth_le (I := I) (M := M) g₀
        ((a : ℝ) + (k : ℝ) - 1) T₀) ?_
    exact le_of_eq (smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
      (show (a : ℝ) + (k : ℝ) - 1 + 2 = (a : ℝ) + (k : ℝ) + 1 by ring) T₀)
  have hR_nn : 0 ≤ R := by rw [hR_def]; exact norm_nonneg _
  have hB_nn : 0 ≤ B := by rw [hB_def]; exact norm_nonneg _
  have hNA_nn : 0 ≤ NA := by rw [hNA_def]; exact norm_nonneg _
  have hL_nn : 0 ≤ L := by rw [hL_def]; exact norm_nonneg _
  have htop : δ / (1 - δ) * R ≤ 1 / 2 * B := by
    refine le_trans (mul_le_mul_of_nonneg_right hhalf hR_nn) ?_
    exact mul_le_mul_of_nonneg_left hshift (by norm_num)
  have htop_mul : δ / (1 - δ) * R * NA ≤ 1 / 2 * B * NA :=
    mul_le_mul_of_nonneg_right htop hNA_nn
  have hrhs_nn : 0 ≤ 1 / 2 * B + Clower k * L :=
    add_nonneg (mul_nonneg (by norm_num) hB_nn) (mul_nonneg (hCl k) hL_nn)
  have hsq : NA ^ 2 ≤ (1 / 2 * B + Clower k * L) * NA := by
    have hexp : (1 / 2 * B + Clower k * L) * NA = 1 / 2 * B * NA + Clower k * L * NA := by ring
    rw [hexp]; linarith [hpair', htop_mul]
  rcases eq_or_lt_of_le hNA_nn with hNA0 | hNApos
  · rw [← hNA0]; linarith [hrhs_nn]
  · rw [pow_two] at hsq
    exact le_of_mul_le_mul_right hsq hNApos

theorem deTurckSmoothRemainderDiff_ballUniform_spectralSplit
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.gFibreOpBound
        (I := I) (M := M) g₀
        (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.ccTensorBilinSymm
          (I := I) g₀ T₀) δ) :
    ∃ (Cδ₀ : ℝ) (Crem : ℕ → ℝ), 0 ≤ Cδ₀ ∧ Cδ₀ < 1 ∧ (∀ k, 0 ≤ Crem k) ∧
      ∀ (k : ℕ) (T₀ : SmoothCcTensor g₀ 0 2)
        (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
            (deTurckSmoothRemainder (I := I) g₀ g_bg T₀
                (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball) -
              deTurckSmoothRemainder (I := I) g₀ g_bg
                (0 : SmoothCcTensor g₀ 0 2)
                (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                  (by
                    rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                        from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                      tensorHs_norm_smul]
                    simpa using hR₀)))‖ ≤
          Cδ₀ * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) + 1) T₀‖ +
            Crem k * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) T₀‖ := by
  obtain ⟨Ctame, hCtame_nn, htame⟩ :=
    exists_deTurckSmoothRemainderDiff_eq_principalCometricArm_add_tame
      (I := I) (M := M) g₀ g_bg a ha_super hR₀ hδ_le hδ_fibre
  obtain ⟨Clower, hClower_nn, harm⟩ :=
    deTurckPrincipalCometricArm_realize_ballUniform_spectralShift_le
      (I := I) (M := M) g₀ a ha_super hR₀ hδ_le hδ_fibre
  refine ⟨1 / 2, fun k => Ctame k + Clower k, by norm_num, by norm_num,
    fun k => add_nonneg (hCtame_nn k) (hClower_nn k), fun k T₀ hball => ?_⟩
  obtain ⟨tame, hdecomp, htame_le⟩ := htame k T₀ hball
  rw [hdecomp, smoothCcToTensorHs_add]
  set N1 : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) + 1) T₀‖
    with hN1_def
  set N0 : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) T₀‖
    with hN0_def
  have harm_le := harm k T₀ hball
  rw [← hN1_def, ← hN0_def] at harm_le
  have htame_le' :
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1) tame‖ ≤
        Ctame k * N0 := by
    rw [hN0_def]; exact htame_le
  refine le_trans (norm_add_le _ _) ?_
  have hsum := add_le_add harm_le htame_le'
  have hcombine : (1 / 2 : ℝ) * N1 + Clower k * N0 + Ctame k * N0 =
      (1 / 2 : ℝ) * N1 + (Ctame k + Clower k) * N0 := by ring
  rw [hcombine] at hsum
  exact hsum

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
