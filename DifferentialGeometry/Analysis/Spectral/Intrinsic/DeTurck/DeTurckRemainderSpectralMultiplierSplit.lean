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

theorem deTurckRemainderDiff_principalArm_spectralOrderShift_sharp
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ deTurckArmContractionThreshold (Module.finrank ℝ E))
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.gFibreOpBound
        (I := I) (M := M) g₀
        (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.ccTensorBilinSymm
          (I := I) g₀ T₀) δ) :
    ∃ Crem : ℕ → ℝ, (∀ k, 0 ≤ Crem k) ∧
      ∀ (k : ℕ) (T₀ : SmoothCcTensor g₀ 0 2)
        (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
            (deTurckSmoothRemainder (I := I) g₀ g_bg T₀
                (lt_of_le_of_lt hδ_le
                  (deTurckArmContractionThreshold_lt_one' (Module.finrank ℝ E)))
                (hδ_fibre T₀ hball) -
              deTurckSmoothRemainder (I := I) g₀ g_bg
                (0 : SmoothCcTensor g₀ 0 2)
                (lt_of_le_of_lt hδ_le
                  (deTurckArmContractionThreshold_lt_one' (Module.finrank ℝ E)))
                (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                  (by
                    rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                        from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                      tensorHs_norm_smul]
                    simpa using hR₀)))‖ ≤
          (1 / 2 : ℝ) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) + 1) T₀‖ +
            Crem k * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) T₀‖ := by
  classical
  have hδ_le13 : δ ≤ 1 / 3 :=
    le_trans hδ_le (deTurckArmContractionThreshold_le_third' (Module.finrank ℝ E))
  have ha1 : 1 ≤ a := by
    have h1 := Nat.one_le_iff_ne_zero.mpr (NeZero.ne (Module.finrank ℝ E))
    omega
  obtain ⟨Ctame, hCtame_nn, htame⟩ :=
    exists_deTurckSmoothRemainderDiff_eq_principalCometricArm_add_tame
      (I := I) (M := M) g₀ g_bg a (by omega) hR₀ hδ_le13 hδ_fibre
  obtain ⟨Clower, hClower_nn, hopn⟩ :=
    exists_smoothCcToTensorHs_deTurckPrincipalCometricArm_opNorm_le
      (I := I) (M := M) g₀ a ha_super hR₀ hδ_le13 hδ_fibre
  have hhalf : deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) ≤ 1 / 2 :=
    deTurckArmFibreConst_mul_div_le_half
      (Nat.one_le_iff_ne_zero.mpr (NeZero.ne (Module.finrank ℝ E))) hδ_le
  refine ⟨fun k => Ctame k + Clower (a - 1 + k),
    fun k => add_nonneg (hCtame_nn k) (hClower_nn _), fun k T₀ hball => ?_⟩
  obtain ⟨tame, hdecomp, htame_le⟩ := htame k T₀ hball
  have hgoal_eq : (deTurckSmoothRemainder (I := I) g₀ g_bg T₀
        (lt_of_le_of_lt hδ_le
          (deTurckArmContractionThreshold_lt_one' (Module.finrank ℝ E)))
        (hδ_fibre T₀ hball) -
      deTurckSmoothRemainder (I := I) g₀ g_bg
        (0 : SmoothCcTensor g₀ 0 2)
        (lt_of_le_of_lt hδ_le
          (deTurckArmContractionThreshold_lt_one' (Module.finrank ℝ E)))
        (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
          (by
            rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
              tensorHs_norm_smul]
            simpa using hR₀))) =
      (deTurckSmoothRemainder (I := I) g₀ g_bg T₀
          (lt_of_le_of_lt hδ_le13 (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball) -
        deTurckSmoothRemainder (I := I) g₀ g_bg
          (0 : SmoothCcTensor g₀ 0 2)
          (lt_of_le_of_lt hδ_le13 (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
            (by
              rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                  from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                tensorHs_norm_smul]
              simpa using hR₀))) := rfl
  rw [hgoal_eq, hdecomp, smoothCcToTensorHs_add]
  set N1 : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) + 1) T₀‖
    with hN1_def
  set N0 : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) T₀‖
    with hN0_def
  have hN1_nn : 0 ≤ N1 := by rw [hN1_def]; exact norm_nonneg _
  have harm_le :
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
          (deTurckPrincipalCometricArm (I := I) (M := M) g₀
            (tensorSectionRealizeMetric (I := I) g₀ T₀
              (lt_of_le_of_lt hδ_le13 (by norm_num : (1 : ℝ) / 3 < 1))
              (hδ_fibre T₀ hball)) T₀)‖ ≤
        (1 / 2 : ℝ) * N1 + Clower (a - 1 + k) * N0 := by
    have hσ : ((a - 1 + k : ℕ) : ℝ) = (a : ℝ) + (k : ℝ) - 1 := by
      have hs : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by
        rw [Nat.cast_sub ha1, Nat.cast_one]
      rw [Nat.cast_add, hs]; ring
    have hopk := hopn (a - 1 + k) T₀ hball
    have h1 := smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ hσ
      (deTurckPrincipalCometricArm (I := I) (M := M) g₀
        (tensorSectionRealizeMetric (I := I) g₀ T₀
          (lt_of_le_of_lt hδ_le13 (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre T₀ hball)) T₀)
    have h2 := smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
      (show ((a - 1 + k : ℕ) : ℝ) + 2 = (a : ℝ) + (k : ℝ) + 1 by rw [hσ]; ring) T₀
    have h3 := smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
      (show ((a - 1 + k : ℕ) : ℝ) + 1 = (a : ℝ) + (k : ℝ) by rw [hσ]; ring) T₀
    rw [h1, h2, h3, ← hN1_def, ← hN0_def] at hopk
    refine le_trans hopk ?_
    have htop : deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) * N1 ≤
        (1 / 2 : ℝ) * N1 :=
      mul_le_mul_of_nonneg_right hhalf hN1_nn
    linarith
  have htame_le' :
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1) tame‖ ≤
        Ctame k * N0 := by
    rw [hN0_def]; exact htame_le
  refine le_trans (norm_add_le _ _) ?_
  have hsum := add_le_add harm_le htame_le'
  have hcombine : (1 / 2 : ℝ) * N1 + Clower (a - 1 + k) * N0 + Ctame k * N0 =
      (1 / 2 : ℝ) * N1 + (Ctame k + Clower (a - 1 + k)) * N0 := by ring
  rw [hcombine] at hsum
  exact hsum

theorem deTurckSmoothRemainderDiff_spectralMultiplier_split
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ deTurckArmContractionThreshold (Module.finrank ℝ E))
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
                (lt_of_le_of_lt hδ_le
                  (deTurckArmContractionThreshold_lt_one' (Module.finrank ℝ E)))
                (hδ_fibre T₀ hball) -
              deTurckSmoothRemainder (I := I) g₀ g_bg
                (0 : SmoothCcTensor g₀ 0 2)
                (lt_of_le_of_lt hδ_le
                  (deTurckArmContractionThreshold_lt_one' (Module.finrank ℝ E)))
                (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                  (by
                    rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                        from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                      tensorHs_norm_smul]
                    simpa using hR₀)))‖ ≤
          Cδ₀ * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) + 1) T₀‖ +
            Crem k * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) T₀‖ := by
  obtain ⟨Crem, hCrem_nn, hbound⟩ :=
    deTurckRemainderDiff_principalArm_spectralOrderShift_sharp (I := I) (M := M) g₀ g_bg a
      ha_super hR₀ hδ_le hδ_fibre
  exact ⟨1 / 2, Crem, by norm_num, by norm_num, hCrem_nn, hbound⟩

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
