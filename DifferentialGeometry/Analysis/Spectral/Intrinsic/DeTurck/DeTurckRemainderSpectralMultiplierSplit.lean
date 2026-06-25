import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderHigherOrderTame
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderPrincipalArmOpNorm
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralPouNormEquiv
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricInverseDifferenceMultiplier

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
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

theorem deTurckRemainderDiff_principalArm_spectralOrderShift_sharp
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
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
          (1 / 2 : ℝ) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) + 1) T₀‖ +
            Crem k * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) T₀‖ := by
  have hδ_lt1 : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)
  have hcoeff_pos : 0 < 1 - δ := by linarith
  obtain ⟨Ctame, hCtame_nn, htame⟩ :=
    exists_deTurckSmoothRemainderDiff_eq_principalCometricArm_add_tame
      (I := I) (M := M) g₀ g_bg a ha_super hR₀ hδ_le hδ_fibre
  set Clower : ℕ → ℝ := fun k =>
    (exists_smoothCcToTensorHs_deTurckPrincipalCometricArm_opNorm_le
      (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)).choose with hClower_def
  have hClower_nn : ∀ k, 0 ≤ Clower k := fun k =>
    (exists_smoothCcToTensorHs_deTurckPrincipalCometricArm_opNorm_le
      (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)).choose_spec.1
  have hClower_bound := fun k =>
    (exists_smoothCcToTensorHs_deTurckPrincipalCometricArm_opNorm_le
      (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)).choose_spec.2
  refine ⟨fun k => Ctame k + Clower k, fun k => add_nonneg (hCtame_nn k) (hClower_nn k),
    fun k T₀ hball => ?_⟩
  rcases isEmpty_or_nonempty M with hM | hM
  · have hzero : ∀ (σ : ℝ) (X : SmoothCcTensor g₀ 0 2),
        smoothCcToTensorHs (I := I) (M := M) g₀ σ X = 0 := by
      intro σ X
      have hL2norm : ‖SmoothCcTensor.toL2 X‖ = 0 := by
        rw [SmoothCcTensor.norm_toL2, SmoothCcTensor.norm_def, tensorL2Norm,
          tensorL2Inner, MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
      have hL2 : SmoothCcTensor.toL2 X = 0 := norm_eq_zero.mp hL2norm
      refine tensorHs.ext (funext fun i => ?_)
      rw [smoothCcToTensorHs_coeff, tensorHs.zero_coeff, hL2, tensorL2Coeff_eq_inner,
        inner_zero_right]
    rw [hzero, hzero, hzero, norm_zero, norm_zero, norm_zero, mul_zero, mul_zero, add_zero]
  have hδ_nn : 0 ≤ δ := by
    obtain ⟨x₀⟩ := hM
    obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x₀, v ≠ 0 := by
      haveI : Nontrivial (TangentSpace I x₀) := by
        have hfr : 0 < Module.finrank ℝ (TangentSpace I x₀) := by
          have hrk : Module.finrank ℝ (TangentSpace I x₀) = Module.finrank ℝ E := rfl
          rw [hrk]; exact Nat.pos_of_ne_zero (NeZero.ne _)
        exact Module.nontrivial_of_finrank_pos hfr
      exact exists_ne 0
    have hpos : 0 < g₀.inner x₀ v v := g₀.pos x₀ v hv
    have hbound := hδ_fibre T₀ hball x₀ v v
    have hsqrt_pos : 0 < Real.sqrt (g₀.inner x₀ v v) := Real.sqrt_pos.mpr hpos
    have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀ T₀ x₀ v v| := abs_nonneg _
    by_contra hδc
    have hδc' : δ < 0 := lt_of_not_ge hδc
    have hrhs_neg : δ * Real.sqrt (g₀.inner x₀ v v) * Real.sqrt (g₀.inner x₀ v v) < 0 := by
      have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 :=
        mul_neg_of_neg_of_pos hδc' hsqrt_pos
      exact mul_neg_of_neg_of_pos h1 hsqrt_pos
    linarith [le_trans habs_nn hbound]
  have hratio_le : δ / (1 - δ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hcoeff_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  obtain ⟨tame, hdecomp, htame_le⟩ := htame k T₀ hball
  rw [hdecomp, smoothCcToTensorHs_add]
  set Nspec1 : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) + 1) T₀‖
    with hNspec1_def
  set Nspec0 : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) T₀‖
    with hNspec0_def
  have hNspec1_nn : 0 ≤ Nspec1 := norm_nonneg _
  have hNspec0_nn : 0 ≤ Nspec0 := norm_nonneg _
  have harm_le :
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1)
          (deTurckPrincipalCometricArm (I := I) (M := M) g₀
            (tensorSectionRealizeMetric (I := I) g₀ T₀
              (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)) T₀)‖ ≤
        (1 / 2 : ℝ) * Nspec1 + Clower k * Nspec0 := by
    have hopnorm :=
      hClower_bound k
        (tensorSectionRealizeMetric (I := I) g₀ T₀
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball))
        (fun y => ccTensorBilinSymm (I := I) g₀ T₀ y)
        (fun y v w => tensorSectionRealizeMetric_inner (I := I) g₀ T₀
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball) y v w)
        hδ_lt1 hδ_nn (hδ_fibre T₀ hball) T₀
    have heq2 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1 + 2) T₀‖ =
        Nspec1 := by
      rw [hNspec1_def]
      exact smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by ring) T₀
    have heq1 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1 + 1) T₀‖ =
        Nspec0 := by
      rw [hNspec0_def]
      exact smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by ring) T₀
    rw [heq2, heq1] at hopnorm
    refine le_trans hopnorm ?_
    have htop : (δ / (1 - δ)) * Nspec1 ≤ (1 / 2 : ℝ) * Nspec1 :=
      mul_le_mul_of_nonneg_right hratio_le hNspec1_nn
    linarith
  have htame_le' :
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1) tame‖ ≤
        Ctame k * Nspec0 := by
    rw [hNspec0_def]; exact htame_le
  refine le_trans (norm_add_le _ _) ?_
  have hsum := add_le_add harm_le htame_le'
  have hcombine : (1 / 2 : ℝ) * Nspec1 + Clower k * Nspec0 + Ctame k * Nspec0 =
      (1 / 2 : ℝ) * Nspec1 + (Ctame k + Clower k) * Nspec0 := by ring
  rw [hcombine] at hsum
  exact hsum

theorem deTurckSmoothRemainderDiff_spectralMultiplier_split
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
  obtain ⟨Crem, hCrem_nn, hbound⟩ :=
    deTurckRemainderDiff_principalArm_spectralOrderShift_sharp (I := I) (M := M) g₀ g_bg a
      ha_super hR₀ hδ_le hδ_fibre
  exact ⟨1 / 2, Crem, by norm_num, by norm_num, hCrem_nn, hbound⟩

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
