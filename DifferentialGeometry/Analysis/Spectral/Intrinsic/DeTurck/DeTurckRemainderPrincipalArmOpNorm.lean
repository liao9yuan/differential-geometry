import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckPrincipalCometricExtraction
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckPrincipalArmSpectralGarding
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderHigherOrderTame
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralPouNormEquiv
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricInverseDifferenceMultiplier
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.ConnLapCommutatorCoefficientTame
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingSharpC0JetSum
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.ChartH2GardingConstant
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.IntegratedOrder2Weitzenbock
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.PointwiseToL2Packaging
import DifferentialGeometry.Geometry.Connection.TensorNabla.HomFieldActionIteratedCovGradWindow
import DifferentialGeometry.Analysis.Integration.L2.FiniteProductHolderFiberNorm
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricPathResolventFactorization

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

theorem smoothCcToTensorHs_rawTensorConnLapSmooth_le
    (g₀ : SmoothRiemannianMetric I M) (σ : ℝ) (T : SmoothCcTensor g₀ 0 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T)‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (σ + 2) T‖ := by
  classical
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
    with hcompact_def
  set lam : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g₀ 0 2 → ℝ :=
    fun i => DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
      (I := I) (M := M) i with hlam_def
  set c : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g₀ 0 2 → ℝ :=
    fun i => tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 T) i
    with hc_def
  have hnn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ (σ + 2) T‖ := norm_nonneg _
  have hlam_nn : ∀ i, 0 ≤ lam i := fun i =>
    DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensor_lambda_nonneg
      (I := I) (M := M) i
  have hLHS_term : ∀ i,
      tensorSobolevWeight (I := I) (M := M) i σ *
          (tensorL2Coeff (I := I) (M := M) h_compact
            (SmoothCcTensor.toL2 (rawTensorConnLapSmooth (I := I) g₀ 0 2 T)) i) ^ 2 =
        tensorSobolevWeight (I := I) (M := M) i σ * (lam i) ^ 2 * (c i) ^ 2 := by
    intro i
    rw [tensorL2Coeff_ofCompact_rawTensorConnLapSmooth (I := I) (M := M) g₀ h_compact T i]
    rw [show (- lam i * c i) ^ 2 = (lam i) ^ 2 * (c i) ^ 2 by ring]
    ring
  have hRHS_term : ∀ i,
      tensorSobolevWeight (I := I) (M := M) i (σ + 2) * (c i) ^ 2 =
        tensorSobolevWeight (I := I) (M := M) i σ * (1 + lam i) ^ 2 * (c i) ^ 2 := by
    intro i
    rw [tensorHs.tensorSobolevWeight_add (I := I) (M := M) i σ 2]
    have hw2 : tensorSobolevWeight (I := I) (M := M) i (2 : ℝ) = (1 + lam i) ^ 2 := by
      unfold tensorSobolevWeight
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hw2]
  have hsummable_RHS : Summable (fun i =>
      tensorSobolevWeight (I := I) (M := M) i σ * (1 + lam i) ^ 2 * (c i) ^ 2) := by
    have hw := (ccSpectralEmbed (I := I) (M := M) g₀ (σ + 2) T).weighted_summable
    refine hw.congr (fun i => ?_)
    rw [ccSpectralEmbed_coeff,
      show tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 T) i = c i from rfl]
    exact hRHS_term i
  have hsummable_LHS : Summable (fun i =>
      tensorSobolevWeight (I := I) (M := M) i σ * (lam i) ^ 2 * (c i) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hsummable_RHS
    · have := tensorSobolevWeight_pos (I := I) (M := M) i σ
      have := hlam_nn i
      positivity
    · have hwpos : 0 ≤ tensorSobolevWeight (I := I) (M := M) i σ :=
        le_of_lt (tensorSobolevWeight_pos (I := I) (M := M) i σ)
      have hbase : (lam i) ^ 2 ≤ (1 + lam i) ^ 2 := by
        have := hlam_nn i; nlinarith
      have hc2 : 0 ≤ (c i) ^ 2 := sq_nonneg _
      nlinarith [mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hbase hwpos) hc2]
  have hsq : ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T)‖ ^ 2 ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (σ + 2) T‖ ^ 2 := by
    rw [tensorHs.norm_sq_eq_tsum, tensorHs.norm_sq_eq_tsum]
    rw [show (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          ((smoothCcToTensorHs (I := I) (M := M) g₀ σ
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 T)).coeff i) ^ 2) =
        fun i => tensorSobolevWeight (I := I) (M := M) i σ * (lam i) ^ 2 * (c i) ^ 2 by
      funext i
      rw [smoothCcToTensorHs_coeff, ← hcompact_def]
      exact hLHS_term i]
    rw [show (fun i => tensorSobolevWeight (I := I) (M := M) i (σ + 2) *
          ((smoothCcToTensorHs (I := I) (M := M) g₀ (σ + 2) T).coeff i) ^ 2) =
        fun i => tensorSobolevWeight (I := I) (M := M) i σ * (1 + lam i) ^ 2 * (c i) ^ 2 by
      funext i
      rw [smoothCcToTensorHs_coeff, ← hcompact_def,
        show tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 T) i = c i from rfl]
      exact hRHS_term i]
    refine Summable.tsum_le_tsum (fun i => ?_) hsummable_LHS hsummable_RHS
    have hwpos : 0 ≤ tensorSobolevWeight (I := I) (M := M) i σ :=
      le_of_lt (tensorSobolevWeight_pos (I := I) (M := M) i σ)
    have hbase : (lam i) ^ 2 ≤ (1 + lam i) ^ 2 := by
      have := hlam_nn i; nlinarith
    have hc2 : 0 ≤ (c i) ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbase hwpos) hc2]
  exact le_of_sq_le_sq hsq hnn

theorem exists_smoothCcToTensorHs_deTurckPrincipalCometricArm_opNorm_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 4 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ Clower : ℕ → ℝ, (∀ m, 0 ≤ Clower m) ∧
      ∀ (m : ℕ) (T₀ : SmoothCcTensor g₀ 0 2)
        (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀
              (tensorSectionRealizeMetric (I := I) g₀ T₀
                (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                (hδ_fibre T₀ hball)) T₀)‖ ≤
          deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T₀‖ +
            Clower m * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1) T₀‖ := by
  classical
  obtain ⟨Clower, hClower_nn, hbound⟩ :=
    exists_smoothCcToTensorHs_deTurckPrincipalCometricArm_principal_le
      (I := I) (M := M) g₀ a ha_super hR₀ hδ_le hδ_fibre
  refine ⟨Clower, hClower_nn, fun m T₀ hball => ?_⟩
  rcases isEmpty_or_nonempty M with hM | hM
  · have hzero : ∀ (τ : ℝ) (X : SmoothCcTensor g₀ 0 2),
        smoothCcToTensorHs (I := I) (M := M) g₀ τ X = 0 := by
      intro τ X
      have hL2norm : ‖SmoothCcTensor.toL2 X‖ = 0 := by
        rw [SmoothCcTensor.norm_toL2, SmoothCcTensor.norm_def,
          DifferentialGeometry.Integral.L2.tensorL2Norm,
          DifferentialGeometry.Integral.L2.tensorL2Inner,
          MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
      have hL2 : SmoothCcTensor.toL2 X = 0 := norm_eq_zero.mp hL2norm
      refine tensorHs.ext (funext fun i => ?_)
      rw [smoothCcToTensorHs_coeff, tensorHs.zero_coeff,
        hL2, tensorL2Coeff_eq_inner, inner_zero_right]
    rw [hzero, hzero, hzero]
    simp
  · have hδ_nn : 0 ≤ δ :=
      delta_nonneg_of_ball_gFibreOpBound (I := I) (M := M) g₀ a hR₀ hδ_fibre
    have hδ_lt1 : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)
    have hκ_nn : 0 ≤ δ / (1 - δ) := div_nonneg hδ_nn (by linarith)
    have hCEκ_nn : 0 ≤ deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) :=
      mul_nonneg (deTurckArmFibreConst_nonneg _) hκ_nn
    refine le_trans (hbound m T₀ hball) ?_
    have hshift : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ ≤
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T₀‖ :=
      smoothCcToTensorHs_rawTensorConnLapSmooth_le (I := I) (M := M) g₀ (m : ℝ) T₀
    have htop : deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ ≤
        deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) *
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T₀‖ :=
      mul_le_mul_of_nonneg_left hshift hCEκ_nn
    linarith

theorem exists_appCc_iteratedCovGrad_l2_dataJetWindow_le
    (g₀ : SmoothRiemannianMetric I M) (m : ℕ) :
    ∃ Cgrid : ℕ → ℝ, (∀ q, 0 ≤ Cgrid q) ∧
      ∀ (q : ℕ) (C : SmoothCcTensor g₀ (2 + m) 2) (Kc : ℝ) (T₀ : SmoothCcTensor g₀ 0 2),
        0 ≤ Kc →
        (∀ (i : ℕ), i ≤ q → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) (2 + i) x
            ((iteratedCovGrad (I := I) g₀ (2 + m) 2 i C).toSection x) ≤ Kc ^ 2) →
        ‖iteratedCovGrad (I := I) g₀ 0 2 q
            (appCc (I := I) (M := M) g₀ (2 + m) 2 C
              (iteratedCovGrad (I := I) g₀ 0 2 m T₀))‖ ≤
          Cgrid q * Kc * Real.sqrt (∑ i ∈ Finset.range (q + m + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) := by
  classical
  refine ⟨fun q => Real.sqrt (appCcGdiag (E := E) q * ((q : ℝ) + 1)) *
      Real.sqrt ((q + m + 1 : ℕ) : ℝ),
    fun q => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _),
    fun q C Kc T₀ hKc hjet => ?_⟩
  have hG_nn : 0 ≤ appCcGdiag (E := E) q := appCcGdiag_nonneg (E := E) q
  have hGq_nn : 0 ≤ appCcGdiag (E := E) q * ((q : ℝ) + 1) :=
    mul_nonneg hG_nn (by positivity)
  set Cpk : ℝ := Kc * Real.sqrt (appCcGdiag (E := E) q * ((q : ℝ) + 1)) with hCpk_def
  have hCpk_nn : 0 ≤ Cpk := mul_nonneg hKc (Real.sqrt_nonneg _)
  have hCpksq : Cpk ^ 2 = Kc ^ 2 * (appCcGdiag (E := E) q * ((q : ℝ) + 1)) := by
    rw [hCpk_def, mul_pow, Real.sq_sqrt hGq_nn]
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
          ((iteratedCovGrad (I := I) g₀ 0 2 q
            (appCc (I := I) (M := M) g₀ (2 + m) 2 C
              (iteratedCovGrad (I := I) g₀ 0 2 m T₀))).toSection x) ≤
        Cpk ^ 2 * ∑ i ∈ Finset.range (q + m + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i T₀).toSection x) := by
    intro x
    set Sfull : ℝ := ∑ i ∈ Finset.range (q + m + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 2 i T₀).toSection x) with hSfull_def
    have hshift : ∀ (F : ℕ → ℝ), (∀ i, 0 ≤ F i) →
        (∑ l ∈ Finset.range (q + 1), F (m + l)) ≤ ∑ i ∈ Finset.range (q + m + 1), F i := by
      intro F hF
      have hinj : ∀ l₁ ∈ Finset.range (q + 1), ∀ l₂ ∈ Finset.range (q + 1),
          m + l₁ = m + l₂ → l₁ = l₂ := fun l₁ _ l₂ _ h => by omega
      have himg : (Finset.range (q + 1)).image (fun l => m + l) ⊆
          Finset.range (q + m + 1) := by
        intro i hi
        rw [Finset.mem_image] at hi
        obtain ⟨l, hl, rfl⟩ := hi
        rw [Finset.mem_range] at hl ⊢; omega
      calc (∑ l ∈ Finset.range (q + 1), F (m + l))
          = ∑ i ∈ (Finset.range (q + 1)).image (fun l => m + l), F i :=
            (Finset.sum_image hinj).symm
        _ ≤ ∑ i ∈ Finset.range (q + m + 1), F i :=
            Finset.sum_le_sum_of_subset_of_nonneg himg (fun i _ _ => hF i)
    have hWfull : (∑ l ∈ Finset.range (q + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l
              (iteratedCovGrad (I := I) g₀ 0 2 m T₀)).toSection x)) ≤ Sfull := by
      rw [show (∑ l ∈ Finset.range (q + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
              ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l
                (iteratedCovGrad (I := I) g₀ 0 2 m T₀)).toSection x)) =
          ∑ l ∈ Finset.range (q + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (m + l)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (m + l) T₀).toSection x) from
        Finset.sum_congr rfl (fun l _ =>
          rfns_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 2 m l T₀ x)]
      rw [hSfull_def]
      exact hshift (fun i => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 2 i T₀).toSection x))
        (fun i => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + i) x _)
    have hterm : ∀ i ∈ Finset.range (q + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) (2 + i) x
            ((iteratedCovGrad (I := I) g₀ (2 + m) 2 i C).toSection x) *
          ∑ l ∈ Finset.range (q + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
              ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l
                (iteratedCovGrad (I := I) g₀ 0 2 m T₀)).toSection x) ≤
          Kc ^ 2 * Sfull := by
      intro i hi
      have hi_le : i ≤ q := by rw [Finset.mem_range] at hi; omega
      have hgC := hjet i hi_le x
      have hsub : Finset.range (q + 1 - i) ⊆ Finset.range (q + 1) :=
        Finset.range_mono (by omega)
      have hWi : (∑ l ∈ Finset.range (q + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
              ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l
                (iteratedCovGrad (I := I) g₀ 0 2 m T₀)).toSection x)) ≤
          ∑ l ∈ Finset.range (q + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
              ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l
                (iteratedCovGrad (I := I) g₀ 0 2 m T₀)).toSection x) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun l _ _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 ((2 + m) + l) x _)
      have hWi_nn : 0 ≤ ∑ l ∈ Finset.range (q + 1 - i),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l
              (iteratedCovGrad (I := I) g₀ 0 2 m T₀)).toSection x) :=
        Finset.sum_nonneg (fun l _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 ((2 + m) + l) x _)
      exact mul_le_mul hgC (le_trans hWi hWfull) hWi_nn (sq_nonneg Kc)
    have hmono : (∑ i ∈ Finset.range (q + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) (2 + i) x
              ((iteratedCovGrad (I := I) g₀ (2 + m) 2 i C).toSection x) *
            ∑ l ∈ Finset.range (q + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
                ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l
                  (iteratedCovGrad (I := I) g₀ 0 2 m T₀)).toSection x)) ≤
        ((q : ℝ) + 1) * (Kc ^ 2 * Sfull) := by
      refine le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_)
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    refine le_trans
      (appCc_iteratedCovGrad_diagonalProductGrid_le (I := I) (M := M) g₀ (2 + m) 2 C
        (iteratedCovGrad (I := I) g₀ 0 2 m T₀) q x) ?_
    refine le_trans (mul_le_mul_of_nonneg_left hmono hG_nn) ?_
    rw [hCpksq]
    apply le_of_eq; ring
  have hpack := tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum (I := I) (M := M) g₀
    (q + m + 1) (fun i => 2 + i) (fun i => iteratedCovGrad (I := I) g₀ 0 2 i T₀)
    (iteratedCovGrad (I := I) g₀ 0 2 q
      (appCc (I := I) (M := M) g₀ (2 + m) 2 C (iteratedCovGrad (I := I) g₀ 0 2 m T₀)))
    Cpk hCpk_nn hpt
  refine le_trans hpack ?_
  have hCS : ∑ i ∈ Finset.range (q + m + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ≤
      Real.sqrt ((q + m + 1 : ℕ) : ℝ) *
        Real.sqrt (∑ i ∈ Finset.range (q + m + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) := by
    have hcs0 := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (q + m + 1))
      (fun _ => (1 : ℝ)) (fun i => ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one] at hcs0
    have hsum_nn : 0 ≤ ∑ i ∈ Finset.range (q + m + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    rw [← Real.sqrt_sq hsum_nn,
      show Real.sqrt ((q + m + 1 : ℕ) : ℝ) *
          Real.sqrt (∑ i ∈ Finset.range (q + m + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) =
        Real.sqrt (((q + m + 1 : ℕ) : ℝ) *
          ∑ i ∈ Finset.range (q + m + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) from
        (Real.sqrt_mul (by positivity) _).symm]
    exact Real.sqrt_le_sqrt hcs0
  refine le_trans (mul_le_mul_of_nonneg_left hCS hCpk_nn) ?_
  rw [hCpk_def]
  apply le_of_eq; ring

theorem exists_smoothCcToTensorHs_real_le_of_iteratedCovGrad_jet_window
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (ha : 1 ≤ a)
    (Clow : ℕ → ℝ) (hClow_nn : ∀ q, 0 ≤ Clow q) :
    ∃ Ctame : ℕ → ℝ, (∀ k, 0 ≤ Ctame k) ∧
      ∀ (k : ℕ) (U V : SmoothCcTensor g₀ 0 2),
        (∀ q : ℕ, ‖iteratedCovGrad (I := I) g₀ 0 2 q U‖ ≤
          Clow q * Real.sqrt (∑ i ∈ Finset.range (q + 1 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i V‖ ^ 2)) →
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1) U‖ ≤
          Ctame k * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) V‖ := by
  classical
  set C1 : ℕ → ℝ := fun k =>
    (exists_smoothCcToTensorHs_le_iteratedCovGrad_sum_general (I := I) (M := M) g₀
      (a + k - 1)).choose with hC1_def
  set C2 : ℕ → ℝ := fun k =>
    (exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general (I := I) (M := M) g₀
      (a + k - 1 + 1)).choose with hC2_def
  have hC1_spec : ∀ k, 0 ≤ C1 k ∧ ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + k - 1 : ℕ) : ℝ) S‖ ≤
        C1 k * ∑ j ∈ Finset.range (a + k - 1 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ :=
    fun k => (exists_smoothCcToTensorHs_le_iteratedCovGrad_sum_general (I := I) (M := M) g₀
      (a + k - 1)).choose_spec
  have hC2_spec : ∀ k, 0 ≤ C2 k ∧ ∀ S : SmoothCcTensor g₀ 0 2,
      ∑ j ∈ Finset.range (a + k - 1 + 1 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ ≤
        C2 k * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + k - 1 + 1 : ℕ) : ℝ) S‖ :=
    fun k => (exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general (I := I) (M := M) g₀
      (a + k - 1 + 1)).choose_spec
  refine ⟨fun k => C1 k * (∑ j ∈ Finset.range (a + k - 1 + 1), Clow j) * C2 k,
    fun k => ?_, fun k U V hU => ?_⟩
  · exact mul_nonneg (mul_nonneg (hC1_spec k).1
      (Finset.sum_nonneg (fun j _ => hClow_nn j))) (hC2_spec k).1
  · have hUexp : (a : ℝ) + (k : ℝ) - 1 = ((a + k - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (show 1 ≤ a + k by omega)]; push_cast; ring
    have hVexp : (a : ℝ) + (k : ℝ) = ((a + k - 1 + 1 : ℕ) : ℝ) := by
      rw [show a + k - 1 + 1 = a + k by omega]; push_cast; ring
    rw [hUexp, hVexp]
    set SV : ℝ := ∑ i ∈ Finset.range (a + k - 1 + 1 + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 i V‖ with hSV_def
    have hSV_nn : 0 ≤ SV := Finset.sum_nonneg (fun i _ => norm_nonneg _)
    have hsq_le : ∑ i ∈ Finset.range (a + k - 1 + 1 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 i V‖ ^ 2 ≤ SV ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => norm_nonneg _)
    have hsqrtV_le : Real.sqrt (∑ i ∈ Finset.range (a + k - 1 + 1 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 i V‖ ^ 2) ≤ SV :=
      le_trans (Real.sqrt_le_sqrt hsq_le) (le_of_eq (Real.sqrt_sq hSV_nn))
    have hUj : ∀ j ∈ Finset.range (a + k - 1 + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j U‖ ≤ Clow j * SV := by
      intro j hj
      have hj_le : j ≤ a + k - 1 := by rw [Finset.mem_range] at hj; omega
      refine le_trans (hU j) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hClow_nn j)
      have hsub : Finset.range (j + 1 + 1) ⊆ Finset.range (a + k - 1 + 1 + 1) :=
        Finset.range_mono (by omega)
      have hwin : ∑ i ∈ Finset.range (j + 1 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i V‖ ^ 2 ≤
          ∑ i ∈ Finset.range (a + k - 1 + 1 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i V‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => sq_nonneg _)
      exact le_trans (Real.sqrt_le_sqrt hwin) hsqrtV_le
    have hUsum : ∑ j ∈ Finset.range (a + k - 1 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j U‖ ≤
        (∑ j ∈ Finset.range (a + k - 1 + 1), Clow j) * SV := by
      refine le_trans (Finset.sum_le_sum hUj) ?_
      rw [Finset.sum_mul]
    have hb1 := (hC1_spec k).2 U
    have hb2 := (hC2_spec k).2 V
    have hSV_le : SV ≤ C2 k *
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + k - 1 + 1 : ℕ) : ℝ) V‖ := hb2
    calc ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + k - 1 : ℕ) : ℝ) U‖
        ≤ C1 k * ∑ j ∈ Finset.range (a + k - 1 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j U‖ := hb1
      _ ≤ C1 k * ((∑ j ∈ Finset.range (a + k - 1 + 1), Clow j) * SV) :=
          mul_le_mul_of_nonneg_left hUsum (hC1_spec k).1
      _ ≤ C1 k * ((∑ j ∈ Finset.range (a + k - 1 + 1), Clow j) *
            (C2 k * ‖smoothCcToTensorHs (I := I) (M := M) g₀
              ((a + k - 1 + 1 : ℕ) : ℝ) V‖)) := by
          refine mul_le_mul_of_nonneg_left ?_ (hC1_spec k).1
          exact mul_le_mul_of_nonneg_left hSV_le
            (Finset.sum_nonneg (fun j _ => hClow_nn j))
      _ = C1 k * (∑ j ∈ Finset.range (a + k - 1 + 1), Clow j) * C2 k *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + k - 1 + 1 : ℕ) : ℝ) V‖ := by
          ring

def deTurckArmContractionThreshold' (n : ℕ) : ℝ :=
  1 / (1 + 2 * (deTurckArmFibreConst n + deTurckArmFibreConst n ^ 3))

lemma deTurckArmContractionThreshold'_le {n : ℕ} (hn : 1 ≤ n) :
    deTurckArmContractionThreshold' n ≤ deTurckArmContractionThreshold n := by
  have hC := one_le_deTurckArmFibreConst hn
  unfold deTurckArmContractionThreshold' deTurckArmContractionThreshold
  have hC3 : 0 ≤ deTurckArmFibreConst n ^ 3 := by positivity
  apply one_div_le_one_div_of_le (by linarith)
  linarith

lemma deTurckArmContractionThreshold'_le_third {n : ℕ} (hn : 1 ≤ n) :
    deTurckArmContractionThreshold' n ≤ 1 / 3 :=
  le_trans (deTurckArmContractionThreshold'_le hn)
    (deTurckArmContractionThreshold_le_third hn)

lemma deTurckArmContractionThreshold'_lt_one {n : ℕ} (hn : 1 ≤ n) :
    deTurckArmContractionThreshold' n < 1 :=
  lt_of_le_of_lt (deTurckArmContractionThreshold'_le_third hn)
    (by norm_num : (1 : ℝ) / 3 < 1)

lemma deTurckArmContractionThreshold'_le_third' (n : ℕ) [NeZero n] :
    deTurckArmContractionThreshold' n ≤ 1 / 3 :=
  deTurckArmContractionThreshold'_le_third (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))

lemma deTurckArmContractionThreshold'_lt_one' (n : ℕ) [NeZero n] :
    deTurckArmContractionThreshold' n < 1 :=
  deTurckArmContractionThreshold'_lt_one (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))

lemma deTurckArmFibreConst_cube_mul_div_le {n : ℕ} (hn : 1 ≤ n) {δ : ℝ}
    (hδ_le : δ ≤ deTurckArmContractionThreshold' n) :
    deTurckArmFibreConst n ^ 3 * (δ / (1 - δ)) ≤
      deTurckArmFibreConst n ^ 2 / (2 * (1 + deTurckArmFibreConst n ^ 2)) := by
  have hC := one_le_deTurckArmFibreConst hn
  set C := deTurckArmFibreConst n with hC_def
  set K : ℝ := C + C ^ 3 with hK_def
  have hC3_nn : (0 : ℝ) ≤ C ^ 3 := by positivity
  have hK1 : 1 ≤ K := by rw [hK_def]; linarith
  have hden : (0 : ℝ) < 1 + 2 * K := by linarith
  have hthr_lt : deTurckArmContractionThreshold' n < 1 :=
    deTurckArmContractionThreshold'_lt_one hn
  have hδ_lt1 : δ < 1 := lt_of_le_of_lt hδ_le hthr_lt
  have h1δ_pos : (0 : ℝ) < 1 - δ := by linarith
  have hRHS_pos : (0 : ℝ) <
      C ^ 2 / (2 * (1 + C ^ 2)) := by positivity
  by_cases hδ0 : δ ≤ 0
  · have hratio_np : δ / (1 - δ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hδ0 h1δ_pos.le
    have : C ^ 3 * (δ / (1 - δ)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hratio_np
    linarith
  · have hδ_mul : δ * (1 + 2 * K) ≤ 1 := by
      have := (le_div_iff₀ hden).mp
        (show δ ≤ 1 / (1 + 2 * K) from hδ_le)
      linarith
    have hratio : δ / (1 - δ) ≤ 1 / (2 * K) := by
      rw [div_le_div_iff₀ h1δ_pos (by linarith : (0 : ℝ) < 2 * K)]
      nlinarith
    have hkey : C ^ 3 / (2 * K) = C ^ 2 / (2 * (1 + C ^ 2)) := by
      rw [hK_def]
      have hCpos : (0 : ℝ) < C := by linarith
      rw [div_eq_div_iff (by positivity) (by positivity)]
      ring
    calc C ^ 3 * (δ / (1 - δ)) ≤ C ^ 3 * (1 / (2 * K)) :=
          mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = C ^ 3 / (2 * K) := by ring
      _ = C ^ 2 / (2 * (1 + C ^ 2)) := hkey

lemma deTurckBudget_half_add_lt_one (n : ℕ) :
    (1 / 2 : ℝ) + deTurckArmFibreConst n ^ 2 / (2 * (1 + deTurckArmFibreConst n ^ 2)) < 1 := by
  have hC2 : (0 : ℝ) ≤ deTurckArmFibreConst n ^ 2 := sq_nonneg _
  have hden : (0 : ℝ) < 2 * (1 + deTurckArmFibreConst n ^ 2) := by linarith
  have hlt : deTurckArmFibreConst n ^ 2 / (2 * (1 + deTurckArmFibreConst n ^ 2)) <
      1 / 2 := by
    rw [div_lt_div_iff₀ hden (by norm_num : (0:ℝ) < 2)]
    linarith
  linarith

def deTurckArmContractionThreshold'' (n : ℕ) : ℝ :=
  1 / (1 + 2 * (deTurckArmFibreConst n + 32 * deTurckArmFibreConst n ^ 3))

lemma deTurckArmContractionThreshold''_le {n : ℕ} (hn : 1 ≤ n) :
    deTurckArmContractionThreshold'' n ≤ deTurckArmContractionThreshold n := by
  have hC := one_le_deTurckArmFibreConst hn
  unfold deTurckArmContractionThreshold'' deTurckArmContractionThreshold
  have hC3 : 0 ≤ deTurckArmFibreConst n ^ 3 := by positivity
  apply one_div_le_one_div_of_le (by linarith)
  linarith

lemma deTurckArmContractionThreshold''_le_third {n : ℕ} (hn : 1 ≤ n) :
    deTurckArmContractionThreshold'' n ≤ 1 / 3 :=
  le_trans (deTurckArmContractionThreshold''_le hn)
    (deTurckArmContractionThreshold_le_third hn)

lemma deTurckArmContractionThreshold''_lt_one {n : ℕ} (hn : 1 ≤ n) :
    deTurckArmContractionThreshold'' n < 1 :=
  lt_of_le_of_lt (deTurckArmContractionThreshold''_le_third hn)
    (by norm_num : (1 : ℝ) / 3 < 1)

lemma deTurckArmContractionThreshold''_le_third' (n : ℕ) [NeZero n] :
    deTurckArmContractionThreshold'' n ≤ 1 / 3 :=
  deTurckArmContractionThreshold''_le_third (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))

lemma deTurckArmContractionThreshold''_lt_one' (n : ℕ) [NeZero n] :
    deTurckArmContractionThreshold'' n < 1 :=
  deTurckArmContractionThreshold''_lt_one (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))

lemma deTurckArmFibreConst_cube_mul_div_le_thirtyTwo {n : ℕ} (hn : 1 ≤ n) {δ : ℝ}
    (hδ_le : δ ≤ deTurckArmContractionThreshold'' n) :
    32 * deTurckArmFibreConst n ^ 3 * (δ / (1 - δ)) ≤
      32 * deTurckArmFibreConst n ^ 2 / (2 * (1 + 32 * deTurckArmFibreConst n ^ 2)) := by
  have hC := one_le_deTurckArmFibreConst hn
  set C := deTurckArmFibreConst n with hC_def
  set K : ℝ := C + 32 * C ^ 3 with hK_def
  have hC3_nn : (0 : ℝ) ≤ C ^ 3 := by positivity
  have hK1 : 1 ≤ K := by rw [hK_def]; nlinarith
  have hden : (0 : ℝ) < 1 + 2 * K := by linarith
  have hthr_lt : deTurckArmContractionThreshold'' n < 1 :=
    deTurckArmContractionThreshold''_lt_one hn
  have hδ_lt1 : δ < 1 := lt_of_le_of_lt hδ_le hthr_lt
  have h1δ_pos : (0 : ℝ) < 1 - δ := by linarith
  by_cases hδ0 : δ ≤ 0
  · have hratio_np : δ / (1 - δ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hδ0 h1δ_pos.le
    have hL : 32 * C ^ 3 * (δ / (1 - δ)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hratio_np
    have hR : (0 : ℝ) ≤ 32 * C ^ 2 / (2 * (1 + 32 * C ^ 2)) := by positivity
    linarith
  · have hδ_mul : δ * (1 + 2 * K) ≤ 1 := by
      have := (le_div_iff₀ hden).mp
        (show δ ≤ 1 / (1 + 2 * K) from hδ_le)
      linarith
    have hratio : δ / (1 - δ) ≤ 1 / (2 * K) := by
      rw [div_le_div_iff₀ h1δ_pos (by linarith : (0 : ℝ) < 2 * K)]
      nlinarith
    have hkey : 32 * C ^ 3 / (2 * K) = 32 * C ^ 2 / (2 * (1 + 32 * C ^ 2)) := by
      rw [hK_def]
      have hCpos : (0 : ℝ) < C := by linarith
      rw [div_eq_div_iff (by positivity) (by positivity)]
      ring
    calc 32 * C ^ 3 * (δ / (1 - δ)) ≤ 32 * C ^ 3 * (1 / (2 * K)) :=
          mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = 32 * C ^ 3 / (2 * K) := by ring
      _ = 32 * C ^ 2 / (2 * (1 + 32 * C ^ 2)) := hkey

lemma deTurckBudget_half_add_thirtyTwo_lt_one (n : ℕ) :
    (1 / 2 : ℝ) + 32 * deTurckArmFibreConst n ^ 2 /
        (2 * (1 + 32 * deTurckArmFibreConst n ^ 2)) < 1 := by
  have hC2 : (0 : ℝ) ≤ 32 * deTurckArmFibreConst n ^ 2 := by positivity
  have hden : (0 : ℝ) < 2 * (1 + 32 * deTurckArmFibreConst n ^ 2) := by linarith
  have hlt : 32 * deTurckArmFibreConst n ^ 2 /
      (2 * (1 + 32 * deTurckArmFibreConst n ^ 2)) < 1 / 2 := by
    rw [div_lt_div_iff₀ hden (by norm_num : (0:ℝ) < 2)]
    linarith
  linarith

section

open Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
private lemma kscr_g1_inner_injective (g₁ : SmoothRiemannianMetric I M) (x : M)
    {a b : TangentSpace I x} (hab : ∀ u : TangentSpace I x, g₁.inner x a u = g₁.inner x b u) :
    a = b := by
  by_contra hne
  have hsub : a - b ≠ 0 := sub_ne_zero.mpr hne
  have hpos := g₁.pos x (a - b) hsub
  have hzero : g₁.inner x (a - b) (a - b) = 0 := by
    have hsplit : g₁.inner x (a - b) (a - b)
        = g₁.inner x (a - b) a - g₁.inner x (a - b) b := by rw [← map_sub]
    rw [hsplit, g₁.symm x (a - b) a, g₁.symm x (a - b) b, hab (a - b)]
    ring
  exact absurd hzero (ne_of_gt hpos)

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
private lemma kscr_cometricLmodel_covectorOfCLM_inner_loc
    (g₁ : SmoothRiemannianMetric I M) (y : M)
    (φ : E →L[ℝ] ℝ) (u : TangentSpace I y) :
    g₁.inner y (cometricLmodel (I := I) g₁ y
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) φ)) u = φ (u : E) := by
  have h1 : cometricLmodel (I := I) g₁ y
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) φ) =
      inverseMetricSharpFib (I := I) g₁ y
        ((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 1 y).symm
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) φ)) := rfl
  rw [h1, inverseMetricSharpFib_inner (I := I) g₁ y _ u, cotangentToDualLinear_apply,
    cotangentToDual_apply]
  change (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) φ)
      (fun _ : Fin 1 => (u : E)) = φ (u : E)
  rw [Tensor0SBundle.model_covectorOfCLM_apply]

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
private lemma kscr_cometricLmodel_covOf_g0flat_eq (g₀ : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    cometricLmodel (I := I) g₀ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((g₀.inner x v).toLinearMap.toContinuousLinearMap)) = v := by
  apply kscr_g1_inner_injective (I := I) g₀ x
  intro u
  rw [kscr_cometricLmodel_covectorOfCLM_inner_loc (I := I) g₀ x
    ((g₀.inner x v).toLinearMap.toContinuousLinearMap) u]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
private lemma kscr_flatRecon_eq_basisVec (g₀ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (b : Fin n) :
    ∑ k : Fin (Module.finrank ℝ E),
        (g₀.inner x (e b) ((Module.finBasis ℝ E) k) : ℝ) •
          cometricLmodel (I := I) g₀ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)) = e b := by
  classical
  have hsmul : ∀ k : Fin (Module.finrank ℝ E),
      (g₀.inner x (e b) ((Module.finBasis ℝ E) k) : ℝ) •
          cometricLmodel (I := I) g₀ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k))
        = cometricLmodel (I := I) g₀ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((g₀.inner x (e b) ((Module.finBasis ℝ E) k) : ℝ) •
                ((Module.finBasis ℝ E).cDualBasis k))) := by
    intro k
    rw [map_smul, map_smul]
  rw [Finset.sum_congr rfl (fun k _ => hsmul k)]
  rw [← map_sum, ← map_sum]
  have hcoe : ∀ k : Fin (Module.finrank ℝ E),
      ((Module.finBasis ℝ E).cDualBasis k)
        = LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord k) := by
    intro k
    rw [Module.Basis.cDualBasis, Module.Basis.map_apply]
    congr 1
    exact congrFun (Module.Basis.coe_dualBasis (Module.finBasis ℝ E)) k
  have hsum : (∑ k : Fin (Module.finrank ℝ E),
        (g₀.inner x (e b) ((Module.finBasis ℝ E) k) : ℝ) •
          ((Module.finBasis ℝ E).cDualBasis k))
      = (g₀.inner x (e b)).toLinearMap.toContinuousLinearMap := by
    have hrepr := cdual_sum_repr (Module.finBasis ℝ E)
      ((g₀.inner x (e b)).toLinearMap.toContinuousLinearMap)
    refine Eq.trans ?_ hrepr
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hcoe k]
    congr 1
  rw [hsum]
  exact kscr_cometricLmodel_covOf_g0flat_eq (I := I) g₀ x (e b)

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
private lemma kscr_deTurckCoeff_toModel_eq (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (w : Tensor0SSpace 4 I x) (m : Fin 2 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
          (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁).toSection x) w) m =
      ∑ k : Fin (Module.finrank ℝ E),
        (Tensor0SSpace.toModel w)
          (Fin.cons
            ((gInvDiffRaisedEndo (I := I) g₀ g₁ x
              (cometricLmodel (I := I) g₀ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))) : TangentSpace I x) : E)
            (Fin.cons (((Module.finBasis ℝ E) k : E)) m)) := by
  classical
  rw [deTurckPrincipalCometricCoeff_toSection_clm_eq (I := I) (M := M) g₀ g₁ x,
    ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub,
    ContinuousMultilinearMap.sub_apply,
    cometricDoubleTraceFib_toModel, cometricDoubleTraceFib_toModel,
    modelDoubleTrace_apply, modelDoubleTrace_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  set wm : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ := Tensor0SSpace.toModel w with hwm
  set tail : Fin 3 → E := Fin.cons (((Module.finBasis ℝ E) k : E)) m with htail
  have hcurry : ∀ z : TangentSpace I x,
      wm (Fin.cons ((z : E)) tail)
        = ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 4 => E) ℝ) wm
            ((z : TangentSpace I x) : E)) tail := by
    intro z; rw [continuousMultilinearCurryLeftEquiv_apply]
  rw [hcurry (cometricLmodel (I := I) g₁ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k))),
    hcurry (cometricLmodel (I := I) g₀ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k))),
    hcurry (gInvDiffRaisedEndo (I := I) g₀ g₁ x
        (cometricLmodel (I := I) g₀ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k))))]
  rw [← ContinuousMultilinearMap.sub_apply, ← map_sub]
  congr 2
  rw [cometricLmodel_sub_eq_gInvDiffRaisedEndo (I := I) g₀ g₁ x
    ((Module.finBasis ℝ E).cDualBasis k)]

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
private lemma kscr_deTurckCoeff_component_eq (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g₀.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (K : Fin 4 → Fin n) (J : Fin 2 → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
        (show TensorRSSpace 4 2 I x from
          (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁).toSection x) n e K J =
      g₀.inner x (e (K 0)) (gInvDiffRaisedEndo (I := I) g₀ g₁ x (e (K 1))) *
        ((if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0)) := by
  classical
  have hcomp : fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
        (show TensorRSSpace 4 2 I x from
          (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁).toSection x) n e K J =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
          (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁).toSection x)
          (coframeS (I := I) (M := M) g₀ x 4 e K))
        (fun k => ((e (J k) : TangentSpace I x) : E)) := rfl
  rw [hcomp, kscr_deTurckCoeff_toModel_eq (I := I) (M := M) g₀ g₁ x
    (coframeS (I := I) (M := M) g₀ x 4 e K) (fun k => ((e (J k) : TangentSpace I x) : E))]
  set Rk : Fin (Module.finrank ℝ E) → TangentSpace I x := fun k =>
    cometricLmodel (I := I) g₀ x
      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
        ((Module.finBasis ℝ E).cDualBasis k)) with hRk
  set Λ : TangentSpace I x →L[ℝ] TangentSpace I x :=
    gInvDiffRaisedEndo (I := I) g₀ g₁ x with hΛ
  have hk : ∀ k : Fin (Module.finrank ℝ E),
      (Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 4 e K))
          (Fin.cons ((Λ (Rk k) : TangentSpace I x) : E)
            (Fin.cons (((Module.finBasis ℝ E) k : E))
              (fun j => ((e (J j) : TangentSpace I x) : E))))
        = g₀.inner x (e (K 0)) (Λ (Rk k))
          * g₀.inner x (e (K 1)) ((Module.finBasis ℝ E) k)
          * ((if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0)) := by
    intro k
    have hcf : (Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 4 e K))
          (Fin.cons ((Λ (Rk k) : TangentSpace I x) : E)
            (Fin.cons (((Module.finBasis ℝ E) k : E))
              (fun j => ((e (J j) : TangentSpace I x) : E))))
        = coframeS (I := I) (M := M) g₀ x 4 e K
            (Fin.cons ((Λ (Rk k)) : TangentSpace I x)
              (Fin.cons (((Module.finBasis ℝ E) k : TangentSpace I x))
                (fun j => (e (J j) : TangentSpace I x)))) := rfl
    rw [hcf, coframeS_apply, Fin.prod_univ_four]
    change g₀.inner x (e (K 0)) (Λ (Rk k))
          * g₀.inner x (e (K 1)) ((Module.finBasis ℝ E) k)
          * g₀.inner x (e (K 2)) (e (J 0))
          * g₀.inner x (e (K 3)) (e (J 1))
        = _
    rw [horth (K 2) (J 0), horth (K 3) (J 1)]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hk k)]
  rw [← Finset.sum_mul]
  congr 1
  have hpull : g₀.inner x (e (K 0)) (Λ
          (∑ k : Fin (Module.finrank ℝ E),
            (g₀.inner x (e (K 1)) ((Module.finBasis ℝ E) k) : ℝ) • Rk k))
      = ∑ k : Fin (Module.finrank ℝ E),
          g₀.inner x (e (K 0)) (Λ (Rk k)) * g₀.inner x (e (K 1)) ((Module.finBasis ℝ E) k) := by
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_smul, ContinuousLinearMap.map_smul, smul_eq_mul]
    ring
  rw [← hpull, kscr_flatRecon_eq_basisVec (I := I) g₀ x e (K 1)]

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
private lemma kscr_sum_pi_fin_succ {n : ℕ} {β : Type*} [AddCommMonoid β]
    {N : ℕ} (g : (Fin (N + 1) → Fin n) → β) :
    (∑ p : Fin (N + 1) → Fin n, g p)
      = ∑ a : Fin n, ∑ q : Fin N → Fin n, g (Fin.cons a q) := by
  classical
  rw [← (Fin.consEquiv (fun _ : Fin (N + 1) => Fin n)).sum_comp g]
  rw [Fintype.sum_prod_type]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
private lemma kscr_deTurckCoeff_componentSqSum_eq (n : ℕ) (f : Fin n → Fin n → ℝ) :
    (∑ K : Fin 4 → Fin n, ∑ J : Fin 2 → Fin n,
      (f (K 0) (K 1) *
        ((if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0))) ^ 2)
      = (n : ℝ) ^ 2 * ∑ a : Fin n, ∑ b : Fin n, (f a b) ^ 2 := by
  classical
  have hJcollapse : ∀ K : Fin 4 → Fin n,
      (∑ J : Fin 2 → Fin n,
        (f (K 0) (K 1) *
          ((if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0))) ^ 2)
        = (f (K 0) (K 1)) ^ 2 := by
    intro K
    have hsplit : ∀ J : Fin 2 → Fin n,
        (f (K 0) (K 1) *
          ((if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0))) ^ 2
          = (f (K 0) (K 1)) ^ 2 *
              ((if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0)) := by
      intro J
      by_cases h2 : K 2 = J 0 <;> by_cases h3 : K 3 = J 1 <;>
        simp [h2, h3]
    rw [Finset.sum_congr rfl (fun J _ => hsplit J), ← Finset.mul_sum]
    rw [kscr_sum_pi_fin_succ (fun J : Fin 2 → Fin n =>
      (if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0))]
    have hinner : ∀ a : Fin n, (∑ q : Fin 1 → Fin n,
        (if K 2 = (Fin.cons a q : Fin 2 → Fin n) 0 then (1 : ℝ) else 0) *
          (if K 3 = (Fin.cons a q : Fin 2 → Fin n) 1 then (1 : ℝ) else 0))
        = (if K 2 = a then (1 : ℝ) else 0) := by
      intro a
      rw [kscr_sum_pi_fin_succ (fun q : Fin 1 → Fin n =>
        (if K 2 = (Fin.cons a q : Fin 2 → Fin n) 0 then (1 : ℝ) else 0) *
          (if K 3 = (Fin.cons a q : Fin 2 → Fin n) 1 then (1 : ℝ) else 0))]
      have hb : ∀ b : Fin n, (∑ _r : Fin 0 → Fin n,
          (if K 2 = (Fin.cons a (Fin.cons b (_r : Fin 0 → Fin n)) : Fin 2 → Fin n) 0
            then (1 : ℝ) else 0) *
            (if K 3 = (Fin.cons a (Fin.cons b (_r : Fin 0 → Fin n)) : Fin 2 → Fin n) 1
              then (1 : ℝ) else 0))
          = (if K 2 = a then (1 : ℝ) else 0) * (if K 3 = b then (1 : ℝ) else 0) := by
        intro b
        have hbody : ∀ r : Fin 0 → Fin n,
            (if K 2 = (Fin.cons a (Fin.cons b r) : Fin 2 → Fin n) 0 then (1 : ℝ) else 0) *
              (if K 3 = (Fin.cons a (Fin.cons b r) : Fin 2 → Fin n) 1 then (1 : ℝ) else 0)
            = (if K 2 = a then (1 : ℝ) else 0) * (if K 3 = b then (1 : ℝ) else 0) := by
          intro r
          rw [show (Fin.cons a (Fin.cons b r) : Fin 2 → Fin n) 0 = a from rfl,
            show (Fin.cons a (Fin.cons b r) : Fin 2 → Fin n) 1 = b from rfl]
        rw [Finset.sum_congr rfl (fun r _ => hbody r), Finset.sum_const, Finset.card_univ]
        simp only [Fintype.card_fun, Fintype.card_fin, pow_zero, one_smul]
      rw [Finset.sum_congr rfl (fun b _ => hb b), ← Finset.mul_sum]
      rw [Finset.sum_ite_eq Finset.univ (K 3) (fun _ => (1 : ℝ))]
      simp
    rw [Finset.sum_congr rfl (fun a _ => hinner a)]
    rw [Finset.sum_ite_eq Finset.univ (K 2) (fun _ => (1 : ℝ))]
    simp
  rw [Finset.sum_congr rfl (fun K _ => hJcollapse K)]
  rw [kscr_sum_pi_fin_succ (fun K : Fin 4 → Fin n => (f (K 0) (K 1)) ^ 2)]
  have hstep : ∀ a : Fin n, (∑ q : Fin 3 → Fin n,
      (f ((Fin.cons a q : Fin 4 → Fin n) 0) ((Fin.cons a q : Fin 4 → Fin n) 1)) ^ 2)
      = (n : ℝ) ^ 2 * ∑ b : Fin n, (f a b) ^ 2 := by
    intro a
    rw [kscr_sum_pi_fin_succ (fun q : Fin 3 → Fin n =>
      (f ((Fin.cons a q : Fin 4 → Fin n) 0) ((Fin.cons a q : Fin 4 → Fin n) 1)) ^ 2)]
    have hb : ∀ b : Fin n, (∑ r : Fin 2 → Fin n,
        (f ((Fin.cons a (Fin.cons b r) : Fin 4 → Fin n) 0)
          ((Fin.cons a (Fin.cons b r) : Fin 4 → Fin n) 1)) ^ 2)
        = (n : ℝ) ^ 2 * (f a b) ^ 2 := by
      intro b
      have hval : ∀ r : Fin 2 → Fin n,
          (f ((Fin.cons a (Fin.cons b r) : Fin 4 → Fin n) 0)
            ((Fin.cons a (Fin.cons b r) : Fin 4 → Fin n) 1)) ^ 2 = (f a b) ^ 2 := by
        intro r
        rw [show (Fin.cons a (Fin.cons b r) : Fin 4 → Fin n) 0 = a from rfl,
          show (Fin.cons a (Fin.cons b r) : Fin 4 → Fin n) 1 = b from rfl]
      rw [Finset.sum_congr rfl (fun r _ => hval r), Finset.sum_const, Finset.card_univ]
      simp only [Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
    rw [Finset.sum_congr rfl (fun b _ => hb b), ← Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun a _ => hstep a), ← Finset.mul_sum]

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
/-- Sharp deviation Parseval: the fibre norm of the difference of two principal
cometric coefficients over the same base, bounded by the resolvent-factorized rate. -/
private lemma kscr_rfns_pcc_deviation_le (g₀ ga gb : SmoothRiemannianMetric I M)
    (ha hb : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie_a : ∀ (y : M) (v w : TangentSpace I y),
      ga.inner y v w = g₀.inner y v w + ha y v w)
    (htie_b : ∀ (y : M) (v w : TangentSpace I y),
      gb.inner y v w = g₀.inner y v w + hb y v w)
    {δa δb δab : ℝ} (hδa_lt : δa < 1)
    (hδa : gFibreOpBound (I := I) (M := M) g₀ ha δa)
    (hδb_lt : δb < 1) (hδb_nn : 0 ≤ δb)
    (hδb : gFibreOpBound (I := I) (M := M) g₀ hb δb)
    (hδab_nn : 0 ≤ δab)
    (hδab : gFibreOpBound (I := I) (M := M) g₀ (fun y => ha y - hb y) δab)
    (hδa_nn : 0 ≤ δa)
    (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        ((deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ ga
          - deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ gb).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 3 * (δab / ((1 - δa) * (1 - δb))) ^ 2 := by
  classical
  set Λ : TangentSpace I x →L[ℝ] TangentSpace I x :=
    gInvDiffRaisedEndo (I := I) g₀ ga x - gInvDiffRaisedEndo (I := I) g₀ gb x with hΛ
  obtain ⟨n, e, hn, horth, hpar, hrepr⟩ :=
    exists_orthonormal_frame_riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
  have hnE : (n : ℝ) = (Module.finrank ℝ E : ℝ) := by rw [hn]; rfl
  have hsec : (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ ga
        - deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ gb).toSection x =
      (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ ga).toSection x
        - (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ gb).toSection x := by
    rw [SmoothCcTensor.toSection_sub]; rfl
  rw [hsec]
  rw [riemannianFiberNormSq_eq_sum_componentRS_sq (I := I) (M := M) g₀ x 4 2 e hrepr
    (show TensorRSSpace 4 2 I x from
      (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ ga).toSection x
        - (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ gb).toSection x)]
  have hcompsub : ∀ (K : Fin 4 → Fin n) (J : Fin 2 → Fin n),
      fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
          (show TensorRSSpace 4 2 I x from
            (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ ga).toSection x
              - (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ gb).toSection x) n e K J =
        fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
          (show TensorRSSpace 4 2 I x from
            (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ ga).toSection x) n e K J
        - fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
          (show TensorRSSpace 4 2 I x from
            (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ gb).toSection x) n e K J := by
    intro K J
    rw [show ((deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ ga).toSection x
          - (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ gb).toSection x :
            TensorRSSpace 4 2 I x)
        = (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ ga).toSection x
          + (-1 : ℝ) • (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ gb).toSection x from
      by rw [neg_one_smul]; exact sub_eq_add_neg _ _]
    rw [fiberNormSqComponent_add, fiberNormSqComponent_smul]
    ring
  have hcompsq : ∀ (K : Fin 4 → Fin n) (J : Fin 2 → Fin n),
      (fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
          (show TensorRSSpace 4 2 I x from
            (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ ga).toSection x
              - (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ gb).toSection x)
          n e K J) ^ 2
        = (g₀.inner x (e (K 0)) (Λ (e (K 1))) *
            ((if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0))) ^ 2 := by
    intro K J
    rw [hcompsub K J, kscr_deTurckCoeff_component_eq (I := I) (M := M) g₀ ga x e horth K J,
      kscr_deTurckCoeff_component_eq (I := I) (M := M) g₀ gb x e horth K J, hΛ,
      ContinuousLinearMap.sub_apply, map_sub]
    ring
  rw [Finset.sum_congr rfl (fun K _ => Finset.sum_congr rfl (fun J _ => hcompsq K J))]
  rw [kscr_deTurckCoeff_componentSqSum_eq n (fun a b => g₀.inner x (e a) (Λ (e b)))]
  have h1δa : (0 : ℝ) < 1 - δa := by linarith
  have h1δb : (0 : ℝ) < 1 - δb := by linarith
  have hr_nn : (0 : ℝ) ≤ δab / ((1 - δa) * (1 - δb)) :=
    div_nonneg hδab_nn (le_of_lt (mul_pos h1δa h1δb))
  set r : ℝ := δab / ((1 - δa) * (1 - δb)) with hr
  have hper : ∀ b : Fin n, g₀.inner x (Λ (e b)) (Λ (e b)) ≤ r ^ 2 := by
    intro b
    have hsqrt := DifferentialGeometry.Analysis.Sobolev.TensorHilbert.sqrt_inner_gInvDiffRaisedEndo_sub_le
      (I := I) (M := M) g₀ ga gb ha hb htie_a htie_b hδa_lt hδa hδb_lt hδb_nn hδb
      hδab_nn hδab x (e b)
    have hΛb : Λ (e b) = gInvDiffRaisedEndo (I := I) g₀ ga x (e b)
        - gInvDiffRaisedEndo (I := I) g₀ gb x (e b) := by
      rw [hΛ, ContinuousLinearMap.sub_apply]
    rw [← hΛb, ← hr] at hsqrt
    have he1 : g₀.inner x (e b) (e b) = 1 := by rw [horth b b]; simp
    rw [he1, Real.sqrt_one, mul_one] at hsqrt
    have hLnn : 0 ≤ g₀.inner x (Λ (e b)) (Λ (e b)) :=
      DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg (I := I) (M := M)
        g₀ x (Λ (e b))
    have hsq := Real.sq_sqrt hLnn
    nlinarith [Real.sqrt_nonneg (g₀.inner x (Λ (e b)) (Λ (e b))), hsqrt, hsq, hr_nn]
  have hParseval : ∀ b : Fin n,
      (∑ a : Fin n, (g₀.inner x (e a) (Λ (e b))) ^ 2) = g₀.inner x (Λ (e b)) (Λ (e b)) := by
    intro b
    have hpb := hpar (Λ (e b))
    refine hpb ▸ ?_
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [g₀.symm x (e a) (Λ (e b))]
  have hAB : (∑ a : Fin n, ∑ b : Fin n, (g₀.inner x (e a) (Λ (e b))) ^ 2)
      ≤ (n : ℝ) * r ^ 2 := by
    rw [Finset.sum_comm]
    calc (∑ b : Fin n, ∑ a : Fin n, (g₀.inner x (e a) (Λ (e b))) ^ 2)
        = ∑ b : Fin n, g₀.inner x (Λ (e b)) (Λ (e b)) :=
          Finset.sum_congr rfl (fun b _ => hParseval b)
      _ ≤ ∑ _b : Fin n, r ^ 2 := Finset.sum_le_sum (fun b _ => hper b)
      _ = (n : ℝ) * r ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  calc (n : ℝ) ^ 2 * ∑ a : Fin n, ∑ b : Fin n, (g₀.inner x (e a) (Λ (e b))) ^ 2
      ≤ (n : ℝ) ^ 2 * ((n : ℝ) * r ^ 2) := mul_le_mul_of_nonneg_left hAB hn_nn
    _ = (Module.finrank ℝ E : ℝ) ^ 3 * r ^ 2 := by rw [← hnE]; ring

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
private lemma kscr_combinedTrace42Model_apply_symbolic
    (L : Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E)
    (D : Tensor0SBundle.Tensor0SModel 4 ℝ E) (m : Fin 2 → E) :
    combinedTrace42Model (E := E) L D m =
      (1 / 2 : ℝ) *
        (modelDoubleTrace (E := E) 2 L
            (ContinuousMultilinearMap.domDomCongr koszulSlotPerm D) m
          + modelDoubleTrace (E := E) 2 L (ContinuousMultilinearMap.domDomCongr koszulSlotPerm D)
              (fun j : Fin 2 => m ((Equiv.swap (0 : Fin 2) 1) j))
          - modelDoubleTrace (E := E) 2 L D m) := by
  rw [combinedTrace42Model, ContinuousLinearMap.smul_apply,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  congr 1

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
private lemma kscr_ricciArmPrincipalCoeff_sub_add_self_eq_reindexSum
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
          - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)
        + (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
          - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀) =
      reindexCoeffGen (I := I) (M := M) g₀ 4 2
          (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁) koszulSlotPerm
        + reindexCoeffGen (I := I) (M := M) g₀ 4 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 4 2 (Equiv.swap (0 : Fin 2) 1)
              (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)) koszulSlotPerm
        - deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁ := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  refine tensorRSSpace_ext 4 2 x (fun w => ?_)
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  beta_reduce
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply,
    ricciArmPrincipalCoeff_toSection, ricciArmPrincipalCoeff_toSection,
    ricciArmPrincipalCoeffFib_toModel, ricciArmPrincipalCoeffFib_toModel,
    kscr_combinedTrace42Model_apply_symbolic, kscr_combinedTrace42Model_apply_symbolic]
  rw [SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_add, ContMDiffSection.coe_sub,
    ContMDiffSection.coe_add, Pi.sub_apply, Pi.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_sub, Tensor0SSpace.toModel_add,
    ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.add_apply]
  simp only [reindexCoeffGen_toSection, reindexCoeffFibGen_apply, rsDomDomCongrSection_toSection,
    toModel_rsDomDomCongr_apply, deTurckPrincipalCometricCoeff_toSection_clm_eq,
    cometricDoubleTraceFib_toModel,
    Tensor0SSpace.toModel_ofModel, Tensor0SSpace.toModel_sub, ContinuousLinearMap.sub_apply,
    ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.sub_apply]
  ring

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
private lemma kscr_traceHessianCoeff_sub_eq_reindex_pcc
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    traceHessianCoeff (I := I) (M := M) g₀ g₁ - traceHessianCoeff (I := I) (M := M) g₀ g₀ =
      reindexCoeffGen (I := I) (M := M) g₀ 4 2
        (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁) traceHessianSlotPerm := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    traceHessianCoeff_toSection, traceHessianCoeff_toSection, reindexCoeffGen_toSection]
  apply ContinuousLinearMap.ext
  intro D
  rw [ContinuousLinearMap.sub_apply, reindexCoeffFibGen_apply,
    deTurckPrincipalCometricCoeff_toSection_clm_eq, ContinuousLinearMap.sub_apply,
    traceHessianFib, traceHessianFib, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, domDomCongrFib_apply]

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
private theorem kscr_reindexCoeffGen_sub (g₀ : SmoothRiemannianMetric I M)
    (A B : SmoothCcTensor g₀ 4 2) (ρ : Equiv.Perm (Fin 4)) :
    reindexCoeffGen (I := I) (M := M) g₀ 4 2 (A - B) ρ =
      reindexCoeffGen (I := I) (M := M) g₀ 4 2 A ρ -
        reindexCoeffGen (I := I) (M := M) g₀ 4 2 B ρ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    reindexCoeffGen_toSection, reindexCoeffGen_toSection, reindexCoeffGen_toSection,
    SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  apply ContinuousLinearMap.ext
  intro D
  rw [ContinuousLinearMap.sub_apply, reindexCoeffFibGen_apply, reindexCoeffFibGen_apply,
    reindexCoeffFibGen_apply, ContinuousLinearMap.sub_apply]



set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
private theorem kscr_jointTotalSpaceRS_sub {r s : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (B p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p - B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
    (fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hB p₀ hp₀)
  refine (hA'.2.sub hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_sub (A p) (B p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_sub
      (A p₀) (B p₀)

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
private theorem kscr_jointTotalSpaceRS_add {r s : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (B p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p + B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
    (fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hB p₀ hp₀)
  refine (hA'.2.add hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_add (A p) (B p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_add
      (A p₀) (B p₀)

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
private lemma kscr_phiMet_realizedFam_eq_lieSubLich
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) :
    deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg (realizedFam (I := I) g₀ T T' hδ hδ' s) =
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieArm2PrincipalCoeff
          (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
        - (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s
            + linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s) := by
  rw [deTurckPhiMetTotal, linearizedRicciArm2FieldLichnerowicz]
  set X : SmoothCcTensor g₀ 4 2 :=
    ricciArmPrincipalCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) with hX
  set Y : SmoothCcTensor g₀ 4 2 :=
    traceHessianCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) with hY
  have hhalf : (1 / 2 : ℝ) • Y + (1 / 2 : ℝ) • Y = Y := by
    rw [← add_smul]
    norm_num
  have hgrp : (X - (1 / 2 : ℝ) • Y) + (X - (1 / 2 : ℝ) • Y) =
      (X + X) - ((1 / 2 : ℝ) • Y + (1 / 2 : ℝ) • Y) := by abel
  rw [hgrp, hhalf]
  abel

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
private theorem kscr_phiMet_realizedFam_jointSmooth
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4
      (fun s => deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
        (realizedFam (I := I) g₀ T T' hδ hδ' s)) (δ := δ) (δ' := δ') := by
  have hLie :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieArm2PrincipalCoeff_realizedFam_jointSmooth
      (I := I) g₀ T T' hδ hδ' g_bg
  have hLich := linearizedRicci_arm2FieldLichnerowicz_jointSmooth (I := I) g₀ T T' hδ hδ'
  have hadd := kscr_jointTotalSpaceRS_add (I := I) (r := 4) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ =>
      (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' p.2).toSection p.1)
    (fun p : M × ℝ =>
      (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' p.2).toSection p.1)
    hLich hLich
  have hsub := kscr_jointTotalSpaceRS_sub (I := I) (r := 4) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ =>
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieArm2PrincipalCoeff
        (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg).toSection p.1)
    (fun p : M × ℝ =>
      (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' p.2).toSection p.1
        + (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' p.2).toSection p.1)
    hLie hadd
  refine hsub.congr (fun p _ => ?_)
  beta_reduce
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1 t) ?_
  rw [kscr_phiMet_realizedFam_eq_lieSubLich (I := I) (M := M) g₀ g_bg T T' hδ hδ' p.2,
    SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]

set_option maxHeartbeats 25600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
theorem exists_deTurckPhiTotPathIntegral_sub_background_sub_principalCometricCoeff_fibreSup_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ εCD : ℝ, 0 ≤ εCD ∧
      (0 ≤ δ → εCD ≤ 3 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2),
        (∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T₀ x v w = ccTensorBilin (I := I) g₀ T₀ x w v) →
        ∀ (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) 2 x
            ((deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
                  (0 : SmoothCcTensor g₀ 0 2)
                  (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
                  (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                  (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                    (by
                      rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                          from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                        tensorHs_norm_smul]
                      simpa using hR₀)) -
                deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀ -
                deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
                  (tensorSectionRealizeMetric (I := I) g₀ T₀
                    (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                    (hδ_fibre T₀ hball))).toSection x) ≤ εCD ^ 2 := by
  classical
  have hfC_nn : (0 : ℝ) ≤ deTurckArmFibreConst (Module.finrank ℝ E) :=
    deTurckArmFibreConst_nonneg _
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  have h1δ : (0 : ℝ) < 1 - δ := by linarith
  rcases isEmpty_or_nonempty M with hM | hM
  · refine ⟨0, le_refl 0, fun hδ0' => ?_, fun T₀ hTsymm hball x => (hM.false x).elim⟩
    have hκ_nn : (0 : ℝ) ≤ δ / (1 - δ) := div_nonneg hδ0' (le_of_lt h1δ)
    positivity
  · have hδ0 : 0 ≤ δ :=
      delta_nonneg_of_ball_gFibreOpBound (I := I) (M := M) g₀ a hR₀ hδ_fibre
    have hκ_nn : (0 : ℝ) ≤ δ / (1 - δ) := div_nonneg hδ0 (le_of_lt h1δ)
    refine ⟨(11 / 4 : ℝ) * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)),
      mul_nonneg (mul_nonneg (by norm_num) hfC_nn) hκ_nn,
      fun _ => by nlinarith [mul_nonneg hfC_nn hκ_nn], ?_⟩
    intro T₀ hTsymm hball x
    set fC : ℝ := deTurckArmFibreConst (Module.finrank ℝ E) with hfC_def
    have hfC_sqrt : fC = Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 3) := rfl
    set κ : ℝ := δ / (1 - δ) with hκ_def
    have hδT := hδ_fibre T₀ hball
    have hδZ := hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
      (by
        rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
            from (zero_smul _ _).symm, smoothCcToTensorHs_smul, tensorHs_norm_smul]
        simpa using hR₀)
    set g₁ : SmoothRiemannianMetric I M := tensorSectionRealizeMetric (I := I) g₀ T₀
      (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball) with hg₁_def
    set P : SmoothCcTensor g₀ 4 2 := deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
      (0 : SmoothCcTensor g₀ 0 2)
      (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
      (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
      (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
        (by
          rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
              from (zero_smul _ _).symm, smoothCcToTensorHs_smul, tensorHs_norm_smul]
          simpa using hR₀)) with hP_def
    set C1 : SmoothCcTensor g₀ 4 2 := deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀
      with hC1_def
    set Δ1 : SmoothCcTensor g₀ 4 2 := deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁
      with hΔ1_def
    set Φ : ℝ → SmoothCcTensor g₀ 4 2 := fun s =>
      deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
        (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ s) with hΦ_def
    have hjoint : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4 Φ
        (δ := δ) (δ' := δ) :=
      kscr_phiMet_realizedFam_jointSmooth (I := I) (M := M) g₀ g_bg T₀
        (0 : SmoothCcTensor g₀ 0 2) hδT hδZ
    have hSIu : Set.uIcc (0 : ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ) := by
      rw [Set.uIcc_of_le zero_le_one]
      exact Icc_subset_realizedSmallSet hδ_lt hδ_lt
    have hIccS : Set.Icc (0 : ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ) :=
      Icc_subset_realizedSmallSet hδ_lt hδ_lt
    have hjointC : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1
          ((Φ p.2).toSection p.1))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) := by
      have h := hjoint
      rw [linearizedRicciThreeArmHjoint] at h
      exact h
    have hslice : ContinuousOn (fun t : ℝ =>
        Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x))
        (realizedSmallSet (δ := δ) (δ' := δ)) :=
      DifferentialGeometry.PDE.DeTurck.RicciLinearization.jointContMDiff_toModel_continuous_slice
        (I := I) g₀ 4 2 Φ (realizedSmallSet (δ := δ) (δ' := δ)) hjointC x
    have hcontIcc : ContinuousOn (fun t : ℝ =>
        Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x)) (Set.Icc (0 : ℝ) 1) :=
      hslice.mono hIccS
    set Cx : Tensor0SBundle.TensorRSModel 4 2 ℝ E :=
      Tensor0SBundle.TensorRSSpace.toModel (C1.toSection x)
        + Tensor0SBundle.TensorRSSpace.toModel (Δ1.toSection x) with hCx_def
    have hsecPD : ((P - C1 - Δ1).toSection x : Tensor0SBundle.TensorRSSpace 4 2 I x) =
        P.toSection x - C1.toSection x - Δ1.toSection x := by
      rw [show ((P - C1 - Δ1).toSection x : Tensor0SBundle.TensorRSSpace 4 2 I x) =
          (P - C1).toSection x - Δ1.toSection x from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
      rw [show ((P - C1).toSection x : Tensor0SBundle.TensorRSSpace 4 2 I x) =
          P.toSection x - C1.toSection x from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
    have hint_fPhi : IntervalIntegrable (fun t : ℝ =>
        Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x))
        MeasureTheory.volume 0 1 :=
      (hslice.mono hSIu).intervalIntegrable
    have hDmodel : Tensor0SBundle.TensorRSSpace.toModel ((P - C1 - Δ1).toSection x) =
        ∫ t in (0 : ℝ)..1,
          (Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x) - Cx) := by
      rw [hsecPD, Tensor0SBundle.TensorRSSpace.toModel_sub,
        Tensor0SBundle.TensorRSSpace.toModel_sub]
      rw [show Tensor0SBundle.TensorRSSpace.toModel (P.toSection x) =
          ∫ t in (0 : ℝ)..1, Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x) from by
        rw [hP_def]
        unfold deTurckPhiTotPathIntegral
        rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pathIntegralCoeffField_toModel]]
      rw [intervalIntegral.integral_sub hint_fPhi intervalIntegrable_const,
        intervalIntegral.integral_const, hCx_def]
      norm_num
      abel
    clear_value P C1 Δ1 g₁ Φ Cx
    have htpn_val : ∀ (W : SmoothCcTensor g₀ 4 2),
        tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x
            (Tensor0SBundle.TensorRSSpace.toModel (W.toSection x)) =
          Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (W.toSection x)) := by
      intro W
      rw [riemannianFiberNormSq_eq_tensorInnerPointwise]
      rfl
    have htpn_neg : ∀ m : Tensor0SBundle.TensorRSModel 4 2 ℝ E,
        tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x (-m) =
          tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x m := by
      intro m
      unfold tensorPointwiseNorm
      rw [show (-m : Tensor0SBundle.TensorRSModel 4 2 ℝ E) = (-1 : ℝ) • m from
        (neg_one_smul ℝ m).symm, tensorInnerPointwise_smul_left,
        tensorInnerPointwise_smul_right]
      norm_num
    have hsqrt_n3 : ∀ r : ℝ, 0 ≤ r →
        Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 3 * r ^ 2) = fC * r := by
      intro r hr
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hr, hfC_sqrt]
    have hsup : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x
            (Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x) - Cx) ≤
          fC * κ * (4 * t + (3 / 2) * (1 - t)) := by
      intro t ht
      have ht0 : (0 : ℝ) ≤ t := ht.1
      have ht1 : t ≤ 1 := ht.2
      set g_t : SmoothRiemannianMetric I M :=
        realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ t with hg_t_def
      set Δt : SmoothCcTensor g₀ 4 2 :=
        deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g_t with hΔt_def
      clear_value Δt
      have htδ_nn : (0 : ℝ) ≤ t * δ := mul_nonneg ht0 hδ0
      have htδ_le : t * δ ≤ δ := by nlinarith
      have htδ_lt : t * δ < 1 := lt_of_le_of_lt htδ_le hδ_lt
      have h1tδ : (0 : ℝ) < 1 - t * δ := by linarith
      have htie_t : ∀ (y : M) (v w : TangentSpace I y),
          g_t.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀
              (convexPerturbation (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) t) y v w :=
        fun y v w => realizedFam_inner_of_mem (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
          hδT hδZ (hIccS ht) y v w
      clear_value g_t
      have hcp : convexPerturbation (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) t
          = t • T₀ := by
        rw [show convexPerturbation (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) t =
            (1 - t) • (0 : SmoothCcTensor g₀ 0 2) + t • T₀ from rfl, smul_zero, zero_add]
      have hbilin_cp : ∀ (y : M) (v w : TangentSpace I y),
          ccTensorBilinSymm (I := I) g₀
            (convexPerturbation (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) t) y v w =
            t * ccTensorBilinSymm (I := I) g₀ T₀ y v w := by
        intro y v w
        rw [hcp, ccTensorBilinSymm_smul]
      have hδa : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀
            (convexPerturbation (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) t)) (t * δ) := by
        intro y v w
        rw [hbilin_cp y v w, abs_mul, abs_of_nonneg ht0]
        have hbase := hδT y v w
        have hs1 : (0 : ℝ) ≤ Real.sqrt (g₀.inner y v v) := Real.sqrt_nonneg _
        have hs2 : (0 : ℝ) ≤ Real.sqrt (g₀.inner y w w) := Real.sqrt_nonneg _
        calc t * |ccTensorBilinSymm (I := I) g₀ T₀ y v w|
            ≤ t * (δ * Real.sqrt (g₀.inner y v v) * Real.sqrt (g₀.inner y w w)) :=
              mul_le_mul_of_nonneg_left hbase ht0
          _ = t * δ * Real.sqrt (g₀.inner y v v) * Real.sqrt (g₀.inner y w w) := by ring
      have hδab : gFibreOpBound (I := I) (M := M) g₀
          (fun y => ccTensorBilinSymm (I := I) g₀
              (convexPerturbation (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) t) y
            - ccTensorBilinSymm (I := I) g₀ T₀ y) ((1 - t) * δ) := by
        intro y v w
        beta_reduce
        have hval : (ccTensorBilinSymm (I := I) g₀
            (convexPerturbation (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) t) y
            - ccTensorBilinSymm (I := I) g₀ T₀ y) v w =
            ccTensorBilinSymm (I := I) g₀
              (convexPerturbation (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) t) y v w
              - ccTensorBilinSymm (I := I) g₀ T₀ y v w := rfl
        rw [hval, hbilin_cp y v w]
        have hfact : t * (ccTensorBilinSymm (I := I) g₀ T₀ y v w)
            - ccTensorBilinSymm (I := I) g₀ T₀ y v w =
            (t - 1) * (ccTensorBilinSymm (I := I) g₀ T₀ y v w) := by ring
        rw [hfact, abs_mul, abs_of_nonpos (by linarith : t - 1 ≤ 0)]
        have hbase := hδT y v w
        have habs_nn : (0 : ℝ) ≤ |ccTensorBilinSymm (I := I) g₀ T₀ y v w| := abs_nonneg _
        calc -(t - 1) * |ccTensorBilinSymm (I := I) g₀ T₀ y v w|
            = (1 - t) * |ccTensorBilinSymm (I := I) g₀ T₀ y v w| := by ring
          _ ≤ (1 - t) * (δ * Real.sqrt (g₀.inner y v v) * Real.sqrt (g₀.inner y w w)) :=
              mul_le_mul_of_nonneg_left hbase (by linarith)
          _ = (1 - t) * δ * Real.sqrt (g₀.inner y v v) * Real.sqrt (g₀.inner y w w) := by ring
      have htie_1 : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₀ y v w := by
        intro y v w
        rw [hg₁_def]
        exact tensorSectionRealizeMetric_inner (I := I) g₀ T₀
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball) y v w
      have hΔt_rfns : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (Δt.toSection x) ≤
          (Module.finrank ℝ E : ℝ) ^ 3 * (t * δ / (1 - t * δ)) ^ 2 := by
        rw [hΔt_def]
        exact riemannianFiberNormSq_deTurckPrincipalCometricCoeff_le (I := I) (M := M)
          g₀ g_t _ htie_t htδ_lt htδ_nn hδa x
      have hΔt_sqrt : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          (Δt.toSection x)) ≤ fC * (t * δ / (1 - t * δ)) := by
        refine le_trans (Real.sqrt_le_sqrt hΔt_rfns) ?_
        rw [hsqrt_n3 _ (div_nonneg htδ_nn (le_of_lt h1tδ))]
      have hdev_rfns : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          ((Δt - Δ1).toSection x) ≤
          (Module.finrank ℝ E : ℝ) ^ 3 *
            ((1 - t) * δ / ((1 - t * δ) * (1 - δ))) ^ 2 := by
        rw [hΔt_def, hΔ1_def]
        exact kscr_rfns_pcc_deviation_le (I := I) (M := M) g₀ g_t g₁ _ _
          htie_t htie_1 htδ_lt hδa hδ_lt hδ0 hδT
          (mul_nonneg (by linarith) hδ0) hδab htδ_nn x
      have hdev_sqrt : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          ((Δt - Δ1).toSection x)) ≤
          fC * ((1 - t) * δ / ((1 - t * δ) * (1 - δ))) := by
        refine le_trans (Real.sqrt_le_sqrt hdev_rfns) ?_
        rw [hsqrt_n3 _ (div_nonneg (mul_nonneg (by linarith) hδ0)
          (le_of_lt (mul_pos h1tδ h1δ)))]
      have hdec_t := deTurckPhiMetTotal_eq_reindex_decomp_fw (I := I) (M := M) g₀ g_bg g_t
      have hdec_0 := deTurckPhiMetTotal_eq_reindex_decomp_fw (I := I) (M := M) g₀ g_bg g₀
      set ρA : Equiv.Perm (Fin 4) := traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA
        with hρA_def
      set ρAT : Equiv.Perm (Fin 4) := traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT
        with hρAT_def
      set A1 : SmoothCcTensor g₀ 4 2 := reindexCoeffGen (I := I) (M := M) g₀ 4 2
        (reindexCoeffGen (I := I) (M := M) g₀ 4 2 Δt traceHessianSlotPerm) ρA with hA1_def
      set A2 : SmoothCcTensor g₀ 4 2 := reindexCoeffGen (I := I) (M := M) g₀ 4 2
        (reindexCoeffGen (I := I) (M := M) g₀ 4 2 Δt traceHessianSlotPerm) ρAT with hA2_def
      set R1 : SmoothCcTensor g₀ 4 2 := reindexCoeffGen (I := I) (M := M) g₀ 4 2 Δt
        koszulSlotPerm with hR1_def
      set R2 : SmoothCcTensor g₀ 4 2 := reindexCoeffGen (I := I) (M := M) g₀ 4 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 4 2 (Equiv.swap (0 : Fin 2) 1) Δt)
        koszulSlotPerm with hR2_def
      clear_value A1 A2 R1 R2
      have hXX : (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g_t
            + ricciArmPrincipalCoeff (I := I) (M := M) g₀ g_t)
          - (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀
            + ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀) = R1 + R2 - Δt := by
        have h691 := kscr_ricciArmPrincipalCoeff_sub_add_self_eq_reindexSum
          (I := I) (M := M) g₀ g_t
        calc (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g_t
              + ricciArmPrincipalCoeff (I := I) (M := M) g₀ g_t)
            - (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀
              + ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)
            = (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g_t
                - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)
              + (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g_t
                - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀) := by abel
          _ = R1 + R2 - Δt := by rw [h691, hR1_def, hR2_def, hΔt_def]
      have hΨ : Φ t - C1 - Δ1 = A1 + A2 - R1 - R2 + (Δt - Δ1) := by
        have h327 := kscr_traceHessianCoeff_sub_eq_reindex_pcc (I := I) (M := M) g₀ g_t
        calc Φ t - C1 - Δ1
            = (reindexCoeffGen (I := I) (M := M) g₀ 4 2
                  (traceHessianCoeff (I := I) (M := M) g₀ g_t) ρA
                - reindexCoeffGen (I := I) (M := M) g₀ 4 2
                  (traceHessianCoeff (I := I) (M := M) g₀ g₀) ρA)
              + (reindexCoeffGen (I := I) (M := M) g₀ 4 2
                  (traceHessianCoeff (I := I) (M := M) g₀ g_t) ρAT
                - reindexCoeffGen (I := I) (M := M) g₀ 4 2
                  (traceHessianCoeff (I := I) (M := M) g₀ g₀) ρAT)
              - ((ricciArmPrincipalCoeff (I := I) (M := M) g₀ g_t
                  + ricciArmPrincipalCoeff (I := I) (M := M) g₀ g_t)
                - (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀
                  + ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀))
              - Δ1 := by
              rw [hΦ_def]
              beta_reduce
              rw [show deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
                  (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ t) =
                  deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g_t from by rw [hg_t_def]]
              rw [hdec_t, hC1_def, hdec_0, hρA_def, hρAT_def]
              abel
          _ = (reindexCoeffGen (I := I) (M := M) g₀ 4 2
                (traceHessianCoeff (I := I) (M := M) g₀ g_t
                  - traceHessianCoeff (I := I) (M := M) g₀ g₀) ρA)
              + (reindexCoeffGen (I := I) (M := M) g₀ 4 2
                (traceHessianCoeff (I := I) (M := M) g₀ g_t
                  - traceHessianCoeff (I := I) (M := M) g₀ g₀) ρAT)
              - (R1 + R2 - Δt) - Δ1 := by
              rw [kscr_reindexCoeffGen_sub (I := I) (M := M) g₀ _ _ ρA,
                kscr_reindexCoeffGen_sub (I := I) (M := M) g₀ _ _ ρAT, hXX]
          _ = A1 + A2 - R1 - R2 + (Δt - Δ1) := by
              rw [h327, ← hΔt_def, hA1_def, hA2_def]
              abel
      have hΨsec : ((Φ t - C1 - Δ1).toSection x : Tensor0SBundle.TensorRSSpace 4 2 I x) =
          A1.toSection x + A2.toSection x - R1.toSection x - R2.toSection x
            + (Δt - Δ1).toSection x := by
        rw [hΨ]
        rw [show ((A1 + A2 - R1 - R2 + (Δt - Δ1)).toSection x :
            Tensor0SBundle.TensorRSSpace 4 2 I x) =
            (A1 + A2 - R1 - R2).toSection x + (Δt - Δ1).toSection x from by
          rw [SmoothCcTensor.toSection_add]; rfl]
        rw [show ((A1 + A2 - R1 - R2).toSection x :
            Tensor0SBundle.TensorRSSpace 4 2 I x) =
            (A1 + A2 - R1).toSection x - R2.toSection x from by
          rw [SmoothCcTensor.toSection_sub]; rfl]
        rw [show ((A1 + A2 - R1).toSection x : Tensor0SBundle.TensorRSSpace 4 2 I x) =
            (A1 + A2).toSection x - R1.toSection x from by
          rw [SmoothCcTensor.toSection_sub]; rfl]
        rw [show ((A1 + A2).toSection x : Tensor0SBundle.TensorRSSpace 4 2 I x) =
            A1.toSection x + A2.toSection x from by
          rw [SmoothCcTensor.toSection_add]; rfl]
      have hΨmodel : Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x) - Cx =
          Tensor0SBundle.TensorRSSpace.toModel ((Φ t - C1 - Δ1).toSection x) := by
        rw [show ((Φ t - C1 - Δ1).toSection x : Tensor0SBundle.TensorRSSpace 4 2 I x) =
            (Φ t - C1).toSection x - Δ1.toSection x from by
          rw [SmoothCcTensor.toSection_sub]; rfl]
        rw [show ((Φ t - C1).toSection x : Tensor0SBundle.TensorRSSpace 4 2 I x) =
            (Φ t).toSection x - C1.toSection x from by
          rw [SmoothCcTensor.toSection_sub]; rfl]
        rw [Tensor0SBundle.TensorRSSpace.toModel_sub,
          Tensor0SBundle.TensorRSSpace.toModel_sub, hCx_def]
        abel
      have hexA1 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (A1.toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (Δt.toSection x) := by
        rw [hA1_def]
        rw [reindexCoeffGen_toSection]
        rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannianFiberNormSq_reindexCoeffFibGen
          (I := I) (M := M) g₀ 4 2 x ρA _]
        rw [reindexCoeffGen_toSection]
        exact DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannianFiberNormSq_reindexCoeffFibGen
          (I := I) (M := M) g₀ 4 2 x traceHessianSlotPerm _
      have hexA2 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (A2.toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (Δt.toSection x) := by
        rw [hA2_def]
        rw [reindexCoeffGen_toSection]
        rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannianFiberNormSq_reindexCoeffFibGen
          (I := I) (M := M) g₀ 4 2 x ρAT _]
        rw [reindexCoeffGen_toSection]
        exact DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannianFiberNormSq_reindexCoeffFibGen
          (I := I) (M := M) g₀ 4 2 x traceHessianSlotPerm _
      have hexR1 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (R1.toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (Δt.toSection x) := by
        rw [hR1_def, reindexCoeffGen_toSection]
        exact DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannianFiberNormSq_reindexCoeffFibGen
          (I := I) (M := M) g₀ 4 2 x koszulSlotPerm _
      have hexR2 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (R2.toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (Δt.toSection x) := by
        have h20 := rfns_iteratedCovGrad_rsDomDomCongr_both_eq (I := I) (M := M) g₀ 4 2
          koszulSlotPerm (Equiv.swap (0 : Fin 2) 1) Δt 0 x
        rw [hR2_def]
        simpa [iteratedCovGrad_zero] using h20
      have htpn_piece : ∀ (W : SmoothCcTensor g₀ 4 2),
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (W.toSection x) =
            riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (Δt.toSection x) →
          tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x
              (Tensor0SBundle.TensorRSSpace.toModel (W.toSection x)) ≤
            fC * (t * δ / (1 - t * δ)) := by
        intro W hW
        rw [htpn_val W, hW]
        exact hΔt_sqrt
      have htpn_sub_le : ∀ u v : Tensor0SBundle.TensorRSModel 4 2 ℝ E,
          tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x (u - v) ≤
            tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x u
              + tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x v := by
        intro u v
        rw [sub_eq_add_neg]
        refine le_trans (tensorPointwiseNorm_add_le (I := I) (M := M) g₀ 4 2 x u (-v)) ?_
        rw [htpn_neg v]
      have htri : tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x
          (Tensor0SBundle.TensorRSSpace.toModel ((Φ t - C1 - Δ1).toSection x)) ≤
          4 * (fC * (t * δ / (1 - t * δ)))
            + fC * ((1 - t) * δ / ((1 - t * δ) * (1 - δ))) := by
        rw [hΨsec]
        rw [Tensor0SBundle.TensorRSSpace.toModel_add, Tensor0SBundle.TensorRSSpace.toModel_sub,
          Tensor0SBundle.TensorRSSpace.toModel_sub, Tensor0SBundle.TensorRSSpace.toModel_add]
        have t4 := tensorPointwiseNorm_add_le (I := I) (M := M) g₀ 4 2 x
          (Tensor0SBundle.TensorRSSpace.toModel (A1.toSection x)
            + Tensor0SBundle.TensorRSSpace.toModel (A2.toSection x)
            - Tensor0SBundle.TensorRSSpace.toModel (R1.toSection x)
            - Tensor0SBundle.TensorRSSpace.toModel (R2.toSection x))
          (Tensor0SBundle.TensorRSSpace.toModel ((Δt - Δ1).toSection x))
        have t3 := htpn_sub_le
          (Tensor0SBundle.TensorRSSpace.toModel (A1.toSection x)
            + Tensor0SBundle.TensorRSSpace.toModel (A2.toSection x)
            - Tensor0SBundle.TensorRSSpace.toModel (R1.toSection x))
          (Tensor0SBundle.TensorRSSpace.toModel (R2.toSection x))
        have t2 := htpn_sub_le
          (Tensor0SBundle.TensorRSSpace.toModel (A1.toSection x)
            + Tensor0SBundle.TensorRSSpace.toModel (A2.toSection x))
          (Tensor0SBundle.TensorRSSpace.toModel (R1.toSection x))
        have t1 := tensorPointwiseNorm_add_le (I := I) (M := M) g₀ 4 2 x
          (Tensor0SBundle.TensorRSSpace.toModel (A1.toSection x))
          (Tensor0SBundle.TensorRSSpace.toModel (A2.toSection x))
        have b1 := htpn_piece A1 hexA1
        have b2 := htpn_piece A2 hexA2
        have b3 := htpn_piece R1 hexR1
        have b4 := htpn_piece R2 hexR2
        have b5 : tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x
            (Tensor0SBundle.TensorRSSpace.toModel ((Δt - Δ1).toSection x)) ≤
            fC * ((1 - t) * δ / ((1 - t * δ) * (1 - δ))) := by
          rw [htpn_val (Δt - Δ1)]
          exact hdev_sqrt
        linarith [t1, t2, t3, t4, b1, b2, b3, b4, b5]
      have hrate1 : t * δ / (1 - t * δ) ≤ t * κ := by
        rw [hκ_def, div_le_iff₀ h1tδ]
        have h1 : t * (δ / (1 - δ)) * (1 - t * δ) = (t * δ * (1 - t * δ)) / (1 - δ) := by
          field_simp
        rw [h1, le_div_iff₀ h1δ]
        nlinarith [mul_nonneg (mul_nonneg (mul_nonneg ht0 hδ0) hδ0)
          (by linarith : (0:ℝ) ≤ 1 - t)]
      have hrate2 : (1 - t) * δ / ((1 - t * δ) * (1 - δ)) ≤ (3 / 2) * ((1 - t) * κ) := by
        rw [hκ_def, div_le_iff₀ (mul_pos h1tδ h1δ)]
        have h1 : (3 / 2 : ℝ) * ((1 - t) * (δ / (1 - δ))) * ((1 - t * δ) * (1 - δ)) =
            (3 / 2) * ((1 - t) * δ) * (1 - t * δ) := by
          field_simp
        rw [h1]
        have hkey : (0 : ℝ) ≤ 1 / 2 - (3 / 2) * (t * δ) := by nlinarith
        nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 1 - t) hδ0) hkey]
      calc tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x
            (Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x) - Cx)
          = tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x
            (Tensor0SBundle.TensorRSSpace.toModel ((Φ t - C1 - Δ1).toSection x)) := by
            rw [hΨmodel]
        _ ≤ 4 * (fC * (t * δ / (1 - t * δ)))
            + fC * ((1 - t) * δ / ((1 - t * δ) * (1 - δ))) := htri
        _ ≤ 4 * (fC * (t * κ)) + fC * ((3 / 2) * ((1 - t) * κ)) := by
            have e1 : fC * (t * δ / (1 - t * δ)) ≤ fC * (t * κ) :=
              mul_le_mul_of_nonneg_left hrate1 hfC_nn
            have e2 : fC * ((1 - t) * δ / ((1 - t * δ) * (1 - δ))) ≤
                fC * ((3 / 2) * ((1 - t) * κ)) :=
              mul_le_mul_of_nonneg_left hrate2 hfC_nn
            linarith
        _ = fC * κ * (4 * t + (3 / 2) * (1 - t)) := by ring
    have hrfns_tpn : riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) 2 x
        ((P - C1 - Δ1).toSection x) =
        tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x
          (Tensor0SBundle.TensorRSSpace.toModel ((P - C1 - Δ1).toSection x)) ^ 2 := by
      rw [riemannianFiberNormSq_eq_tensorInnerPointwise]
      unfold tensorPointwiseNorm
      rw [Real.sq_sqrt (tensorInnerPointwise_nonneg (I := I) (M := M) g₀ 4 2 x _)]
    rw [hrfns_tpn, hDmodel]
    have hcont_shift : ContinuousOn (fun t : ℝ =>
        Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x) - Cx)
        (Set.Icc (0 : ℝ) 1) := hcontIcc.sub continuousOn_const
    have hint_le := tensorPointwiseNorm_intervalIntegral_le (I := I) (M := M) g₀ 4 2 x
      (fun t => Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x) - Cx) hcont_shift
    have hint1 : IntervalIntegrable (fun t : ℝ =>
        tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x
          (Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x) - Cx))
        MeasureTheory.volume 0 1 :=
      ((tensorPointwiseNorm_continuous (I := I) (M := M) g₀ 4 2 x).comp_continuousOn
        hcont_shift).intervalIntegrable_of_Icc (by norm_num)
    have hint2 : IntervalIntegrable (fun t : ℝ => fC * κ * (4 * t + (3 / 2) * (1 - t)))
        MeasureTheory.volume 0 1 := by
      apply Continuous.intervalIntegrable
      continuity
    have hmono : (∫ t in (0 : ℝ)..1, tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x
        (Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x) - Cx)) ≤
        ∫ t in (0 : ℝ)..1, fC * κ * (4 * t + (3 / 2) * (1 - t)) :=
      intervalIntegral.integral_mono_on (by norm_num) hint1 hint2 hsup
    have hwval : (∫ t in (0 : ℝ)..1, fC * κ * (4 * t + (3 / 2) * (1 - t))) =
        (11 / 4) * fC * κ := by
      rw [intervalIntegral.integral_const_mul]
      rw [show (fun t : ℝ => 4 * t + (3 / 2) * (1 - t)) =
          fun t : ℝ => (5 / 2) * t + 3 / 2 from funext fun t => by ring]
      rw [intervalIntegral.integral_add ((intervalIntegral.intervalIntegrable_id).const_mul _)
        intervalIntegrable_const]
      rw [intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const]
      norm_num
      ring
    have htpn_nn : (0 : ℝ) ≤ tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x
        (∫ t in (0 : ℝ)..1,
          (Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x) - Cx)) :=
      tensorPointwiseNorm_nonneg (I := I) (M := M) g₀ 4 2 x _
    have hfinal : tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x
        (∫ t in (0 : ℝ)..1,
          (Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x) - Cx)) ≤
        (11 / 4) * fC * κ := by
      refine le_trans hint_le ?_
      rw [← hwval]
      exact hmono
    calc tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x
          (∫ t in (0 : ℝ)..1,
            (Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x) - Cx)) ^ 2
        ≤ ((11 / 4) * fC * κ) ^ 2 := by
          exact pow_le_pow_left₀ htpn_nn hfinal 2
      _ = ((11 / 4 : ℝ) * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) ^ 2 := by
          rw [hfC_def, hκ_def]

end


set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
open DifferentialGeometry.Integral.Measure in
theorem exists_gInvDiffSlotCoeff_grid_l2_jetLinear_highOrder
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
    ∃ Kg : ℕ → ℝ, (∀ i, 0 ≤ Kg i) ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        ∀ (i : ℕ),
          (∫ x, (∑ n' ∈ Finset.range (i + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n' i,
                ∏ m : Fin n',
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x))
            ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g₀)) ≤
          Kg i * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨C2, hC2_nn, hC2⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general (I := I) (M := M) g₀ (a + 2)
  set B : ℝ := C2 * R₀ with hB_def
  have hB_nn : 0 ≤ B := mul_nonneg hC2_nn hR₀
  obtain ⟨Cemb, hCemb_nn, hCemb⟩ :=
    deTurckSmoothRemainderDiff_supercritical_pointwise_jet_le_fixedWindow
      (I := I) (M := M) g₀ a ha_super
  set Λ₀ : ℝ := Cemb * Real.sqrt ((a + 1 + 1 : ℕ) : ℝ) * B with hΛ₀_def
  have hΛ₀_nn : 0 ≤ Λ₀ := by rw [hΛ₀_def]; positivity
  set L : ℝ := max (Λ₀ ^ 2) 1 with hL_def
  have hL_one : (1 : ℝ) ≤ L := le_max_right _ _
  have hL_nn : (0 : ℝ) ≤ L := le_trans zero_le_one hL_one
  set Cgn : ℕ → ℝ := fun k =>
    if h : 1 ≤ k then
      (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 2 k h).choose
    else 0 with hCgn_def
  set Cg1 : ℕ → ℝ := fun k => max (Cgn k) 1 with hCg1_def
  have hCg1_one : ∀ k, (1 : ℝ) ≤ Cg1 k := fun k => le_max_right _ _
  have hCgL_one : ∀ k, (1 : ℝ) ≤ Cg1 k * L :=
    fun k => le_trans (hCg1_one k) (le_mul_of_one_le_right
      (le_trans zero_le_one (hCg1_one k)) hL_one)
  set Cbig : ℕ → ℝ := fun k => L ^ k * (Cg1 k * L) ^ k with hCbig_def
  have hCbig_nn : ∀ k, 0 ≤ Cbig k := fun k =>
    mul_nonneg (pow_nonneg hL_nn k)
      (pow_nonneg (le_trans zero_le_one (hCgL_one k)) k)
  set vol : ℝ := ((riemannianVolumeMeasure (I := I) (M := M) g₀) Set.univ).toReal
    with hvol_def
  have hvol_nn : 0 ≤ vol := ENNReal.toReal_nonneg
  refine ⟨fun k => (∑ n' ∈ Finset.range (k + 1),
      ((Finset.Nat.antidiagonalTuple n' k).card : ℝ)) * Cbig k + vol, ?_, ?_⟩
  · intro k
    exact add_nonneg
      (mul_nonneg (Finset.sum_nonneg fun n' _ => Nat.cast_nonneg _) (hCbig_nn k)) hvol_nn
  · intro T₀ hball i
    have hS_nn : 0 ≤ ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 :=
      Finset.sum_nonneg fun j _ => sq_nonneg _
    have h1S : (1 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 := by linarith
    have hPball : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤ B := by
      intro j hj
      have hsum := hC2 T₀
      have hcast : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + 2 : ℕ) : ℝ) T₀‖ =
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ :=
        smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
      rw [hcast] at hsum
      have hsumB : ∑ l ∈ Finset.range (a + 2 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ≤ B := by
        rw [hB_def]
        exact le_trans hsum (mul_le_mul_of_nonneg_left hball hC2_nn)
      exact le_trans
        (Finset.single_le_sum
          (f := fun l => ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖)
          (fun l _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))) hsumB
    have hsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        (T₀.toSection x) ≤ Λ₀ ^ 2 := by
      intro x
      have hsum_le : ∑ j ∈ Finset.range (a + 1 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 ≤ ((a + 1 + 1 : ℕ) : ℝ) * B ^ 2 := by
        calc ∑ j ∈ Finset.range (a + 1 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2
            ≤ ∑ j ∈ Finset.range (a + 1 + 1), B ^ 2 := by
              apply Finset.sum_le_sum
              intro j hj
              have hjle : j ≤ a + 2 := by have := Finset.mem_range.mp hj; omega
              nlinarith [norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 j T₀),
                hPball j hjle, hB_nn]
          _ = ((a + 1 + 1 : ℕ) : ℝ) * B ^ 2 := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hsingle : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (T₀.toSection x) ≤
          ∑ m ∈ Finset.range 3, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 m T₀).toSection x) := by
        have h0mem : (0 : ℕ) ∈ Finset.range 3 := by norm_num
        have hsl := Finset.single_le_sum
          (f := fun m => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 m T₀).toSection x))
          (fun m _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + m) x _) h0mem
        simpa using hsl
      have hLam2 : Λ₀ ^ 2 = Cemb ^ 2 * ((a + 1 + 1 : ℕ) : ℝ) * B ^ 2 := by
        rw [hΛ₀_def, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
      have hchain : ∑ m ∈ Finset.range 3, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 m T₀).toSection x) ≤ Λ₀ ^ 2 := by
        refine le_trans (hCemb T₀ x) ?_
        rw [hLam2]
        calc Cemb ^ 2 * ∑ j ∈ Finset.range (a + 1 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2
            ≤ Cemb ^ 2 * (((a + 1 + 1 : ℕ) : ℝ) * B ^ 2) :=
              mul_le_mul_of_nonneg_left hsum_le (by positivity)
          _ = Cemb ^ 2 * ((a + 1 + 1 : ℕ) : ℝ) * B ^ 2 := by ring
      exact le_trans hsingle hchain
    by_cases hi0 : i = 0
    · subst hi0
      have hgrid0 : (fun x => ∑ n' ∈ Finset.range (0 + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n' 0, ∏ m : Fin n',
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x)) =
          (fun _ : M => (1 : ℝ)) := by
        funext x
        simp only [Nat.zero_add, Finset.sum_range_one, Finset.Nat.antidiagonalTuple_zero_zero,
          Finset.sum_singleton, Finset.univ_eq_empty, Finset.prod_empty]
      rw [hgrid0, MeasureTheory.integral_const, smul_eq_mul, mul_one,
        MeasureTheory.measureReal_def, ← hvol_def]
      have hvolKg : vol ≤ (∑ n' ∈ Finset.range (0 + 1),
          ((Finset.Nat.antidiagonalTuple n' 0).card : ℝ)) * Cbig 0 + vol :=
        le_add_of_nonneg_left
          (mul_nonneg (Finset.sum_nonneg fun n' _ => Nat.cast_nonneg _) (hCbig_nn 0))
      calc vol = vol * 1 := (mul_one _).symm
        _ ≤ ((∑ n' ∈ Finset.range (0 + 1),
              ((Finset.Nat.antidiagonalTuple n' 0).card : ℝ)) * Cbig 0 + vol) *
            (1 + ∑ j ∈ Finset.range (0 + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) :=
          mul_le_mul hvolKg h1S zero_le_one
            (add_nonneg (mul_nonneg (Finset.sum_nonneg fun n' _ => Nat.cast_nonneg _)
              (hCbig_nn 0)) hvol_nn)
    · have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
      have hiR_pos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hi0
      have hN2_le : ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 ≤
          1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 := by
        have hmem : i ∈ Finset.range (i + 2) := Finset.mem_range.mpr (by omega)
        have := Finset.single_le_sum
          (f := fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)
          (fun j _ => sq_nonneg _) hmem
        linarith
      have hGNspec := (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 2 i hi1).choose_spec.2
      have hCgn_i : (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
          (I := I) (M := M) g₀ 0 2 i hi1).choose = Cgn i := by
        rw [hCgn_def]; simp only [dif_pos hi1]
      have hLbound : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 2 → Λ₀ ^ θ ≤ L := by
        intro θ hθ0 hθ2
        rcases le_or_gt 1 Λ₀ with hΛ1 | hΛ1
        · calc Λ₀ ^ θ ≤ Λ₀ ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hΛ1 hθ2
            _ = Λ₀ ^ 2 := Real.rpow_two Λ₀
            _ ≤ L := le_max_left _ _
        · calc Λ₀ ^ θ ≤ 1 := Real.rpow_le_one hΛ₀_nn (le_of_lt hΛ1) hθ0
            _ ≤ L := hL_one
      have hcont_prod : ∀ (n' : ℕ) (e : Fin n' → ℕ), Continuous (fun x : M =>
          ∏ m : Fin n', riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x)) := by
        intro n' e
        refine continuous_finset_prod _ fun m _ => ?_
        have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M)
          (iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀)
        refine hc.congr fun x => ?_
        rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x),
          ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M)
            (iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀) x]
      have hint_prod : ∀ (n' : ℕ) (e : Fin n' → ℕ), MeasureTheory.Integrable
          (fun x : M => ∏ m : Fin n',
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x))
          (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
        fun n' e => integrable_of_continuous_compactSpace (I := I) (M := M) g₀
          (hcont_prod n' e)
      have hPT : ∀ n' ∈ Finset.range (i + 1), ∀ e ∈ Finset.Nat.antidiagonalTuple n' i,
          (∫ x, ∏ m : Fin n',
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
          Cbig i * ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 := by
        intro n' hn' e he
        have hn'_le : n' ≤ i := by have := Finset.mem_range.mp hn'; omega
        have hsum_univ : ∑ m, e m = i := Finset.Nat.mem_antidiagonalTuple.mp he
        have hem_le : ∀ m : Fin n', e m ≤ i := by
          intro m
          have h1 := Finset.single_le_sum (f := fun m' => e m')
            (fun m' _ => Nat.zero_le (e m')) (Finset.mem_univ m)
          rw [hsum_univ] at h1
          exact h1
        have hΛzero : ∀ m ∈ (Finset.univ : Finset (Fin n')), e m = 0 → ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x) ≤ Λ₀ ^ 2 := by
          intro m _ hm0 x
          revert hm0
          generalize e m = j
          intro hj
          subst hj
          simpa [iteratedCovGrad_zero] using hsup x
        have hHold := holder_integral_prod_riemannianFiberNormSq_natWeight_le_of_sup_bound
          (I := I) (M := M) g₀ (Finset.univ : Finset (Fin n')) (fun _ => 0)
          (fun m => 2 + e m) (fun m => iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀) e i
          hi1 hsum_univ (fun _ => Λ₀ ^ 2) (fun m _ _ => sq_nonneg _) hΛzero
        beta_reduce at hHold
        have hsum_pos_nat : ∑ m ∈ Finset.univ.filter (fun m : Fin n' => 0 < e m), e m = i := by
          rw [← hsum_univ]
          refine Finset.sum_subset (Finset.filter_subset _ _) fun m _ hm => ?_
          by_contra h0
          exact hm (Finset.mem_filter.mpr ⟨Finset.mem_univ m, Nat.pos_of_ne_zero h0⟩)
        have h2sum : ∑ m ∈ Finset.univ.filter (fun m : Fin n' => 0 < e m),
            (2 * (e m : ℝ) / (i : ℝ)) = 2 := by
          have hterm : ∀ m ∈ Finset.univ.filter (fun m : Fin n' => 0 < e m),
              2 * (e m : ℝ) / (i : ℝ) = (e m : ℝ) * (2 / (i : ℝ)) := fun m _ => by ring
          rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← Nat.cast_sum, hsum_pos_nat]
          field_simp
        have hposcard : (Finset.univ.filter (fun m : Fin n' => 0 < e m)).card ≤ i := by
          calc (Finset.univ.filter (fun m : Fin n' => 0 < e m)).card
              ≤ (Finset.univ : Finset (Fin n')).card := Finset.card_filter_le _ _
            _ = n' := by simp
            _ ≤ i := hn'_le
        have hzercard : (Finset.univ.filter (fun m : Fin n' => e m = 0)).card ≤ i := by
          calc (Finset.univ.filter (fun m : Fin n' => e m = 0)).card
              ≤ (Finset.univ : Finset (Fin n')).card := Finset.card_filter_le _ _
            _ = n' := by simp
            _ ≤ i := hn'_le
        have hFG : ∀ m ∈ Finset.univ.filter (fun m : Fin n' => 0 < e m),
            (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x)
                  ^ ((i : ℝ) / (e m : ℝ))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((e m : ℝ) / (i : ℝ)) ≤
            Cg1 i * L * ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖
              ^ (2 * (e m : ℝ) / (i : ℝ)) := by
          intro m hm
          have hem_pos : 0 < e m := (Finset.mem_filter.mp hm).2
          rcases eq_or_lt_of_le (hem_le m) with hemi | hemi
          · subst hemi
            have hd1 : ((e m : ℝ) / (e m : ℝ)) = 1 := div_self (ne_of_gt hiR_pos)
            rw [hd1, Real.rpow_one, mul_div_assoc, hd1, mul_one, Real.rpow_two]
            simp only [Real.rpow_one]
            have hbr := tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
              (I := I) (M := M) g₀ 0 (2 + e m)
              (iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀)
            rw [← SmoothCcTensor.norm_def] at hbr
            rw [← hbr]
            have h1 : (1 : ℝ) ≤ Cg1 (e m) * L := hCgL_one (e m)
            nlinarith [sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀‖]
          · have hb := hGNspec T₀ Λ₀ hΛ₀_nn hsup (e m) hem_pos hemi
            rw [hCgn_i] at hb
            refine le_trans hb ?_
            have hnorm : Integral.L2.tensorL2Norm (I := I) g₀ 0 (2 + i)
                (iteratedCovGrad (I := I) g₀ 0 2 i T₀).toFun =
                ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ :=
              (SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 2 i T₀)).symm
            rw [hnorm]
            have hθL_nn : (0 : ℝ) ≤ 2 * (1 - (e m : ℝ) / (i : ℝ)) := by
              have : (e m : ℝ) / (i : ℝ) ≤ 1 :=
                (div_le_one hiR_pos).mpr (by exact_mod_cast hem_le m)
              linarith
            have hθL_le2 : 2 * (1 - (e m : ℝ) / (i : ℝ)) ≤ 2 := by
              have : (0 : ℝ) ≤ (e m : ℝ) / (i : ℝ) := by positivity
              linarith
            have hΛfac : Λ₀ ^ (2 * (1 - (e m : ℝ) / (i : ℝ))) ≤ L :=
              hLbound _ hθL_nn hθL_le2
            have hNfac_nn : (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖
                ^ (2 * (e m : ℝ) / (i : ℝ)) :=
              Real.rpow_nonneg (norm_nonneg _) _
            calc Cgn i * Λ₀ ^ (2 * (1 - (e m : ℝ) / (i : ℝ))) *
                  ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ (2 * (e m : ℝ) / (i : ℝ))
                ≤ Cg1 i * Λ₀ ^ (2 * (1 - (e m : ℝ) / (i : ℝ))) *
                  ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ (2 * (e m : ℝ) / (i : ℝ)) := by
                  refine mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_right (le_max_left _ _)
                      (Real.rpow_nonneg hΛ₀_nn _)) hNfac_nn
              _ ≤ Cg1 i * L * ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖
                  ^ (2 * (e m : ℝ) / (i : ℝ)) := by
                  refine mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hΛfac
                      (le_trans zero_le_one (hCg1_one i))) hNfac_nn
        have hF_nn : ∀ m ∈ Finset.univ.filter (fun m : Fin n' => 0 < e m),
            (0 : ℝ) ≤ (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x)
                  ^ ((i : ℝ) / (e m : ℝ))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((e m : ℝ) / (i : ℝ)) :=
          fun m _ => Real.rpow_nonneg
            (MeasureTheory.integral_nonneg fun x => Real.rpow_nonneg
              (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + e m) x _) _) _
        have hprodF_le : (∏ m ∈ Finset.univ.filter (fun m : Fin n' => 0 < e m),
            (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x)
                  ^ ((i : ℝ) / (e m : ℝ))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((e m : ℝ) / (i : ℝ))) ≤
            ∏ m ∈ Finset.univ.filter (fun m : Fin n' => 0 < e m),
              (Cg1 i * L * ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖
                ^ (2 * (e m : ℝ) / (i : ℝ))) :=
          Finset.prod_le_prod hF_nn hFG
        have hprodG : (∏ m ∈ Finset.univ.filter (fun m : Fin n' => 0 < e m),
            (Cg1 i * L * ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖
              ^ (2 * (e m : ℝ) / (i : ℝ)))) =
            (Cg1 i * L) ^ (Finset.univ.filter (fun m : Fin n' => 0 < e m)).card *
              ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ (2 : ℝ) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const,
            ← Real.rpow_sum_of_nonneg (norm_nonneg _) (fun m _ => by positivity), h2sum]
        have hzer_le : ((Λ₀ ^ 2) ^ (Finset.univ.filter
            (fun m : Fin n' => e m = 0)).card : ℝ) ≤ L ^ i :=
          le_trans (pow_le_pow_left₀ (sq_nonneg _) (le_max_left _ _) _)
            (pow_le_pow_right₀ hL_one hzercard)
        have hpos_le : ((Cg1 i * L) ^ (Finset.univ.filter
            (fun m : Fin n' => 0 < e m)).card : ℝ) ≤ (Cg1 i * L) ^ i :=
          pow_le_pow_right₀ (hCgL_one i) hposcard
        calc (∫ x, ∏ m : Fin n',
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀))
            ≤ (∏ _m ∈ Finset.univ.filter (fun m : Fin n' => e m = 0), Λ₀ ^ 2) *
              ∏ m ∈ Finset.univ.filter (fun m : Fin n' => 0 < e m),
                (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x)
                      ^ ((i : ℝ) / (e m : ℝ))
                  ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((e m : ℝ) / (i : ℝ)) :=
            hHold
          _ ≤ (∏ _m ∈ Finset.univ.filter (fun m : Fin n' => e m = 0), Λ₀ ^ 2) *
              ((Cg1 i * L) ^ (Finset.univ.filter (fun m : Fin n' => 0 < e m)).card *
                ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ (2 : ℝ)) := by
            refine mul_le_mul_of_nonneg_left (le_of_le_of_eq hprodF_le hprodG) ?_
            exact Finset.prod_nonneg fun _ _ => sq_nonneg _
          _ = (Λ₀ ^ 2) ^ (Finset.univ.filter (fun m : Fin n' => e m = 0)).card *
              ((Cg1 i * L) ^ (Finset.univ.filter (fun m : Fin n' => 0 < e m)).card *
                ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) := by
            rw [Finset.prod_const, Real.rpow_two]
          _ ≤ L ^ i * ((Cg1 i * L) ^ i *
                ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) := by
            refine mul_le_mul hzer_le
              (mul_le_mul_of_nonneg_right hpos_le (sq_nonneg _))
              (mul_nonneg (pow_nonneg (le_trans zero_le_one (hCgL_one i)) _)
                (sq_nonneg _))
              (pow_nonneg hL_nn i)
          _ = Cbig i * ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 := by
            simp only [hCbig_def]
            ring
      rw [MeasureTheory.integral_finset_sum _
        (fun n' _ => MeasureTheory.integrable_finset_sum _ (fun e _ => hint_prod n' e))]
      have hinner : ∀ n' ∈ Finset.range (i + 1),
          (∫ x, ∑ e ∈ Finset.Nat.antidiagonalTuple n' i, ∏ m : Fin n',
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x)
            ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g₀)) =
          ∑ e ∈ Finset.Nat.antidiagonalTuple n' i,
            ∫ x, ∏ m : Fin n',
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x)
            ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g₀) :=
        fun n' _ => MeasureTheory.integral_finset_sum _ (fun e _ => hint_prod n' e)
      rw [Finset.sum_congr rfl hinner]
      have hle1 : ∑ n' ∈ Finset.range (i + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n' i,
            (∫ x, ∏ m : Fin n',
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x)
            ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g₀)) ≤
          ∑ n' ∈ Finset.range (i + 1), ∑ _e ∈ Finset.Nat.antidiagonalTuple n' i,
            (Cbig i * ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) := by
        refine Finset.sum_le_sum fun n' hn' => Finset.sum_le_sum fun e he => ?_
        exact hPT n' hn' e he
      refine le_trans hle1 ?_
      have heq2 : ∑ n' ∈ Finset.range (i + 1), ∑ _e ∈ Finset.Nat.antidiagonalTuple n' i,
          (Cbig i * ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) =
          (∑ n' ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n' i).card : ℝ)) *
            (Cbig i * ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun n' _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul]
      rw [heq2]
      have hcard_nn : (0 : ℝ) ≤ ∑ n' ∈ Finset.range (i + 1),
          ((Finset.Nat.antidiagonalTuple n' i).card : ℝ) :=
        Finset.sum_nonneg fun n' _ => Nat.cast_nonneg _
      calc (∑ n' ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n' i).card : ℝ)) *
            (Cbig i * ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2)
          = ((∑ n' ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n' i).card : ℝ)) *
              Cbig i) * ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 := by ring
        _ ≤ ((∑ n' ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n' i).card : ℝ)) *
              Cbig i) * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hN2_le (mul_nonneg hcard_nn (hCbig_nn i))
        _ ≤ ((∑ n' ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n' i).card : ℝ)) *
              Cbig i + vol) * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) :=
            mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hvol_nn)
              (le_trans zero_le_one h1S)

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
open DifferentialGeometry.Integral.Measure in
theorem exists_deTurckPrincipalCometricCoeff_realize_coeffJetEnvelope_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2),
        (∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T₀ x v w = ccTensorBilin (I := I) g₀ T₀ x w v) →
        ∀ (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
              (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
                  (tensorSectionRealizeMetric (I := I) g₀ T₀
                    (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                    (hδ_fibre T₀ hball)))‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) := by
  classical
  have hrsub : ∀ k l : ℕ, k ≤ l → Finset.range k ⊆ Finset.range l :=
    fun k l hkl x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hkl)
  obtain ⟨Kg, hKg_nn, hKg⟩ :=
    exists_gInvDiffSlotCoeff_grid_l2_jetLinear_highOrder (I := I) (M := M) g₀ a ha_super hR₀
  obtain ⟨Cd, hCd_nn, hCd⟩ :=
    deTurckPrincipalCometricCoeff_perOrder_rfns_le_gInvDiffSlotCoeff (I := I) (M := M) g₀
  obtain ⟨C2, hC2_nn, hC2⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general (I := I) (M := M) g₀ (a + 2)
  set B : ℝ := C2 * R₀ with hB_def
  have hB_nn : 0 ≤ B := mul_nonneg hC2_nn hR₀
  obtain ⟨Klo, hKlo_nn, hKlo⟩ :=
    gInvDiffSlotCoeff_perOrder_l2_ballUniform_generic (I := I) (M := M) g₀ a ha_super hB_nn
      (by norm_num : (1 : ℝ) / 3 < 1)
  obtain ⟨Cg, hCg_nn, hCg⟩ :=
    rfns_iteratedCovGrad_gInvDiffSlotCoeff_diagonalProductGrid_le (I := I) (M := M) g₀
      (by norm_num : (1 : ℝ) / 3 < 1)
  set KcF : ℕ → ℝ := fun i => Cd i * ∑ j ∈ Finset.range (i + 1),
    (Klo j + Cg j * Kg j) with hKcF_def
  have hKcF_nn : ∀ i, 0 ≤ KcF i := fun i =>
    mul_nonneg (hCd_nn i) (Finset.sum_nonneg fun j _ =>
      add_nonneg (hKlo_nn j) (mul_nonneg (hCg_nn j) (hKg_nn j)))
  refine ⟨KcF, hKcF_nn, ?_⟩
  intro T₀ hTsymm hball i
  set g₁ : SmoothRiemannianMetric I M := tensorSectionRealizeMetric (I := I) g₀ T₀
    (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball) with hg₁_def
  have hS_nn : 0 ≤ ∑ l ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 :=
    Finset.sum_nonneg fun l _ => sq_nonneg _
  have h1S_nn : (0 : ℝ) ≤ 1 + ∑ l ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 := by linarith
  rcases isEmpty_or_nonempty M with hM | hM
  · have hzero : ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
        (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)‖ = 0 := by
      rw [SmoothCcTensor.norm_def, DifferentialGeometry.Integral.L2.tensorL2Norm,
        DifferentialGeometry.Integral.L2.tensorL2Inner, MeasureTheory.integral_of_isEmpty,
        Real.sqrt_zero]
    rw [hzero]
    have hpos : (0 : ℝ) ≤ KcF i * (1 + ∑ l ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := mul_nonneg (hKcF_nn i) h1S_nn
    simpa using hpos
  · have hδ0 : 0 ≤ δ :=
      delta_nonneg_of_ball_gFibreOpBound (I := I) (M := M) g₀ a hR₀ hδ_fibre
    have htie : ∀ (y : M) (v w : TangentSpace I y),
        g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₀ y v w := by
      intro y v w
      rw [hg₁_def]
      exact tensorSectionRealizeMetric_inner (I := I) g₀ T₀
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball) y v w
    have hPball : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤ B := by
      intro j hj
      have hsum := hC2 T₀
      have hcast : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + 2 : ℕ) : ℝ) T₀‖ =
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ :=
        smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
      rw [hcast] at hsum
      have hsumB : ∑ l ∈ Finset.range (a + 2 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ≤ B := by
        rw [hB_def]
        exact le_trans hsum (mul_le_mul_of_nonneg_left hball hC2_nn)
      have hsingle : ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤
          ∑ l ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ :=
        Finset.single_le_sum
          (f := fun l => ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖)
          (fun l _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
      exact le_trans hsingle hsumB
    have hint_slot : ∀ j : ℕ, MeasureTheory.Integrable
        (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 2 2 j
            (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
      fun j => integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 2 (2 + j) _
    have hL2trans : ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
        (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
        Cd i * ∑ j ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 := by
      have hF_int : MeasureTheory.Integrable
          (fun x => Cd i * ∑ j ∈ Finset.range (i + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 2 2 j
                (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x))
          (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
        (MeasureTheory.integrable_finset_sum _ (fun j _ => hint_slot j)).const_mul (Cd i)
      have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀
        (2 + 2) (2 + i)
        (iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
          (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁))
        (fun x => Cd i * ∑ j ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 2 2 j
              (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x))
        hF_int (fun x => hCd g₁ i x)
      refine le_trans hkey ?_
      rw [MeasureTheory.integral_const_mul]
      refine mul_le_mul_of_nonneg_left ?_ (hCd_nn i)
      rw [MeasureTheory.integral_finset_sum _ (fun j _ => hint_slot j)]
      refine Finset.sum_le_sum fun j _ => ?_
      have hbr := tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M)
        g₀ 2 (2 + j) (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁))
      rw [← SmoothCcTensor.norm_def] at hbr
      exact le_of_eq hbr.symm
    have hslot : ∀ j : ℕ, j ≤ i →
        ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 ≤
          (Klo j + Cg j * Kg j) * (1 + ∑ l ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by
      intro j hj
      have h1S_ge : (1 : ℝ) ≤ 1 + ∑ l ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 := by linarith
      rcases le_or_gt j a with hja | hja
      · have hlo := hKlo g₁ T₀ hδ_le (hδ_fibre T₀ hball) htie hPball j hja
        calc ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2
            ≤ Klo j := hlo
          _ = Klo j * 1 := (mul_one _).symm
          _ ≤ Klo j * (1 + ∑ l ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) :=
            mul_le_mul_of_nonneg_left h1S_ge (hKlo_nn j)
          _ ≤ (Klo j + Cg j * Kg j) * (1 + ∑ l ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by
            refine mul_le_mul_of_nonneg_right ?_ h1S_nn
            exact le_add_of_nonneg_right (mul_nonneg (hCg_nn j) (hKg_nn j))
      · have hpt : ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 2 2 j
                (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) ≤
            Cg j * ∑ n' ∈ Finset.range (j + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n' j,
                ∏ m : Fin n',
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x) :=
          fun x => hCg g₁ T₀ htie hδ_le hδ0 (hδ_fibre T₀ hball) j x
        have hcont_grid : Continuous (fun x : M =>
            ∑ n' ∈ Finset.range (j + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n' j,
                ∏ m : Fin n',
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x)) := by
          refine continuous_finset_sum _ fun n' _ => continuous_finset_sum _ fun e _ =>
            continuous_finset_prod _ fun m _ => ?_
          have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M)
            (iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀)
          refine hc.congr fun x => ?_
          rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x),
            ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M)
              (iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀) x]
        have hint_grid : MeasureTheory.Integrable
            (fun x : M => ∑ n' ∈ Finset.range (j + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n' j,
                ∏ m : Fin n',
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
          integrable_of_continuous_compactSpace (I := I) (M := M) g₀ hcont_grid
        have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀
          2 (2 + j)
          (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁))
          (fun x => Cg j * ∑ n' ∈ Finset.range (j + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n' j,
              ∏ m : Fin n',
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x))
          (hint_grid.const_mul (Cg j)) hpt
        have hgridE := hKg T₀ hball j
        have hwin : ∑ l ∈ Finset.range (j + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 ≤
            ∑ l ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (hrsub _ _ (by omega))
            (fun l _ _ => sq_nonneg _)
        calc ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2
            ≤ ∫ x, (Cg j * ∑ n' ∈ Finset.range (j + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n' j,
                  ∏ m : Fin n',
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := hkey
          _ = Cg j * ∫ x, (∑ n' ∈ Finset.range (j + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n' j,
                  ∏ m : Fin n',
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
            rw [MeasureTheory.integral_const_mul]
          _ ≤ Cg j * (Kg j * (1 + ∑ l ∈ Finset.range (j + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left hgridE (hCg_nn j)
          _ ≤ Cg j * (Kg j * (1 + ∑ l ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2)) := by
            refine mul_le_mul_of_nonneg_left ?_ (hCg_nn j)
            refine mul_le_mul_of_nonneg_left ?_ (hKg_nn j)
            linarith
          _ = Cg j * Kg j * (1 + ∑ l ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by ring
          _ ≤ (Klo j + Cg j * Kg j) * (1 + ∑ l ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by
            refine mul_le_mul_of_nonneg_right ?_ h1S_nn
            exact le_add_of_nonneg_left (hKlo_nn j)
    calc ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
          (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2
        ≤ Cd i * ∑ j ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 :=
          hL2trans
      _ ≤ Cd i * ∑ j ∈ Finset.range (i + 1),
            ((Klo j + Cg j * Kg j) * (1 + ∑ l ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2)) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj => ?_) (hCd_nn i)
          exact hslot j (by have := Finset.mem_range.mp hj; omega)
      _ = KcF i * (1 + ∑ l ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by
          simp only [hKcF_def]
          rw [← Finset.sum_mul]
          ring

section

open Tensor0SBundle
open DifferentialGeometry.Integral.Measure

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem dscr_iteratedCovGrad_jointSmooth
    (g₀ : SmoothRiemannianMetric I M) (r sIdx i : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r sIdx) (S : Set ℝ)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r sIdx ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r sIdx ℝ E)
        (E := fun z : M => TensorRSSpace r sIdx I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r (sIdx + i) ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r (sIdx + i) ℝ E)
        (E := fun z : M => TensorRSSpace r (sIdx + i) I z) q.1
        ((iteratedCovGrad (I := I) g₀ r sIdx i (Φ q.2)).toSection q.1))
      ((Set.univ : Set M) ×ˢ S) := by
  induction i with
  | zero => exact hjoint
  | succ j ih =>
    exact covGrad_step_jointContMDiffOn (I := I) (M := M) g₀ r (sIdx + j)
      (fun t => iteratedCovGrad (I := I) g₀ r sIdx j (Φ t)) S ih

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem dscr_rfns_jointContinuous
    (g₀ : SmoothRiemannianMetric I M) (r sIdx : ℕ)
    (Ψ : ℝ → SmoothCcTensor g₀ r sIdx) (S : Set ℝ)
    (hSI : Set.Icc (0 : ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r sIdx ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r sIdx ℝ E)
        (E := fun z : M => TensorRSSpace r sIdx I z) q.1 ((Ψ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContinuousOn (fun p : ℝ × M =>
      riemannianFiberNormSq (I := I) (M := M) g₀ r sIdx p.2 ((Ψ p.1).toSection p.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) := by
  have hIccprod : (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) ⊆
      (fun p : ℝ × M => (p.2, p.1)) ⁻¹' ((Set.univ : Set M) ×ˢ S) := by
    rintro ⟨t, x⟩ ⟨ht, -⟩
    exact ⟨Set.mem_univ _, hSI ht⟩
  have hswapCont : Continuous (fun p : ℝ × M => (p.2, p.1)) := by fun_prop
  have hv : ContinuousOn
      (fun p : ℝ × M => TotalSpace.mk' (TensorRSModel r sIdx ℝ E)
        (E := fun z : M => TensorRSSpace r sIdx I z) p.2 ((Ψ p.1).toSection p.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) := by
    refine (hjoint.continuousOn.comp hswapCont.continuousOn hIccprod).congr ?_
    rintro ⟨t, x⟩ -
    rfl
  have hψ : ContinuousOn
      (fun p : ℝ × M => TotalSpace.mk'
        (TensorRSModel r sIdx ℝ E →L[ℝ] TensorRSModel r sIdx ℝ E →L[ℝ] ℝ)
        (E := fun x : M => TensorRSSpace r sIdx I x →L[ℝ] TensorRSSpace r sIdx I x →L[ℝ] ℝ)
        p.2
        (DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
          (I := I) (M := M) g₀ r sIdx p.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) :=
    ((DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorRSRiemannianInnerCLM_continuous
      (I := I) (M := M) g₀ r sIdx).comp continuous_snd).continuousOn
  have happ : ContinuousOn
      (fun p : ℝ × M => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) p.2
        (DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
          (I := I) (M := M) g₀ r sIdx p.2 ((Ψ p.1).toSection p.2) ((Ψ p.1).toSection p.2)))
      (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) :=
    ContinuousOn.clm_bundle_apply₂ (F₁ := TensorRSModel r sIdx ℝ E)
      (F₂ := TensorRSModel r sIdx ℝ E) (F₃ := ℝ) (b := fun p : ℝ × M => p.2) hψ hv hv
  have hscalar : ContinuousOn
      (fun p : ℝ × M =>
        DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
          (I := I) (M := M) g₀ r sIdx p.2 ((Ψ p.1).toSection p.2) ((Ψ p.1).toSection p.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) := by
    intro p hp
    have hp2 := ((FiberBundle.continuousWithinAt_totalSpace ℝ
      (fun p : ℝ × M => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) p.2
        (DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
          (I := I) (M := M) g₀ r sIdx p.2
          ((Ψ p.1).toSection p.2) ((Ψ p.1).toSection p.2)))).mp (happ p hp)).2
    exact hp2
  refine hscalar.congr ?_
  rintro ⟨t, x⟩ -
  simp only
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ r sIdx x
      ((Ψ t).toSection x),
    DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_apply]

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 3200000 in
set_option backward.isDefEq.respectTransparency false in
private theorem dscr_pathIntegralCoeffField_congr
    (g₀ : SmoothRiemannianMetric I M) (r sIdx : ℕ)
    (Ψ₁ Ψ₂ : ℝ → SmoothCcTensor g₀ r sIdx) (S : Set ℝ) (hS : IsOpen S)
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hj₁ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r sIdx ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r sIdx ℝ E)
        (E := fun z : M => TensorRSSpace r sIdx I z) q.1 ((Ψ₁ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (hj₂ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r sIdx ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r sIdx ℝ E)
        (E := fun z : M => TensorRSSpace r sIdx I z) q.1 ((Ψ₂ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (hΨ : Ψ₁ = Ψ₂) :
    pathIntegralCoeffField (I := I) (M := M) g₀ r sIdx Ψ₁ S hS hSI hj₁ =
      pathIntegralCoeffField (I := I) (M := M) g₀ r sIdx Ψ₂ S hS hSI hj₂ := by
  subst hΨ
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rfl

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 3200000 in
set_option backward.isDefEq.respectTransparency false in
private theorem dscr_iteratedCovGrad_pathIntegral_comm
    (g₀ : SmoothRiemannianMetric I M) (r sIdx i : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r sIdx) (S : Set ℝ) (hS : IsOpen S)
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r sIdx ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r sIdx ℝ E)
        (E := fun z : M => TensorRSSpace r sIdx I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (hji : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r (sIdx + i) ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r (sIdx + i) ℝ E)
        (E := fun z : M => TensorRSSpace r (sIdx + i) I z) q.1
        ((iteratedCovGrad (I := I) g₀ r sIdx i (Φ q.2)).toSection q.1))
      ((Set.univ : Set M) ×ˢ S)) :
    iteratedCovGrad (I := I) g₀ r sIdx i
        (pathIntegralCoeffField (I := I) (M := M) g₀ r sIdx Φ S hS hSI hjoint) =
      pathIntegralCoeffField (I := I) (M := M) g₀ r (sIdx + i)
        (fun t => iteratedCovGrad (I := I) g₀ r sIdx i (Φ t)) S hS hSI hji := by
  induction i with
  | zero =>
    rw [iteratedCovGrad_zero]
    exact dscr_pathIntegralCoeffField_congr (I := I) g₀ r sIdx Φ
      (fun t => iteratedCovGrad (I := I) g₀ r sIdx 0 (Φ t)) S hS hSI hjoint hji
      (by funext t; rw [iteratedCovGrad_zero])
  | succ j ih =>
    have hjg_j : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r (sIdx + j) ℝ E)) ∞
        (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r (sIdx + j) ℝ E)
          (E := fun z : M => TensorRSSpace r (sIdx + j) I z) q.1
          ((iteratedCovGrad (I := I) g₀ r sIdx j (Φ q.2)).toSection q.1))
        ((Set.univ : Set M) ×ˢ S) :=
      dscr_iteratedCovGrad_jointSmooth (I := I) g₀ r sIdx j Φ S hjoint
    have hjgsucc : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, TensorRSModel r (sIdx + j + 1) ℝ E)) ∞
        (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r (sIdx + j + 1) ℝ E)
          (E := fun z : M => TensorRSSpace r (sIdx + j + 1) I z) q.1
          ((covGrad (I := I) (M := M) g₀ r (sIdx + j)
              (iteratedCovGrad (I := I) g₀ r sIdx j (Φ q.2))).toSection q.1))
        ((Set.univ : Set M) ×ˢ S) :=
      covGrad_step_jointContMDiffOn (I := I) (M := M) g₀ r (sIdx + j)
        (fun t => iteratedCovGrad (I := I) g₀ r sIdx j (Φ t)) S hjg_j
    rw [iteratedCovGrad_succ, ih hjg_j]
    rw [covGrad_pathIntegral_comm (I := I) (M := M) g₀ r (sIdx + j)
      (fun t => iteratedCovGrad (I := I) g₀ r sIdx j (Φ t)) S hS hSI hjg_j hjgsucc]
    exact dscr_pathIntegralCoeffField_congr (I := I) g₀ r (sIdx + j + 1)
      (fun t => covGrad (I := I) (M := M) g₀ r (sIdx + j)
        (iteratedCovGrad (I := I) g₀ r sIdx j (Φ t)))
      (fun t => iteratedCovGrad (I := I) g₀ r sIdx (j + 1) (Φ t)) S hS hSI hjgsucc hji
      (by funext t; rw [iteratedCovGrad_succ])

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
theorem armField_pathIntegral_jetL2_perOrder_le
    (g₀ : SmoothRiemannianMetric I M) (r : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r 2) {δ δ' : ℝ}
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedSmallSet (δ := δ) (δ' := δ'))
    (hSopen : IsOpen (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedSmallSet (δ := δ) (δ' := δ')))
    (hjoint : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r Φ (δ := δ) (δ' := δ'))
    (i : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hΦjet : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ‖iteratedCovGrad (I := I) g₀ r 2 i (Φ s)‖ ^ 2 ≤ B ^ 2) :
    ‖iteratedCovGrad (I := I) g₀ r 2 i
        (pathIntegralCoeffField (I := I) (M := M) g₀ r 2 Φ
          (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hjoint)‖ ^ 2 ≤ B ^ 2 := by
  classical
  set S : Set ℝ :=
    DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedSmallSet
      (δ := δ) (δ' := δ') with hS_def
  have hjointC : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r 2 ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r 2 ℝ E)
        (E := fun z : M => TensorRSSpace r 2 I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S) := hjoint
  have hji : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r (2 + i) ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r (2 + i) ℝ E)
        (E := fun z : M => TensorRSSpace r (2 + i) I z) q.1
        ((iteratedCovGrad (I := I) g₀ r 2 i (Φ q.2)).toSection q.1))
      ((Set.univ : Set M) ×ˢ S) :=
    dscr_iteratedCovGrad_jointSmooth (I := I) g₀ r 2 i Φ S hjointC
  have hcomm : iteratedCovGrad (I := I) g₀ r 2 i
      (pathIntegralCoeffField (I := I) (M := M) g₀ r 2 Φ S hSopen hSI hjoint) =
      pathIntegralCoeffField (I := I) (M := M) g₀ r (2 + i)
        (fun t => iteratedCovGrad (I := I) g₀ r 2 i (Φ t)) S hSopen hSI hji :=
    dscr_iteratedCovGrad_pathIntegral_comm (I := I) g₀ r 2 i Φ S hSopen hSI hjointC hji
  rw [hcomm]
  have hci : ∀ x : M, ContinuousOn (fun t : ℝ =>
      TensorRSSpace.toModel ((iteratedCovGrad (I := I) g₀ r 2 i (Φ t)).toSection x))
      (Set.Icc (0 : ℝ) 1) := by
    intro x
    exact (DifferentialGeometry.PDE.DeTurck.RicciLinearization.jointContMDiff_toModel_continuous_slice
      (I := I) g₀ r (2 + i)
      (fun t => iteratedCovGrad (I := I) g₀ r 2 i (Φ t)) S hji x).mono
      (by rw [← Set.uIcc_of_le (zero_le_one (α := ℝ))]; exact hSI)
  have hri : ContinuousOn (fun p : ℝ × M =>
      riemannianFiberNormSq (I := I) (M := M) g₀ r (2 + i) p.2
        ((iteratedCovGrad (I := I) g₀ r 2 i (Φ p.1)).toSection p.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) :=
    dscr_rfns_jointContinuous (I := I) g₀ r (2 + i)
      (fun t => iteratedCovGrad (I := I) g₀ r 2 i (Φ t)) S
      (by rw [← Set.uIcc_of_le (zero_le_one (α := ℝ))]; exact hSI) hji
  have hL2 := tensorL2NormSq_pathIntegralCoeffField_le_intervalIntegral_normSq
    (I := I) (M := M) g₀ r (2 + i)
    (fun t => iteratedCovGrad (I := I) g₀ r 2 i (Φ t)) S hSopen hSI hji hci hri
  refine le_trans hL2 ?_
  have hmono : (∫ t in (0 : ℝ)..1, ‖iteratedCovGrad (I := I) g₀ r 2 i (Φ t)‖ ^ 2) ≤
      ∫ _t in (0 : ℝ)..1, B ^ 2 := by
    refine intervalIntegral.integral_mono_on (by norm_num) ?_ intervalIntegrable_const ?_
    · have hFcont : ContinuousOn (fun p : ℝ × M =>
          riemannianFiberNormSq (I := I) (M := M) g₀ r (2 + i) p.2
            ((iteratedCovGrad (I := I) g₀ r 2 i (Φ p.1)).toSection p.2))
          (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) := hri
      letI : MeasurableSpace E := borel E
      haveI : BorelSpace E := ⟨rfl⟩
      letI : MeasurableSpace M := borel M
      haveI : BorelSpace M := ⟨rfl⟩
      set μ : Measure M := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ
      haveI : IsFiniteMeasure μ :=
        riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
      have hnormsq : ∀ t : ℝ,
          ‖iteratedCovGrad (I := I) g₀ r 2 i (Φ t)‖ ^ 2 =
            ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ r (2 + i) x
              ((iteratedCovGrad (I := I) g₀ r 2 i (Φ t)).toSection x) ∂μ := by
        intro t
        rw [SmoothCcTensor.norm_def]
        have hsec : (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
              (r := r) (s := 2 + i) (x := x)
              ((iteratedCovGrad (I := I) g₀ r 2 i (Φ t)).toSection x)) =
            (iteratedCovGrad (I := I) g₀ r 2 i (Φ t)).toFun := by
          funext x
          rw [SmoothCcTensor.toFun_apply]
        rw [← hsec,
          tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ r (2 + i)
            (fun x => (iteratedCovGrad (I := I) g₀ r 2 i (Φ t)).toSection x)]
      have hcontInt : ContinuousOn (fun t : ℝ =>
          ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ r (2 + i) x
            ((iteratedCovGrad (I := I) g₀ r 2 i (Φ t)).toSection x) ∂μ)
          (Set.Icc (0 : ℝ) 1) :=
        continuousOn_integral_of_compact_support (μ := μ) isCompact_univ hFcont
          (fun _ x _ hx => absurd (Set.mem_univ x) hx)
      have heq : (fun t : ℝ => ‖iteratedCovGrad (I := I) g₀ r 2 i (Φ t)‖ ^ 2) =
          fun t : ℝ => ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ r (2 + i) x
            ((iteratedCovGrad (I := I) g₀ r 2 i (Φ t)).toSection x) ∂μ := funext hnormsq
      rw [heq]
      exact hcontInt.intervalIntegrable_of_Icc (by norm_num)
    · exact fun t ht => hΦjet t ht
  refine le_trans hmono ?_
  rw [intervalIntegral.integral_const]
  simp



end

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem pje_icg_smul (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (c : ℝ) (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) =
      c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih =>
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih,
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_smul]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma pje_rfns_toSection_smul (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (V : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r s x ((c • V).toSection x) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x (V.toSection x) := by
  rw [show ((c • V).toSection x) = c • (V.toSection x) from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x
      (c • V.toSection x),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (V.toSection x)]
  rw [Tensor0SBundle.TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left,
    tensorInnerPointwise_smul_right]
  ring

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem pje_normSq_icg_reindex_eq (g₀ : SmoothRiemannianMetric I M)
    (R : SmoothCcTensor g₀ 4 2) (ρ : Equiv.Perm (Fin 4)) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 4 2 i
        (reindexCoeffGen (I := I) (M := M) g₀ 4 2 R ρ)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ 4 2 i R‖ ^ 2 := by
  have h1 := tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M)
    g₀ 4 (2 + i)
    (iteratedCovGrad (I := I) g₀ 4 2 i (reindexCoeffGen (I := I) (M := M) g₀ 4 2 R ρ))
  have h2 := tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M)
    g₀ 4 (2 + i) (iteratedCovGrad (I := I) g₀ 4 2 i R)
  rw [← SmoothCcTensor.norm_def] at h1 h2
  rw [h1, h2]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact rfns_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 4 2 R ρ i x

set_option maxHeartbeats 25600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
open DifferentialGeometry.PDE.DeTurck.RicciLinearization in
open DifferentialGeometry.Integral.Measure in
theorem exists_deTurckPhiTotPathIntegral_sub_background_coeffJetEnvelope_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2),
        (∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T₀ x v w = ccTensorBilin (I := I) g₀ T₀ x w v) →
        ∀ (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
              (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
                  (0 : SmoothCcTensor g₀ 0 2)
                  (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
                  (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                  (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                    (by
                      rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                          from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                        tensorHs_norm_smul]
                      simpa using hR₀)) -
                deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) := by
  classical
  have hrsub : ∀ k l : ℕ, k ≤ l → Finset.range k ⊆ Finset.range l :=
    fun k l hkl x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hkl)
  obtain ⟨Kg, hKg_nn, hKg⟩ :=
    exists_gInvDiffSlotCoeff_grid_l2_jetLinear_highOrder (I := I) (M := M) g₀ a ha_super hR₀
  obtain ⟨Cth, hCth_nn, hCth⟩ :=
    traceHessianCoeff_sub_background_jetL2_le_gInvDiffSlotCoeff_jetL2 (I := I) (M := M) g₀
  obtain ⟨Cr, hCr_nn, hCr⟩ :=
    ricciArmPrincipalCoeff_sub_background_jetL2_le_gInvDiffSlotCoeff_jetL2 (I := I) (M := M) g₀
  obtain ⟨C2, hC2_nn, hC2⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general (I := I) (M := M) g₀ (a + 2)
  set B : ℝ := C2 * R₀ with hB_def
  have hB_nn : 0 ≤ B := mul_nonneg hC2_nn hR₀
  obtain ⟨Klo, hKlo_nn, hKlo⟩ :=
    gInvDiffSlotCoeff_perOrder_l2_ballUniform_generic (I := I) (M := M) g₀ a ha_super hB_nn
      (by norm_num : (1 : ℝ) / 3 < 1)
  obtain ⟨Cg, hCg_nn, hCg⟩ :=
    rfns_iteratedCovGrad_gInvDiffSlotCoeff_diagonalProductGrid_le (I := I) (M := M) g₀
      (by norm_num : (1 : ℝ) / 3 < 1)
  set KdevF : ℕ → ℝ := fun i => (6 * Cth i + 12 * Cr i) * ∑ j ∈ Finset.range (i + 1),
    (Klo j + Cg j * Kg j) with hKdevF_def
  have hKdevF_nn : ∀ i, 0 ≤ KdevF i := fun i =>
    mul_nonneg (by have := hCth_nn i; have := hCr_nn i; linarith)
      (Finset.sum_nonneg fun j _ =>
        add_nonneg (hKlo_nn j) (mul_nonneg (hCg_nn j) (hKg_nn j)))
  set cB : ℕ → ℝ := fun i =>
    ‖iteratedCovGrad (I := I) g₀ 4 2 i
      (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ ^ 2 with hcB_def
  have hcB_nn : ∀ i, 0 ≤ cB i := fun i => sq_nonneg _
  refine ⟨fun i => 4 * KdevF i + 6 * cB i,
    fun i => by have := hKdevF_nn i; have := hcB_nn i; linarith, ?_⟩
  intro T₀ hTsymm hball i
  show ‖iteratedCovGrad (I := I) g₀ 4 2 i
      (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
          (0 : SmoothCcTensor g₀ 0 2)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
            (by
              rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                  from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                tensorHs_norm_smul]
              simpa using hR₀)) -
        deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ ^ 2 ≤
    (4 * KdevF i + 6 * cB i) * (1 + ∑ l ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2)
  have hS_nn : 0 ≤ ∑ l ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 :=
    Finset.sum_nonneg fun l _ => sq_nonneg _
  have h1S_nn : (0 : ℝ) ≤ 1 + ∑ l ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 := by linarith
  have h1S_ge : (1 : ℝ) ≤ 1 + ∑ l ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 := by linarith
  rcases isEmpty_or_nonempty M with hM | hM
  · have hzero : ‖iteratedCovGrad (I := I) g₀ 4 2 i
        (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
            (0 : SmoothCcTensor g₀ 0 2)
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
              (by
                rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                    from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                  tensorHs_norm_smul]
                simpa using hR₀)) -
          deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ = 0 := by
      rw [SmoothCcTensor.norm_def, DifferentialGeometry.Integral.L2.tensorL2Norm,
        DifferentialGeometry.Integral.L2.tensorL2Inner, MeasureTheory.integral_of_isEmpty,
        Real.sqrt_zero]
    rw [hzero]
    have hpos : (0 : ℝ) ≤ (4 * KdevF i + 6 * cB i) * (1 + ∑ l ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) :=
      mul_nonneg (by have := hKdevF_nn i; have := hcB_nn i; linarith) h1S_nn
    simpa using hpos
  · have hδ0 : 0 ≤ δ :=
      delta_nonneg_of_ball_gFibreOpBound (I := I) (M := M) g₀ a hR₀ hδ_fibre
    have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
    have hZn : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (0 : SmoothCcTensor g₀ 0 2)‖ ≤ R₀ := by
      rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
          from (zero_smul _ _).symm, smoothCcToTensorHs_smul, tensorHs_norm_smul]
      simpa using hR₀
    have hSI : Set.uIcc (0 : ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ) := by
      rw [Set.uIcc_of_le zero_le_one]
      exact Icc_subset_realizedSmallSet hδ_lt hδ_lt
    have hSopen : IsOpen (realizedSmallSet (δ := δ) (δ' := δ)) := realizedSmallSet_isOpen
    have hj2 := kscr_phiMet_realizedFam_jointSmooth (I := I) (M := M) g₀ g_bg T₀
      (0 : SmoothCcTensor g₀ 0 2) (hδ_fibre T₀ hball) (hδ_fibre 0 hZn)
    have hTball : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤ B := by
      intro j hj
      have hsum := hC2 T₀
      have hcast : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + 2 : ℕ) : ℝ) T₀‖ =
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ :=
        smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
      rw [hcast] at hsum
      have hsumB : ∑ l ∈ Finset.range (a + 2 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ≤ B := by
        rw [hB_def]
        exact le_trans hsum (mul_le_mul_of_nonneg_left hball hC2_nn)
      have hsingle : ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤
          ∑ l ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ :=
        Finset.single_le_sum
          (f := fun l => ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖)
          (fun l _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
      exact le_trans hsingle hsumB
    have hdev : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
              (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
                (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) s) -
            deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ ^ 2 ≤
        KdevF i * (1 + ∑ l ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by
      intro s hs
      set g₁ : SmoothRiemannianMetric I M :=
        realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
          (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) s with hg₁_def
      have hsmem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
        Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
      have htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀
              (convexPerturbation (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) s) y v w := by
        intro y v w
        rw [hg₁_def]
        exact realizedFam_inner_of_mem (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
          (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) hsmem y v w
      have hcp : convexPerturbation (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) s = s • T₀ := by
        simp [convexPerturbation, smul_zero, zero_add]
      have hs0 : (0 : ℝ) ≤ s := hs.1
      have hs1 : s ≤ 1 := hs.2
      have hδP : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀
            (convexPerturbation (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) s)) δ := by
        have h := convexPerturbation_gFibreOpBound (I := I) (M := M) g₀ T₀
          (0 : SmoothCcTensor g₀ 0 2) (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) hs0 hs1
        rwa [show (1 - s) * δ + s * δ = δ by ring] at h
      have hPball : ∀ j : ℕ, j ≤ a + 2 →
          ‖iteratedCovGrad (I := I) g₀ 0 2 j
            (convexPerturbation (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) s)‖ ≤ B := by
        intro j hj
        rw [hcp, pje_icg_smul (I := I) g₀ 0 2 j s T₀, norm_smul]
        have habs : ‖s‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hs0]; exact hs1
        calc ‖s‖ * ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖
            ≤ 1 * B := mul_le_mul habs (hTball j hj) (norm_nonneg _) zero_le_one
          _ = B := one_mul B
      have hslot : ∀ j : ℕ, j ≤ i →
          ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 ≤
            (Klo j + Cg j * Kg j) * (1 + ∑ l ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by
        intro j hj
        rcases le_or_gt j a with hja | hja
        · have hlo := hKlo g₁ (convexPerturbation (I := I) g₀ T₀
            (0 : SmoothCcTensor g₀ 0 2) s) hδ_le hδP htie hPball j hja
          calc ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2
              ≤ Klo j := hlo
            _ = Klo j * 1 := (mul_one _).symm
            _ ≤ Klo j * (1 + ∑ l ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) :=
              mul_le_mul_of_nonneg_left h1S_ge (hKlo_nn j)
            _ ≤ (Klo j + Cg j * Kg j) * (1 + ∑ l ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by
              refine mul_le_mul_of_nonneg_right ?_ h1S_nn
              exact le_add_of_nonneg_right (mul_nonneg (hCg_nn j) (hKg_nn j))
        · have hpt0 : ∀ x : M,
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
                ((iteratedCovGrad (I := I) g₀ 2 2 j
                  (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) ≤
              Cg j * ∑ n' ∈ Finset.range (j + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n' j,
                  ∏ m : Fin n',
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m)
                        (convexPerturbation (I := I) g₀ T₀
                          (0 : SmoothCcTensor g₀ 0 2) s)).toSection x) :=
            fun x => hCg g₁ (convexPerturbation (I := I) g₀ T₀
              (0 : SmoothCcTensor g₀ 0 2) s) htie hδ_le hδ0 hδP j x
          have hgm : ∀ x : M,
              (∑ n' ∈ Finset.range (j + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n' j,
                  ∏ m : Fin n',
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m)
                        (convexPerturbation (I := I) g₀ T₀
                          (0 : SmoothCcTensor g₀ 0 2) s)).toSection x)) ≤
              ∑ n' ∈ Finset.range (j + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n' j,
                  ∏ m : Fin n',
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x) := by
            intro x
            refine Finset.sum_le_sum fun n' _ => Finset.sum_le_sum fun e _ => ?_
            have hfac : ∀ m : Fin n',
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m)
                    (convexPerturbation (I := I) g₀ T₀
                      (0 : SmoothCcTensor g₀ 0 2) s)).toSection x) =
                s ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x) := by
              intro m
              rw [hcp, pje_icg_smul (I := I) g₀ 0 2 (e m) s T₀,
                pje_rfns_toSection_smul (I := I) (M := M) g₀ 0 (2 + e m) s
                  (iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀) x]
            calc (∏ m : Fin n',
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m)
                      (convexPerturbation (I := I) g₀ T₀
                        (0 : SmoothCcTensor g₀ 0 2) s)).toSection x))
                = ∏ m : Fin n', (s ^ 2 *
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x)) :=
                  Finset.prod_congr rfl fun m _ => hfac m
              _ = (s ^ 2) ^ (n' : ℕ) * ∏ m : Fin n',
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x) := by
                  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
                    Fintype.card_fin]
              _ ≤ 1 * ∏ m : Fin n',
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x) := by
                  refine mul_le_mul_of_nonneg_right ?_
                    (Finset.prod_nonneg fun m _ =>
                      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + e m) x _)
                  exact pow_le_one₀ (sq_nonneg s) (by nlinarith)
              _ = ∏ m : Fin n',
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x) := one_mul _
          have hpt : ∀ x : M,
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
                ((iteratedCovGrad (I := I) g₀ 2 2 j
                  (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) ≤
              Cg j * ∑ n' ∈ Finset.range (j + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n' j,
                  ∏ m : Fin n',
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x) :=
            fun x => le_trans (hpt0 x) (mul_le_mul_of_nonneg_left (hgm x) (hCg_nn j))
          have hcont_grid : Continuous (fun x : M =>
              ∑ n' ∈ Finset.range (j + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n' j,
                  ∏ m : Fin n',
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x)) := by
            refine continuous_finset_sum _ fun n' _ => continuous_finset_sum _ fun e _ =>
              continuous_finset_prod _ fun m _ => ?_
            have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M)
              (iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀)
            refine hc.congr fun x => ?_
            rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x),
              ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M)
                (iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀) x]
          have hint_grid : MeasureTheory.Integrable
              (fun x : M => ∑ n' ∈ Finset.range (j + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n' j,
                  ∏ m : Fin n',
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x))
              (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
            integrable_of_continuous_compactSpace (I := I) (M := M) g₀ hcont_grid
          have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀
            2 (2 + j)
            (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁))
            (fun x => Cg j * ∑ n' ∈ Finset.range (j + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n' j,
                ∏ m : Fin n',
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x))
            (hint_grid.const_mul (Cg j)) hpt
          have hgridE := hKg T₀ hball j
          have hwin : ∑ l ∈ Finset.range (j + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 ≤
              ∑ l ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (hrsub _ _ (by omega))
              (fun l _ _ => sq_nonneg _)
          calc ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2
              ≤ ∫ x, (Cg j * ∑ n' ∈ Finset.range (j + 1),
                  ∑ e ∈ Finset.Nat.antidiagonalTuple n' j,
                    ∏ m : Fin n',
                      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x))
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := hkey
            _ = Cg j * ∫ x, (∑ n' ∈ Finset.range (j + 1),
                  ∑ e ∈ Finset.Nat.antidiagonalTuple n' j,
                    ∏ m : Fin n',
                      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T₀).toSection x))
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
                rw [MeasureTheory.integral_const_mul]
            _ ≤ Cg j * (Kg j * (1 + ∑ l ∈ Finset.range (j + 2),
                  ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2)) :=
              mul_le_mul_of_nonneg_left hgridE (hCg_nn j)
            _ ≤ Cg j * (Kg j * (1 + ∑ l ∈ Finset.range (i + 2),
                  ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2)) := by
                refine mul_le_mul_of_nonneg_left ?_ (hCg_nn j)
                refine mul_le_mul_of_nonneg_left ?_ (hKg_nn j)
                linarith
            _ = Cg j * Kg j * (1 + ∑ l ∈ Finset.range (i + 2),
                  ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by ring
            _ ≤ (Klo j + Cg j * Kg j) * (1 + ∑ l ∈ Finset.range (i + 2),
                  ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by
                refine mul_le_mul_of_nonneg_right ?_ h1S_nn
                exact le_add_of_nonneg_left (hKlo_nn j)
      have hslotSum : ∑ j ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 ≤
          (∑ j ∈ Finset.range (i + 1), (Klo j + Cg j * Kg j)) *
            (1 + ∑ l ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by
        calc (∑ j ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2)
            ≤ ∑ j ∈ Finset.range (i + 1), ((Klo j + Cg j * Kg j) *
                (1 + ∑ l ∈ Finset.range (i + 2),
                  ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2)) :=
              Finset.sum_le_sum fun j hj =>
                hslot j (by have := Finset.mem_range.mp hj; omega)
          _ = (∑ j ∈ Finset.range (i + 1), (Klo j + Cg j * Kg j)) *
                (1 + ∑ l ∈ Finset.range (i + 2),
                  ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by
              rw [Finset.sum_mul]
      have hdev_eq :
          deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₁ -
            deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀ =
          reindexCoeffGen (I := I) (M := M) g₀ 4 2
              (traceHessianCoeff (I := I) (M := M) g₀ g₁
                - traceHessianCoeff (I := I) (M := M) g₀ g₀)
              (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA)
            + reindexCoeffGen (I := I) (M := M) g₀ 4 2
              (traceHessianCoeff (I := I) (M := M) g₀ g₁
                - traceHessianCoeff (I := I) (M := M) g₀ g₀)
              (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT)
            - ((ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
                - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)
              + (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
                - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)) := by
        rw [deTurckPhiMetTotal_eq_reindex_decomp_fw (I := I) (M := M) g₀ g_bg g₁,
          deTurckPhiMetTotal_eq_reindex_decomp_fw (I := I) (M := M) g₀ g_bg g₀,
          kscr_reindexCoeffGen_sub (I := I) (M := M) g₀ _ _
            (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA),
          kscr_reindexCoeffGen_sub (I := I) (M := M) g₀ _ _
            (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT)]
        abel
      have hreiA := pje_normSq_icg_reindex_eq (I := I) (M := M) g₀
        (traceHessianCoeff (I := I) (M := M) g₀ g₁
          - traceHessianCoeff (I := I) (M := M) g₀ g₀)
        (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA) i
      have hreiB := pje_normSq_icg_reindex_eq (I := I) (M := M) g₀
        (traceHessianCoeff (I := I) (M := M) g₀ g₁
          - traceHessianCoeff (I := I) (M := M) g₀ g₀)
        (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT) i
      have hth := hCth g₁ i
      have hr := hCr g₁ i
      have htri : ‖iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₁ -
            deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ ≤
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (reindexCoeffGen (I := I) (M := M) g₀ 4 2
              (traceHessianCoeff (I := I) (M := M) g₀ g₁
                - traceHessianCoeff (I := I) (M := M) g₀ g₀)
              (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA))‖ +
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (reindexCoeffGen (I := I) (M := M) g₀ 4 2
              (traceHessianCoeff (I := I) (M := M) g₀ g₁
                - traceHessianCoeff (I := I) (M := M) g₀ g₀)
              (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT))‖ +
          2 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
              - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)‖ := by
        rw [hdev_eq, iteratedCovGrad_sub, iteratedCovGrad_add, iteratedCovGrad_add]
        have h1 := norm_sub_le
          (iteratedCovGrad (I := I) g₀ 4 2 i
            (reindexCoeffGen (I := I) (M := M) g₀ 4 2
              (traceHessianCoeff (I := I) (M := M) g₀ g₁
                - traceHessianCoeff (I := I) (M := M) g₀ g₀)
              (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA)) +
            iteratedCovGrad (I := I) g₀ 4 2 i
              (reindexCoeffGen (I := I) (M := M) g₀ 4 2
                (traceHessianCoeff (I := I) (M := M) g₀ g₁
                  - traceHessianCoeff (I := I) (M := M) g₀ g₀)
                (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT)))
          (iteratedCovGrad (I := I) g₀ 4 2 i
            (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
              - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀) +
           iteratedCovGrad (I := I) g₀ 4 2 i
            (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
              - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀))
        have h2 := norm_add_le
          (iteratedCovGrad (I := I) g₀ 4 2 i
            (reindexCoeffGen (I := I) (M := M) g₀ 4 2
              (traceHessianCoeff (I := I) (M := M) g₀ g₁
                - traceHessianCoeff (I := I) (M := M) g₀ g₀)
              (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA)))
          (iteratedCovGrad (I := I) g₀ 4 2 i
            (reindexCoeffGen (I := I) (M := M) g₀ 4 2
              (traceHessianCoeff (I := I) (M := M) g₀ g₁
                - traceHessianCoeff (I := I) (M := M) g₀ g₀)
              (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT)))
        have h3 := norm_add_le
          (iteratedCovGrad (I := I) g₀ 4 2 i
            (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
              - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀))
          (iteratedCovGrad (I := I) g₀ 4 2 i
            (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
              - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀))
        linarith
      have hsq : ‖iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₁ -
            deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ ^ 2 ≤
          3 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (reindexCoeffGen (I := I) (M := M) g₀ 4 2
              (traceHessianCoeff (I := I) (M := M) g₀ g₁
                - traceHessianCoeff (I := I) (M := M) g₀ g₀)
              (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA))‖ ^ 2 +
          3 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (reindexCoeffGen (I := I) (M := M) g₀ 4 2
              (traceHessianCoeff (I := I) (M := M) g₀ g₁
                - traceHessianCoeff (I := I) (M := M) g₀ g₀)
              (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT))‖ ^ 2 +
          12 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
              - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 := by
        nlinarith [htri,
          norm_nonneg (iteratedCovGrad (I := I) g₀ 4 2 i
            (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₁ -
              deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)),
          norm_nonneg (iteratedCovGrad (I := I) g₀ 4 2 i
            (reindexCoeffGen (I := I) (M := M) g₀ 4 2
              (traceHessianCoeff (I := I) (M := M) g₀ g₁
                - traceHessianCoeff (I := I) (M := M) g₀ g₀)
              (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA))),
          norm_nonneg (iteratedCovGrad (I := I) g₀ 4 2 i
            (reindexCoeffGen (I := I) (M := M) g₀ 4 2
              (traceHessianCoeff (I := I) (M := M) g₀ g₁
                - traceHessianCoeff (I := I) (M := M) g₀ g₀)
              (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT))),
          norm_nonneg (iteratedCovGrad (I := I) g₀ 4 2 i
            (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
              - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)),
          sq_nonneg (‖iteratedCovGrad (I := I) g₀ 4 2 i
              (reindexCoeffGen (I := I) (M := M) g₀ 4 2
                (traceHessianCoeff (I := I) (M := M) g₀ g₁
                  - traceHessianCoeff (I := I) (M := M) g₀ g₀)
                (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA))‖ -
            ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (reindexCoeffGen (I := I) (M := M) g₀ 4 2
                (traceHessianCoeff (I := I) (M := M) g₀ g₁
                  - traceHessianCoeff (I := I) (M := M) g₀ g₀)
                (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT))‖),
          sq_nonneg (‖iteratedCovGrad (I := I) g₀ 4 2 i
              (reindexCoeffGen (I := I) (M := M) g₀ 4 2
                (traceHessianCoeff (I := I) (M := M) g₀ g₁
                  - traceHessianCoeff (I := I) (M := M) g₀ g₀)
                (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA))‖ -
            2 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
                - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)‖),
          sq_nonneg (‖iteratedCovGrad (I := I) g₀ 4 2 i
              (reindexCoeffGen (I := I) (M := M) g₀ 4 2
                (traceHessianCoeff (I := I) (M := M) g₀ g₁
                  - traceHessianCoeff (I := I) (M := M) g₀ g₀)
                (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT))‖ -
            2 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
                - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)‖)]
      calc ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₁ -
              deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ ^ 2
          ≤ 3 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (reindexCoeffGen (I := I) (M := M) g₀ 4 2
                (traceHessianCoeff (I := I) (M := M) g₀ g₁
                  - traceHessianCoeff (I := I) (M := M) g₀ g₀)
                (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA))‖ ^ 2 +
            3 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (reindexCoeffGen (I := I) (M := M) g₀ 4 2
                (traceHessianCoeff (I := I) (M := M) g₀ g₁
                  - traceHessianCoeff (I := I) (M := M) g₀ g₀)
                (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT))‖ ^ 2 +
            12 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
                - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 := hsq
        _ = 6 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (traceHessianCoeff (I := I) (M := M) g₀ g₁
                - traceHessianCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 +
            12 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
                - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 := by
            rw [hreiA, hreiB]; ring
        _ ≤ (6 * Cth i + 12 * Cr i) * (∑ j ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 2 2 j
                (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2) := by
            nlinarith [hth, hr]
        _ ≤ (6 * Cth i + 12 * Cr i) * ((∑ j ∈ Finset.range (i + 1), (Klo j + Cg j * Kg j)) *
              (1 + ∑ l ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left hslotSum
              (by have := hCth_nn i; have := hCr_nn i; linarith)
        _ = KdevF i * (1 + ∑ l ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by
            simp only [hKdevF_def]; ring
    have hbare : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
            (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
              (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) s))‖ ^ 2 ≤
        (2 * KdevF i + 2 * cB i) * (1 + ∑ l ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by
      intro s hs
      have hsplit1 : ‖iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
            (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
              (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) s))‖ ≤
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
                (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
                  (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) s) -
              deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ +
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ := by
        have hid : deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
            (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
              (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) s) =
            (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
                (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
                  (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) s) -
              deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀) +
              deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀ := (sub_add_cancel _ _).symm
        calc ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
                (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
                  (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) s))‖
            = ‖iteratedCovGrad (I := I) g₀ 4 2 i
                ((deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
                    (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
                      (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) s) -
                  deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀) +
                  deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ := by rw [← hid]
          _ = ‖iteratedCovGrad (I := I) g₀ 4 2 i
                (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
                    (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
                      (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) s) -
                  deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀) +
                iteratedCovGrad (I := I) g₀ 4 2 i
                  (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ := by
              rw [iteratedCovGrad_add]
          _ ≤ _ := norm_add_le _ _
      have hd := hdev s hs
      have hcBi : cB i = ‖iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ ^ 2 := rfl
      have hcmul : cB i * 1 ≤ cB i * (1 + ∑ l ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h1S_ge (hcB_nn i)
      nlinarith [hsplit1, hd, hcBi, hcmul,
        norm_nonneg (iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
            (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
              (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) s))),
        norm_nonneg (iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
              (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
                (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) s) -
            deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)),
        norm_nonneg (iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)),
        sq_nonneg (‖iteratedCovGrad (I := I) g₀ 4 2 i
            (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
                (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
                  (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) s) -
              deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ -
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖)]
    have hprod2_nn : (0 : ℝ) ≤ (2 * KdevF i + 2 * cB i) * (1 + ∑ l ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) :=
      mul_nonneg (by have := hKdevF_nn i; have := hcB_nn i; linarith) h1S_nn
    have htower := armField_pathIntegral_jetL2_perOrder_le (I := I) (M := M) g₀ 4
      (fun s => deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
        (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
          (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) s))
      hSI hSopen hj2 i
      (B := Real.sqrt ((2 * KdevF i + 2 * cB i) * (1 + ∑ l ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2)))
      (Real.sqrt_nonneg _)
      (fun s hs => by rw [Real.sq_sqrt hprod2_nn]; exact hbare s hs)
    rw [Real.sq_sqrt hprod2_nn] at htower
    have hPeq : deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
        (0 : SmoothCcTensor g₀ 0 2)
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
        (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
          (by
            rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
              tensorHs_norm_smul]
            simpa using hR₀)) =
        pathIntegralCoeffField (I := I) (M := M) g₀ 4 2
          (fun s => deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
            (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
              (hδ_fibre T₀ hball) (hδ_fibre 0 hZn) s))
          (realizedSmallSet (δ := δ) (δ' := δ)) hSopen hSI hj2 := rfl
    have htower' : ‖iteratedCovGrad (I := I) g₀ 4 2 i
        (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
          (0 : SmoothCcTensor g₀ 0 2)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
            (by
              rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                  from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                tensorHs_norm_smul]
              simpa using hR₀)))‖ ^ 2 ≤
        (2 * KdevF i + 2 * cB i) * (1 + ∑ l ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) := by
      rw [hPeq]; exact htower
    have hsplit : ‖iteratedCovGrad (I := I) g₀ 4 2 i
        (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
            (0 : SmoothCcTensor g₀ 0 2)
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
              (by
                rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                    from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                  tensorHs_norm_smul]
                simpa using hR₀)) -
          deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ ^ 2 ≤
        2 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
            (0 : SmoothCcTensor g₀ 0 2)
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
              (by
                rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                    from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                  tensorHs_norm_smul]
                simpa using hR₀)))‖ ^ 2 +
        2 * cB i := by
      have h := norm_sub_le
        (iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
            (0 : SmoothCcTensor g₀ 0 2)
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
              (by
                rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                    from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                  tensorHs_norm_smul]
                simpa using hR₀))))
        (iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀))
      rw [← iteratedCovGrad_sub] at h
      have hcBi : cB i = ‖iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ ^ 2 := rfl
      nlinarith [h,
        norm_nonneg (iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
              (0 : SmoothCcTensor g₀ 0 2)
              (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
              (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
              (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                (by
                  rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                      from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                    tensorHs_norm_smul]
                  simpa using hR₀)) -
            deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)),
        norm_nonneg (iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
            (0 : SmoothCcTensor g₀ 0 2)
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
              (by
                rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                    from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                  tensorHs_norm_smul]
                simpa using hR₀)))),
        norm_nonneg (iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)),
        sq_nonneg (‖iteratedCovGrad (I := I) g₀ 4 2 i
            (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
              (0 : SmoothCcTensor g₀ 0 2)
              (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
              (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
              (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                (by
                  rw [show (0 : SmoothCcTensor g₀ 0 2) =
                      (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                      from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                    tensorHs_norm_smul]
                  simpa using hR₀)))‖ -
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖)]
    have hcmul : cB i * 1 ≤ cB i * (1 + ∑ l ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2) :=
      mul_le_mul_of_nonneg_left h1S_ge (hcB_nn i)
    nlinarith [hsplit, htower', hcmul, hKdevF_nn i, hcB_nn i, h1S_nn, hS_nn]

theorem exists_deTurckPhiTotPathIntegral_sub_background_sub_principalCometricCoeff_coeffJetEnvelope_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2),
        (∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T₀ x v w = ccTensorBilin (I := I) g₀ T₀ x w v) →
        ∀ (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
              (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
                  (0 : SmoothCcTensor g₀ 0 2)
                  (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
                  (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                  (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                    (by
                      rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                          from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                        tensorHs_norm_smul]
                      simpa using hR₀)) -
                deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀ -
                deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
                  (tensorSectionRealizeMetric (I := I) g₀ T₀
                    (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                    (hδ_fibre T₀ hball)))‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) := by
  classical
  obtain ⟨K1, hK1_nn, h1⟩ :=
    exists_deTurckPhiTotPathIntegral_sub_background_coeffJetEnvelope_le
      (I := I) (M := M) g₀ g_bg a ha_super hR₀ hδ_le hδ_fibre
  obtain ⟨K2, hK2_nn, h2⟩ :=
    exists_deTurckPrincipalCometricCoeff_realize_coeffJetEnvelope_le
      (I := I) (M := M) g₀ g_bg a ha_super hR₀ hδ_le hδ_fibre
  refine ⟨fun i => 2 * K1 i + 2 * K2 i,
    fun i => by have := hK1_nn i; have := hK2_nn i; linarith,
    fun T₀ hTsymm hball i => ?_⟩
  have hsub := iteratedCovGrad_sub (I := I) g₀ (2 + 2) 2 i
    (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
        (0 : SmoothCcTensor g₀ 0 2)
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
        (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
          (by
            rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
              tensorHs_norm_smul]
            simpa using hR₀)) -
      deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)
    (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
      (tensorSectionRealizeMetric (I := I) g₀ T₀
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
        (hδ_fibre T₀ hball)))
  rw [show (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
        (0 : SmoothCcTensor g₀ 0 2)
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
        (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
          (by
            rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
              tensorHs_norm_smul]
            simpa using hR₀)) -
      deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀ -
      deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
        (tensorSectionRealizeMetric (I := I) g₀ T₀
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre T₀ hball))) =
    (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
        (0 : SmoothCcTensor g₀ 0 2)
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
        (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
          (by
            rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
              tensorHs_norm_smul]
            simpa using hR₀)) -
      deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀) -
      deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
        (tensorSectionRealizeMetric (I := I) g₀ T₀
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre T₀ hball)) from rfl, hsub]
  have hA := h1 T₀ hTsymm hball i
  have hB := h2 T₀ hTsymm hball i
  set nA := ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
    (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
        (0 : SmoothCcTensor g₀ 0 2)
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
        (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
          (by
            rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
              tensorHs_norm_smul]
            simpa using hR₀)) -
      deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ with hnA
  set nB := ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
    (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
      (tensorSectionRealizeMetric (I := I) g₀ T₀
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
        (hδ_fibre T₀ hball)))‖ with hnB
  have hnA_nn : 0 ≤ nA := by rw [hnA]; exact norm_nonneg _
  have hnB_nn : 0 ≤ nB := by rw [hnB]; exact norm_nonneg _
  have hn : ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
      (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
          (0 : SmoothCcTensor g₀ 0 2)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
            (by
              rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                  from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                tensorHs_norm_smul]
              simpa using hR₀)) -
        deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀) -
      iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
        (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
          (tensorSectionRealizeMetric (I := I) g₀ T₀
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre T₀ hball)))‖ ≤ nA + nB :=
    norm_sub_le _ _
  have hsq : ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
      (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
          (0 : SmoothCcTensor g₀ 0 2)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
            (by
              rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                  from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                tensorHs_norm_smul]
              simpa using hR₀)) -
        deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀) -
      iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
        (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
          (tensorSectionRealizeMetric (I := I) g₀ T₀
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre T₀ hball)))‖ ^ 2 ≤ 2 * nA ^ 2 + 2 * nB ^ 2 := by
    have hlhs_nn : (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
        (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
            (0 : SmoothCcTensor g₀ 0 2)
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
              (by
                rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                    from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                  tensorHs_norm_smul]
                simpa using hR₀)) -
          deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀) -
        iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
          (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
            (tensorSectionRealizeMetric (I := I) g₀ T₀
              (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
              (hδ_fibre T₀ hball)))‖ := norm_nonneg _
    nlinarith [sq_nonneg (nA - nB), mul_le_mul hn hn hlhs_nn (by linarith : (0:ℝ) ≤ nA + nB)]
  refine le_trans hsq ?_
  have hSig_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 := by positivity
  nlinarith [hA, hB, hSig_nn, hK1_nn i, hK2_nn i]

theorem exists_deTurckPhiTotPathIntegral_sub_background_sub_principalCometricCoeff_fibreSmall_coeffJetEnvelope
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ εCD : ℝ, 0 ≤ εCD ∧
      (0 ≤ δ → εCD ≤ 3 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) ∧
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2),
        (∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T₀ x v w = ccTensorBilin (I := I) g₀ T₀ x w v) →
        ∀ (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) 2 x
            ((deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
                  (0 : SmoothCcTensor g₀ 0 2)
                  (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
                  (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                  (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                    (by
                      rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                          from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                        tensorHs_norm_smul]
                      simpa using hR₀)) -
                deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀ -
                deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
                  (tensorSectionRealizeMetric (I := I) g₀ T₀
                    (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                    (hδ_fibre T₀ hball))).toSection x) ≤ εCD ^ 2) ∧
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i
              (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
                  (0 : SmoothCcTensor g₀ 0 2)
                  (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
                  (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                  (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                    (by
                      rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                          from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                        tensorHs_norm_smul]
                      simpa using hR₀)) -
                deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀ -
                deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
                  (tensorSectionRealizeMetric (I := I) g₀ T₀
                    (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                    (hδ_fibre T₀ hball)))‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) := by
  classical
  obtain ⟨εCD, hεCD_nn, hεCD_cap, hsup⟩ :=
    exists_deTurckPhiTotPathIntegral_sub_background_sub_principalCometricCoeff_fibreSup_le
      (I := I) (M := M) g₀ g_bg a ha_super hR₀ hδ_le hδ_fibre
  obtain ⟨Kc, hKc_nn, henv⟩ :=
    exists_deTurckPhiTotPathIntegral_sub_background_sub_principalCometricCoeff_coeffJetEnvelope_le
      (I := I) (M := M) g₀ g_bg a ha_super hR₀ hδ_le hδ_fibre
  exact ⟨εCD, hεCD_nn, hεCD_cap, Kc, hKc_nn, fun T₀ hTsymm hball =>
    ⟨hsup T₀ hTsymm hball, henv T₀ hTsymm hball⟩⟩

set_option maxHeartbeats 1000000 in
theorem exists_deTurckSmoothRemainderDiff_sub_principalCometricArm_threeArmAppCc_endpointResidual_coeffJetEnvelope
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ εCr : ℝ, 0 ≤ εCr ∧
      (0 ≤ δ → εCr ≤ 19 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) ∧
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
    ∃ εa : ℝ, 0 ≤ εa ∧
      2 * Real.sqrt (Module.finrank ℝ E) * εa ≤
        32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
          28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 ∧
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2),
        (∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T₀ x v w = ccTensorBilin (I := I) g₀ T₀ x w v) →
        ∀ (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ∃ (C₀ : SmoothCcTensor g₀ (2 + 0) 2) (C₁ : SmoothCcTensor g₀ (2 + 1) 2)
          (C₂r : SmoothCcTensor g₀ (2 + 2) 2),
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
                    simpa using hR₀)) -
              deTurckPrincipalCometricArm (I := I) (M := M) g₀
                (tensorSectionRealizeMetric (I := I) g₀ T₀
                  (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                  (hδ_fibre T₀ hball)) T₀) =
            appCc (I := I) (M := M) g₀ (2 + 0) 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 T₀) +
              appCc (I := I) (M := M) g₀ (2 + 1) 2 C₁ (iteratedCovGrad (I := I) g₀ 0 2 1 T₀) +
              appCc (I := I) (M := M) g₀ (2 + 2) 2
                ((deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
                      (0 : SmoothCcTensor g₀ 0 2)
                      (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
                      (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                      (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                        (by
                          rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                              from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                            tensorHs_norm_smul]
                          simpa using hR₀)) -
                    deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀ -
                    deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
                      (tensorSectionRealizeMetric (I := I) g₀ T₀
                        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                        (hδ_fibre T₀ hball))) + C₂r)
                (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) 2 x (C₂r.toSection x) ≤
              εCr ^ 2) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 0) 2 x (C₀.toSection x) ≤
              Λ ^ 2) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 1) 2 x (C₁.toSection x) ≤
              Λ ^ 2) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
                εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g₀ (2 + 1) 2 i C₁‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i C₂r‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) := by
  classical
  obtain ⟨εCr, hεCr_nn, hεCr_cap, Kc1, hKc1_nn, εar, hεar_nn, hεar_cap, Λ₁, hΛ₁_nn, harm⟩ :=
    exists_deTurckRHSArmDiff_zero_canonicalTop_curvatureRefold_coeffSup_jetEnvelope_of_symm
      (I := I) (M := M) g₀ g_bg a ha_super hR₀ hδ_le hδ_fibre
  obtain ⟨K₀, hK₀fold⟩ :=
    exists_deTurckPhiMetTotal_background_curvatureFold_of_symm (I := I) (M := M) g₀ g_bg
  obtain ⟨ΛK, hΛK_nn, hΛK⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 2 K₀
  have hεa_cap : 2 * Real.sqrt (Module.finrank ℝ E) * ((3 : ℝ) / 2 * εar) ≤
      32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
        28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 := by
    calc 2 * Real.sqrt (Module.finrank ℝ E) * ((3 : ℝ) / 2 * εar)
        = 3 * Real.sqrt (Module.finrank ℝ E) * εar := by ring
      _ ≤ 32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
          28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 := hεar_cap
  refine ⟨εCr, hεCr_nn, hεCr_cap,
    fun i => 2 * Kc1 i + 2 * ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i K₀‖ ^ 2,
    fun i => add_nonneg (mul_nonneg (by norm_num) (hKc1_nn i)) (by positivity),
    (3 : ℝ) / 2 * εar, by linarith, hεa_cap,
    Real.sqrt (2 * Λ₁ ^ 2 + 2 * ΛK) + Λ₁,
    add_nonneg (Real.sqrt_nonneg _) hΛ₁_nn,
    fun T₀ hTsymm hball => ?_⟩
  obtain ⟨C₀k, C₁k, C₂r, hidArm, hC₀sup, hC₁sup, hC₂rsup, hC₀env, hC₁env, hC₂renv⟩ :=
    harm T₀ hTsymm hball
  have hsqA : Real.sqrt (2 * Λ₁ ^ 2 + 2 * ΛK) ^ 2 = 2 * Λ₁ ^ 2 + 2 * ΛK :=
    Real.sq_sqrt (by nlinarith [hΛ₁_nn, hΛK_nn])
  refine ⟨C₀k + K₀, C₁k, C₂r, ?_, hC₂rsup, ?_, ?_, ?_, ?_, ?_⟩
  · have h884 := deTurckSmoothRemainderDiff_eq_armDiff_sub_connLapDiff (I := I) g₀ g_bg T₀
      (0 : SmoothCcTensor g₀ 0 2)
      (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
      (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
      (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
        (by
              rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                  from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                tensorHs_norm_smul]
              simpa using hR₀))
    rw [sub_zero] at h884
    have hidArm' : deTurckRHSArmG0 (I := I) g₀ g_bg T₀
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball) -
        deTurckRHSArmG0 (I := I) g₀ g_bg (0 : SmoothCcTensor g₀ 0 2)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
            (by
              rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                  from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                tensorHs_norm_smul]
              simpa using hR₀)) =
        appCc (I := I) (M := M) g₀ (2 + 0) 2 C₀k (iteratedCovGrad (I := I) g₀ 0 2 0 T₀) +
          appCc (I := I) (M := M) g₀ (2 + 1) 2 C₁k (iteratedCovGrad (I := I) g₀ 0 2 1 T₀) +
          appCc (I := I) (M := M) g₀ (2 + 2) 2
            (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
              (0 : SmoothCcTensor g₀ 0 2)
              (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
              (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
              (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                (by
              rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                  from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                tensorHs_norm_smul]
              simpa using hR₀)))
            (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) +
          appCc (I := I) (M := M) g₀ (2 + 2) 2 C₂r (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) :=
      hidArm
    have hfold := hK₀fold T₀ hTsymm
    have hfold' : appCc (I := I) (M := M) g₀ (2 + 2) 2
          (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)
          (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) -
        appCc (I := I) (M := M) g₀ (2 + 2) 2
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
            (I := I) (M := M) g₀ g₀)
          (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) =
        appCc (I := I) (M := M) g₀ (2 + 0) 2 K₀ (iteratedCovGrad (I := I) g₀ 0 2 0 T₀) := by
      rw [← appCc_sub_left]
      exact hfold
    have hlift : rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀ =
        appCc (I := I) (M := M) g₀ (2 + 2) 2
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
            (I := I) (M := M) g₀ g₀)
          (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) := by
      apply smoothCcTensor_ext_of_unitModel
      intro x
      apply ContinuousMultilinearMap.ext
      intro v
      exact
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.rawTensorConnLapSmooth_eq_appCc_cometricDoubleTrace
          (I := I) (M := M) g₀ T₀ x v
    have hArm : deTurckPrincipalCometricArm (I := I) (M := M) g₀
        (tensorSectionRealizeMetric (I := I) g₀ T₀
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre T₀ hball)) T₀ =
        appCc (I := I) (M := M) g₀ (2 + 2) 2
          (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
            (tensorSectionRealizeMetric (I := I) g₀ T₀
              (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
              (hδ_fibre T₀ hball)))
          (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) := rfl
    have hPCC : deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
        (tensorSectionRealizeMetric (I := I) g₀ T₀
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre T₀ hball)) =
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
          (I := I) (M := M) g₀
          (tensorSectionRealizeMetric (I := I) g₀ T₀
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre T₀ hball)) -
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
          (I := I) (M := M) g₀ g₀ := rfl
    rw [h884, hlift, hArm, hidArm']
    rw [appCc_add_left (I := I) (M := M) g₀ (2 + 0) 2 C₀k K₀
      (iteratedCovGrad (I := I) g₀ 0 2 0 T₀)]
    rw [appCc_add_left (I := I) (M := M) g₀ (2 + 2) 2 _ C₂r
      (iteratedCovGrad (I := I) g₀ 0 2 2 T₀)]
    rw [show (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
          (0 : SmoothCcTensor g₀ 0 2)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
            (by
              rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                  from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                tensorHs_norm_smul]
              simpa using hR₀)) -
        deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀ -
        deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
          (tensorSectionRealizeMetric (I := I) g₀ T₀
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre T₀ hball))) =
      (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
          (0 : SmoothCcTensor g₀ 0 2)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
            (by
              rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                  from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                tensorHs_norm_smul]
              simpa using hR₀)) -
        deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀) -
      deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
        (tensorSectionRealizeMetric (I := I) g₀ T₀
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre T₀ hball)) from rfl]
    rw [appCc_sub_left (I := I) (M := M) g₀ (2 + 2) 2 _
      (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
        (tensorSectionRealizeMetric (I := I) g₀ T₀
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre T₀ hball)))
      (iteratedCovGrad (I := I) g₀ 0 2 2 T₀)]
    rw [appCc_sub_left (I := I) (M := M) g₀ (2 + 2) 2 _
      (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)
      (iteratedCovGrad (I := I) g₀ 0 2 2 T₀)]
    rw [hPCC]
    rw [appCc_sub_left (I := I) (M := M) g₀ (2 + 2) 2 _
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
        (I := I) (M := M) g₀ g₀)
      (iteratedCovGrad (I := I) g₀ 0 2 2 T₀)]
    rw [← hfold']
    abel
  · intro x
    have hsec : ((C₀k + K₀).toSection x) = C₀k.toSection x + K₀.toSection x := by
      rw [SmoothCcTensor.toSection_add]; rfl
    rw [hsec]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ (2 + 0) 2 x _ _) ?_
    have h1 := hC₀sup x
    have h2 := hΛK x
    nlinarith [Real.sqrt_nonneg (2 * Λ₁ ^ 2 + 2 * ΛK), hΛ₁_nn, hsqA]
  · intro x
    have h1 := hC₁sup x
    have hle : Λ₁ ≤ Real.sqrt (2 * Λ₁ ^ 2 + 2 * ΛK) + Λ₁ :=
      le_add_of_nonneg_left (Real.sqrt_nonneg _)
    have := pow_le_pow_left₀ hΛ₁_nn hle 2
    linarith
  · intro i
    have hdist := iteratedCovGrad_add (I := I) g₀ (2 + 0) 2 i C₀k K₀
    rw [hdist]
    have hn := norm_add_le (iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀k)
      (iteratedCovGrad (I := I) g₀ (2 + 0) 2 i K₀)
    have hAB : 0 ≤ ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀k +
        iteratedCovGrad (I := I) g₀ (2 + 0) 2 i K₀‖ := norm_nonneg _
    have htri : ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀k +
          iteratedCovGrad (I := I) g₀ (2 + 0) 2 i K₀‖ ^ 2 ≤
        2 * ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀k‖ ^ 2 +
          2 * ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i K₀‖ ^ 2 := by
      nlinarith [sq_nonneg (‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀k‖ -
        ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i K₀‖),
        mul_le_mul hn hn hAB (by positivity), norm_nonneg
          (iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀k), norm_nonneg
          (iteratedCovGrad (I := I) g₀ (2 + 0) 2 i K₀)]
    refine le_trans htri ?_
    have hD := hC₀env i
    have hSig_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 :=
      Finset.sum_nonneg (fun j _ => sq_nonneg _)
    have hKW : (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i K₀‖ ^ 2 *
        (∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) :=
      mul_nonneg (sq_nonneg _) hSig_nn
    have hεX : (0 : ℝ) ≤ εar ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    nlinarith [hD, hSig_nn, sq_nonneg ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i K₀‖,
      hKc1_nn i, hKW, hεX]
  · intro i
    refine le_trans (hC₁env i) ?_
    have hSig_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 := by
      have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range (i + 2)) =>
        sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖)
      linarith
    refine mul_le_mul_of_nonneg_right ?_ hSig_nn
    have h1 := hKc1_nn i
    have h2 : (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i K₀‖ ^ 2 := sq_nonneg _
    linarith
  · intro i
    refine le_trans (hC₂renv i) ?_
    have hSig_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 := by
      have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range (i + 2)) =>
        sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖)
      linarith
    refine mul_le_mul_of_nonneg_right ?_ hSig_nn
    have h1 := hKc1_nn i
    have h2 : (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i K₀‖ ^ 2 := sq_nonneg _
    linarith

set_option maxHeartbeats 1000000 in
theorem exists_deTurckSmoothRemainderDiff_sub_principalCometricArm_threeArmAppCc_coeffJetEnvelope
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ εC : ℝ, 0 ≤ εC ∧
      (0 ≤ δ → εC ≤ 32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 * (δ / (1 - δ))) ∧
      (0 ≤ δ → εC ≤ 28 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) ∧
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
    ∃ εa : ℝ, 0 ≤ εa ∧
      2 * Real.sqrt (Module.finrank ℝ E) * εa ≤
        32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
          28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 ∧
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2),
        (∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T₀ x v w = ccTensorBilin (I := I) g₀ T₀ x w v) →
        ∀ (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ∃ (C₀ : SmoothCcTensor g₀ (2 + 0) 2) (C₁ : SmoothCcTensor g₀ (2 + 1) 2)
          (C₂ : SmoothCcTensor g₀ (2 + 2) 2),
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
                    simpa using hR₀)) -
              deTurckPrincipalCometricArm (I := I) (M := M) g₀
                (tensorSectionRealizeMetric (I := I) g₀ T₀
                  (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                  (hδ_fibre T₀ hball)) T₀) =
            appCc (I := I) (M := M) g₀ (2 + 0) 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 T₀) +
              appCc (I := I) (M := M) g₀ (2 + 1) 2 C₁ (iteratedCovGrad (I := I) g₀ 0 2 1 T₀) +
              appCc (I := I) (M := M) g₀ (2 + 2) 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) 2 x (C₂.toSection x) ≤
              εC ^ 2) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 0) 2 x (C₀.toSection x) ≤
              Λ ^ 2) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 1) 2 x (C₁.toSection x) ≤
              Λ ^ 2) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
                εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g₀ (2 + 1) 2 i C₁‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i C₂‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) := by
  classical
  obtain ⟨εCD, hεCD_nn, hεCD_cap, KcD, hKcD_nn, hK2⟩ :=
    exists_deTurckPhiTotPathIntegral_sub_background_sub_principalCometricCoeff_fibreSmall_coeffJetEnvelope
      (I := I) (M := M) g₀ g_bg a ha_super hR₀ hδ_le hδ_fibre
  obtain ⟨εCr, hεCr_nn, hεCr_cap, Kc1, hKc1_nn, εa, hεa_nn, hεa_cap, Λ1, hΛ1_nn, hK1⟩ :=
    exists_deTurckSmoothRemainderDiff_sub_principalCometricArm_threeArmAppCc_endpointResidual_coeffJetEnvelope
      (I := I) (M := M) g₀ g_bg a ha_super hR₀ hδ_le hδ_fibre
  have hn1 : 1 ≤ Module.finrank ℝ E :=
    Nat.one_le_iff_ne_zero.mpr (NeZero.ne (Module.finrank ℝ E))
  have hC1 : (1 : ℝ) ≤ deTurckArmFibreConst (Module.finrank ℝ E) :=
    one_le_deTurckArmFibreConst hn1
  refine ⟨Real.sqrt (2 * εCD ^ 2 + 2 * εCr ^ 2), Real.sqrt_nonneg _,
    fun hδ_nn => ?_, fun hδ_nn => ?_,
    fun i => 3 * Kc1 i + 2 * KcD i,
    fun i => by have := hKc1_nn i; have := hKcD_nn i; linarith,
    εa, hεa_nn, hεa_cap,
    Λ1, hΛ1_nn, fun T₀ hTsymm hball => ?_⟩
  · have hδ_lt1 : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)
    have hκ_nn : 0 ≤ δ / (1 - δ) := div_nonneg hδ_nn (by linarith)
    set C : ℝ := deTurckArmFibreConst (Module.finrank ℝ E) with hC_def
    set κ : ℝ := δ / (1 - δ) with hκ_def
    have hd := hεCD_cap hδ_nn
    have hr := hεCr_cap hδ_nn
    have hsq : (2 * εCD ^ 2 + 2 * εCr ^ 2) ≤ (32 * C ^ 2 * κ) ^ 2 := by
      have hεCD_sq : εCD ^ 2 ≤ (3 * C * κ) ^ 2 := by nlinarith
      have hεCr_sq : εCr ^ 2 ≤ (19 * C * κ) ^ 2 := by nlinarith
      have hC2 : (1 : ℝ) ≤ C ^ 2 := by nlinarith
      nlinarith [sq_nonneg (C * κ), sq_nonneg κ]
    calc Real.sqrt (2 * εCD ^ 2 + 2 * εCr ^ 2)
        ≤ Real.sqrt ((32 * C ^ 2 * κ) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = 32 * C ^ 2 * κ := Real.sqrt_sq (by positivity)
      _ = 32 * C ^ 2 * (δ / (1 - δ)) := by rw [hκ_def]
  · have hδ_lt1 : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)
    have hκ_nn : 0 ≤ δ / (1 - δ) := div_nonneg hδ_nn (by linarith)
    have hC_nn : 0 ≤ deTurckArmFibreConst (Module.finrank ℝ E) :=
      deTurckArmFibreConst_nonneg _
    have hd := hεCD_cap hδ_nn
    have hr := hεCr_cap hδ_nn
    have h28_nn : (0 : ℝ) ≤
        28 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) := by positivity
    have hsq : 2 * εCD ^ 2 + 2 * εCr ^ 2 ≤
        (28 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) ^ 2 := by
      nlinarith [hd, hr, hεCD_nn, hεCr_nn, mul_nonneg hC_nn hκ_nn]
    calc Real.sqrt (2 * εCD ^ 2 + 2 * εCr ^ 2)
        ≤ Real.sqrt ((28 * deTurckArmFibreConst (Module.finrank ℝ E) *
            (δ / (1 - δ))) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = 28 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)) :=
          Real.sqrt_sq h28_nn
  obtain ⟨hDsup, hDenv⟩ := hK2 T₀ hTsymm hball
  obtain ⟨C₀, C₁, C₂r, hid, hC₂r_sup, hC₀sup, hC₁sup, hC₀env, hC₁env, hC₂r_env⟩ :=
    hK1 T₀ hTsymm hball
  have hεC_sq : Real.sqrt (2 * εCD ^ 2 + 2 * εCr ^ 2) ^ 2 =
      2 * εCD ^ 2 + 2 * εCr ^ 2 := Real.sq_sqrt (by positivity)
  refine ⟨C₀, C₁,
    (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
        (0 : SmoothCcTensor g₀ 0 2)
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
        (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
          (by
            rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
              tensorHs_norm_smul]
            simpa using hR₀)) -
      deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀ -
      deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
        (tensorSectionRealizeMetric (I := I) g₀ T₀
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre T₀ hball))) + C₂r,
    hid, ?_, hC₀sup, hC₁sup, ?_, ?_, ?_⟩
  · intro x
    rw [hεC_sq]
    have hsec : ((deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
          (0 : SmoothCcTensor g₀ 0 2)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
            (by
              rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                  from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                tensorHs_norm_smul]
              simpa using hR₀)) -
        deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀ -
        deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
          (tensorSectionRealizeMetric (I := I) g₀ T₀
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre T₀ hball))) + C₂r).toSection x =
        (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
          (0 : SmoothCcTensor g₀ 0 2)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
            (by
              rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                  from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                tensorHs_norm_smul]
              simpa using hR₀)) -
        deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀ -
        deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
          (tensorSectionRealizeMetric (I := I) g₀ T₀
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre T₀ hball))).toSection x + C₂r.toSection x := by
      rw [SmoothCcTensor.toSection_add]; rfl
    rw [hsec]
    refine le_trans
      (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ (2 + 2) 2 x _ _) ?_
    have h1 := hDsup x
    have h2 := hC₂r_sup x
    linarith
  · intro i
    refine le_trans (hC₀env i) ?_
    have hSig_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 := by
      have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range (i + 2)) =>
        sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖)
      linarith
    have hmono : Kc1 i * (1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) ≤
        (3 * Kc1 i + 2 * KcD i) * (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) := by
      refine mul_le_mul_of_nonneg_right ?_ hSig_nn
      have := hKc1_nn i; have := hKcD_nn i
      linarith
    linarith
  · intro i
    refine le_trans (hC₁env i) ?_
    have hSig_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 := by
      have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range (i + 2)) =>
        sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖)
      linarith
    refine mul_le_mul_of_nonneg_right ?_ hSig_nn
    have := hKc1_nn i; have := hKcD_nn i
    linarith
  · intro i
    have hdist := iteratedCovGrad_add (I := I) g₀ (2 + 2) 2 i
      (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
          (0 : SmoothCcTensor g₀ 0 2)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
          (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
            (by
              rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                  from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                tensorHs_norm_smul]
              simpa using hR₀)) -
        deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀ -
        deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
          (tensorSectionRealizeMetric (I := I) g₀ T₀
            (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
            (hδ_fibre T₀ hball)))
      C₂r
    rw [hdist]
    have htri : ∀ A B : SmoothCcTensor g₀ (2 + 2) (2 + i),
        ‖A + B‖ ^ 2 ≤ 2 * ‖A‖ ^ 2 + 2 * ‖B‖ ^ 2 := by
      intro A B
      have hn := norm_add_le A B
      have hA := norm_nonneg A
      have hB := norm_nonneg B
      have hAB : 0 ≤ ‖A + B‖ := norm_nonneg _
      nlinarith [sq_nonneg (‖A‖ - ‖B‖), mul_le_mul hn hn hAB (by linarith)]
    refine le_trans (htri _ _) ?_
    have hD := hDenv i
    have hr := hC₂r_env i
    have hSig_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 := by
      have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range (i + 2)) =>
        sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖)
      linarith
    have hKc1i := hKc1_nn i
    nlinarith [hD, hr, hSig_nn]

open DifferentialGeometry.Integral.Measure in
private theorem iteratedCovGrad_comp_l2_sq_eq_rs
    (g₀ : SmoothRiemannianMetric I M) (r s m l : ℕ) (W : SmoothCcTensor g₀ r s) :
    ‖iteratedCovGrad (I := I) g₀ r (s + m) l (iteratedCovGrad (I := I) g₀ r s m W)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ r s (m + l) W‖ ^ 2 := by
  have hbridgeL : ‖iteratedCovGrad (I := I) g₀ r (s + m) l
        (iteratedCovGrad (I := I) g₀ r s m W)‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ r ((s + m) + l) x
        ((iteratedCovGrad (I := I) g₀ r (s + m) l
          (iteratedCovGrad (I := I) g₀ r s m W)).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    rw [SmoothCcTensor.norm_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ r
      ((s + m) + l)
      (iteratedCovGrad (I := I) g₀ r (s + m) l (iteratedCovGrad (I := I) g₀ r s m W))
  have hbridgeR : ‖iteratedCovGrad (I := I) g₀ r s (m + l) W‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ r (s + (m + l)) x
        ((iteratedCovGrad (I := I) g₀ r s (m + l) W).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    rw [SmoothCcTensor.norm_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ r
      (s + (m + l)) (iteratedCovGrad (I := I) g₀ r s (m + l) W)
  rw [hbridgeL, hbridgeR]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  have hrw := rfns_iteratedCovGrad_comp (I := I) (M := M) g₀ r s m l W x
  simpa only [Nat.add_assoc] using hrw

theorem exists_appCc_iteratedCovGrad_l2_coeffJetEnvelope_dataJetWindow_le_of_lowOrder
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) :
    ∃ Cm : ℕ → ℝ, (∀ q, 0 ≤ Cm q) ∧
      ∀ (m : ℕ), m ≤ 1 →
      ∀ (C : SmoothCcTensor g₀ (2 + m) 2) (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i C‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) →
        ∀ q : ℕ, q + (Module.finrank ℝ E / 2 + 3) ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 0 2 q
              (appCc (I := I) (M := M) g₀ (2 + m) 2 C
                (iteratedCovGrad (I := I) g₀ 0 2 m T₀))‖ ≤
            Cm q * Real.sqrt (∑ i ∈ Finset.range (q + 1 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) := by
  classical
  have hrsub : ∀ k l : ℕ, k ≤ l → Finset.range k ⊆ Finset.range l :=
    fun k l hkl x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hkl)
  have hB2 : ∀ m i : ℕ, ∃ Csh : ℝ, 0 ≤ Csh ∧
      ∀ (T : SmoothCcTensor g₀ (2 + m) (2 + i)) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) (2 + i) x (T.toSection x) ≤
          Csh ^ 2 * ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
            ‖iteratedCovGrad (I := I) g₀ (2 + m) (2 + i) j T‖ ^ 2 :=
    fun m i =>
      exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
        (I := I) (M := M) g₀ (2 + m) (2 + i)
  choose Csh2 hCsh2_nn hCsh2 using hB2
  obtain ⟨C2, hC2_nn, hC2⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general (I := I) (M := M) g₀ (a + 2)
  set B : ℝ := C2 * R₀ with hB_def
  have hB_nn : 0 ≤ B := mul_nonneg hC2_nn hR₀
  set Lam : ℕ → ℕ → ℝ := fun m i => (Csh2 m i) ^ 2 *
    ((∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2), Kc (i + j)) * (1 + B ^ 2))
    with hLam_def
  have hLam_nn : ∀ m i, 0 ≤ Lam m i := by
    intro m i
    rw [hLam_def]
    have h1 : 0 ≤ ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2), Kc (i + j) :=
      Finset.sum_nonneg (fun j _ => hKc_nn _)
    have h2 : (0 : ℝ) ≤ 1 + B ^ 2 := by positivity
    exact mul_nonneg (sq_nonneg _) (mul_nonneg h1 h2)
  set D : ℕ → ℕ → ℝ := fun m q => Real.sqrt (appCcGdiag (E := E) q *
    ∑ i ∈ Finset.range (q + 1), Lam m i) * ((q : ℝ) + 1) with hD_def
  have hD_nn : ∀ m q, 0 ≤ D m q := by
    intro m q
    rw [hD_def]
    exact mul_nonneg (Real.sqrt_nonneg _) (by positivity)
  refine ⟨fun q => D 0 q + D 1 q, fun q => add_nonneg (hD_nn 0 q) (hD_nn 1 q), ?_⟩
  intro m hm C T₀ hball henv q hband
  set S : ℝ := ∑ i ∈ Finset.range (q + 1 + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 with hS_def
  have hS_nn : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  set W : SmoothCcTensor g₀ 0 (2 + m) := iteratedCovGrad (I := I) g₀ 0 2 m T₀ with hW_def
  have hball_sq : (∑ i ∈ Finset.range (a + 2 + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) ≤ B ^ 2 := by
    have hsq_le : ∑ i ∈ Finset.range (a + 2 + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 ≤
        (∑ i ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖) ^ 2 := by
      have hnn : ∀ i ∈ Finset.range (a + 2 + 1),
          (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ := fun i _ => norm_nonneg _
      have hstep : ∀ i ∈ Finset.range (a + 2 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 ≤
            ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ *
              (∑ j ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖) := by
        intro i hi
        rw [sq]
        exact mul_le_mul_of_nonneg_left (Finset.single_le_sum hnn hi) (norm_nonneg _)
      refine le_trans (Finset.sum_le_sum hstep) ?_
      rw [← Finset.sum_mul, sq]
    refine le_trans hsq_le ?_
    have hjets : ∑ i ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ≤
        C2 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + 2 : ℕ) : ℝ) T₀‖ := hC2 T₀
    have hcast : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + 2 : ℕ) : ℝ) T₀‖ =
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
    rw [hcast] at hjets
    have hjets2 : ∑ i ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ≤
        B := by
      rw [hB_def]
      exact le_trans hjets (mul_le_mul_of_nonneg_left hball hC2_nn)
    have hsum_nn : 0 ≤ ∑ i ∈ Finset.range (a + 2 + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ :=
      Finset.sum_nonneg (fun i _ => norm_nonneg _)
    exact pow_le_pow_left₀ hsum_nn hjets2 2
  have hCoeff : ∀ i : ℕ, i ≤ q → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) (2 + i) x
        ((iteratedCovGrad (I := I) g₀ (2 + m) 2 i C).toSection x) ≤ Lam m i := by
    intro i hi x
    refine le_trans (hCsh2 m i (iteratedCovGrad (I := I) g₀ (2 + m) 2 i C) x) ?_
    rw [hLam_def]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    have hterm : ∀ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
        ‖iteratedCovGrad (I := I) g₀ (2 + m) (2 + i) j
          (iteratedCovGrad (I := I) g₀ (2 + m) 2 i C)‖ ^ 2 ≤ Kc (i + j) * (1 + B ^ 2) := by
      intro j hj
      rw [iteratedCovGrad_comp_l2_sq_eq_rs (I := I) g₀ (2 + m) 2 i j C]
      refine le_trans (henv (i + j)) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hKc_nn _)
      have hjw : j < Module.finrank ℝ E / 2 + 2 := Finset.mem_range.mp hj
      have hwin : ∑ l ∈ Finset.range (i + j + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 ≤
          ∑ l ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (hrsub _ _ (show i + j + 2 ≤ a + 2 + 1 by omega))
          (fun l _ _ => sq_nonneg _)
      linarith [hball_sq]
    calc ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
          ‖iteratedCovGrad (I := I) g₀ (2 + m) (2 + i) j
            (iteratedCovGrad (I := I) g₀ (2 + m) 2 i C)‖ ^ 2
        ≤ ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2), Kc (i + j) * (1 + B ^ 2) :=
          Finset.sum_le_sum hterm
      _ = (∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2), Kc (i + j)) * (1 + B ^ 2) := by
          rw [← Finset.sum_mul]
  set Cpt : ℝ := Real.sqrt (appCcGdiag (E := E) q *
    ∑ i ∈ Finset.range (q + 1), Lam m i) with hCpt_def
  have hGq_nn : 0 ≤ appCcGdiag (E := E) q := appCcGdiag_nonneg (E := E) q
  have hSumLam_nn : 0 ≤ ∑ i ∈ Finset.range (q + 1), Lam m i :=
    Finset.sum_nonneg (fun i _ => hLam_nn m i)
  have hCpt_nn : 0 ≤ Cpt := Real.sqrt_nonneg _
  have hCpt_sq : Cpt ^ 2 = appCcGdiag (E := E) q * ∑ i ∈ Finset.range (q + 1), Lam m i := by
    rw [hCpt_def]
    exact Real.sq_sqrt (mul_nonneg hGq_nn hSumLam_nn)
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
        ((iteratedCovGrad (I := I) g₀ 0 2 q
          (appCc (I := I) (M := M) g₀ (2 + m) 2 C W)).toSection x) ≤
      Cpt ^ 2 * ∑ l ∈ Finset.range (q + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
          ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l W).toSection x) := by
    intro x
    refine le_trans
      (appCc_iteratedCovGrad_diagonalProductGrid_le (I := I) (M := M) g₀ (2 + m) 2 C W q x) ?_
    rw [hCpt_sq]
    have hb_nn : 0 ≤ ∑ l ∈ Finset.range (q + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
          ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l W).toSection x) :=
      Finset.sum_nonneg (fun l _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ _ _ _ _)
    have hstep : ∀ i ∈ Finset.range (q + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) (2 + i) x
            ((iteratedCovGrad (I := I) g₀ (2 + m) 2 i C).toSection x) *
          (∑ l ∈ Finset.range (q + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
              ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l W).toSection x)) ≤
        Lam m i * ∑ l ∈ Finset.range (q + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l W).toSection x) := by
      intro i hi
      have hi' : i ≤ q := by
        have := Finset.mem_range.mp hi
        omega
      have hinner : (∑ l ∈ Finset.range (q + 1 - i),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l W).toSection x)) ≤
          ∑ l ∈ Finset.range (q + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
              ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l W).toSection x) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (hrsub _ _ (show q + 1 - i ≤ q + 1 by omega))
          (fun l _ _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ _ _ _ _)
      have hinner_nn : 0 ≤ ∑ l ∈ Finset.range (q + 1 - i),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l W).toSection x) :=
        Finset.sum_nonneg (fun l _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ _ _ _ _)
      exact mul_le_mul (hCoeff i hi' x) hinner hinner_nn (hLam_nn m i)
    refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hstep) hGq_nn) ?_
    rw [← Finset.sum_mul, ← mul_assoc]
  have hPTLP := tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum (I := I) (M := M) g₀
    (q + 1) (fun l => (2 + m) + l)
    (fun l => iteratedCovGrad (I := I) g₀ 0 (2 + m) l W)
    (iteratedCovGrad (I := I) g₀ 0 2 q (appCc (I := I) (M := M) g₀ (2 + m) 2 C W))
    Cpt hCpt_nn hpt
  have hWl : ∀ l ∈ Finset.range (q + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖ ≤ Real.sqrt S := by
    intro l hl
    have hl' : l ≤ q := by
      have := Finset.mem_range.mp hl
      omega
    have hsq : ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖ ^ 2 =
        ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) T₀‖ ^ 2 := by
      rw [hW_def]
      exact iteratedCovGrad_comp_l2_sq_eq_rs (I := I) g₀ 0 2 m l T₀
    have hin : ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) T₀‖ ^ 2 ≤ S := by
      rw [hS_def]
      exact Finset.single_le_sum
        (f := fun i => ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2)
        (fun i _ => sq_nonneg _)
        (Finset.mem_range.mpr (show m + l < q + 1 + 1 by omega))
    calc ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖
        = Real.sqrt (‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt (‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) T₀‖ ^ 2) := by rw [hsq]
      _ ≤ Real.sqrt S := Real.sqrt_le_sqrt hin
  have hsumW : ∑ l ∈ Finset.range (q + 1), ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖ ≤
      ((q : ℝ) + 1) * Real.sqrt S := by
    have := Finset.sum_le_card_nsmul (Finset.range (q + 1))
      (fun l => ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖) (Real.sqrt S) hWl
    rw [Finset.card_range, nsmul_eq_mul] at this
    calc ∑ l ∈ Finset.range (q + 1), ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖
        ≤ ((q + 1 : ℕ) : ℝ) * Real.sqrt S := this
      _ = ((q : ℝ) + 1) * Real.sqrt S := by push_cast; ring
  refine le_trans hPTLP ?_
  have hfin : Cpt * (∑ l ∈ Finset.range (q + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖) ≤ Cpt * (((q : ℝ) + 1) * Real.sqrt S) :=
    mul_le_mul_of_nonneg_left hsumW hCpt_nn
  refine le_trans hfin ?_
  have hDm : Cpt * (((q : ℝ) + 1) * Real.sqrt S) = D m q * Real.sqrt S := by
    rw [hD_def, hCpt_def]
    ring
  rw [hDm]
  have hDle : D m q ≤ D 0 q + D 1 q := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hm with h | h
    · rw [h]; have := hD_nn 1 q; linarith
    · rw [h]; have := hD_nn 0 q; linarith
  exact mul_le_mul_of_nonneg_right hDle (Real.sqrt_nonneg _)


open DifferentialGeometry.Integral.Measure in
private theorem iteratedCovGrad_comp_l2_sq_eq
    (g₀ : SmoothRiemannianMetric I M) (m l : ℕ) (W : SmoothCcTensor g₀ 0 2) :
    ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l (iteratedCovGrad (I := I) g₀ 0 2 m W)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) W‖ ^ 2 := by
  have hbridgeL : ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
        (iteratedCovGrad (I := I) g₀ 0 2 m W)‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
        ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l
          (iteratedCovGrad (I := I) g₀ 0 2 m W)).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    rw [SmoothCcTensor.norm_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ ((2 + m) + l)
      (iteratedCovGrad (I := I) g₀ 0 (2 + m) l (iteratedCovGrad (I := I) g₀ 0 2 m W))
  have hbridgeR : ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) W‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (m + l)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (m + l) W).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    rw [SmoothCcTensor.norm_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ (2 + (m + l))
      (iteratedCovGrad (I := I) g₀ 0 2 (m + l) W)
  rw [hbridgeL, hbridgeR]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  have hrw := rfns_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 2 m l W x
  simpa only [Nat.add_assoc] using hrw

open DifferentialGeometry.Integral.Measure in
private theorem iteratedCovGrad_comp_jetSum_le
    (g₀ : SmoothRiemannianMetric I M) (p m : ℕ) (W : SmoothCcTensor g₀ 0 2) :
    (∑ l ∈ Finset.range (p + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l (iteratedCovGrad (I := I) g₀ 0 2 m W)‖ ^ 2) ≤
      ∑ i ∈ Finset.range (p + m + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2 := by
  rw [show (∑ l ∈ Finset.range (p + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l (iteratedCovGrad (I := I) g₀ 0 2 m W)‖ ^ 2) =
      ∑ l ∈ Finset.range (p + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) W‖ ^ 2 from
    Finset.sum_congr rfl (fun l _ => iteratedCovGrad_comp_l2_sq_eq (I := I) g₀ m l W)]
  set f : ℕ → ℝ := fun i => ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2 with hf_def
  have hf_nn : ∀ i, 0 ≤ f i := fun i => sq_nonneg _
  have himg : (Finset.range (p + 1)).image (fun l => m + l) ⊆ Finset.range (p + m + 1) := by
    intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨l, hl, rfl⟩ := hi
    rw [Finset.mem_range] at hl ⊢
    omega
  have hinj : ∀ l₁ ∈ Finset.range (p + 1), ∀ l₂ ∈ Finset.range (p + 1),
      m + l₁ = m + l₂ → l₁ = l₂ := fun l₁ _ l₂ _ h => by omega
  calc (∑ l ∈ Finset.range (p + 1), f (m + l))
      = ∑ i ∈ (Finset.range (p + 1)).image (fun l => m + l), f i :=
        (Finset.sum_image hinj).symm
    _ ≤ ∑ i ∈ Finset.range (p + m + 1), f i :=
        Finset.sum_le_sum_of_subset_of_nonneg himg (fun i _ _ => hf_nn i)

theorem exists_appCc_iteratedCovGrad_l2_coeffJetEnvelope_dataJetWindow_le_of_highOrder
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) (Λ : ℝ) (hΛ_nn : 0 ≤ Λ) :
    ∃ Cm : ℕ → ℝ, (∀ q, 0 ≤ Cm q) ∧
      ∀ (m : ℕ), m ≤ 1 →
      ∀ (C : SmoothCcTensor g₀ (2 + m) 2) (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) 2 x (C.toSection x) ≤ Λ ^ 2) →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i C‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) →
        ∀ q : ℕ, a ≤ q + (Module.finrank ℝ E / 2 + 3) →
          ‖iteratedCovGrad (I := I) g₀ 0 2 q
              (appCc (I := I) (M := M) g₀ (2 + m) 2 C
                (iteratedCovGrad (I := I) g₀ 0 2 m T₀))‖ ≤
            Cm q * Real.sqrt (∑ i ∈ Finset.range (q + 1 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) := by
  classical
  have hrsub : ∀ k l : ℕ, k ≤ l → Finset.range k ⊆ Finset.range l :=
    fun k l hkl x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hkl)
  have hE : ∀ m q : ℕ, ∃ CE : ℝ, 0 ≤ CE ∧
      ∀ (Φ : SmoothCcTensor g₀ (2 + m) 2) (W : SmoothCcTensor g₀ 0 (2 + m)) (ΛΦ ΛW : ℝ),
        0 ≤ ΛΦ → 0 ≤ ΛW →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) 2 x (Φ.toSection x) ≤
          ΛΦ ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x (W.toSection x) ≤
          ΛW ^ 2) →
        ‖iteratedCovGrad (I := I) g₀ 0 2 q
            (appCc (I := I) (M := M) g₀ (2 + m) 2 Φ W)‖ ^ 2 ≤
          CE * (ΛW ^ 2 * ∑ i ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Φ‖ ^ 2
              + ΛΦ ^ 2 * ∑ l ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖ ^ 2) :=
    fun m q => appCc_topOrder_l2_twoArm_mixed_le (I := I) (M := M) g₀ (2 + m) 2 q
  choose CE hCE_nn hCE using hE
  have hB : ∀ m : ℕ, ∃ Csh : ℝ, 0 ≤ Csh ∧
      ∀ (T : SmoothCcTensor g₀ 0 (2 + m)) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x (T.toSection x) ≤
          Csh ^ 2 * ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) j T‖ ^ 2 :=
    fun m =>
      exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
        (I := I) (M := M) g₀ 0 (2 + m)
  choose Csh hCsh_nn hCsh using hB
  obtain ⟨C2, hC2_nn, hC2⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general (I := I) (M := M) g₀ (a + 2)
  set B : ℝ := C2 * R₀ with hB_def
  have hB_nn : 0 ≤ B := mul_nonneg hC2_nn hR₀
  set D : ℕ → ℕ → ℝ := fun m q => Real.sqrt (CE m q *
    ((Csh m) ^ 2 * (∑ i ∈ Finset.range (q + 1), Kc i) * (1 + B ^ 2) + Λ ^ 2)) with hD_def
  have hD_nn : ∀ m q, 0 ≤ D m q := fun m q => Real.sqrt_nonneg _
  refine ⟨fun q => D 0 q + D 1 q, fun q => add_nonneg (hD_nn 0 q) (hD_nn 1 q), ?_⟩
  intro m hm C T₀ hball hsup henv q hband
  set S : ℝ := ∑ i ∈ Finset.range (q + 1 + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 with hS_def
  have hS_nn : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  set W : SmoothCcTensor g₀ 0 (2 + m) := iteratedCovGrad (I := I) g₀ 0 2 m T₀ with hW_def
  set SW : ℝ := ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
    ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) j W‖ ^ 2 with hSW_def
  have hSW_nn : 0 ≤ SW := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  set ΛW : ℝ := Csh m * Real.sqrt SW with hΛW_def
  have hΛW_nn : 0 ≤ ΛW := mul_nonneg (hCsh_nn m) (Real.sqrt_nonneg _)
  have hWsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
      (W.toSection x) ≤ ΛW ^ 2 := by
    intro x
    have h := hCsh m W x
    rw [hΛW_def, mul_pow, Real.sq_sqrt hSW_nn, hSW_def]
    exact h
  have hMain := hCE m q C W Λ ΛW hΛ_nn hΛW_nn hsup hWsup
  have hSW_case : SW ≤ ∑ i ∈ Finset.range (Module.finrank ℝ E / 2 + 1 + m + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 := by
    have h := iteratedCovGrad_comp_jetSum_le (I := I) g₀ (Module.finrank ℝ E / 2 + 1) m T₀
    rw [hSW_def, hW_def]
    exact h
  have hSW_le_S : SW ≤ S := by
    refine le_trans hSW_case ?_
    rw [hS_def]
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (hrsub _ _ (show Module.finrank ℝ E / 2 + 1 + m + 1 ≤ q + 1 + 1 by omega))
      (fun i _ _ => sq_nonneg _)
  have hSW_le_B : SW ≤ B ^ 2 := by
    refine le_trans hSW_case ?_
    have hsub : ∑ i ∈ Finset.range (Module.finrank ℝ E / 2 + 1 + m + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 ≤
        ∑ i ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (hrsub _ _ (show Module.finrank ℝ E / 2 + 1 + m + 1 ≤ a + 2 + 1 by omega))
        (fun i _ _ => sq_nonneg _)
    refine le_trans hsub ?_
    have hsq_le : ∑ i ∈ Finset.range (a + 2 + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 ≤
        (∑ i ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖) ^ 2 := by
      have hnn : ∀ i ∈ Finset.range (a + 2 + 1),
          (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ := fun i _ => norm_nonneg _
      have hstep : ∀ i ∈ Finset.range (a + 2 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2 ≤
            ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ *
              (∑ j ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖) := by
        intro i hi
        rw [sq]
        exact mul_le_mul_of_nonneg_left
          (Finset.single_le_sum hnn hi) (norm_nonneg _)
      refine le_trans (Finset.sum_le_sum hstep) ?_
      rw [← Finset.sum_mul, sq]
    refine le_trans hsq_le ?_
    have hjets : ∑ i ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ≤
        C2 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + 2 : ℕ) : ℝ) T₀‖ := hC2 T₀
    have hcast : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + 2 : ℕ) : ℝ) T₀‖ =
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
    rw [hcast] at hjets
    have hjets2 : ∑ i ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ≤
        B := by
      rw [hB_def]
      exact le_trans hjets (mul_le_mul_of_nonneg_left hball hC2_nn)
    have hsum_nn : 0 ≤ ∑ i ∈ Finset.range (a + 2 + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ :=
      Finset.sum_nonneg (fun i _ => norm_nonneg _)
    exact pow_le_pow_left₀ hsum_nn hjets2 2
  have hSigC : ∑ i ∈ Finset.range (q + 1), ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i C‖ ^ 2 ≤
      (∑ i ∈ Finset.range (q + 1), Kc i) * (1 + S) := by
    have hstep : ∀ i ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i C‖ ^ 2 ≤ Kc i * (1 + S) := by
      intro i hi
      rw [Finset.mem_range] at hi
      refine le_trans (henv i) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hKc_nn i)
      have hwin : ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2 ≤
          S := by
        rw [hS_def]
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (hrsub _ _ (show i + 2 ≤ q + 1 + 1 by omega))
          (fun j _ _ => sq_nonneg _)
      linarith
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [← Finset.sum_mul]
  have hSigW : ∑ l ∈ Finset.range (q + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖ ^ 2 ≤ S := by
    have := iteratedCovGrad_comp_jetSum_le (I := I) g₀ q m T₀
    rw [← hW_def] at this
    refine le_trans this ?_
    rw [hS_def]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (hrsub _ _ (show q + m + 1 ≤ q + 1 + 1 by omega))
      (fun i _ _ => sq_nonneg _)
  have hcore : ‖iteratedCovGrad (I := I) g₀ 0 2 q
      (appCc (I := I) (M := M) g₀ (2 + m) 2 C W)‖ ^ 2 ≤ (D m q) ^ 2 * S := by
    have hΛW_sq : ΛW ^ 2 = (Csh m) ^ 2 * SW := by
      rw [hΛW_def, mul_pow, Real.sq_sqrt hSW_nn]
    have h1 : ΛW ^ 2 * (∑ i ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i C‖ ^ 2) ≤
        (Csh m) ^ 2 * ((∑ i ∈ Finset.range (q + 1), Kc i) * (SW + SW * S)) := by
      rw [hΛW_sq]
      have hKcS_nn : 0 ≤ (∑ i ∈ Finset.range (q + 1), Kc i) :=
        Finset.sum_nonneg (fun i _ => hKc_nn i)
      calc (Csh m) ^ 2 * SW * (∑ i ∈ Finset.range (q + 1),
            ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i C‖ ^ 2)
          ≤ (Csh m) ^ 2 * SW * ((∑ i ∈ Finset.range (q + 1), Kc i) * (1 + S)) := by
            refine mul_le_mul_of_nonneg_left hSigC ?_
            positivity
        _ = (Csh m) ^ 2 * ((∑ i ∈ Finset.range (q + 1), Kc i) * (SW + SW * S)) := by ring
    have h2 : SW + SW * S ≤ (1 + B ^ 2) * S := by
      have ha' : SW * S ≤ B ^ 2 * S := mul_le_mul_of_nonneg_right hSW_le_B hS_nn
      have hb' : SW ≤ S := hSW_le_S
      have : (1 + B ^ 2) * S = S + B ^ 2 * S := by ring
      linarith
    have h3 : (Csh m) ^ 2 * ((∑ i ∈ Finset.range (q + 1), Kc i) * (SW + SW * S)) ≤
        (Csh m) ^ 2 * ((∑ i ∈ Finset.range (q + 1), Kc i) * ((1 + B ^ 2) * S)) := by
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      refine mul_le_mul_of_nonneg_left h2 ?_
      exact Finset.sum_nonneg (fun i _ => hKc_nn i)
    have h4 : Λ ^ 2 * (∑ l ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖ ^ 2) ≤ Λ ^ 2 * S :=
      mul_le_mul_of_nonneg_left hSigW (sq_nonneg _)
    have hD_sq : (D m q) ^ 2 = CE m q *
        ((Csh m) ^ 2 * (∑ i ∈ Finset.range (q + 1), Kc i) * (1 + B ^ 2) + Λ ^ 2) := by
      rw [hD_def]
      refine Real.sq_sqrt ?_
      have hKcS_nn : 0 ≤ ∑ i ∈ Finset.range (q + 1), Kc i :=
        Finset.sum_nonneg (fun i _ => hKc_nn i)
      have h6 : 0 ≤ (Csh m) ^ 2 * (∑ i ∈ Finset.range (q + 1), Kc i) * (1 + B ^ 2) := by
        refine mul_nonneg (mul_nonneg (sq_nonneg _) hKcS_nn) ?_
        have := sq_nonneg B
        linarith
      exact mul_nonneg (hCE_nn m q) (by linarith [sq_nonneg Λ])
    calc ‖iteratedCovGrad (I := I) g₀ 0 2 q
          (appCc (I := I) (M := M) g₀ (2 + m) 2 C W)‖ ^ 2
        ≤ CE m q * (ΛW ^ 2 * ∑ i ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i C‖ ^ 2
            + Λ ^ 2 * ∑ l ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖ ^ 2) := hMain
      _ ≤ CE m q * ((Csh m) ^ 2 * ((∑ i ∈ Finset.range (q + 1), Kc i) * ((1 + B ^ 2) * S))
            + Λ ^ 2 * S) := by
          refine mul_le_mul_of_nonneg_left ?_ (hCE_nn m q)
          have := le_trans h1 h3
          linarith
      _ = (CE m q * ((Csh m) ^ 2 * (∑ i ∈ Finset.range (q + 1), Kc i) * (1 + B ^ 2)
            + Λ ^ 2)) * S := by ring
      _ = (D m q) ^ 2 * S := by rw [hD_sq]
  have hfinal : ‖iteratedCovGrad (I := I) g₀ 0 2 q
      (appCc (I := I) (M := M) g₀ (2 + m) 2 C W)‖ ≤ D m q * Real.sqrt S := by
    have h1 : ‖iteratedCovGrad (I := I) g₀ 0 2 q
        (appCc (I := I) (M := M) g₀ (2 + m) 2 C W)‖ =
        Real.sqrt (‖iteratedCovGrad (I := I) g₀ 0 2 q
          (appCc (I := I) (M := M) g₀ (2 + m) 2 C W)‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    rw [h1]
    refine le_trans (Real.sqrt_le_sqrt hcore) ?_
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (hD_nn m q)]
  refine le_trans hfinal ?_
  have hDle : D m q ≤ D 0 q + D 1 q := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hm with h | h
    · rw [h]; have := hD_nn 1 q; linarith
    · rw [h]; have := hD_nn 0 q; linarith
  exact mul_le_mul_of_nonneg_right hDle (Real.sqrt_nonneg _)


theorem exists_appCc_iteratedCovGrad_l2_coeffJetEnvelope_dataJetWindow_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) (Λ : ℝ) (hΛ_nn : 0 ≤ Λ) :
    ∃ Cm : ℕ → ℝ, (∀ q, 0 ≤ Cm q) ∧
      ∀ (m : ℕ), m ≤ 1 →
      ∀ (C : SmoothCcTensor g₀ (2 + m) 2) (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) 2 x (C.toSection x) ≤ Λ ^ 2) →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i C‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) →
        ∀ q : ℕ,
          ‖iteratedCovGrad (I := I) g₀ 0 2 q
              (appCc (I := I) (M := M) g₀ (2 + m) 2 C
                (iteratedCovGrad (I := I) g₀ 0 2 m T₀))‖ ≤
            Cm q * Real.sqrt (∑ i ∈ Finset.range (q + 1 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) := by
  classical
  obtain ⟨CmA, hCmA_nn, hA⟩ :=
    exists_appCc_iteratedCovGrad_l2_coeffJetEnvelope_dataJetWindow_le_of_lowOrder
      (I := I) (M := M) g₀ a ha_super hR₀ Kc hKc_nn
  obtain ⟨CmB, hCmB_nn, hB⟩ :=
    exists_appCc_iteratedCovGrad_l2_coeffJetEnvelope_dataJetWindow_le_of_highOrder
      (I := I) (M := M) g₀ a ha_super hR₀ Kc hKc_nn Λ hΛ_nn
  refine ⟨fun q => CmA q + CmB q,
    fun q => add_nonneg (hCmA_nn q) (hCmB_nn q), ?_⟩
  intro m hm C T₀ hball hsup henv q
  have hsqrt_nn : 0 ≤ Real.sqrt (∑ i ∈ Finset.range (q + 1 + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) := Real.sqrt_nonneg _
  rcases le_total (q + (Module.finrank ℝ E / 2 + 3)) a with hband | hband
  · refine le_trans (hA m hm C T₀ hball henv q hband) ?_
    have := mul_le_mul_of_nonneg_right
      (show CmA q ≤ CmA q + CmB q by have := hCmB_nn q; linarith) hsqrt_nn
    linarith
  · refine le_trans (hB m hm C T₀ hball hsup henv q hband) ?_
    have := mul_le_mul_of_nonneg_right
      (show CmB q ≤ CmA q + CmB q by have := hCmA_nn q; linarith) hsqrt_nn
    linarith

set_option maxHeartbeats 1000000 in
/-- Jet-window split of the remainder difference minus the principal cometric arm: two small
objects are extracted — the fibre-small `(2+2,2)`-coefficient `C₂` and the arm-zero
`(2+0,2)`-coefficient `C₀` carrying the two-arm jet envelope (naked window plus the
`εa`-rated top arm) — and the residual is the order-one arm, whose jets obey the pure
naked-window bound. The `C₀`-envelope's top arm rides the two-arm correction-field interface,
so consumers transitively depend on `sorryAx` until corr-discharge lands. -/
theorem exists_deTurckSmoothRemainderDiff_sub_principalCometricArm_smallThirdArm_iteratedCovGrad_jet_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ εC : ℝ, 0 ≤ εC ∧
      (0 ≤ δ → εC ≤ 32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 * (δ / (1 - δ))) ∧
      (0 ≤ δ → εC ≤ 28 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) ∧
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
    ∃ εa : ℝ, 0 ≤ εa ∧
      2 * Real.sqrt (Module.finrank ℝ E) * εa ≤
        32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
          28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 ∧
    ∃ Λa : ℝ, 0 ≤ Λa ∧
    ∃ Clow : ℕ → ℝ, (∀ q, 0 ≤ Clow q) ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2)
        (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T₀ x v w = ccTensorBilin (I := I) g₀ T₀ x w v)
        (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ∃ (C₂ : SmoothCcTensor g₀ (2 + 2) 2) (C₀ : SmoothCcTensor g₀ (2 + 0) 2),
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) 2 x (C₂.toSection x) ≤ εC ^ 2) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i C₂‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 0) 2 x (C₀.toSection x) ≤
              Λa ^ 2) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
                εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) ∧
          ∀ q : ℕ,
            ‖iteratedCovGrad (I := I) g₀ 0 2 q
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
                        simpa using hR₀)) -
                  deTurckPrincipalCometricArm (I := I) (M := M) g₀
                    (tensorSectionRealizeMetric (I := I) g₀ T₀
                      (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                      (hδ_fibre T₀ hball)) T₀ -
                  appCc (I := I) (M := M) g₀ (2 + 2) 2 C₂
                    (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) -
                  appCc (I := I) (M := M) g₀ (2 + 0) 2 C₀
                    (iteratedCovGrad (I := I) g₀ 0 2 0 T₀))‖ ≤
              Clow q * Real.sqrt (∑ i ∈ Finset.range (q + 1 + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ ^ 2) := by
  classical
  obtain ⟨εC, hεC_nn, hεC_cap, hεC_cap', Kc, hKc_nn, εa, hεa_nn, hεa_cap, Λ, hΛ_nn, hL1⟩ :=
    exists_deTurckSmoothRemainderDiff_sub_principalCometricArm_threeArmAppCc_coeffJetEnvelope
      (I := I) (M := M) g₀ g_bg a ha_super hR₀ hδ_le hδ_fibre
  obtain ⟨Cm, hCm_nn, hM2⟩ :=
    exists_appCc_iteratedCovGrad_l2_coeffJetEnvelope_dataJetWindow_le
      (I := I) (M := M) g₀ a ha_super hR₀ Kc hKc_nn Λ hΛ_nn
  refine ⟨εC, hεC_nn, hεC_cap, hεC_cap', Kc, hKc_nn, εa, hεa_nn, hεa_cap, Λ, hΛ_nn,
    Cm, hCm_nn, fun T₀ hTsymm hball => ?_⟩
  obtain ⟨C₀, C₁, C₂, hid, hC₂sup, hC₀sup, hC₁sup, hC₀jet, hC₁jet, hC₂jet⟩ :=
    hL1 T₀ hTsymm hball
  refine ⟨C₂, C₀, hC₂sup, hC₂jet, hC₀sup, hC₀jet, fun q => ?_⟩
  have hsplit :
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
                simpa using hR₀)) -
          deTurckPrincipalCometricArm (I := I) (M := M) g₀
            (tensorSectionRealizeMetric (I := I) g₀ T₀
              (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
              (hδ_fibre T₀ hball)) T₀ -
          appCc (I := I) (M := M) g₀ (2 + 2) 2 C₂
            (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) -
          appCc (I := I) (M := M) g₀ (2 + 0) 2 C₀
            (iteratedCovGrad (I := I) g₀ 0 2 0 T₀)) =
        appCc (I := I) (M := M) g₀ (2 + 1) 2 C₁ (iteratedCovGrad (I := I) g₀ 0 2 1 T₀) := by
    rw [sub_eq_iff_eq_add, sub_eq_iff_eq_add, hid]
    abel
  rw [hsplit]
  exact hM2 1 (by omega) C₁ T₀ hball hC₁sup hC₁jet q

set_option maxHeartbeats 1000000 in
/-- Sobolev-scale tame split of the remainder difference minus the principal cometric arm:
the fibre-small `(2+2,2)`-coefficient `C₂` and the arm-zero `(2+0,2)`-coefficient `C₀` (the
latter carrying the two-arm jet envelope) are handed over with their fibre-sup and envelope
rows, and the residual order-one arm obeys the pure one-order-loss tame bound on the spectral
scale. Consumers transitively depend on `sorryAx` via the two-arm correction-field interface
until corr-discharge lands. -/
theorem exists_smoothCcToTensorHs_deTurckSmoothRemainderDiff_sub_principalCometricArm_smallThirdArm_tame_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ εC : ℝ, 0 ≤ εC ∧
      (0 ≤ δ → εC ≤ 32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 * (δ / (1 - δ))) ∧
      (0 ≤ δ → εC ≤ 28 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) ∧
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
    ∃ εa : ℝ, 0 ≤ εa ∧
      2 * Real.sqrt (Module.finrank ℝ E) * εa ≤
        32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
          28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 ∧
    ∃ Λa : ℝ, 0 ≤ Λa ∧
    ∃ Ctame : ℕ → ℝ, (∀ k, 0 ≤ Ctame k) ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2)
        (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T₀ x v w = ccTensorBilin (I := I) g₀ T₀ x w v)
        (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ∃ (C₂ : SmoothCcTensor g₀ (2 + 2) 2) (C₀ : SmoothCcTensor g₀ (2 + 0) 2),
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) 2 x (C₂.toSection x) ≤ εC ^ 2) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i C₂‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 0) 2 x (C₀.toSection x) ≤
              Λa ^ 2) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
                εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) ∧
          ∀ k : ℕ,
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
                        simpa using hR₀)) -
                  deTurckPrincipalCometricArm (I := I) (M := M) g₀
                    (tensorSectionRealizeMetric (I := I) g₀ T₀
                      (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                      (hδ_fibre T₀ hball)) T₀ -
                  appCc (I := I) (M := M) g₀ (2 + 2) 2 C₂
                    (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) -
                  appCc (I := I) (M := M) g₀ (2 + 0) 2 C₀
                    (iteratedCovGrad (I := I) g₀ 0 2 0 T₀))‖ ≤
              Ctame k * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) T₀‖ := by
  classical
  obtain ⟨εC, hεC_nn, hεC_cap, hεC_cap', Kc, hKc_nn, εa, hεa_nn, hεa_cap, Λa, hΛa_nn,
    Clow, hClow_nn, hjet⟩ :=
    exists_deTurckSmoothRemainderDiff_sub_principalCometricArm_smallThirdArm_iteratedCovGrad_jet_le
      (I := I) (M := M) g₀ g_bg a ha_super hR₀ hδ_le hδ_fibre
  obtain ⟨Ctame, hCtame_nn, hCtame⟩ :=
    exists_smoothCcToTensorHs_real_le_of_iteratedCovGrad_jet_window
      (I := I) (M := M) g₀ a (by omega) Clow hClow_nn
  refine ⟨εC, hεC_nn, hεC_cap, hεC_cap', Kc, hKc_nn, εa, hεa_nn, hεa_cap, Λa, hΛa_nn,
    Ctame, hCtame_nn, fun T₀ hTsymm hball => ?_⟩
  obtain ⟨C₂, C₀, hC₂sup, hC₂jet, hC₀sup, hC₀jet, hwin⟩ := hjet T₀ hTsymm hball
  exact ⟨C₂, C₀, hC₂sup, hC₂jet, hC₀sup, hC₀jet, fun k => hCtame k _ T₀ hwin⟩

set_option maxHeartbeats 1000000 in
theorem exists_smoothCcToTensorHs_appCc_fibreSmallCoeff_opNorm_le_zero
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (εC : ℝ) (hεC_nn : 0 ≤ εC) (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) :
    ∃ Cop : ℝ, 0 ≤ Cop ∧
      ∀ (C₂ : SmoothCcTensor g₀ (2 + 2) 2) (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) 2 x (C₂.toSection x) ≤ εC ^ 2) →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i C₂‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) →
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ)
            (appCc (I := I) (M := M) g₀ (2 + 2) 2 C₂
              (iteratedCovGrad (I := I) g₀ 0 2 2 T₀))‖ ≤
          deTurckArmFibreConst (Module.finrank ℝ E) * εC *
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖ +
            Cop * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (1 : ℝ) T₀‖ := by
  classical
  obtain ⟨Ccross, hCcross_nn, hcross⟩ := exists_Ccross_for_secondCovGrad (I := I) (M := M) g₀
  obtain ⟨C21, hC21_nn, hC21⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general (I := I) (M := M) g₀ 1
  refine ⟨εC * Real.sqrt Ccross * (2 * C21),
    mul_nonneg (mul_nonneg hεC_nn (Real.sqrt_nonneg _)) (by linarith), ?_⟩
  intro C₂ T₀ hball hsup hjets
  set W₂ : SmoothCcTensor g₀ 0 (2 + 2) := iteratedCovGrad (I := I) g₀ 0 2 2 T₀ with hW₂_def
  set P : SmoothCcTensor g₀ 0 2 :=
    appCc (I := I) (M := M) g₀ (2 + 2) 2 C₂ W₂ with hP_def
  have hLHS_eq : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ) P‖ = ‖P‖ := by
    rw [smoothCcToTensorHs_zero_norm_eq (I := I) (M := M) g₀ P, SmoothCcTensor.norm_toL2]
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤
        εC ^ 2 * ∑ i ∈ Finset.range 1,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 2) x (W₂.toSection x) := by
    intro x
    have hgrid := appCc_iteratedCovGrad_diagonalProductGrid_le
      (I := I) (M := M) g₀ (2 + 2) 2 C₂ W₂ 0 x
    rw [show Finset.range (0 + 1) = Finset.range 1 from rfl, Finset.sum_range_one] at hgrid
    rw [show Finset.range (0 + 1 - 0) = Finset.range 1 from rfl,
      Finset.sum_range_one] at hgrid
    rw [show appCcGdiag (E := E) 0 = 1 by simp [appCcGdiag], one_mul] at hgrid
    rw [Finset.sum_range_one]
    have hW_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 2) x
        (W₂.toSection x) :=
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ _ _ _ _
    refine le_trans hgrid ?_
    exact mul_le_mul_of_nonneg_right (hsup x) hW_nn
  have hprod : ‖P‖ ≤ εC * ‖W₂‖ := by
    have hPTLP := tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum (I := I) (M := M) g₀
      1 (fun _ => 2 + 2) (fun _ => W₂) P εC hεC_nn hpt
    rw [Finset.sum_range_one] at hPTLP
    exact hPTLP
  clear_value W₂ P
  have hweitz := weitzenbock_integrated_covGrad_l2_normSq (I := I) (M := M) g₀ 2 T₀
  have hcrossT := hcross T₀
  set nHess : ℝ := tensorL2Norm (I := I) (M := M) g₀ 0 (2 + 1 + 1)
    (covGrad (I := I) (M := M) g₀ 0 (2 + 1)
      (covGrad (I := I) (M := M) g₀ 0 2 T₀)).toFun with hnHess_def
  set nGrad : ℝ := tensorL2Norm (I := I) (M := M) g₀ 0 (2 + 1)
    (covGrad (I := I) (M := M) g₀ 0 2 T₀).toFun with hnGrad_def
  set nLap : ℝ := tensorL2Norm (I := I) (M := M) g₀ 0 2
    (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀).toFun with hnLap_def
  set nT : ℝ := tensorL2Norm (I := I) (M := M) g₀ 0 2 T₀.toFun with hnT_def
  have hnHess_nn : 0 ≤ nHess := tensorL2Norm_nonneg (I := I) (M := M) g₀ 0 (2 + 1 + 1) _
  have hnGrad_nn : 0 ≤ nGrad := tensorL2Norm_nonneg (I := I) (M := M) g₀ 0 (2 + 1) _
  have hnLap_nn : 0 ≤ nLap := tensorL2Norm_nonneg (I := I) (M := M) g₀ 0 2 _
  have hnT_nn : 0 ≤ nT := tensorL2Norm_nonneg (I := I) (M := M) g₀ 0 2 _
  clear_value nHess nGrad nLap nT
  have hW₂_norm : ‖W₂‖ = nHess := by
    have hW2eq : W₂ = covGrad (I := I) (M := M) g₀ 0 (2 + 1)
        (covGrad (I := I) (M := M) g₀ 0 2 T₀) := by
      rw [hW₂_def]
      rw [iteratedCovGrad_succ (I := I) (M := M) g₀ 0 2 1 T₀,
        iteratedCovGrad_succ (I := I) (M := M) g₀ 0 2 0 T₀,
        iteratedCovGrad_zero (I := I) (M := M) g₀ 0 2 T₀]
    rw [hW2eq, SmoothCcTensor.norm_def]
    exact hnHess_def.symm
  have hstep1 : nHess ^ 2 ≤ nLap ^ 2 + Ccross * (nGrad ^ 2 + nT * nGrad) := by
    linarith [hweitz, hcrossT]
  have hstep2 : nHess ^ 2 ≤ (nLap + Real.sqrt Ccross * (nGrad + nT)) ^ 2 := by
    have hsq : Real.sqrt Ccross ^ 2 = Ccross := Real.sq_sqrt hCcross_nn
    have hexp : (nLap + Real.sqrt Ccross * (nGrad + nT)) ^ 2 =
        nLap ^ 2 + 2 * nLap * (Real.sqrt Ccross * (nGrad + nT)) +
          Ccross * (nGrad + nT) ^ 2 := by
      rw [show (nLap + Real.sqrt Ccross * (nGrad + nT)) ^ 2 =
        nLap ^ 2 + 2 * nLap * (Real.sqrt Ccross * (nGrad + nT)) +
          Real.sqrt Ccross ^ 2 * (nGrad + nT) ^ 2 by ring, hsq]
    rw [hexp]
    have hc1 : 0 ≤ 2 * nLap * (Real.sqrt Ccross * (nGrad + nT)) := by positivity
    have hc2 : nGrad ^ 2 + nT * nGrad ≤ (nGrad + nT) ^ 2 := by nlinarith
    have hc3 : Ccross * (nGrad ^ 2 + nT * nGrad) ≤ Ccross * (nGrad + nT) ^ 2 :=
      mul_le_mul_of_nonneg_left hc2 hCcross_nn
    linarith [hstep1]
  have hHess_le : nHess ≤ nLap + Real.sqrt Ccross * (nGrad + nT) := by
    have hrhs_nn : 0 ≤ nLap + Real.sqrt Ccross * (nGrad + nT) := by positivity
    calc nHess = Real.sqrt (nHess ^ 2) := (Real.sqrt_sq hnHess_nn).symm
      _ ≤ Real.sqrt ((nLap + Real.sqrt Ccross * (nGrad + nT)) ^ 2) :=
          Real.sqrt_le_sqrt hstep2
      _ = nLap + Real.sqrt Ccross * (nGrad + nT) := Real.sqrt_sq hrhs_nn
  have hLap_le : nLap ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖ := by
    have h1 : nLap = ‖rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀‖ := by
      rw [hnLap_def, SmoothCcTensor.norm_def]
    have h2 : ‖rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀‖ =
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ)
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ := by
      rw [smoothCcToTensorHs_zero_norm_eq, SmoothCcTensor.norm_toL2]
    have h3 := smoothCcToTensorHs_rawTensorConnLapSmooth_le (I := I) (M := M) g₀ (0 : ℝ) T₀
    have h4 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((0 : ℝ) + 2) T₀‖ =
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖ :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by norm_num) T₀
    rw [h1, h2]
    rw [h4] at h3
    exact h3
  have hjets1 : ∀ j : ℕ, j < 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ≤
        C21 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (1 : ℝ) T₀‖ := by
    intro j hj
    have hsum := hC21 T₀
    have hcast : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T₀‖ =
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (1 : ℝ) T₀‖ :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by norm_num) T₀
    rw [hcast] at hsum
    refine le_trans ?_ hsum
    exact Finset.single_le_sum
      (f := fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖)
      (fun i _ => norm_nonneg _) (Finset.mem_range.mpr hj)
  have hnT_le : nT ≤ C21 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (1 : ℝ) T₀‖ := by
    have h0 : nT = ‖iteratedCovGrad (I := I) g₀ 0 2 0 T₀‖ := by
      rw [hnT_def, iteratedCovGrad_zero (I := I) (M := M) g₀ 0 2 T₀,
        SmoothCcTensor.norm_def]
    rw [h0]
    exact hjets1 0 (by norm_num)
  have hnGrad_le : nGrad ≤ C21 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (1 : ℝ) T₀‖ := by
    have h1 : iteratedCovGrad (I := I) g₀ 0 2 1 T₀ =
        covGrad (I := I) (M := M) g₀ 0 2 T₀ := by
      rw [iteratedCovGrad_succ (I := I) (M := M) g₀ 0 2 0 T₀,
        iteratedCovGrad_zero (I := I) (M := M) g₀ 0 2 T₀]
    have h0 : nGrad = ‖iteratedCovGrad (I := I) g₀ 0 2 1 T₀‖ := by
      rw [hnGrad_def, h1, SmoothCcTensor.norm_def]
    rw [h0]
    exact hjets1 1 (by norm_num)
  have hfibre1 : (1 : ℝ) ≤ deTurckArmFibreConst (Module.finrank ℝ E) :=
    one_le_deTurckArmFibreConst (Nat.one_le_iff_ne_zero.mpr (NeZero.ne (Module.finrank ℝ E)))
  have hHs2_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖ := norm_nonneg _
  have hHs1_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ (1 : ℝ) T₀‖ := norm_nonneg _
  have hchain : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (0 : ℝ) P‖ ≤
      εC * (‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖ +
        Real.sqrt Ccross * (2 * C21 *
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (1 : ℝ) T₀‖)) := by
    rw [hLHS_eq]
    refine le_trans hprod ?_
    rw [hW₂_norm]
    refine le_trans (mul_le_mul_of_nonneg_left hHess_le hεC_nn) ?_
    refine mul_le_mul_of_nonneg_left ?_ hεC_nn
    have hGT : nGrad + nT ≤ 2 * C21 *
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (1 : ℝ) T₀‖ := by
      linarith [hnGrad_le, hnT_le]
    have := mul_le_mul_of_nonneg_left hGT (Real.sqrt_nonneg Ccross)
    linarith [hLap_le]
  refine le_trans hchain ?_
  have hexpand : εC * (‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖ +
      Real.sqrt Ccross * (2 * C21 *
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (1 : ℝ) T₀‖)) =
      εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖ +
        εC * Real.sqrt Ccross * (2 * C21) *
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (1 : ℝ) T₀‖ := by ring
  rw [hexpand]
  have h1 : εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖ ≤
      deTurckArmFibreConst (Module.finrank ℝ E) * εC *
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖ := by
    have h2 : (1 : ℝ) * εC ≤ deTurckArmFibreConst (Module.finrank ℝ E) * εC :=
      mul_le_mul_of_nonneg_right hfibre1 hεC_nn
    have h3 := mul_le_mul_of_nonneg_right h2 hHs2_nn
    calc εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖
        = 1 * εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖ := by ring
      _ ≤ deTurckArmFibreConst (Module.finrank ℝ E) * εC *
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T₀‖ := h3
  linarith [h1]


theorem exists_smoothCcToTensorHs_appCc_fibreSmallCoeff_opNorm_le_succ
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (εC : ℝ) (hεC_nn : 0 ≤ εC) (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) :
    ∃ Cop : ℕ → ℝ, (∀ m, 0 ≤ Cop m) ∧
      ∀ (C₂ : SmoothCcTensor g₀ (2 + 2) 2) (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) 2 x (C₂.toSection x) ≤ εC ^ 2) →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i C₂‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) →
        ∀ m : ℕ,
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1)
              (appCc (I := I) (M := M) g₀ (2 + 2) 2 C₂
                (iteratedCovGrad (I := I) g₀ 0 2 2 T₀))‖ ≤
            deTurckArmFibreConst (Module.finrank ℝ E) * εC *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 3) T₀‖ +
              Cop m * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T₀‖ := by
  classical
  obtain ⟨Clower, hClower_nn, hfam⟩ :=
    exists_appCc_secondCovGrad_fibreSmallCoeff_Hs_family_le (I := I) (M := M) g₀ a
      (by omega) hR₀ εC hεC_nn Kc hKc_nn
  refine ⟨fun m => Clower (m + 1), fun m => hClower_nn (m + 1), ?_⟩
  intro C₂ T₀ hball hsup hjets m
  have hbase := hfam C₂ T₀ hball hsup hjets (m + 1) T₀
    ⟨0, (oneMinusConnLapSmoothIter_zero (I := I) (M := M) (T := T₀)).symm⟩
  have hΔ : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m + 1 : ℕ) : ℝ)
      (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 3) T₀‖ := by
    have h1 := smoothCcToTensorHs_rawTensorConnLapSmooth_le (I := I) (M := M) g₀
      (((m + 1 : ℕ) : ℝ)) T₀
    have h2 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((m + 1 : ℕ) : ℝ) + 2) T₀‖ =
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 3) T₀‖ :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
    rw [h2] at h1
    exact h1
  have hcastL : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m + 1 : ℕ) : ℝ)
      (appCc (I := I) (M := M) g₀ (2 + 2) 2 C₂
        (iteratedCovGrad (I := I) g₀ 0 2 2 T₀))‖ =
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1)
        (appCc (I := I) (M := M) g₀ (2 + 2) 2 C₂
          (iteratedCovGrad (I := I) g₀ 0 2 2 T₀))‖ :=
    smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) _
  have hcastQ : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m + 1 + 1 : ℕ) : ℝ) T₀‖ =
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T₀‖ :=
    smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀ (by push_cast; ring) T₀
  rw [hcastL, hcastQ] at hbase
  have hfibre1 : (1 : ℝ) ≤ deTurckArmFibreConst (Module.finrank ℝ E) :=
    one_le_deTurckArmFibreConst (Nat.one_le_iff_ne_zero.mpr (NeZero.ne (Module.finrank ℝ E)))
  have hH3_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 3) T₀‖ :=
    norm_nonneg _
  have htop : εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m + 1 : ℕ) : ℝ)
      (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ ≤
      deTurckArmFibreConst (Module.finrank ℝ E) * εC *
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 3) T₀‖ := by
    have hstep1 : εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m + 1 : ℕ) : ℝ)
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ ≤
        εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 3) T₀‖ :=
      mul_le_mul_of_nonneg_left hΔ hεC_nn
    have hstep2 : εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 3) T₀‖ ≤
        deTurckArmFibreConst (Module.finrank ℝ E) * εC *
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 3) T₀‖ := by
      have h2 : (1 : ℝ) * εC ≤ deTurckArmFibreConst (Module.finrank ℝ E) * εC :=
        mul_le_mul_of_nonneg_right hfibre1 hεC_nn
      have h3 := mul_le_mul_of_nonneg_right h2 hH3_nn
      calc εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 3) T₀‖
          = 1 * εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 3) T₀‖ := by ring
        _ ≤ deTurckArmFibreConst (Module.finrank ℝ E) * εC *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 3) T₀‖ := h3
    exact le_trans hstep1 hstep2
  linarith [hbase, htop]

theorem exists_smoothCcToTensorHs_appCc_fibreSmallCoeff_opNorm_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (εC : ℝ) (hεC_nn : 0 ≤ εC) (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) :
    ∃ Cop : ℕ → ℝ, (∀ m, 0 ≤ Cop m) ∧
      ∀ (C₂ : SmoothCcTensor g₀ (2 + 2) 2) (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) 2 x (C₂.toSection x) ≤ εC ^ 2) →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i C₂‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) →
        ∀ m : ℕ,
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
              (appCc (I := I) (M := M) g₀ (2 + 2) 2 C₂
                (iteratedCovGrad (I := I) g₀ 0 2 2 T₀))‖ ≤
            deTurckArmFibreConst (Module.finrank ℝ E) * εC *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T₀‖ +
              Cop m * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1) T₀‖ := by
  classical
  obtain ⟨Cop0, hCop0_nn, h0⟩ :=
    exists_smoothCcToTensorHs_appCc_fibreSmallCoeff_opNorm_le_zero
      (I := I) (M := M) g₀ a ha_super hR₀ εC hεC_nn Kc hKc_nn
  obtain ⟨Cops, hCops_nn, hs⟩ :=
    exists_smoothCcToTensorHs_appCc_fibreSmallCoeff_opNorm_le_succ
      (I := I) (M := M) g₀ a ha_super hR₀ εC hεC_nn Kc hKc_nn
  refine ⟨fun m => match m with
    | 0 => Cop0
    | (k + 1) => Cops k, fun m => ?_, fun C₂ T₀ hball hsup hjets m => ?_⟩
  · match m with
    | 0 => exact hCop0_nn
    | (k + 1) => exact hCops_nn k
  · match m with
    | 0 =>
      have hb := h0 C₂ T₀ hball hsup hjets
      have hnormL := smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
        (show ((0 : ℕ) : ℝ) = (0 : ℝ) by norm_num)
        (appCc (I := I) (M := M) g₀ (2 + 2) 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 T₀))
      have hnorm2 := smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
        (show ((0 : ℕ) : ℝ) + 2 = (2 : ℝ) by norm_num) T₀
      have hnorm1 := smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
        (show ((0 : ℕ) : ℝ) + 1 = (1 : ℝ) by norm_num) T₀
      rw [hnormL, hnorm2, hnorm1]
      exact hb
    | (k + 1) =>
      have hb := hs C₂ T₀ hball hsup hjets k
      have hnormL := smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
        (show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 by push_cast; ring)
        (appCc (I := I) (M := M) g₀ (2 + 2) 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 T₀))
      have hnorm2 := smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
        (show ((k + 1 : ℕ) : ℝ) + 2 = (k : ℝ) + 3 by push_cast; ring) T₀
      have hnorm1 := smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
        (show ((k + 1 : ℕ) : ℝ) + 1 = (k : ℝ) + 2 by push_cast; ring) T₀
      rw [hnormL, hnorm2, hnorm1]
      exact hb

/-- Deferred two-arm engine for the arm-zero coefficient application: for a
`(2+0,2)`-coefficient `C₀` with fibre sup `Λa` and the two-arm jet envelope against the data
`T₀` — naked window plus the `εa`-rated top arm — and for symmetric ball data whose fibre
bilinear form is `δ`-small in the `g₀`-operator sense, the applied field `appCc C₀ (∇⁰ T₀)`
is tame of order two on the spectral Sobolev scale with the δ-rated top coefficient
`εB ≤ 2 √n εa δ`: the unique top Leibniz term pairs the coefficient's `ε`-arm top jets
against the pointwise `√n δ`-small symmetric data (eigenvalue bound), while every other term
loses at least one order into the family-uniform lower slot. Mirrors the proven fibre-small
third-arm machine (`exists_smoothCcToTensorHs_appCc_fibreSmallCoeff_opNorm_le`) with the
roles of coefficient and data smallness exchanged; discharged at corr-discharge. Every
consumer transitively depends on `sorryAx` until that lands. -/
private theorem exists_smoothCcToTensorHs_appCc_armZeroTwoArmCoeff_opNorm_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i)
    (εa : ℝ) (hεa_nn : 0 ≤ εa) (Λa : ℝ) (hΛa_nn : 0 ≤ Λa) :
    ∃ εB : ℝ, 0 ≤ εB ∧
      (0 ≤ δ → εB ≤ 2 * Real.sqrt (Module.finrank ℝ E) * εa * δ) ∧
    ∃ Cop : ℕ → ℝ, (∀ m, 0 ≤ Cop m) ∧
      ∀ (C₀ : SmoothCcTensor g₀ (2 + 0) 2) (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T₀ x v w = ccTensorBilin (I := I) g₀ T₀ x w v) →
        gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 0) 2 x (C₀.toSection x) ≤
            Λa ^ 2) →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + 0) 2 i C₀‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
              εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) →
        ∀ m : ℕ,
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
              (appCc (I := I) (M := M) g₀ (2 + 0) 2 C₀
                (iteratedCovGrad (I := I) g₀ 0 2 0 T₀))‖ ≤
            εB * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T₀‖ +
              Cop m * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1) T₀‖ :=
  sorry

set_option maxHeartbeats 1000000 in
/-- Split of the remainder difference into the principal cometric arm, a small third arm whose
top-jet coefficient carries the full `32 f³ (δ/(1-δ))` budget cap, and a tame remainder: the
third arm folds the fibre-small `C₂`-application together with the two-arm `C₀`-application,
whose δ-rated top coefficients assemble under the cap via `28 f² + (32 f³ - 28 f²) = 32 f³`.
Consumers transitively depend on `sorryAx` via the two-arm correction-field interface and the
arm-zero two-arm engine until corr-discharge lands. -/
theorem exists_deTurckSmoothRemainderDiff_eq_principalCometricArm_add_smallThirdArm_add_tame
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ εwrap : ℝ, 0 ≤ εwrap ∧
      (0 ≤ δ → εwrap ≤ 32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 * (δ / (1 - δ))) ∧
    ∃ Cthird Ctame : ℕ → ℝ, (∀ k, 0 ≤ Cthird k) ∧ (∀ k, 0 ≤ Ctame k) ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2)
        (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T₀ x v w = ccTensorBilin (I := I) g₀ T₀ x w v)
        (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ∃ third tame : SmoothCcTensor g₀ 0 2,
          deTurckSmoothRemainder (I := I) g₀ g_bg T₀
              (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball) -
            deTurckSmoothRemainder (I := I) g₀ g_bg
              (0 : SmoothCcTensor g₀ 0 2)
              (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
              (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                (by
                  rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                      from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                    tensorHs_norm_smul]
                  simpa using hR₀)) =
            deTurckPrincipalCometricArm (I := I) (M := M) g₀
              (tensorSectionRealizeMetric (I := I) g₀ T₀
                (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)) T₀
              + third + tame ∧
          (∀ k : ℕ,
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1) third‖ ≤
              εwrap * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) + 1) T₀‖ +
                Cthird k * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) T₀‖) ∧
          (∀ k : ℕ,
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ) - 1) tame‖ ≤
              Ctame k * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + (k : ℝ)) T₀‖) := by
  classical
  obtain ⟨εC, hεC_nn, hεC_cap, hεC_cap', Kc, hKc_nn, εa, hεa_nn, hεa_cap, Λa, hΛa_nn,
    Ctame, hCtame_nn, htame⟩ :=
    exists_smoothCcToTensorHs_deTurckSmoothRemainderDiff_sub_principalCometricArm_smallThirdArm_tame_le
      (I := I) (M := M) g₀ g_bg a ha_super hR₀ hδ_le hδ_fibre
  obtain ⟨Cop, hCop_nn, hH3⟩ :=
    exists_smoothCcToTensorHs_appCc_fibreSmallCoeff_opNorm_le
      (I := I) (M := M) g₀ a ha_super hR₀ εC hεC_nn Kc hKc_nn
  obtain ⟨εB, hεB_nn, hεB_cap, CopB, hCopB_nn, hB'⟩ :=
    exists_smoothCcToTensorHs_appCc_armZeroTwoArmCoeff_opNorm_le
      (I := I) (M := M) g₀ a ha_super hR₀ (δ := δ) Kc hKc_nn εa hεa_nn Λa hΛa_nn
  refine ⟨deTurckArmFibreConst (Module.finrank ℝ E) * εC + εB,
    add_nonneg (mul_nonneg (deTurckArmFibreConst_nonneg _) hεC_nn) hεB_nn,
    fun hδ_nn => ?_,
    fun k => Cop (a + k - 1) + CopB (a + k - 1), Ctame,
    fun k => add_nonneg (hCop_nn _) (hCopB_nn _), hCtame_nn, fun T₀ hTsymm hball => ?_⟩
  · have hδ_lt1 : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)
    have hκ_nn : 0 ≤ δ / (1 - δ) := div_nonneg hδ_nn (by linarith)
    have hδκ : δ ≤ δ / (1 - δ) := by
      rw [le_div_iff₀ (by linarith : (0 : ℝ) < 1 - δ)]
      nlinarith [sq_nonneg δ]
    have hf_nn : 0 ≤ deTurckArmFibreConst (Module.finrank ℝ E) :=
      deTurckArmFibreConst_nonneg _
    have h1 : deTurckArmFibreConst (Module.finrank ℝ E) * εC ≤
        28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 * (δ / (1 - δ)) := by
      calc deTurckArmFibreConst (Module.finrank ℝ E) * εC
          ≤ deTurckArmFibreConst (Module.finrank ℝ E) *
              (28 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) :=
            mul_le_mul_of_nonneg_left (hεC_cap' hδ_nn) hf_nn
        _ = 28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 * (δ / (1 - δ)) := by ring
    have h2sq_nn : (0 : ℝ) ≤ 2 * Real.sqrt (Module.finrank ℝ E) * εa :=
      mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hεa_nn
    have h2 : εB ≤ (32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
        28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2) * (δ / (1 - δ)) := by
      refine le_trans (hεB_cap hδ_nn) ?_
      calc 2 * Real.sqrt (Module.finrank ℝ E) * εa * δ
          ≤ 2 * Real.sqrt (Module.finrank ℝ E) * εa * (δ / (1 - δ)) :=
            mul_le_mul_of_nonneg_left hδκ h2sq_nn
        _ ≤ (32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
              28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2) * (δ / (1 - δ)) :=
            mul_le_mul_of_nonneg_right hεa_cap hκ_nn
    calc deTurckArmFibreConst (Module.finrank ℝ E) * εC + εB
        ≤ 28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2 * (δ / (1 - δ)) +
            (32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
              28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2) * (δ / (1 - δ)) :=
          add_le_add h1 h2
      _ = 32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 * (δ / (1 - δ)) := by ring
  obtain ⟨C₂, C₀, hC₂sup, hC₂jet, hC₀sup, hC₀jet, hHsbound⟩ := htame T₀ hTsymm hball
  refine ⟨appCc (I := I) (M := M) g₀ (2 + 2) 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) +
      appCc (I := I) (M := M) g₀ (2 + 0) 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 T₀),
    deTurckSmoothRemainder (I := I) g₀ g_bg T₀
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball) -
      deTurckSmoothRemainder (I := I) g₀ g_bg
        (0 : SmoothCcTensor g₀ 0 2)
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
        (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
          (by
            rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
              tensorHs_norm_smul]
            simpa using hR₀)) -
      deTurckPrincipalCometricArm (I := I) (M := M) g₀
        (tensorSectionRealizeMetric (I := I) g₀ T₀
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)) T₀ -
      appCc (I := I) (M := M) g₀ (2 + 2) 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 T₀) -
      appCc (I := I) (M := M) g₀ (2 + 0) 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 T₀),
    by abel, fun k => ?_, hHsbound⟩
  · have hm1 : (a : ℝ) + (k : ℝ) - 1 = ((a + k - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (show 1 ≤ a + k by omega)]; push_cast; ring
    have hm2 : (a : ℝ) + (k : ℝ) + 1 = ((a + k - 1 : ℕ) : ℝ) + 2 := by
      rw [← hm1]; ring
    have hm3 : (a : ℝ) + (k : ℝ) = ((a + k - 1 : ℕ) : ℝ) + 1 := by
      rw [← hm1]; ring
    rw [hm1, hm2, hm3, smoothCcToTensorHs_add]
    refine le_trans (norm_add_le _ _) ?_
    have hA := hH3 C₂ T₀ hball hC₂sup hC₂jet (a + k - 1)
    have hB2 := hB' C₀ T₀ hball hTsymm (hδ_fibre T₀ hball) hC₀sup hC₀jet (a + k - 1)
    linarith [hA, hB2]


end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
