import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RemainderShortTimeExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.ChartDeTurckRemainderPolynomial
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapIterL2WtwokTwoBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHSSection
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.FaithfulH1Embedding
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.LocallyLipschitzTruncation
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingManifoldC0
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingReverseHebeyToHs
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralPouNormEquiv
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitz

noncomputable section

open Bundle MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

def deTurckSmoothN (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ) :
    tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) where
  coeff i :=
    tensorL2Coeff (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
      (SmoothCcTensor.toL2 (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ)) i
  weighted_summable :=
    smoothCcTensor_tensorL2Coeff_weighted_summable (I := I) (M := M) g₀
      (a : ℝ) (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)

@[simp] theorem deTurckSmoothN_coeff (g₀ g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g₀ 0 2) :
    (deTurckSmoothN (I := I) (M := M) g₀ g_bg a T hδ_lt hδ).coeff i =
      tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
        (SmoothCcTensor.toL2 (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ)) i :=
  rfl

theorem smoothCcToTensorHs_denseRange (g₀ : SmoothRiemannianMetric I M) (σ : ℝ) :
    DenseRange (smoothCcToTensorHs (I := I) (M := M) g₀ σ) := by
  classical
  have hsub :
      (tensorHs.finiteSupportSubmodule (I := I) (M := M) (g := g₀) (r := 0) (s := 2) σ :
          Set (tensorHs (I := I) (M := M) g₀ 0 2 σ)) ⊆
        Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ σ) := by
    intro x hx
    have hxfin : (Function.support x.coeff).Finite :=
      (tensorHs.mem_finiteSupportSubmodule (I := I) (M := M) x).1 hx
    refine ⟨finiteEigenCombo (I := I) (M := M) g₀ hxfin.toFinset x.coeff, ?_⟩
    refine tensorHs.ext ?_
    funext i
    rw [smoothCcToTensorHs_coeff]
    have hcoeff :
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2
              (finiteEigenCombo (I := I) (M := M) g₀ hxfin.toFinset x.coeff)) i =
          (if i ∈ hxfin.toFinset then x.coeff i else 0) := by
      rw [SmoothCcTensor.toL2_apply,
        finiteEigenCombo_tensorL2Coeff (I := I) (M := M) g₀ hxfin.toFinset x.coeff i]
    rw [hcoeff]
    by_cases hi : i ∈ hxfin.toFinset
    · rw [if_pos hi]
    · rw [if_neg hi]
      rw [Set.Finite.mem_toFinset] at hi
      exact (Function.notMem_support.mp hi).symm
  exact (tensorHsFiniteSupportSubmodule_dense (I := I) (M := M)).mono hsub

theorem smoothCcToTensorHs_add (g₀ : SmoothRiemannianMetric I M) (σ : ℝ)
    (S T : SmoothCcTensor g₀ 0 2) :
    smoothCcToTensorHs (I := I) (M := M) g₀ σ (S + T) =
      smoothCcToTensorHs (I := I) (M := M) g₀ σ S +
        smoothCcToTensorHs (I := I) (M := M) g₀ σ T := by
  refine tensorHs.ext ?_
  funext i
  rw [tensorHs.add_coeff]
  simp only [smoothCcToTensorHs_coeff]
  rw [show SmoothCcTensor.toL2 (S + T) =
        SmoothCcTensor.toL2 S + SmoothCcTensor.toL2 T from map_add _ _ _,
    tensorL2Coeff_add]

theorem smoothCcToTensorHs_neg (g₀ : SmoothRiemannianMetric I M) (σ : ℝ)
    (S : SmoothCcTensor g₀ 0 2) :
    smoothCcToTensorHs (I := I) (M := M) g₀ σ (-S) =
      -smoothCcToTensorHs (I := I) (M := M) g₀ σ S := by
  refine tensorHs.ext ?_
  funext i
  rw [tensorHs.neg_coeff]
  simp only [smoothCcToTensorHs_coeff]
  rw [show SmoothCcTensor.toL2 (-S) = -SmoothCcTensor.toL2 S from map_neg _ _]
  rw [show (-SmoothCcTensor.toL2 S : TensorL2 0 2 g₀) = (-1 : ℝ) • SmoothCcTensor.toL2 S by
    rw [neg_one_smul]]
  rw [tensorL2Coeff_smul]
  ring

theorem smoothCcToTensorHs_sub (g₀ : SmoothRiemannianMetric I M) (σ : ℝ)
    (S T : SmoothCcTensor g₀ 0 2) :
    smoothCcToTensorHs (I := I) (M := M) g₀ σ (S - T) =
      smoothCcToTensorHs (I := I) (M := M) g₀ σ S -
        smoothCcToTensorHs (I := I) (M := M) g₀ σ T := by
  rw [sub_eq_add_neg, sub_eq_add_neg, smoothCcToTensorHs_add, smoothCcToTensorHs_neg]

theorem deTurckSmoothN_sub_eq_smoothCcToTensorHs_remainderSub
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    deTurckSmoothN (I := I) (M := M) g₀ g_bg a T hδ_lt hδ -
        deTurckSmoothN (I := I) (M := M) g₀ g_bg a T' hδ'_lt hδ' =
      smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ)
        (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
          deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') := by
  refine tensorHs.ext ?_
  funext i
  have hsub :
      (deTurckSmoothN (I := I) (M := M) g₀ g_bg a T hδ_lt hδ -
          deTurckSmoothN (I := I) (M := M) g₀ g_bg a T' hδ'_lt hδ').coeff i =
        (deTurckSmoothN (I := I) (M := M) g₀ g_bg a T hδ_lt hδ).coeff i -
          (deTurckSmoothN (I := I) (M := M) g₀ g_bg a T' hδ'_lt hδ').coeff i := by
    rw [sub_eq_add_neg, tensorHs.add_coeff, tensorHs.neg_coeff]
    rfl
  have hcoeff_sub :
      tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (SmoothCcTensor.toL2
            (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
              deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ')) i =
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ)) i -
          tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ')) i := by
    rw [show SmoothCcTensor.toL2
            (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
              deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') =
          SmoothCcTensor.toL2 (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ) -
            SmoothCcTensor.toL2 (deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ')
        from map_sub _ _ _]
    rw [sub_eq_add_neg, tensorL2Coeff_add]
    rw [show (-SmoothCcTensor.toL2 (deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') :
          TensorL2 0 2 g₀) =
        (-1 : ℝ) • SmoothCcTensor.toL2 (deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') by
      rw [neg_one_smul]]
    rw [tensorL2Coeff_smul]
    ring
  rw [hsub, deTurckSmoothN_coeff, deTurckSmoothN_coeff, smoothCcToTensorHs_coeff, hcoeff_sub]

private theorem oneMinusConnLapSmoothIter_succ'
    (g₀ : SmoothRiemannianMetric I M) (k : ℕ) (S : SmoothCcTensor g₀ 0 2) :
    oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (k + 1) S =
      oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k (oneMinusConnLapSmooth (I := I) g₀ 0 2 S) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [oneMinusConnLapSmoothIter_succ, ih, ← oneMinusConnLapSmoothIter_succ]

private theorem exists_oneMinusConnLapSmooth_toHs_le_toHs_succ
    (g₀ : SmoothRiemannianMetric I M) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ U : SmoothCcTensor g₀ 0 2,
        ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
            (g := g₀) (r := 0) (s := 2) m (oneMinusConnLapSmooth (I := I) g₀ 0 2 U)‖ ≤
          C * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
            (g := g₀) (r := 0) (s := 2) (m + 1) U‖ := by
  obtain ⟨C₁, hC₁_nn, hC₁⟩ := exists_rawConnLapSmooth_toHs_le_toHs_succ (I := I) g₀ m
  refine ⟨1 + C₁, by positivity, fun U => ?_⟩
  have hsub : oneMinusConnLapSmooth (I := I) g₀ 0 2 U =
      U - rawTensorConnLapSmooth (I := I) g₀ 0 2 U := rfl
  rw [hsub, SmoothCcTensor.toHs_sub]
  have hmono : ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
        (g := g₀) (r := 0) (s := 2) m U‖ ≤
      ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
        (g := g₀) (r := 0) (s := 2) (m + 1) U‖ :=
    toHs_norm_mono (I := I) g₀ (Nat.le_succ m) U
  have hlap := hC₁ U
  calc ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
          (g := g₀) (r := 0) (s := 2) m U -
          DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
            (g := g₀) (r := 0) (s := 2) m (rawTensorConnLapSmooth (I := I) g₀ 0 2 U)‖
      ≤ ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
            (g := g₀) (r := 0) (s := 2) m U‖ +
          ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
            (g := g₀) (r := 0) (s := 2) m (rawTensorConnLapSmooth (I := I) g₀ 0 2 U)‖ :=
        norm_sub_le _ _
    _ ≤ ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
            (g := g₀) (r := 0) (s := 2) (m + 1) U‖ +
          C₁ * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
            (g := g₀) (r := 0) (s := 2) (m + 1) U‖ := add_le_add hmono hlap
    _ = (1 + C₁) * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
            (g := g₀) (r := 0) (s := 2) (m + 1) U‖ := by ring

private theorem exists_oneMinusConnLapSmoothIter_toHs_le_toHs
    (g₀ : SmoothRiemannianMetric I M) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g₀ 0 2,
        ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
            (g := g₀) (r := 0) (s := 2) 0 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k S)‖ ≤
          C * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
            (g := g₀) (r := 0) (s := 2) k S‖ := by
  induction k with
  | zero =>
      refine ⟨1, zero_le_one, fun S => ?_⟩
      simp only [oneMinusConnLapSmoothIter_zero, one_mul, le_refl]
  | succ k ih =>
      obtain ⟨Ck, hCk_nn, hCk⟩ := ih
      obtain ⟨Cstep, hCstep_nn, hCstep⟩ :=
        exists_oneMinusConnLapSmooth_toHs_le_toHs_succ (I := I) g₀ k
      refine ⟨Ck * Cstep, mul_nonneg hCk_nn hCstep_nn, fun S => ?_⟩
      rw [oneMinusConnLapSmoothIter_succ']
      calc ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
              (g := g₀) (r := 0) (s := 2) 0
              (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k
                (oneMinusConnLapSmooth (I := I) g₀ 0 2 S))‖
          ≤ Ck * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
              (g := g₀) (r := 0) (s := 2) k (oneMinusConnLapSmooth (I := I) g₀ 0 2 S)‖ :=
            hCk (oneMinusConnLapSmooth (I := I) g₀ 0 2 S)
        _ ≤ Ck * (Cstep * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
              (g := g₀) (r := 0) (s := 2) (k + 1) S‖) :=
            mul_le_mul_of_nonneg_left (hCstep S) hCk_nn
        _ = (Ck * Cstep) * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
              (g := g₀) (r := 0) (s := 2) (k + 1) S‖ := by ring

theorem exists_smoothCcToTensorHs_even_le_iteratedCovGrad_sum
    (g₀ : SmoothRiemannianMetric I M) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g₀ 0 2,
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S‖ ≤
          C * ∑ j ∈ Finset.range (2 * k + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ := by
  classical
  obtain ⟨Cl2, hCl2_nn, hCl2⟩ := exists_l2Norm_le_toHs_zero (I := I) g₀
  obtain ⟨Cdrop, hCdrop_nn, hCdrop⟩ := exists_oneMinusConnLapSmoothIter_toHs_le_toHs (I := I) g₀ k
  obtain ⟨Chebey, hChebey_nn, hChebey⟩ :=
    exists_toHs_norm_le_iteratedCovGrad_tensorL2Norm_sum (I := I) (M := M) g₀ 0 2 k
  refine ⟨Cl2 * Cdrop * Chebey, by positivity, fun S => ?_⟩
  
  have hembed_eq : smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S =
      ccSpectralEmbed (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S :=
    tensorHs.ext (funext (fun i => rfl))
  have hsq := ccSpectralEmbed_even_norm_sq_eq_oneMinusConnLap_l2 (I := I) (M := M) g₀ k S
  have hnorm_eq : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S‖ =
      ‖SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k S)‖ := by
    have h1 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S‖ =
        ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S‖ := by rw [hembed_eq]
    have h2 : ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S‖ =
        ‖SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k S)‖ := by
      have hnn1 : (0 : ℝ) ≤ ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S‖ :=
        norm_nonneg _
      have hnn2 : (0 : ℝ) ≤
          ‖SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k S)‖ := norm_nonneg _
      nlinarith [hsq, hnn1, hnn2]
    rw [h1, h2]
  rw [hnorm_eq]
  
  
  have hjet_eq : ∀ j : ℕ,
      tensorL2Norm (I := I) (M := M) g₀ 0 (2 + j) (iteratedCovGrad (I := I) g₀ 0 2 j S).toFun =
        ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ := fun j =>
    (SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 2 j S)).symm
  have hl2 := hCl2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k S)
  have hdrop := hCdrop S
  have hhebey := hChebey S
  have hsum_nn : 0 ≤ ∑ j ∈ Finset.range (2 * k + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ :=
    Finset.sum_nonneg (fun j _ => norm_nonneg _)
  have htoHsk_nn : 0 ≤ ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
      (g := g₀) (r := 0) (s := 2) k S‖ := norm_nonneg _
  have htoHs0_nn : 0 ≤ ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
      (g := g₀) (r := 0) (s := 2) 0 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k S)‖ :=
    norm_nonneg _
  have hhebey' : ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
        (g := g₀) (r := 0) (s := 2) k S‖ ≤
      Chebey * ∑ j ∈ Finset.range (2 * k + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ := by
    refine le_trans hhebey ?_
    refine mul_le_mul_of_nonneg_left ?_ hChebey_nn
    exact le_of_eq (Finset.sum_congr rfl (fun j _ => hjet_eq j))
  calc ‖SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k S)‖
      ≤ Cl2 * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
          (g := g₀) (r := 0) (s := 2) 0 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k S)‖ := hl2
    _ ≤ Cl2 * (Cdrop * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
          (g := g₀) (r := 0) (s := 2) k S‖) := mul_le_mul_of_nonneg_left hdrop hCl2_nn
    _ ≤ Cl2 * (Cdrop * (Chebey * ∑ j ∈ Finset.range (2 * k + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖)) := by
        refine mul_le_mul_of_nonneg_left ?_ hCl2_nn
        exact mul_le_mul_of_nonneg_left hhebey' hCdrop_nn
    _ = Cl2 * Cdrop * Chebey * ∑ j ∈ Finset.range (2 * k + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ := by ring

theorem exists_iteratedCovGrad_sum_le_smoothCcToTensorHs
    (g₀ : SmoothRiemannianMetric I M) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g₀ 0 2,
        ∑ j ∈ Finset.range (2 * k + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ ≤
          C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S‖ := by
  classical
  obtain ⟨Cg, hCg_nn, hCg⟩ := exists_iteratedCovGrad_l2Norm_le_sum_rawConnLapIter (I := I) g₀ 2 k
  refine ⟨((2 * k + 1 : ℕ) : ℝ) * (Cg * (k + 1)), by positivity, fun S => ?_⟩
  have hembed_eq : ccSpectralEmbed (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S =
      smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S :=
    tensorHs.ext (funext (fun i => rfl))
  set Nspec : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S‖ with hNspec_def
  have hNspec_nn : 0 ≤ Nspec := norm_nonneg _
  
  have hlap_le : ∀ i ∈ Finset.range (k + 1),
      tensorL2Norm (I := I) (M := M) g₀ 0 2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S).toFun ≤
        Nspec := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have heq : tensorL2Norm (I := I) (M := M) g₀ 0 2
          (rawTensorConnLapIter (I := I) g₀ 0 2 i S).toFun =
        ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖ :=
      (DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm
        (I := I) (M := M) g₀ (rawTensorConnLapIter (I := I) g₀ 0 2 i S)).trans
        (SmoothCcTensor.norm_toL2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S)).symm
    rw [heq]
    have h1 : ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖ ≤
        ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * i : ℕ) : ℝ) S‖ :=
      rawConnLapIter_l2_le_ccSpectralEmbed_even (I := I) (M := M) g₀ i S
    have h2 : ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * i : ℕ) : ℝ) S‖ ≤ Nspec := by
      rw [hNspec_def, ← hembed_eq]
      refine ccSpectralEmbed_norm_mono (I := I) (M := M) g₀ ?_ S
      have : (2 * i : ℕ) ≤ (2 * k : ℕ) := by omega
      exact_mod_cast this
    exact le_trans h1 h2
  
  have hlapsum : ∑ i ∈ Finset.range (k + 1),
      tensorL2Norm (I := I) (M := M) g₀ 0 2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S).toFun ≤
        ((k + 1 : ℕ) : ℝ) * Nspec := by
    calc ∑ i ∈ Finset.range (k + 1),
          tensorL2Norm (I := I) (M := M) g₀ 0 2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S).toFun
        ≤ ∑ _i ∈ Finset.range (k + 1), Nspec := Finset.sum_le_sum hlap_le
      _ = ((k + 1 : ℕ) : ℝ) * Nspec := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  
  have hjet_le : ∀ j ∈ Finset.range (2 * k + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ ≤ Cg * (((k + 1 : ℕ) : ℝ) * Nspec) := by
    intro j hj
    have hj2k : j ≤ 2 * k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hgj := hCg j hj2k S
    have heqj : tensorL2Norm (I := I) (M := M) g₀ 0 (2 + j)
          (iteratedCovGrad (I := I) g₀ 0 2 j S).toFun =
        ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ :=
      (SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 2 j S)).symm
    rw [heqj] at hgj
    exact le_trans hgj (mul_le_mul_of_nonneg_left hlapsum hCg_nn)
  calc ∑ j ∈ Finset.range (2 * k + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖
      ≤ ∑ _j ∈ Finset.range (2 * k + 1), Cg * (((k + 1 : ℕ) : ℝ) * Nspec) :=
        Finset.sum_le_sum hjet_le
    _ = ((2 * k + 1 : ℕ) : ℝ) * (Cg * (((k + 1 : ℕ) : ℝ) * Nspec)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = ((2 * k + 1 : ℕ) : ℝ) * (Cg * (k + 1)) * Nspec := by push_cast; ring

set_option linter.unusedVariables false in

theorem smoothRemainderDiff_ballLipschitz_Ha2
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) (ha_even : Even a)
    {R : ℝ} (hR : 0 < R) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ≥0, ∀ (T T' : SmoothCcTensor g₀ 0 2)
      {δ : ℝ} (hδ_le : δ ≤ δ₀)
      (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
      (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤ R →
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖ ≤ R →
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ)
          (deTurckSmoothRemainder (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
            deTurckSmoothRemainder (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ')‖ ≤
        (K : ℝ) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T -
          smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖ := by
  classical
  
  obtain ⟨m, hm⟩ := ha_even
  have hm2 : a = 2 * m := by omega
  have hordA : ((2 * m : ℕ) : ℝ) = (a : ℝ) := by rw [hm2]
  have hordB : ((2 * (m + 1) : ℕ) : ℝ) = (a : ℝ) + 2 := by rw [hm2]; push_cast; ring
  
  obtain ⟨Ca, hCa_nn, hCa⟩ :=
    exists_smoothCcToTensorHs_even_le_iteratedCovGrad_sum (I := I) (M := M) g₀ m
  
  obtain ⟨Cb, hCb_nn, hCb⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs (I := I) (M := M) g₀ (m + 1)
  
  have hR'_nn : (0 : ℝ) ≤ Cb * R := mul_nonneg hCb_nn hR.le
  obtain ⟨Ccol, hCcol_nn, hCcol⟩ :=
    deTurckRemainderDiff_iteratedCovGradSum_ballLipschitz (I := I) (M := M) g₀ g_bg a ha_super hR'_nn hδ₀
  
  refine ⟨Real.toNNReal (Ca * Real.sqrt (((a : ℝ) + 1) * (Ccol * Cb ^ 2))), ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  set W : SmoothCcTensor g₀ 0 2 := T - T' with hW_def
  set D : SmoothCcTensor g₀ 0 2 :=
    deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
      deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ' with hD_def
  
  set Ndist : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T -
    smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖ with hNdist_def
  have hNdist_nn : 0 ≤ Ndist := norm_nonneg _
  have hNdist_eq : Ndist = ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) W‖ := by
    rw [hNdist_def, hW_def, smoothCcToTensorHs_sub]
  
  have hball_conv : ∀ (S : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S‖ ≤ R →
      ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ ≤ Cb * R := by
    intro S hSball j hj
    have hsum := hCb S
    rw [hordB] at hsum
    have hterm : ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ ≤
        ∑ i ∈ Finset.range (2 * (m + 1) + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i S‖ := by
      refine Finset.single_le_sum (f := fun i => ‖iteratedCovGrad (I := I) g₀ 0 2 i S‖)
        (fun i _ => norm_nonneg _) ?_
      rw [Finset.mem_range]; omega
    calc ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖
        ≤ ∑ i ∈ Finset.range (2 * (m + 1) + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i S‖ := hterm
      _ ≤ Cb * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S‖ := hsum
      _ ≤ Cb * R := mul_le_mul_of_nonneg_left hSball hCb_nn
  have hTcov : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ Cb * R :=
    hball_conv T hTball
  have hT'cov : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ Cb * R :=
    hball_conv T' hT'ball
  
  have hcol := hCcol T T' hδ_le hδ hδ'_le hδ' hTcov hT'cov
  rw [← hD_def] at hcol
  
  have hWsum := hCb W
  rw [hordB, ← hNdist_eq] at hWsum
  set Wsum : ℝ := ∑ i ∈ Finset.range (2 * (m + 1) + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ with hWsum_def
  have hWsum_nn : 0 ≤ Wsum :=
    Finset.sum_nonneg fun i _ => norm_nonneg _
  have hWsumsq_le : Wsum ^ 2 ≤ Cb ^ 2 * Ndist ^ 2 := by
    have := mul_le_mul hWsum hWsum hWsum_nn (by positivity)
    calc Wsum ^ 2 = Wsum * Wsum := by ring
      _ ≤ (Cb * Ndist) * (Cb * Ndist) := this
      _ = Cb ^ 2 * Ndist ^ 2 := by ring
  
  have hsq_le_sumsq : (∑ i ∈ Finset.range (a + 2 + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2) ≤ Wsum ^ 2 := by
    rw [hWsum_def]
    have hcast : Finset.range (a + 2 + 1) = Finset.range (2 * (m + 1) + 1) := by
      congr 1; omega
    rw [hcast]
    exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => norm_nonneg _)
  
  have hcol' : (∑ q ∈ Finset.range (a + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ ^ 2) ≤ Ccol * (Cb ^ 2 * Ndist ^ 2) := by
    refine hcol.trans ?_
    calc Ccol * ∑ i ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2
        ≤ Ccol * Wsum ^ 2 := mul_le_mul_of_nonneg_left hsq_le_sumsq hCcol_nn
      _ ≤ Ccol * (Cb ^ 2 * Ndist ^ 2) := mul_le_mul_of_nonneg_left hWsumsq_le hCcol_nn
  
  set Dsum : ℝ := ∑ q ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ with hDsum_def
  have hDsum_nn : 0 ≤ Dsum := Finset.sum_nonneg fun q _ => norm_nonneg _
  have hDsum_sq : Dsum ^ 2 ≤ ((a : ℝ) + 1) *
      ∑ q ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ ^ 2 := by
    rw [hDsum_def]
    have hcheb := sq_sum_le_card_mul_sum_sq (s := Finset.range (a + 1))
      (f := fun q => ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖)
    rw [Finset.card_range] at hcheb
    refine hcheb.trans (le_of_eq ?_)
    congr 1
    push_cast; ring
  
  have hbridgeA := hCa D
  rw [hordA] at hbridgeA
  have hrange_eq : Finset.range (2 * m + 1) = Finset.range (a + 1) := by
    congr 1; omega
  rw [hrange_eq, ← hDsum_def] at hbridgeA
  
  have hDsum_le : Dsum ≤ Real.sqrt (((a : ℝ) + 1) * (Ccol * Cb ^ 2)) * Ndist := by
    have hDsum_sq_le : Dsum ^ 2 ≤ (((a : ℝ) + 1) * (Ccol * Cb ^ 2)) * Ndist ^ 2 := by
      calc Dsum ^ 2 ≤ ((a : ℝ) + 1) *
            ∑ q ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ ^ 2 := hDsum_sq
        _ ≤ ((a : ℝ) + 1) * (Ccol * (Cb ^ 2 * Ndist ^ 2)) :=
            mul_le_mul_of_nonneg_left hcol' (by positivity)
        _ = (((a : ℝ) + 1) * (Ccol * Cb ^ 2)) * Ndist ^ 2 := by ring
    have hrhs_nn : 0 ≤ Real.sqrt (((a : ℝ) + 1) * (Ccol * Cb ^ 2)) * Ndist :=
      mul_nonneg (Real.sqrt_nonneg _) hNdist_nn
    have hsqrt_sq : (Real.sqrt (((a : ℝ) + 1) * (Ccol * Cb ^ 2)) * Ndist) ^ 2 =
        (((a : ℝ) + 1) * (Ccol * Cb ^ 2)) * Ndist ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
    have hsqle : Dsum ^ 2 ≤ (Real.sqrt (((a : ℝ) + 1) * (Ccol * Cb ^ 2)) * Ndist) ^ 2 := by
      rw [hsqrt_sq]; exact hDsum_sq_le
    have := Real.sqrt_le_sqrt hsqle
    rwa [Real.sqrt_sq hDsum_nn, Real.sqrt_sq hrhs_nn] at this
  have hKcoe : (Real.toNNReal (Ca * Real.sqrt (((a : ℝ) + 1) * (Ccol * Cb ^ 2))) : ℝ) =
      Ca * Real.sqrt (((a : ℝ) + 1) * (Ccol * Cb ^ 2)) :=
    Real.coe_toNNReal _ (by positivity)
  rw [hKcoe]
  calc ‖smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) D‖
      ≤ Ca * Dsum := hbridgeA
    _ ≤ Ca * (Real.sqrt (((a : ℝ) + 1) * (Ccol * Cb ^ 2)) * Ndist) :=
        mul_le_mul_of_nonneg_left hDsum_le hCa_nn
    _ = Ca * Real.sqrt (((a : ℝ) + 1) * (Ccol * Cb ^ 2)) * Ndist := by ring

theorem deTurckRemainderDiff_iteratedCovGrad_ballLipschitz_weighted
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ q : ℕ, q ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 0 2 q
              (deTurckSmoothRemainder (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
                deTurckSmoothRemainder (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ')‖ ≤
            C * (δ₀ * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (T - T')‖ +
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) (T - T')‖) :=
  sorry

set_option linter.unusedVariables false in

theorem smoothRemainderDiff_ballLipschitz_Ha1_weighted
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) (ha_even : Even a)
    {R : ℝ} (hR : 0 < R) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ≥0, ∀ (T T' : SmoothCcTensor g₀ 0 2)
      {δ : ℝ} (hδ_le : δ ≤ δ₀)
      (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
      (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤ R →
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖ ≤ R →
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ)
          (deTurckSmoothRemainder (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
            deTurckSmoothRemainder (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ')‖ ≤
        (K : ℝ) * (δ₀ * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (T - T')‖ +
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) (T - T')‖) := by
  classical
  obtain ⟨m, hm⟩ := ha_even
  have hm2 : a = 2 * m := by omega
  have hordA : ((2 * m : ℕ) : ℝ) = (a : ℝ) := by rw [hm2]
  have hordB : ((2 * (m + 1) : ℕ) : ℝ) = (a : ℝ) + 2 := by rw [hm2]; push_cast; ring
  obtain ⟨Ca, hCa_nn, hCa⟩ :=
    exists_smoothCcToTensorHs_even_le_iteratedCovGrad_sum (I := I) (M := M) g₀ m
  obtain ⟨Cb, hCb_nn, hCb⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs (I := I) (M := M) g₀ (m + 1)
  have hR'_nn : (0 : ℝ) ≤ Cb * R := mul_nonneg hCb_nn hR.le
  obtain ⟨Ccol, hCcol_nn, hCcol⟩ :=
    deTurckRemainderDiff_iteratedCovGrad_ballLipschitz_weighted
      (I := I) (M := M) g₀ g_bg a ha_super hR'_nn hδ₀
  refine ⟨Real.toNNReal (Ca * (((a : ℝ) + 1) * Ccol)), ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  set W : SmoothCcTensor g₀ 0 2 := T - T' with hW_def
  set D : SmoothCcTensor g₀ 0 2 :=
    deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
      deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ' with hD_def
  set rhs : ℝ := δ₀ * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (T - T')‖ +
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) (T - T')‖ with hrhs_def
  have hball_conv : ∀ (S : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S‖ ≤ R →
      ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ ≤ Cb * R := by
    intro S hSball j hj
    have hsum := hCb S
    rw [hordB] at hsum
    have hterm : ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ ≤
        ∑ i ∈ Finset.range (2 * (m + 1) + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i S‖ := by
      refine Finset.single_le_sum (f := fun i => ‖iteratedCovGrad (I := I) g₀ 0 2 i S‖)
        (fun i _ => norm_nonneg _) ?_
      rw [Finset.mem_range]; omega
    calc ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖
        ≤ ∑ i ∈ Finset.range (2 * (m + 1) + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i S‖ := hterm
      _ ≤ Cb * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S‖ := hsum
      _ ≤ Cb * R := mul_le_mul_of_nonneg_left hSball hCb_nn
  have hTcov : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ Cb * R :=
    hball_conv T hTball
  have hT'cov : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ Cb * R :=
    hball_conv T' hT'ball
  have hcol := hCcol T T' hδ_le hδ hδ'_le hδ' hTcov hT'cov
  set Dsum : ℝ := ∑ q ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ with hDsum_def
  have hDsum_nn : 0 ≤ Dsum := Finset.sum_nonneg fun q _ => norm_nonneg _
  have hper : ∀ q ∈ Finset.range (a + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ ≤ Ccol * rhs := by
    intro q hq
    have hqa : q ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
    have hb := hcol q hqa
    rw [← hD_def, ← hrhs_def] at hb
    exact hb
  have hDsum_le : Dsum ≤ ((a : ℝ) + 1) * (Ccol * rhs) := by
    calc Dsum = ∑ q ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ := hDsum_def
      _ ≤ ∑ _q ∈ Finset.range (a + 1), Ccol * rhs := Finset.sum_le_sum hper
      _ = ((a + 1 : ℕ) : ℝ) * (Ccol * rhs) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = ((a : ℝ) + 1) * (Ccol * rhs) := by push_cast; ring
  have hbridgeA := hCa D
  rw [hordA] at hbridgeA
  have hrange_eq : Finset.range (2 * m + 1) = Finset.range (a + 1) := by
    congr 1; omega
  rw [hrange_eq, ← hDsum_def] at hbridgeA
  have hKcoe : (Real.toNNReal (Ca * (((a : ℝ) + 1) * Ccol)) : ℝ) =
      Ca * (((a : ℝ) + 1) * Ccol) :=
    Real.coe_toNNReal _ (by positivity)
  rw [hKcoe]
  calc ‖smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) D‖
      ≤ Ca * Dsum := hbridgeA
    _ ≤ Ca * (((a : ℝ) + 1) * (Ccol * rhs)) :=
        mul_le_mul_of_nonneg_left hDsum_le hCa_nn
    _ = Ca * (((a : ℝ) + 1) * Ccol) * rhs := by ring

theorem deTurckSmoothN_ballLipschitz_Ha2 (g₀ g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) (ha_even : Even a)
    {R : ℝ} (hR : 0 < R) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ≥0, ∀ (T T' : SmoothCcTensor g₀ 0 2)
      {δ : ℝ} (hδ_le : δ ≤ δ₀)
      (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
      (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤ R →
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖ ≤ R →
      ‖deTurckSmoothN (I := I) (M := M) g₀ g_bg a T (lt_of_le_of_lt hδ_le hδ₀) hδ -
          deTurckSmoothN (I := I) (M := M) g₀ g_bg a T' (lt_of_le_of_lt hδ'_le hδ₀) hδ'‖ ≤
        (K : ℝ) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T -
          smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖ := by
  obtain ⟨K, hK⟩ :=
    smoothRemainderDiff_ballLipschitz_Ha2 (I := I) (M := M) g₀ g_bg a ha_super ha_even hR hδ₀
  refine ⟨K, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  rw [deTurckSmoothN_sub_eq_smoothCcToTensorHs_remainderSub
    (I := I) (M := M) g₀ g_bg a T T' hδ_lt hδ hδ'_lt hδ']
  exact hK T T' hδ_le hδ hδ'_le hδ' hTball hT'ball

theorem smoothCcToTensorHs_smul (g₀ : SmoothRiemannianMetric I M) (σ : ℝ) (c : ℝ)
    (T : SmoothCcTensor g₀ 0 2) :
    smoothCcToTensorHs (I := I) (M := M) g₀ σ (c • T) =
      c • smoothCcToTensorHs (I := I) (M := M) g₀ σ T := by
  refine tensorHs.ext ?_
  funext i
  rw [tensorHs.smul_coeff]
  simp only [smoothCcToTensorHs_coeff]
  rw [show SmoothCcTensor.toL2 (c • T) = c • SmoothCcTensor.toL2 T from map_smul _ _ _,
    tensorL2Coeff_smul]

theorem tensorHs_norm_smul (g₀ : SmoothRiemannianMetric I M) {σ : ℝ} (c : ℝ)
    (x : tensorHs (I := I) (M := M) g₀ 0 2 σ) :
    ‖c • x‖ = |c| * ‖x‖ := by
  have h1 : ‖c • x‖ =
      ‖tensorHs.rescaleEquivL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (σ := σ) (c • x)‖ :=
    (tensorHs.rescaleEquivL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (σ := σ)).norm_map (c • x) |>.symm
  have h2 : ‖tensorHs.rescaleEquivL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (σ := σ) x‖ = ‖x‖ :=
    (tensorHs.rescaleEquivL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (σ := σ)).norm_map x
  rw [h1, map_smul, norm_smul, Real.norm_eq_abs, h2]

set_option maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

theorem ccTensorBilinSymm_gFibreOpBound_le_spectral_lossy
    (g₀ : SmoothRiemannianMetric I M) (m : ℕ) (_hm_even : Even m)
    (h_lossy : 2 * Module.finrank ℝ E + 4 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : SmoothCcTensor g₀ 0 2),
      gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T)
        (C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖) := by
  classical
  set kE : ℕ := Module.finrank ℝ E / 2 + 1 with hkE_def
  have hkE_super : 2 * kE > Module.finrank ℝ E + 2 * 0 := by
    rw [hkE_def]; omega
  have h4kEm : (4 * kE : ℕ) ≤ m := by
    rw [hkE_def]; omega
  
  obtain ⟨C₁, hC₁_pos, hC₁⟩ :=
    DifferentialGeometry.PDE.RicciFlow.tensorPouSobolevHilbert_embedding_Ck_gNorm
      (I := I) (M := M) g₀ 0 2 kE 0 hkE_super
  
  obtain ⟨C₂, hC₂_nn, hC₂⟩ :=
    tensorPouSobolevHsNorm_le_ccSpectralEmbed (I := I) (M := M) g₀ (2 * kE)
  refine ⟨C₁ * (C₂ + 1), by positivity, fun T => ?_⟩
  letI : Bundle.RiemannianBundle
      (fun b : M => Tensor0SBundle.TensorRSSpace 0 2 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 2
  
  
  
  have hupper : C₁ * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
        (g := g₀) (r := 0) (s := 2) (2 * kE) T‖ ≤
      (C₁ * (C₂ + 1)) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖ := by
    have hstep2 : ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
          (g := g₀) (r := 0) (s := 2) (2 * kE) T‖ =
        (DifferentialGeometry.Analysis.Sobolev.Tensor.tensorPouSobolevHsNorm (I := I) (M := M) g₀ (2 * kE) T).toReal :=
      DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.tensorPouSobolevHilbert_norm_eq
        (I := I) (M := M) g₀ (2 * kE) T
    have hstep3 : (DifferentialGeometry.Analysis.Sobolev.Tensor.tensorPouSobolevHsNorm (I := I) (M := M) g₀ (2 * kE) T).toReal ≤
        C₂ * ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * (2 * kE) : ℕ) : ℝ) T‖ := hC₂ T
    have hstep4 : ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * (2 * kE) : ℕ) : ℝ) T‖ ≤
        ‖ccSpectralEmbed (I := I) (M := M) g₀ (m : ℝ) T‖ := by
      refine ccSpectralEmbed_norm_mono (I := I) (M := M) g₀ ?_ T
      have : (2 * (2 * kE) : ℕ) ≤ m := by omega
      exact_mod_cast this
    have hembed_eq : ccSpectralEmbed (I := I) (M := M) g₀ (m : ℝ) T =
        smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T :=
      tensorHs.ext (funext (fun i => rfl))
    set Nm : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖ with hNm_def
    have hNm_nn : 0 ≤ Nm := norm_nonneg _
    have hspec_le : ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * (2 * kE) : ℕ) : ℝ) T‖ ≤ Nm := by
      rw [hNm_def, ← hembed_eq]; exact hstep4
    calc C₁ * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
            (g := g₀) (r := 0) (s := 2) (2 * kE) T‖
        = C₁ * (DifferentialGeometry.Analysis.Sobolev.Tensor.tensorPouSobolevHsNorm (I := I) (M := M) g₀ (2 * kE) T).toReal := by rw [hstep2]
      _ ≤ C₁ * (C₂ * ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * (2 * kE) : ℕ) : ℝ) T‖) :=
          mul_le_mul_of_nonneg_left hstep3 hC₁_pos.le
      _ ≤ C₁ * (C₂ * Nm) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hspec_le hC₂_nn) hC₁_pos.le
      _ ≤ (C₁ * (C₂ + 1)) * Nm := by nlinarith [hNm_nn, hC₁_pos.le, hC₂_nn]
  
  have hfibre := fun x : M => le_trans (hC₁ T x) hupper
  
  intro x v w
  have hcs := ccTensorBilin_abs_le_fibreNorm_mul_sqrt (I := I) (M := M) g₀ T x
  have hsv_nn : 0 ≤ Real.sqrt (g₀.inner x v v) := Real.sqrt_nonneg _
  have hsw_nn : 0 ≤ Real.sqrt (g₀.inner x w w) := Real.sqrt_nonneg _
  have hmul_nn : 0 ≤ Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) :=
    mul_nonneg hsv_nn hsw_nn
  
  
  have hvw := hcs v w
  have hwv := hcs w v
  have hfx := hfibre x
  
  rw [ccTensorBilinSymm_apply]
  have habs : |(1 / 2 : ℝ) *
      (ccTensorBilin (I := I) g₀ T x v w + ccTensorBilin (I := I) g₀ T x w v)| ≤
      (1 / 2 : ℝ) * (|ccTensorBilin (I := I) g₀ T x v w| +
        |ccTensorBilin (I := I) g₀ T x w v|) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
    exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)
  refine habs.trans ?_
  
  
  nlinarith [hvw, hwv, hfx, hsv_nn, hsw_nn, hmul_nn, mul_nonneg hsw_nn hsv_nn,
    mul_le_mul_of_nonneg_right hfx hmul_nn,
    mul_le_mul_of_nonneg_right hfx (mul_nonneg hsw_nn hsv_nn)]

theorem sobolevBall_smooth_fibreSmall (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∃ δ₀ : ℝ, δ₀ < 1 ∧
      ∀ (T : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤ R₀ →
        gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ₀ := by
  classical
  
  set m : ℕ := 2 * Module.finrank ℝ E + 4 with hm_def
  have hm_even : Even m := by rw [hm_def]; exact ⟨Module.finrank ℝ E + 2, by ring⟩
  have hm_lossy : 2 * Module.finrank ℝ E + 4 ≤ m := by rw [hm_def]
  have hm_le : (m : ℕ) ≤ a + 2 := by rw [hm_def]; omega
  obtain ⟨C, hC_pos, hC⟩ :=
    ccTensorBilinSymm_gFibreOpBound_le_spectral_lossy (I := I) (M := M) g₀ m hm_even hm_lossy
  refine ⟨1 / (2 * C), by positivity, 1 / 2, by norm_num, fun T hTball => ?_⟩
  
  have hmono : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ := by
    have hembed_m : smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T =
        ccSpectralEmbed (I := I) (M := M) g₀ (m : ℝ) T :=
      tensorHs.ext (funext (fun i => rfl))
    have hembed_a2 : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T =
        ccSpectralEmbed (I := I) (M := M) g₀ ((a : ℝ) + 2) T :=
      tensorHs.ext (funext (fun i => rfl))
    rw [hembed_m, hembed_a2]
    refine ccSpectralEmbed_norm_mono (I := I) (M := M) g₀ ?_ T
    have hcast : (m : ℝ) ≤ (a : ℝ) + 2 := by
      have h2 : (m : ℝ) ≤ (a : ℝ) + (2 : ℕ) := by exact_mod_cast hm_le
      push_cast at h2
      linarith [h2]
    exact hcast
  
  intro x v w
  have hlossy := hC T x v w
  have hNm_le : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖ ≤ 1 / (2 * C) :=
    le_trans hmono hTball
  have hsv_nn : 0 ≤ Real.sqrt (g₀.inner x v v) := Real.sqrt_nonneg _
  have hsw_nn : 0 ≤ Real.sqrt (g₀.inner x w w) := Real.sqrt_nonneg _
  have hmul_nn : 0 ≤ Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) :=
    mul_nonneg hsv_nn hsw_nn
  refine hlossy.trans ?_
  have hCN_le : C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖ ≤ 1 / 2 := by
    calc C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖
        ≤ C * (1 / (2 * C)) := mul_le_mul_of_nonneg_left hNm_le hC_pos.le
      _ = 1 / 2 := by field_simp
  calc (C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖) *
        Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)
      = (C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖) *
          (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) := by ring
    _ ≤ (1 / 2 : ℝ) * (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) :=
        mul_le_mul_of_nonneg_right hCN_le hmul_nn
    _ = 1 / 2 * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by ring

theorem deTurckSmoothN_embedding_wellDefined (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) (ha_even : Even a)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (hTT' : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T =
      smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T') :
    deTurckSmoothN (I := I) (M := M) g₀ g_bg a T hδ_lt hδ =
      deTurckSmoothN (I := I) (M := M) g₀ g_bg a T' hδ'_lt hδ' := by
  
  set δ₀ : ℝ := max δ δ' with hδ₀_def
  have hδ₀ : δ₀ < 1 := by rw [hδ₀_def]; exact max_lt hδ_lt hδ'_lt
  have hδ_le : δ ≤ δ₀ := by rw [hδ₀_def]; exact le_max_left _ _
  have hδ'_le : δ' ≤ δ₀ := by rw [hδ₀_def]; exact le_max_right _ _
  set R : ℝ := max ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖ + 1 with hR_def
  have hR_pos : 0 < R := by
    have : (0 : ℝ) ≤ max ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖ :=
      le_trans (norm_nonneg _) (le_max_left _ _)
    rw [hR_def]; linarith
  obtain ⟨K, hK⟩ :=
    deTurckSmoothN_ballLipschitz_Ha2 (I := I) (M := M) g₀ g_bg a ha_super ha_even hR_pos hδ₀
  have hTball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤ R := by
    rw [hR_def]; linarith [le_max_left ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖]
  have hT'ball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖ ≤ R := by
    rw [hR_def]; linarith [le_max_right ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖]
  have hbound := hK T T' hδ_le hδ hδ'_le hδ' hTball hT'ball
  rw [hTT', sub_self, norm_zero, mul_zero] at hbound
  have hzero : ‖deTurckSmoothN (I := I) (M := M) g₀ g_bg a T hδ_lt hδ -
      deTurckSmoothN (I := I) (M := M) g₀ g_bg a T' hδ'_lt hδ'‖ = 0 :=
    le_antisymm hbound (norm_nonneg _)
  rw [norm_eq_zero, sub_eq_zero] at hzero
  exact hzero

def radialScaleSmooth (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (R₀ : ℝ)
    (T : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 0 2 :=
  (min 1 (R₀ / ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖)) • T

theorem norm_smoothCcToTensorHs_radialScaleSmooth_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (T : SmoothCcTensor g₀ 0 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (radialScaleSmooth (I := I) (M := M) g₀ a R₀ T)‖ ≤ R₀ := by
  set n := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ with hn
  have hn0 : 0 ≤ n := norm_nonneg _
  have hcnn : 0 ≤ min 1 (R₀ / n) := le_min zero_le_one (div_nonneg hR₀ hn0)
  rw [radialScaleSmooth, smoothCcToTensorHs_smul, tensorHs_norm_smul, abs_of_nonneg hcnn]
  rcases eq_or_lt_of_le hn0 with heq | hpos
  · rw [← heq]; simpa using hR₀
  · have hmin_le : min 1 (R₀ / n) ≤ R₀ / n := min_le_right _ _
    calc min 1 (R₀ / n) * n ≤ (R₀ / n) * n :=
          mul_le_mul_of_nonneg_right hmin_le hn0
      _ = R₀ := by field_simp

theorem smoothCcToTensorHs_radialScaleSmooth_eq_ballRetraction
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (R₀ : ℝ) (T : SmoothCcTensor g₀ 0 2) :
    smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (radialScaleSmooth (I := I) (M := M) g₀ a R₀ T) =
      ballRetraction R₀ (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T) := by
  rw [radialScaleSmooth, smoothCcToTensorHs_smul, ballRetraction]

open Classical in

def deTurckSobolevNHa2 (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) :
    tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) :=
  fun v =>
    if h : ∃ p : ℝ × ℝ, 0 < p.1 ∧ p.2 < 1 ∧
        ∀ (T : SmoothCcTensor g₀ 0 2),
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤ p.1 →
          gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) p.2 then
      Dense.extend (smoothCcToTensorHs_denseRange (I := I) (M := M) g₀ ((a : ℝ) + 2))
        (fun x =>
          deTurckSmoothN (I := I) (M := M) g₀ g_bg a
            (radialScaleSmooth (I := I) (M := M) g₀ a (Classical.choose h).1
              (Classical.choose x.2))
            (Classical.choose_spec h).2.1
            ((Classical.choose_spec h).2.2 _
              (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M)
                g₀ a (Classical.choose_spec h).1.le (Classical.choose x.2))))
        (recenteredBallRetraction (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
          (Classical.choose h).1 v)
    else 0

theorem deTurckSobolevNHa2_exists_of_super (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    ∃ p : ℝ × ℝ, 0 < p.1 ∧ p.2 < 1 ∧
      ∀ (T : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤ p.1 →
        gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) p.2 := by
  obtain ⟨R₀, hR₀, δ₀, hδ₀_lt, hball⟩ :=
    sobolevBall_smooth_fibreSmall (I := I) (M := M) g₀ a ha_super
  exact ⟨(R₀, δ₀), hR₀, hδ₀_lt, hball⟩

theorem deTurckSobolevNHa2_lipschitzWith (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) (ha_even : Even a) :
    ∃ K : ℝ≥0, LipschitzWith K (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a) := by
  classical
  have h := deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a ha_super
  set R₀ := (Classical.choose h).1 with hR₀_def
  have hR₀ : 0 < R₀ := (Classical.choose_spec h).1
  have hδ₀_lt : (Classical.choose h).2 < 1 := (Classical.choose_spec h).2.1
  obtain ⟨K, hK⟩ :=
    deTurckSmoothN_ballLipschitz_Ha2 (I := I) (M := M) g₀ g_bg a ha_super ha_even hR₀
      (Classical.choose_spec h).2.1
  
  set F : (Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2))) →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) :=
    fun x =>
      deTurckSmoothN (I := I) (M := M) g₀ g_bg a
        (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose x.2))
        (Classical.choose_spec h).2.1
        ((Classical.choose_spec h).2.2 _
          (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M)
            g₀ a hR₀.le (Classical.choose x.2))) with hF_def
  
  have hembed : ∀ x : Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)),
      smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose x.2)) =
          ballRetraction R₀ (x : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) := by
    intro x
    rw [smoothCcToTensorHs_radialScaleSmooth_eq_ballRetraction, Classical.choose_spec x.2]
  
  have hF_lip : ∀ x y : Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)),
      ‖F x - F y‖ ≤ (K : ℝ) *
        ‖(x : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) - (y : _)‖ := by
    intro x y
    have hbound := hK
      (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose x.2))
      (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose y.2))
      (le_refl _)
      ((Classical.choose_spec h).2.2 _
        (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _))
      (le_refl _)
      ((Classical.choose_spec h).2.2 _
        (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _))
      (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _)
      (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _)
    calc ‖F x - F y‖ ≤ (K : ℝ) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose x.2)) -
              smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose y.2))‖ := hbound
      _ = (K : ℝ) * ‖ballRetraction R₀
              (x : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) -
            ballRetraction R₀ (y : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ := by
            rw [hembed x, hembed y]
      _ ≤ (K : ℝ) * ‖(x : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) -
            (y : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ := by
            have hlip := (lipschitzWith_ballRetraction (X := tensorHs (I := I) (M := M)
              g₀ 0 2 ((a : ℝ) + 2)) hR₀.le).dist_le_mul
              (x : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
              (y : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
            rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm] at hlip
            exact mul_le_mul_of_nonneg_left hlip K.coe_nonneg
  
  have hlipF : LipschitzWith K F := by
    refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
    rw [dist_eq_norm, Subtype.dist_eq, dist_eq_norm]
    exact hF_lip x y
  have hF_cont : Continuous F := hlipF.continuous
  
  have hdense := smoothCcToTensorHs_denseRange (I := I) (M := M) g₀ ((a : ℝ) + 2)
  have hext_eq : ∀ x : Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)),
      Dense.extend hdense F (x : _) = F x := fun x => hdense.extend_eq hF_cont x
  have hext_cont : Continuous (Dense.extend hdense F) :=
    (hdense.uniformContinuous_extend hlipF.uniformContinuous).continuous
  
  have hext_lip_s : LipschitzOnWith K (Dense.extend hdense F)
      (Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2))) := by
    refine lipschitzOnWith_iff_dist_le_mul.mpr (fun p hp q hq => ?_)
    obtain ⟨xp, hxp⟩ := hp
    obtain ⟨xq, hxq⟩ := hq
    have hep : Dense.extend hdense F p = F ⟨p, ⟨xp, hxp⟩⟩ := by
      have := hext_eq ⟨p, ⟨xp, hxp⟩⟩; simpa using this
    have heq : Dense.extend hdense F q = F ⟨q, ⟨xq, hxq⟩⟩ := by
      have := hext_eq ⟨q, ⟨xq, hxq⟩⟩; simpa using this
    rw [dist_eq_norm, hep, heq, dist_eq_norm]
    exact hF_lip ⟨p, ⟨xp, hxp⟩⟩ ⟨q, ⟨xq, hxq⟩⟩
  have hext_lip : LipschitzWith K (Dense.extend hdense F) := by
    have hcl : LipschitzOnWith K (Dense.extend hdense F)
        (closure (Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)))) :=
      hext_lip_s.closure (hext_cont.continuousOn)
    rw [hdense.closure_range] at hcl
    rwa [lipschitzOnWith_univ] at hcl
  
  refine ⟨K, ?_⟩
  have hretr : LipschitzWith 1 (recenteredBallRetraction
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) R₀) :=
    recenteredBallRetraction_lipschitzWith hR₀.le _
  have hcomp : LipschitzWith (K * 1)
      ((Dense.extend hdense F) ∘ (recenteredBallRetraction
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) R₀)) :=
    hext_lip.comp hretr
  rw [mul_one] at hcomp
  have heq_fun : deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a =
      (Dense.extend hdense F) ∘ (recenteredBallRetraction
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) R₀) := by
    funext v
    rw [deTurckSobolevNHa2]
    rw [dif_pos h]
    rfl
  rw [heq_fun]
  exact hcomp

theorem deTurckSobolevNHa2_lipschitzOnWith (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) (ha_even : Even a)
    (R : ℝ) (u₀ : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) :
    ∃ L_R : ℝ≥0, LipschitzOnWith L_R (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a)
      (Metric.closedBall u₀ R) := by
  obtain ⟨K, hK⟩ := deTurckSobolevNHa2_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super ha_even
  exact ⟨K, hK.lipschitzOnWith⟩

theorem deTurckSobolevNHa2_eq_smoothN (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) (ha_even : Even a)
    (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤
      (Classical.choose (deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a ha_super)).1) :
    deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T) =
      deTurckSmoothN (I := I) (M := M) g₀ g_bg a T hδ_lt hδ := by
  classical
  have h := deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a ha_super
  set R₀ := (Classical.choose h).1 with hR₀_def
  have hR₀ : 0 < R₀ := (Classical.choose_spec h).1
  
  set hdense := smoothCcToTensorHs_denseRange (I := I) (M := M) g₀ ((a : ℝ) + 2) with hdense_def
  set F : (Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2))) →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) :=
    fun x =>
      deTurckSmoothN (I := I) (M := M) g₀ g_bg a
        (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose x.2))
        (Classical.choose_spec h).2.1
        ((Classical.choose_spec h).2.2 _
          (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M)
            g₀ a hR₀.le (Classical.choose x.2))) with hF_def
  
  obtain ⟨K, hK⟩ :=
    deTurckSmoothN_ballLipschitz_Ha2 (I := I) (M := M) g₀ g_bg a ha_super ha_even hR₀
      (Classical.choose_spec h).2.1
  have hembed : ∀ x : Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)),
      smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose x.2)) =
          ballRetraction R₀ (x : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) := by
    intro x
    rw [smoothCcToTensorHs_radialScaleSmooth_eq_ballRetraction, Classical.choose_spec x.2]
  have hF_cont : Continuous F := by
    refine (LipschitzWith.of_dist_le_mul (K := K) (fun x y => ?_)).continuous
    rw [dist_eq_norm, Subtype.dist_eq, dist_eq_norm]
    have hbound := hK
      (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose x.2))
      (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose y.2))
      (le_refl _)
      ((Classical.choose_spec h).2.2 _
        (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _))
      (le_refl _)
      ((Classical.choose_spec h).2.2 _
        (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _))
      (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _)
      (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _)
    calc ‖F x - F y‖ ≤ (K : ℝ) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose x.2)) -
              smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose y.2))‖ := hbound
      _ = (K : ℝ) * ‖ballRetraction R₀
              (x : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) -
            ballRetraction R₀ (y : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ := by
            rw [hembed x, hembed y]
      _ ≤ (K : ℝ) * ‖(x : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) -
            (y : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ := by
            have hlip := (lipschitzWith_ballRetraction (X := tensorHs (I := I) (M := M)
              g₀ 0 2 ((a : ℝ) + 2)) hR₀.le).dist_le_mul
              (x : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
              (y : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
            rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm] at hlip
            exact mul_le_mul_of_nonneg_left hlip K.coe_nonneg
  
  have hmem : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T ∈
      Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)) := ⟨T, rfl⟩
  have hunfold : deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
      (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T) =
      Dense.extend hdense F
        (recenteredBallRetraction (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) R₀
          (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T)) := by
    rw [deTurckSobolevNHa2, dif_pos h]
  
  have hfix : recenteredBallRetraction (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) R₀
      (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T) =
      smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T := by
    refine recenteredBallRetraction_eq_self_of_mem ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hball
  rw [hunfold, hfix, hdense.extend_eq hF_cont ⟨_, hmem⟩]
  
  
  change deTurckSmoothN (I := I) (M := M) g₀ g_bg a
      (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose hmem)) _ _ =
    deTurckSmoothN (I := I) (M := M) g₀ g_bg a T hδ_lt hδ
  refine deTurckSmoothN_embedding_wellDefined (I := I) (M := M) g₀ g_bg a ha_super ha_even _ T _ _ _ _ ?_
  rw [smoothCcToTensorHs_radialScaleSmooth_eq_ballRetraction, Classical.choose_spec hmem]
  exact ballRetraction_eq_self_of_mem hball

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
