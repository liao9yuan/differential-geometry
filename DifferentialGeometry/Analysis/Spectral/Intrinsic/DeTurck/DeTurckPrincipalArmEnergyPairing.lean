import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckPrincipalCometricExtraction
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralPouNormEquiv
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricDifferenceSlotPairing
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.OperatorFieldPairingIBP
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorDirichletCurrentGreenIdentityRS
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.FaithfulH1Embedding
import DifferentialGeometry.Analysis.Spectral.Tensor.Spectrum.EigenBasis
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Geometry.Connection.TensorNabla.SlotInsertCovariantNaturality
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.IteratedCovGradHsJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.DirichletSpectralBochnerGap
import DifferentialGeometry.Geometry.Connection.TensorNabla.EndoCovariantDerivativeSelfAdjoint
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.SlotInsertSelfAdjointPairing

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
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
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private theorem tensorL2Inner_eq_tsum_l2Coeff_cross_arm
    (g₀ : SmoothRiemannianMetric I M)
    (A B : SmoothCcTensor g₀ 0 2) :
    tensorL2Inner (I := I) (M := M) g₀ 0 2 A.toFun B.toFun =
      ∑' i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 2,
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 A) i *
          tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 B) i := by
  classical
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
    with hcompact_def
  set b := tensorResolventHilbertEigenbasisSigma (I := I) (M := M) h_compact with hb_def
  have hinner_eq : tensorL2Inner (I := I) (M := M) g₀ 0 2 A.toFun B.toFun =
      (⟪SmoothCcTensor.toL2 A, SmoothCcTensor.toL2 B⟫_ℝ : ℝ) := by
    rw [DifferentialGeometry.Integral.L2.SmoothCcTensor.inner_toL2
      (I := I) (M := M) A B]
    exact (SmoothCcTensor.inner_def (I := I) (M := M) A B).symm
  rw [hinner_eq]
  have h_par := b.tsum_inner_mul_inner (SmoothCcTensor.toL2 A) (SmoothCcTensor.toL2 B)
  rw [← h_par]
  refine tsum_congr (fun i => ?_)
  rw [tensorL2Coeff_eq_inner (I := I) (M := M) h_compact (SmoothCcTensor.toL2 A) i,
    tensorL2Coeff_eq_inner (I := I) (M := M) h_compact (SmoothCcTensor.toL2 B) i]
  rw [show (⟪SmoothCcTensor.toL2 A, b i⟫_ℝ : ℝ) = ⟪b i, SmoothCcTensor.toL2 A⟫_ℝ from
    real_inner_comm _ _]

private theorem spectralPairing_tsum_eq_oneMinusConnLapIter_l2Inner
    (g₀ : SmoothRiemannianMetric I M) (n : ℕ)
    (u₀ : SmoothCcTensor g₀ 0 2) (A : SmoothCcTensor g₀ 0 2) :
    ∑' i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g₀ 0 2,
        tensorSobolevWeight (I := I) (M := M) i ((n : ℕ) : ℝ) *
          ((smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀).coeff i *
            (smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) A).coeff i) =
      tensorL2Inner (I := I) (M := M) g₀ 0 2
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀).toFun
        A.toFun := by
  classical
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
    with hcompact_def
  rw [tensorL2Inner_eq_tsum_l2Coeff_cross_arm (I := I) (M := M) g₀
    (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀) A]
  refine tsum_congr (fun i => ?_)
  rw [smoothCcToTensorHs_coeff, smoothCcToTensorHs_coeff]
  rw [tensorL2Coeff_ofCompact_oneMinusConnLapSmoothIter (I := I) (M := M) g₀ h_compact u₀ i n]
  have hweight : tensorSobolevWeight (I := I) (M := M) i ((n : ℕ) : ℝ) =
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ n := by
    unfold tensorSobolevWeight
    rw [Real.rpow_natCast]
  rw [hweight]
  ring

private noncomputable def negGInvDiffSlotApplied
    (g₀ g₁ : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (W : TensorRSSpace 0 (s + 1) I x) : TensorRSSpace 0 (s + 1) I x :=
  TensorRSSpace.ofCLM
    ((slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x
        (-gInvDiffRaisedEndo (I := I) g₀ g₁ x)).comp
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from W))

private theorem slotInsertEndoFib_neg_left (s : ℕ) (k : Fin s) (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) :
    slotInsertEndoFib (I := I) (M := M) s k x (-Λ) =
      - slotInsertEndoFib (I := I) (M := M) s k x Λ := by
  rw [show (-Λ) = (-1 : ℝ) • Λ from by rw [neg_one_smul],
    slotInsertEndoFib_smul_left (I := I) (M := M) s k x (-1 : ℝ) Λ, neg_one_smul]

private theorem negGInvDiffSlotApplied_eq_neg
    (g₀ g₁ : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (W : TensorRSSpace 0 (s + 1) I x) :
    negGInvDiffSlotApplied (I := I) g₀ g₁ s x W =
      - gInvDiffSlotApplied (I := I) g₀ g₁ s x W := by
  rw [negGInvDiffSlotApplied, gInvDiffSlotApplied,
    slotInsertEndoFib_neg_left (I := I) (M := M) (s + 1) 0 x
      (gInvDiffRaisedEndo (I := I) g₀ g₁ x),
    ContinuousLinearMap.neg_comp]
  rfl

private theorem toModel_negGInvDiffSlotApplied_eq
    (g₀ g₁ : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (W : TensorRSSpace 0 (s + 1) I x) :
    TensorRSSpace.toModel (𝕜 := ℝ) (E := E)
        (negGInvDiffSlotApplied (I := I) g₀ g₁ s x W) =
      - TensorRSSpace.toModel (𝕜 := ℝ) (E := E)
          (gInvDiffSlotApplied (I := I) g₀ g₁ s x W) := by
  rw [negGInvDiffSlotApplied_eq_neg (I := I) g₀ g₁ s x W, TensorRSSpace.toModel_neg]

private theorem negGInvDiffRaisedEndo_g0_self_adjoint
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (a b : TangentSpace I x) :
    g₀.inner x ((-gInvDiffRaisedEndo (I := I) g₀ g₁ x) a) b
      = g₀.inner x a ((-gInvDiffRaisedEndo (I := I) g₀ g₁ x) b) := by
  simp only [ContinuousLinearMap.neg_apply, map_neg]
  rw [gInvDiffRaisedEndo_g0_self_adjoint (I := I) g₀ g₁ x a b]

private theorem negGInvDiffRaisedEndo_inner_self_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : gFibreOpBound (I := I) g₀ h δ)
    (x : M) (v : TangentSpace I x) :
    g₀.inner x ((-gInvDiffRaisedEndo (I := I) g₀ g₁ x) v) v
      ≤ (δ / (1 - δ)) * g₀.inner x v v := by
  rw [ContinuousLinearMap.neg_apply, map_neg]
  have hbnd := abs_inner_gInvDiffRaisedEndo_le (I := I) g₀ g₁ h htie hδ_lt hδ_nn hδ x v v
  have hv_nn : 0 ≤ g₀.inner x v v := metric_inner_self_nonneg (I := I) (M := M) g₀ x v
  have hsq : Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v) = g₀.inner x v v := by
    rw [← Real.sqrt_mul hv_nn, Real.sqrt_mul_self hv_nn]
  have hle : -g₀.inner x (gInvDiffRaisedEndo (I := I) g₀ g₁ x v) v
      ≤ |g₀.inner x (gInvDiffRaisedEndo (I := I) g₀ g₁ x v) v| := neg_le_abs _
  calc -g₀.inner x (gInvDiffRaisedEndo (I := I) g₀ g₁ x v) v
      ≤ |g₀.inner x (gInvDiffRaisedEndo (I := I) g₀ g₁ x v) v| := hle
    _ ≤ (δ / (1 - δ)) * (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v)) := hbnd
    _ = (δ / (1 - δ)) * g₀.inner x v v := by rw [hsq]

private theorem tensorInnerPointwise_negGInvDiffSlot_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : gFibreOpBound (I := I) g₀ h δ)
    (s : ℕ) (x : M) (W : TensorRSSpace 0 (s + 1) I x) :
    tensorInnerPointwise (I := I) (M := M) g₀ 0 (s + 1) x
        (TensorRSSpace.toModel W)
        (TensorRSSpace.toModel (negGInvDiffSlotApplied (I := I) g₀ g₁ s x W))
      ≤ (δ / (1 - δ)) * tensorInnerPointwise (I := I) (M := M) g₀ 0 (s + 1) x
          (TensorRSSpace.toModel W) (TensorRSSpace.toModel W) := by
  obtain ⟨e, bse, hbse, horth⟩ :=
    DifferentialGeometry.Analysis.Sobolev.TensorHilbert.exists_orthoFrame_basis_E
      (I := I) (M := M) g₀ x
  exact DifferentialGeometry.Analysis.Sobolev.TensorHilbert.tensorInnerPointwise_slotΛ_le
    (I := I) (M := M) g₀ s x (-gInvDiffRaisedEndo (I := I) g₀ g₁ x)
    (negGInvDiffRaisedEndo_g0_self_adjoint (I := I) g₀ g₁ x)
    (fun v => negGInvDiffRaisedEndo_inner_self_le (I := I) g₀ g₁ h htie hδ_lt hδ_nn hδ x v)
    W e bse hbse horth

theorem rawConnLap_selfAdjoint (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T v : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r s (rawTensorConnLapSmooth (I := I) g r s T).toFun v.toFun =
      tensorL2Inner (I := I) (M := M) g r s T.toFun
        (rawTensorConnLapSmooth (I := I) g r s v).toFun := by
  have hTv := tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs
    (I := I) (M := M) g r s T v
  have hvT := tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs
    (I := I) (M := M) g r s v T
  have hsymm1 := tensorL2Inner_symm (I := I) (M := M) g r (s + 1)
    (covGrad (I := I) (M := M) g r s T).toFun (covGrad (I := I) (M := M) g r s v).toFun
  have hsymm2 := tensorL2Inner_symm (I := I) (M := M) g r s
    (rawTensorConnLapSmooth (I := I) g r s v).toFun T.toFun
  rw [hsymm1, hvT] at hTv; rw [← hsymm2]; linarith [hTv]

private theorem tensorL2Inner_sub_left_smoothCc (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ T : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r s (S₁.toFun - S₂.toFun) T.toFun =
      tensorL2Inner (I := I) (M := M) g r s S₁.toFun T.toFun -
        tensorL2Inner (I := I) (M := M) g r s S₂.toFun T.toFun := by
  have hsub : (S₁.toFun - S₂.toFun) = S₁.toFun + (-1 : ℝ) • S₂.toFun := by
    funext x
    rw [Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
    module
  have hint2 : MeasureTheory.Integrable (fun x =>
      tensorInnerPointwise (I := I) (M := M) g r s x (((-1 : ℝ) • S₂.toFun) x) (T.toFun x))
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hbase := DifferentialGeometry.Integral.L2.SmoothCcTensor.integrable_inner_cross
      (I := I) (M := M) S₂ T
    have heq : (fun x => tensorInnerPointwise (I := I) (M := M) g r s x
          (((-1 : ℝ) • S₂.toFun) x) (T.toFun x))
        = (fun x => (-1 : ℝ) * tensorInnerPointwise (I := I) (M := M) g r s x
          (S₂.toFun x) (T.toFun x)) := by
      funext x
      show tensorInnerPointwise (I := I) (M := M) g r s x ((-1 : ℝ) • S₂.toFun x) (T.toFun x) = _
      rw [tensorInnerPointwise_smul_left]
    rw [heq]
    exact hbase.const_mul (-1 : ℝ)
  rw [hsub, tensorL2Inner_add_left (I := I) (M := M) g r s S₁.toFun ((-1 : ℝ) • S₂.toFun) T.toFun
    (DifferentialGeometry.Integral.L2.SmoothCcTensor.integrable_inner_cross
      (I := I) (M := M) S₁ T) hint2,
    tensorL2Inner_smul_left]
  ring

private theorem tensorL2Inner_sub_right_smoothCc (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T₁ T₂ : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r s S.toFun (T₁.toFun - T₂.toFun) =
      tensorL2Inner (I := I) (M := M) g r s S.toFun T₁.toFun -
        tensorL2Inner (I := I) (M := M) g r s S.toFun T₂.toFun := by
  have hsub : (T₁.toFun - T₂.toFun) = T₁.toFun + (-1 : ℝ) • T₂.toFun := by
    funext x
    rw [Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
    module
  have hint2 : MeasureTheory.Integrable (fun x =>
      tensorInnerPointwise (I := I) (M := M) g r s x (S.toFun x) (((-1 : ℝ) • T₂.toFun) x))
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hbase := DifferentialGeometry.Integral.L2.SmoothCcTensor.integrable_inner_cross
      (I := I) (M := M) S T₂
    have heq : (fun x => tensorInnerPointwise (I := I) (M := M) g r s x
          (S.toFun x) (((-1 : ℝ) • T₂.toFun) x))
        = (fun x => (-1 : ℝ) * tensorInnerPointwise (I := I) (M := M) g r s x
          (S.toFun x) (T₂.toFun x)) := by
      funext x
      show tensorInnerPointwise (I := I) (M := M) g r s x (S.toFun x) ((-1 : ℝ) • T₂.toFun x) = _
      rw [tensorInnerPointwise_smul_right]
    rw [heq]
    exact hbase.const_mul (-1 : ℝ)
  rw [hsub, tensorL2Inner_add_right (I := I) (M := M) g r s S.toFun T₁.toFun ((-1 : ℝ) • T₂.toFun)
    (DifferentialGeometry.Integral.L2.SmoothCcTensor.integrable_inner_cross
      (I := I) (M := M) S T₁) hint2,
    tensorL2Inner_smul_right]
  ring

theorem oneMinusConnLapSmooth_l2Inner_selfAdjoint (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T v : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r s (oneMinusConnLapSmooth (I := I) g r s T).toFun v.toFun =
      tensorL2Inner (I := I) (M := M) g r s T.toFun
        (oneMinusConnLapSmooth (I := I) g r s v).toFun := by
  have hTfun : (oneMinusConnLapSmooth (I := I) g r s T).toFun =
      T.toFun - (rawTensorConnLapSmooth (I := I) g r s T).toFun := by
    unfold oneMinusConnLapSmooth
    rw [SmoothCcTensor.toFun_sub]
  have hvfun : (oneMinusConnLapSmooth (I := I) g r s v).toFun =
      v.toFun - (rawTensorConnLapSmooth (I := I) g r s v).toFun := by
    unfold oneMinusConnLapSmooth
    rw [SmoothCcTensor.toFun_sub]
  rw [hTfun, hvfun,
    tensorL2Inner_sub_left_smoothCc (I := I) (M := M) g r s T
      (rawTensorConnLapSmooth (I := I) g r s T) v,
    tensorL2Inner_sub_right_smoothCc (I := I) (M := M) g r s T v
      (rawTensorConnLapSmooth (I := I) g r s v)]
  rw [rawConnLap_selfAdjoint (I := I) (M := M) g r s T v]

theorem oneMinusConnLapSmooth_l2Inner_eq_add_covGrad
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (A B : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r s
        (oneMinusConnLapSmooth (I := I) g r s A).toFun B.toFun =
      tensorL2Inner (I := I) (M := M) g r s A.toFun B.toFun +
        tensorL2Inner (I := I) (M := M) g r (s + 1)
          (covGrad (I := I) (M := M) g r s A).toFun
          (covGrad (I := I) (M := M) g r s B).toFun := by
  have hAfun : (oneMinusConnLapSmooth (I := I) g r s A).toFun =
      A.toFun - (rawTensorConnLapSmooth (I := I) g r s A).toFun := by
    unfold oneMinusConnLapSmooth
    rw [SmoothCcTensor.toFun_sub]
  have hgreen := tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs
    (I := I) (M := M) g r s A B
  rw [hAfun,
    tensorL2Inner_sub_left_smoothCc (I := I) (M := M) g r s A
      (rawTensorConnLapSmooth (I := I) g r s A) B,
    hgreen]
  ring

theorem oneMinusConnLapSmoothIter_oneMinusConnLapSmooth_comm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (k : ℕ) (v : SmoothCcTensor g r s) :
    oneMinusConnLapSmoothIter (I := I) g r s k (oneMinusConnLapSmooth (I := I) g r s v) =
      oneMinusConnLapSmooth (I := I) g r s (oneMinusConnLapSmoothIter (I := I) g r s k v) := by
  induction k with
  | zero => simp only [oneMinusConnLapSmoothIter_zero]
  | succ p ih =>
    rw [oneMinusConnLapSmoothIter_succ, ih, oneMinusConnLapSmoothIter_succ]

theorem oneMinusConnLapSmoothIter_l2Inner_selfAdjoint (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (n : ℕ) (T v : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r s
        (oneMinusConnLapSmoothIter (I := I) g r s n T).toFun v.toFun =
      tensorL2Inner (I := I) (M := M) g r s T.toFun
        (oneMinusConnLapSmoothIter (I := I) g r s n v).toFun := by
  induction n generalizing v with
  | zero => simp only [oneMinusConnLapSmoothIter_zero]
  | succ k ih =>
    rw [oneMinusConnLapSmoothIter_succ, oneMinusConnLapSmoothIter_succ]
    rw [oneMinusConnLapSmooth_l2Inner_selfAdjoint (I := I) (M := M) g r s
      (oneMinusConnLapSmoothIter (I := I) g r s k T) v]
    rw [ih (oneMinusConnLapSmooth (I := I) g r s v),
      oneMinusConnLapSmoothIter_oneMinusConnLapSmooth_comm]

theorem oneMinusConnLapSmoothIter_add (g : SmoothRiemannianMetric I M) (r s : ℕ) (a b : ℕ)
    (T : SmoothCcTensor g r s) :
    oneMinusConnLapSmoothIter (I := I) g r s (a + b) T =
      oneMinusConnLapSmoothIter (I := I) g r s a
        (oneMinusConnLapSmoothIter (I := I) g r s b T) := by
  induction a with
  | zero => simp only [Nat.zero_add, oneMinusConnLapSmoothIter_zero]
  | succ k ih =>
    rw [show k + 1 + b = (k + b) + 1 from by omega, oneMinusConnLapSmoothIter_succ,
      oneMinusConnLapSmoothIter_succ, ih]

theorem oneMinusConnLapSmoothIter_l2Inner_sym_split
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (a b : ℕ)
    (A B : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r s
        (oneMinusConnLapSmoothIter (I := I) g r s (a + b) A).toFun B.toFun =
      tensorL2Inner (I := I) (M := M) g r s
        (oneMinusConnLapSmoothIter (I := I) g r s b A).toFun
        (oneMinusConnLapSmoothIter (I := I) g r s a B).toFun := by
  rw [oneMinusConnLapSmoothIter_add (I := I) (M := M) g r s a b A]
  rw [oneMinusConnLapSmoothIter_l2Inner_selfAdjoint (I := I) (M := M) g r s a
    (oneMinusConnLapSmoothIter (I := I) g r s b A) B]

theorem oneMinusConnLapSmoothIter_l2Inner_eq_add_sum_covGrad
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (n : ℕ)
    (A B : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r s
        (oneMinusConnLapSmoothIter (I := I) g r s n A).toFun B.toFun =
      tensorL2Inner (I := I) (M := M) g r s A.toFun B.toFun +
        ∑ m ∈ Finset.range n,
          tensorL2Inner (I := I) (M := M) g r (s + 1)
            (covGrad (I := I) (M := M) g r s
              (oneMinusConnLapSmoothIter (I := I) g r s m A)).toFun
            (covGrad (I := I) (M := M) g r s B).toFun := by
  induction n with
  | zero =>
    simp only [oneMinusConnLapSmoothIter_zero, Finset.range_zero, Finset.sum_empty, add_zero]
  | succ k ih =>
    rw [oneMinusConnLapSmoothIter_succ,
      oneMinusConnLapSmooth_l2Inner_eq_add_covGrad (I := I) (M := M) g r s
        (oneMinusConnLapSmoothIter (I := I) g r s k A) B,
      ih, Finset.sum_range_succ]
    ring

private noncomputable def armPrincipalSlotPairing
    (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ) (u₀ : SmoothCcTensor g₀ 0 2) : ℝ :=
  tensorL2Inner (I := I) (M := M) g₀ 0 ((2 + n) + 1)
    (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E)
      ((iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀).toSection x))
    (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E)
      (negGInvDiffSlotApplied
        (I := I) g₀ g₁ (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀).toSection x)))

private theorem armPrincipalSlotPairing_eq_neg_inner
    (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ) (u₀ : SmoothCcTensor g₀ 0 2) :
    armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀ =
      - (⟪iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀,
          appCc (I := I) (M := M) g₀ ((2 + n) + 1) ((2 + n) + 1)
            (slotInsertEndoCc (I := I) (M := M) g₀ (2 + n)
              (gInvDiffRaisedEndoField (I := I) (M := M) g₀ g₁))
            (iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀)⟫_ℝ : ℝ) := by
  classical
  set A : SmoothCcTensor g₀ 0 ((2 + n) + 1) :=
    iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀ with hA_def
  set B : SmoothCcTensor g₀ 0 ((2 + n) + 1) :=
    appCc (I := I) (M := M) g₀ ((2 + n) + 1) ((2 + n) + 1)
      (slotInsertEndoCc (I := I) (M := M) g₀ (2 + n)
        (gInvDiffRaisedEndoField (I := I) (M := M) g₀ g₁)) A with hB_def
  have hBfun : ∀ x : M,
      B.toFun x =
        TensorRSSpace.toModel (𝕜 := ℝ) (E := E)
          (gInvDiffSlotApplied (I := I) g₀ g₁ (2 + n) x (A.toSection x)) := fun x => rfl
  rw [SmoothCcTensor.inner_def (I := I) (M := M) A B]
  rw [armPrincipalSlotPairing]
  have heq :
      (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E)
          (negGInvDiffSlotApplied (I := I) g₀ g₁ (2 + n) x (A.toSection x)))
        = (fun x => - B.toFun x) := by
    funext x
    rw [hBfun x,
      toModel_negGInvDiffSlotApplied_eq (I := I) g₀ g₁ (2 + n) x (A.toSection x)]
  rw [show (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (A.toSection x)) = A.toFun from rfl,
    heq]
  have hsmul : (fun x => - B.toFun x) = (-1 : ℝ) • B.toFun := by
    funext x; rw [Pi.smul_apply, neg_one_smul]
  rw [hsmul,
    tensorL2Inner_smul_right (I := I) (M := M) g₀ 0 ((2 + n) + 1) (-1 : ℝ) A.toFun B.toFun]
  ring

private theorem oneMinusConnLapIter_arm_add_slotInner_squaredLower
    [Nonempty M] (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : gFibreOpBound (I := I) g₀ h δ) :
    ∃ Ccomm : ℝ, 0 ≤ Ccomm ∧
      ∀ (u₀ : SmoothCcTensor g₀ 0 2),
        tensorL2Inner (I := I) (M := M) g₀ 0 2
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀).toFun
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toFun +
          (⟪iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀,
              appCc (I := I) (M := M) g₀ ((2 + n) + 1) ((2 + n) + 1)
                (slotInsertEndoCc (I := I) (M := M) g₀ (2 + n)
                  (gInvDiffRaisedEndoField (I := I) (M := M) g₀ g₁))
                (iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀)⟫_ℝ : ℝ) ≤
        Ccomm *
          (∑ j ∈ Finset.range (n + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) ^ 2 :=
  sorry

private theorem oneMinusConnLapIter_arm_sub_armPrincipalSlotPairing_squaredLower
    [Nonempty M] (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : gFibreOpBound (I := I) g₀ h δ) :
    ∃ Ccomm : ℝ, 0 ≤ Ccomm ∧
      ∀ (u₀ : SmoothCcTensor g₀ 0 2),
        tensorL2Inner (I := I) (M := M) g₀ 0 2
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀).toFun
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toFun -
          armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀ ≤
        Ccomm *
          (∑ j ∈ Finset.range (n + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖) ^ 2 := by
  obtain ⟨Ccomm, hCcomm_nn, hbound⟩ :=
    oneMinusConnLapIter_arm_add_slotInner_squaredLower
      (I := I) (M := M) g₀ g₁ n h htie hδ_lt hδ_nn hδ
  refine ⟨Ccomm, hCcomm_nn, fun u₀ => ?_⟩
  rw [armPrincipalSlotPairing_eq_neg_inner (I := I) (M := M) g₀ g₁ n u₀, sub_neg_eq_add]
  exact hbound u₀

private theorem deTurckArm_residual_ibp_zero
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    ∃ F₀ : SmoothCcTensor g₀ (2 + 1) (2 + 0),
      ∀ (u₀ : SmoothCcTensor g₀ 0 2),
        tensorL2Inner (I := I) (M := M) g₀ 0 2
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 0 u₀).toFun
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toFun -
          armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ 0 u₀ =
        (⟪iteratedCovGrad (I := I) g₀ 0 2 0 u₀,
            appCc (I := I) (M := M) g₀ (2 + 1) (2 + 0) F₀
              (iteratedCovGrad (I := I) g₀ 0 2 1 u₀)⟫_ℝ : ℝ) :=
  sorry

private theorem deTurckArm_residual_ibp_succ
    (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ)
    (F_n : SmoothCcTensor g₀ (2 + (n + 1)) (2 + n))
    (hF_n : ∀ (u₀ : SmoothCcTensor g₀ 0 2),
      tensorL2Inner (I := I) (M := M) g₀ 0 2
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀).toFun
          (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toFun -
        armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀ =
      (⟪iteratedCovGrad (I := I) g₀ 0 2 n u₀,
          appCc (I := I) (M := M) g₀ (2 + (n + 1)) (2 + n) F_n
            (iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀)⟫_ℝ : ℝ)) :
    ∃ F : SmoothCcTensor g₀ (2 + ((n + 1) + 1)) (2 + (n + 1)),
      ∀ (u₀ : SmoothCcTensor g₀ 0 2),
        tensorL2Inner (I := I) (M := M) g₀ 0 2
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (n + 1) u₀).toFun
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toFun -
          armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ (n + 1) u₀ =
        (⟪iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀,
            appCc (I := I) (M := M) g₀ (2 + ((n + 1) + 1)) (2 + (n + 1)) F
              (iteratedCovGrad (I := I) g₀ 0 2 ((n + 1) + 1) u₀)⟫_ℝ : ℝ) :=
  sorry

private theorem deTurckArm_residual_ibp
    (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ) :
    ∃ F : SmoothCcTensor g₀ (2 + (n + 1)) (2 + n),
      ∀ (u₀ : SmoothCcTensor g₀ 0 2),
        tensorL2Inner (I := I) (M := M) g₀ 0 2
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀).toFun
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toFun -
          armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀ =
        (⟪iteratedCovGrad (I := I) g₀ 0 2 n u₀,
            appCc (I := I) (M := M) g₀ (2 + (n + 1)) (2 + n) F
              (iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀)⟫_ℝ : ℝ) := by
  induction n with
  | zero =>
    exact deTurckArm_residual_ibp_zero (I := I) (M := M) g₀ g₁
  | succ k ih =>
    obtain ⟨F_k, hF_k⟩ := ih
    obtain ⟨F, hF⟩ :=
      deTurckArm_residual_ibp_succ (I := I) (M := M) g₀ g₁ k F_k hF_k
    exact ⟨F, hF⟩

set_option linter.unusedVariables false in
private theorem arm_residual_cross_decomp
    [Nonempty M] (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : gFibreOpBound (I := I) g₀ h δ) :
    ∃ Cop : ℝ, 0 ≤ Cop ∧
      ∀ (u₀ : SmoothCcTensor g₀ 0 2),
        ∃ Z : SmoothCcTensor g₀ 0 (2 + n),
          tensorL2Inner (I := I) (M := M) g₀ 0 2
              (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀).toFun
              (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toFun -
            armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀ =
            (⟪iteratedCovGrad (I := I) g₀ 0 2 n u₀, Z⟫_ℝ : ℝ) ∧
          ‖Z‖ ≤ Cop * ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀‖ := by
  classical
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨F, hF⟩ := deTurckArm_residual_ibp (I := I) (M := M) g₀ g₁ n
  obtain ⟨CopF, hCopF_nn, hCopF⟩ :=
    exists_uniform_riemannianFiberNormSq_appCc_le (I := I) (M := M) g₀ (2 + (n + 1)) (2 + n) F
  refine ⟨Real.sqrt CopF, Real.sqrt_nonneg _, fun u₀ => ?_⟩
  set Z : SmoothCcTensor g₀ 0 (2 + n) :=
    appCc (I := I) (M := M) g₀ (2 + (n + 1)) (2 + n) F
      (iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀) with hZ_def
  refine ⟨Z, hF u₀, ?_⟩
  set W : SmoothCcTensor g₀ 0 (2 + (n + 1)) :=
    iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀ with hW_def
  have hZn : ‖Z‖ = tensorL2Norm (I := I) (M := M) g₀ 0 (2 + n) Z.toFun :=
    SmoothCcTensor.norm_def (I := I) (M := M) Z
  have hWn : ‖W‖ = tensorL2Norm (I := I) (M := M) g₀ 0 (2 + (n + 1)) W.toFun :=
    SmoothCcTensor.norm_def (I := I) (M := M) W
  have hZL2 : ‖Z‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + n) x (Z.toSection x)
        ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    rw [hZn, tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ (2 + n) Z]
  have hWL2 : ‖W‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (n + 1)) x (W.toSection x)
        ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    rw [hWn,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ (2 + (n + 1)) W]
  have hpt : ∀ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + n) x (Z.toSection x) ≤
      CopF * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (n + 1)) x (W.toSection x) := by
    intro x
    exact hCopF W x
  have hWint : MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (n + 1)) x (W.toSection x))
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    DifferentialGeometry.Integral.Connection.integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g₀ 0 (2 + (n + 1)) W
  have hZsq_le : ‖Z‖ ^ 2 ≤ CopF * ‖W‖ ^ 2 := by
    rw [hZL2, hWL2]
    have hg_int : MeasureTheory.Integrable
        (fun x => CopF * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (n + 1)) x (W.toSection x))
        (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) :=
      hWint.const_mul CopF
    have hmono :=
      MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun x => riemannianFiberNormSq_nonneg (I := I) (M := M)
          g₀ 0 (2 + n) x _)) hg_int
        (Filter.Eventually.of_forall hpt)
    rw [integral_const_mul] at hmono
    linarith
  have hWnn : 0 ≤ ‖W‖ := norm_nonneg _
  have hZnn : 0 ≤ ‖Z‖ := norm_nonneg _
  have hCopW_nn : 0 ≤ CopF * ‖W‖ ^ 2 := mul_nonneg hCopF_nn (sq_nonneg _)
  have hkey : ‖Z‖ ≤ Real.sqrt CopF * ‖W‖ := by
    rw [← Real.sqrt_sq hZnn, ← Real.sqrt_sq hWnn]
    refine le_trans (Real.sqrt_le_sqrt hZsq_le) ?_
    rw [Real.sqrt_mul hCopF_nn]
  exact hkey

private theorem arm_residual_cross_bound
    [Nonempty M] (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : gFibreOpBound (I := I) g₀ h δ) :
    ∃ Ccross : ℝ, 0 ≤ Ccross ∧
      ∀ (u₀ : SmoothCcTensor g₀ 0 2),
        tensorL2Inner (I := I) (M := M) g₀ 0 2
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀).toFun
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toFun -
          armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀ ≤
        Ccross *
          (‖iteratedCovGrad (I := I) g₀ 0 2 n u₀‖ *
            ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀‖) := by
  obtain ⟨Cop, hCop_nn, hCop⟩ :=
    arm_residual_cross_decomp (I := I) (M := M) g₀ g₁ n h htie hδ_lt hδ_nn hδ
  refine ⟨Cop, hCop_nn, fun u₀ => ?_⟩
  obtain ⟨Z, hZeq, hZbnd⟩ := hCop u₀
  rw [hZeq]
  have habs : (⟪iteratedCovGrad (I := I) g₀ 0 2 n u₀, Z⟫_ℝ : ℝ) ≤
      ‖iteratedCovGrad (I := I) g₀ 0 2 n u₀‖ * ‖Z‖ :=
    real_inner_le_norm _ _
  calc (⟪iteratedCovGrad (I := I) g₀ 0 2 n u₀, Z⟫_ℝ : ℝ)
      ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 n u₀‖ * ‖Z‖ := habs
    _ ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 n u₀‖ *
        (Cop * ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀‖) :=
      mul_le_mul_of_nonneg_left hZbnd (norm_nonneg _)
    _ = Cop *
        (‖iteratedCovGrad (I := I) g₀ 0 2 n u₀‖ *
          ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀‖) := by ring

private theorem exists_oneMinusConnLapIter_arm_sub_armPrincipalSlotPairing_jetBound_core
    [Nonempty M] (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : gFibreOpBound (I := I) g₀ h δ) :
    ∃ Clower : ℝ, 0 ≤ Clower ∧
      ∀ (u₀ : SmoothCcTensor g₀ 0 2),
        tensorL2Inner (I := I) (M := M) g₀ 0 2
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀).toFun
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toFun -
          armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀ ≤
        (1 / 4 : ℝ) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 +
          Clower * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2 := by
  obtain ⟨Ccross, hCcross_nn, hcross⟩ :=
    arm_residual_cross_bound (I := I) (M := M) g₀ g₁ n h htie hδ_lt hδ_nn hδ
  obtain ⟨Cgap, hCgap_nn, hgap⟩ :=
    exists_iteratedCovGrad_l2NormSq_le_smoothCcToTensorHs_succ_add_lower
      (I := I) (M := M) g₀ n
  obtain ⟨Cjet, hCjet_nn, hjet⟩ :=
    DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_iteratedCovGrad_sum_le_smoothCcToTensorHs
      (I := I) (M := M) g₀ n
  refine ⟨(1 / 4) * Cgap + Ccross ^ 2 * Cjet ^ 2, by positivity, fun u₀ => ?_⟩
  set Mtop := ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ with hMtop_def
  set Mlow := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ with hMlow_def
  set Nn := ‖iteratedCovGrad (I := I) g₀ 0 2 n u₀‖ with hNn_def
  set Nnp := ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀‖ with hNnp_def
  have hMtop_nn : 0 ≤ Mtop := norm_nonneg _
  have hMlow_nn : 0 ≤ Mlow := norm_nonneg _
  have hNn_nn : 0 ≤ Nn := norm_nonneg _
  have hNnp_nn : 0 ≤ Nnp := norm_nonneg _
  have hcu := hcross u₀
  have hgap_u := hgap u₀
  have hjet_u := hjet u₀
  have hNn_sum : Nn ≤ ∑ j ∈ Finset.range (n + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ := by
    rw [hNn_def, Finset.sum_range_succ]
    have hsum_nn : 0 ≤ ∑ j ∈ Finset.range n, ‖iteratedCovGrad (I := I) g₀ 0 2 j u₀‖ :=
      Finset.sum_nonneg (fun j _ => norm_nonneg _)
    linarith
  have hNn_le : Nn ≤ Cjet * Mlow := le_trans hNn_sum hjet_u
  have hNn_sq_le : Nn ^ 2 ≤ (Cjet * Mlow) ^ 2 := by
    apply sq_le_sq'
    · nlinarith [hNn_nn, mul_nonneg hCjet_nn hMlow_nn]
    · exact hNn_le
  have hNnp_toL2 : Nnp =
      ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀)‖ := by
    rw [hNnp_def, SmoothCcTensor.norm_toL2]
  have hNnp_sq_le : Nnp ^ 2 ≤ Mtop ^ 2 + Cgap * Mlow ^ 2 := by
    rw [hNnp_toL2]; exact hgap_u
  have hcross_young : Ccross * (Nn * Nnp) ≤ (1 / 4) * Nnp ^ 2 + Ccross ^ 2 * Nn ^ 2 := by
    nlinarith [sq_nonneg (Nnp / 2 - Ccross * Nn),
      sq_nonneg (Ccross * Nn), sq_nonneg Nnp, hNn_nn, hNnp_nn, hCcross_nn]
  have hMtop_sq_nn : 0 ≤ Mtop ^ 2 := sq_nonneg _
  have hMlow_sq_nn : 0 ≤ Mlow ^ 2 := sq_nonneg _
  calc tensorL2Inner (I := I) (M := M) g₀ 0 2
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀).toFun
          (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toFun -
        armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀
      ≤ Ccross * (Nn * Nnp) := hcu
    _ ≤ (1 / 4) * Nnp ^ 2 + Ccross ^ 2 * Nn ^ 2 := hcross_young
    _ ≤ (1 / 4) * (Mtop ^ 2 + Cgap * Mlow ^ 2) + Ccross ^ 2 * (Cjet * Mlow) ^ 2 := by
        nlinarith [hNnp_sq_le, hNn_sq_le, hMtop_sq_nn, hMlow_sq_nn, hCcross_nn, hCjet_nn]
    _ = (1 / 4 : ℝ) * Mtop ^ 2 + ((1 / 4) * Cgap + Ccross ^ 2 * Cjet ^ 2) * Mlow ^ 2 := by ring

private theorem oneMinusConnLapIter_arm_sub_armPrincipalSlotPairing_le
    [Nonempty M] (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : gFibreOpBound (I := I) g₀ h δ) :
    ∃ Clower : ℝ, 0 ≤ Clower ∧
      ∀ (u₀ : SmoothCcTensor g₀ 0 2),
        tensorL2Inner (I := I) (M := M) g₀ 0 2
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀).toFun
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toFun -
          armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀ ≤
        (1 / 4 : ℝ) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 +
          Clower * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2 :=
  exists_oneMinusConnLapIter_arm_sub_armPrincipalSlotPairing_jetBound_core
    (I := I) (M := M) g₀ g₁ n h htie hδ_lt hδ_nn hδ

private theorem oneMinusConnLapIter_pairing_fold
    [Nonempty M] (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : gFibreOpBound (I := I) g₀ h δ) :
    ∃ rem : SmoothCcTensor g₀ 0 2 → ℝ,
      (∀ (u₀ : SmoothCcTensor g₀ 0 2),
        tensorL2Inner (I := I) (M := M) g₀ 0 2
            (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀).toFun
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toFun =
          armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀ + rem u₀) ∧
      ∃ Clower : ℝ, 0 ≤ Clower ∧
        ∀ (u₀ : SmoothCcTensor g₀ 0 2),
          rem u₀ ≤
            (1 / 4 : ℝ) *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 +
              Clower * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2 := by
  refine ⟨fun u₀ =>
      tensorL2Inner (I := I) (M := M) g₀ 0 2
          (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀).toFun
          (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toFun -
        armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀,
    fun u₀ => by ring, ?_⟩
  obtain ⟨Clower, hClower_nn, hbound⟩ :=
    oneMinusConnLapIter_arm_sub_armPrincipalSlotPairing_le
      (I := I) (M := M) g₀ g₁ n h htie hδ_lt hδ_nn hδ
  exact ⟨Clower, hClower_nn, hbound⟩

private theorem armPrincipalSlotPairing_le_dirichlet_top
    [Nonempty M] (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : gFibreOpBound (I := I) g₀ h δ)
    (u₀ : SmoothCcTensor g₀ 0 2) :
    armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀ ≤
      (δ / (1 - δ)) *
        ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀)‖ ^ 2 := by
  classical
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  set A : SmoothCcTensor g₀ 0 ((2 + n) + 1) :=
    iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀ with hA_def
  set B : SmoothCcTensor g₀ 0 ((2 + n) + 1) :=
    appCc (I := I) (M := M) g₀ ((2 + n) + 1) ((2 + n) + 1)
      (slotInsertEndoCc (I := I) (M := M) g₀ (2 + n)
        (gInvDiffRaisedEndoField (I := I) (M := M) g₀ g₁)) A with hB_def
  have hBfun : ∀ x : M,
      B.toFun x =
        TensorRSSpace.toModel (𝕜 := ℝ) (E := E)
          (gInvDiffSlotApplied (I := I) g₀ g₁ (2 + n) x (A.toSection x)) := by
    intro x
    rfl
  have hWS_int : Integrable
      (fun x => tensorInnerPointwise (I := I) (M := M) g₀ 0 ((2 + n) + 1) x
        (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (A.toSection x))
        (TensorRSSpace.toModel (𝕜 := ℝ) (E := E)
          (negGInvDiffSlotApplied (I := I) g₀ g₁ (2 + n) x (A.toSection x))))
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    have hcross := DifferentialGeometry.Integral.L2.SmoothCcTensor.integrable_inner_cross
      (I := I) (M := M) (g := g₀) (r := 0) (s := (2 + n) + 1) A B
    have heq :
        (fun x => tensorInnerPointwise (I := I) (M := M) g₀ 0 ((2 + n) + 1) x
            (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (A.toSection x))
            (TensorRSSpace.toModel (𝕜 := ℝ) (E := E)
              (negGInvDiffSlotApplied (I := I) g₀ g₁ (2 + n) x (A.toSection x))))
          = (fun x => - tensorInnerPointwise (I := I) (M := M) g₀ 0 ((2 + n) + 1) x
              (A.toFun x) (B.toFun x)) := by
      funext x
      rw [hBfun x, SmoothCcTensor.toFun_apply,
        toModel_negGInvDiffSlotApplied_eq (I := I) g₀ g₁ (2 + n) x (A.toSection x),
        show (- TensorRSSpace.toModel (𝕜 := ℝ) (E := E)
              (gInvDiffSlotApplied (I := I) g₀ g₁ (2 + n) x (A.toSection x)))
            = (-1 : ℝ) • TensorRSSpace.toModel (𝕜 := ℝ) (E := E)
              (gInvDiffSlotApplied (I := I) g₀ g₁ (2 + n) x (A.toSection x)) from
          (neg_one_smul ℝ _).symm,
        tensorInnerPointwise_smul_right]
      ring
    rw [heq]
    exact hcross.neg
  have hWW_int : Integrable
      (fun x => tensorInnerPointwise (I := I) (M := M) g₀ 0 ((2 + n) + 1) x
        (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (A.toSection x))
        (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (A.toSection x)))
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    DifferentialGeometry.Integral.L2.SmoothCcTensor.integrable_inner_cross
      (I := I) (M := M) (g := g₀) (r := 0) (s := (2 + n) + 1) A A
  have htool := DifferentialGeometry.Analysis.Sobolev.TensorHilbert.tensorL2Inner_slotΛ_le
    (I := I) (M := M) g₀ (2 + n) (κ := δ / (1 - δ))
    (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (A.toSection x))
    (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E)
      (negGInvDiffSlotApplied (I := I) g₀ g₁ (2 + n) x (A.toSection x)))
    (fun x => tensorInnerPointwise_negGInvDiffSlot_le
      (I := I) (M := M) g₀ g₁ h htie hδ_lt hδ_nn hδ (2 + n) x (A.toSection x))
    hWS_int hWW_int
  have hnorm :
      tensorL2Inner (I := I) (M := M) g₀ 0 ((2 + n) + 1)
          (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (A.toSection x))
          (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (A.toSection x)) =
        ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀)‖ ^ 2 := by
    have hAA : tensorL2Inner (I := I) (M := M) g₀ 0 ((2 + n) + 1) A.toFun A.toFun =
        (⟪A, A⟫_ℝ : ℝ) := (SmoothCcTensor.inner_def (I := I) (M := M) A A).symm
    rw [show (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (A.toSection x)) = A.toFun from rfl,
      hAA, real_inner_self_eq_norm_sq, SmoothCcTensor.norm_toL2]
  have hslot :
      armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀ ≤
        (δ / (1 - δ)) *
          tensorL2Inner (I := I) (M := M) g₀ 0 ((2 + n) + 1)
            (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (A.toSection x))
            (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (A.toSection x)) := htool
  rw [hnorm] at hslot
  exact hslot

private theorem dirichlet_top_le_spectral_add_lower
    [Nonempty M] (g₀ : SmoothRiemannianMetric I M) (n : ℕ) :
    ∃ Cgap : ℝ, 0 ≤ Cgap ∧
      ∀ (u₀ : SmoothCcTensor g₀ 0 2),
        ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀)‖ ^ 2 ≤
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 +
            Cgap * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2 :=
  exists_iteratedCovGrad_l2NormSq_le_smoothCcToTensorHs_succ_add_lower
    (I := I) (M := M) g₀ n

private theorem oneMinusConnLapIter_l2Inner_deTurckPrincipalCometricArm_le
    [Nonempty M] (g₀ : SmoothRiemannianMetric I M) (n : ℕ) :
    ∀ (g₁ : SmoothRiemannianMetric I M)
      (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ),
      (∀ (y : M) (v w : TangentSpace I y),
        g₁.inner y v w = g₀.inner y v w + h y v w) →
      ∀ {δ : ℝ}, δ < 1 → 0 ≤ δ → gFibreOpBound (I := I) g₀ h δ →
      ∃ Clower : ℝ, 0 ≤ Clower ∧
        ∀ (u₀ : SmoothCcTensor g₀ 0 2),
          tensorL2Inner (I := I) (M := M) g₀ 0 2
              (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 n u₀).toFun
              (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toFun ≤
            (δ / (1 - δ) + 1 / 4) *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 +
              Clower * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2 := by
  intro g₁ h htie δ hδ_lt hδ_nn hδ
  obtain ⟨rem, hsplit, Clower₁, hClower₁_nn, hrem⟩ :=
    oneMinusConnLapIter_pairing_fold (I := I) (M := M) g₀ g₁ n h htie hδ_lt hδ_nn hδ
  obtain ⟨Cgap, hCgap_nn, hgap⟩ :=
    dirichlet_top_le_spectral_add_lower (I := I) (M := M) g₀ n
  have hκ_nn : 0 ≤ δ / (1 - δ) := div_nonneg hδ_nn (by linarith)
  refine ⟨(δ / (1 - δ)) * Cgap + Clower₁, by positivity, fun u₀ => ?_⟩
  rw [hsplit u₀]
  have htop := armPrincipalSlotPairing_le_dirichlet_top
    (I := I) (M := M) g₀ g₁ n h htie hδ_lt hδ_nn hδ u₀
  have hg := hgap u₀
  have hr := hrem u₀
  have hMnp_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 :=
    sq_nonneg _
  have hstep : armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀ ≤
      (δ / (1 - δ)) *
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 +
        (δ / (1 - δ)) * Cgap *
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2 := by
    calc armPrincipalSlotPairing (I := I) (M := M) g₀ g₁ n u₀
        ≤ (δ / (1 - δ)) *
            ‖SmoothCcTensor.toL2 (iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀)‖ ^ 2 := htop
      _ ≤ (δ / (1 - δ)) *
            (‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 +
              Cgap * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hg hκ_nn
      _ = (δ / (1 - δ)) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 +
          (δ / (1 - δ)) * Cgap *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2 := by ring
  nlinarith [hstep, hr, hMnp_nn]

theorem deTurckPrincipalCometricArm_spectralPairing_tsum_le
    [Nonempty M] (g₀ : SmoothRiemannianMetric I M) (n : ℕ) :
    ∀ (g₁ : SmoothRiemannianMetric I M)
      (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ),
      (∀ (y : M) (v w : TangentSpace I y),
        g₁.inner y v w = g₀.inner y v w + h y v w) →
      ∀ {δ : ℝ}, δ < 1 → 0 ≤ δ → gFibreOpBound (I := I) g₀ h δ →
      ∃ Clower : ℝ, 0 ≤ Clower ∧
        ∀ (u₀ : SmoothCcTensor g₀ 0 2),
          2 * ∑' i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) g₀ 0 2,
              tensorSobolevWeight (I := I) (M := M) i ((n : ℕ) : ℝ) *
                ((smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀).coeff i *
                  (smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ)
                    (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀)).coeff i) ≤
            2 * (δ / (1 - δ) + 1 / 4) *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 +
              Clower * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2 := by
  intro g₁ h htie δ hδ_lt hδ_nn hδ
  obtain ⟨Clower, hClower_nn, hbound⟩ :=
    oneMinusConnLapIter_l2Inner_deTurckPrincipalCometricArm_le
      (I := I) (M := M) g₀ n g₁ h htie hδ_lt hδ_nn hδ
  refine ⟨2 * Clower, by positivity, fun u₀ => ?_⟩
  have hpair :=
    spectralPairing_tsum_eq_oneMinusConnLapIter_l2Inner (I := I) (M := M) g₀ n u₀
      (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀)
  rw [hpair]
  have hb := hbound u₀
  have hgoal :
      2 * (δ / (1 - δ) + 1 / 4) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 +
          2 * Clower * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2 =
        2 * ((δ / (1 - δ) + 1 / 4) *
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 +
            Clower * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2) := by
    ring
  rw [hgoal]
  linarith [hb]

theorem two_mul_inner_smoothCcToTensorHs_deTurckPrincipalCometricArm_le
    [Nonempty M] (g₀ : SmoothRiemannianMetric I M) (n : ℕ) :
    ∀ (g₁ : SmoothRiemannianMetric I M)
      (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ),
      (∀ (y : M) (v w : TangentSpace I y),
        g₁.inner y v w = g₀.inner y v w + h y v w) →
      ∀ {δ : ℝ}, δ < 1 → 0 ≤ δ → gFibreOpBound (I := I) g₀ h δ →
      ∃ Clower : ℝ, 0 ≤ Clower ∧
        ∀ (u₀ : SmoothCcTensor g₀ 0 2),
          2 * (inner ℝ (smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀)
                (smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ)
                  (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀)) : ℝ) ≤
            2 * (δ / (1 - δ) + 1 / 4) *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 +
              Clower * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2 := by
  intro g₁ h htie δ hδ_lt hδ_nn hδ
  obtain ⟨Clower, hClower_nn, hbound⟩ :=
    deTurckPrincipalCometricArm_spectralPairing_tsum_le (I := I) (M := M) g₀ n
      g₁ h htie hδ_lt hδ_nn hδ
  refine ⟨Clower, hClower_nn, fun u₀ => ?_⟩
  have hinner :
      (inner ℝ (smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀)
          (smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ)
            (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀)) : ℝ) =
        ∑' i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g₀ 0 2,
            tensorSobolevWeight (I := I) (M := M) i ((n : ℕ) : ℝ) *
              ((smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀).coeff i *
                (smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ)
                  (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀)).coeff i) :=
    tensorHs.inner_def (I := I) (M := M)
      (smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀)
      (smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ)
        (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀))
  rw [hinner]
  exact hbound u₀

theorem two_mul_inner_smoothCcToTensorHs_deTurckPrincipalCometricArm_lt_one
    [Nonempty M] (g₀ : SmoothRiemannianMetric I M) (n : ℕ) :
    ∀ (g₁ : SmoothRiemannianMetric I M)
      (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ),
      (∀ (y : M) (v w : TangentSpace I y),
        g₁.inner y v w = g₀.inner y v w + h y v w) →
      ∀ {δ : ℝ}, δ ≤ 1 / 3 → 0 ≤ δ → gFibreOpBound (I := I) g₀ h δ →
      ∃ Cupper Clower : ℝ, Cupper < 1 ∧ 0 ≤ Cupper ∧ 0 ≤ Clower ∧
        ∀ (u₀ : SmoothCcTensor g₀ 0 2),
          2 * (inner ℝ (smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀)
                (smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ)
                  (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀)) : ℝ) ≤
            2 * Cupper *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 +
              Clower * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2 := by
  intro g₁ h htie δ hδ_le hδ_nn hδ
  have hδ_lt : δ < 1 := by linarith
  obtain ⟨Clower, hClower_nn, hbound⟩ :=
    two_mul_inner_smoothCcToTensorHs_deTurckPrincipalCometricArm_le
      (I := I) (M := M) g₀ n g₁ h htie hδ_lt hδ_nn hδ
  have hone_sub : (0 : ℝ) < 1 - δ := by linarith
  have hκ_le : δ / (1 - δ) ≤ 1 / 2 := by
    rw [div_le_iff₀ hone_sub]
    linarith
  refine ⟨δ / (1 - δ) + 1 / 4, Clower, by linarith, by positivity, hClower_nn, hbound⟩

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
