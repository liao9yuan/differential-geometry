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

set_option linter.unusedSectionVars false in
private lemma armResidual_vecTail_cons {α : Type*} {n : ℕ} (a : α) (w : Fin n → α) :
    Matrix.vecTail (Fin.cons a w) = w := by
  funext j
  simp [Matrix.vecTail, Fin.cons_succ]

set_option linter.unusedSectionVars false in
private lemma armResidual_toModel_sum {s : ℕ} (b : M) {ι : Type*} (fs : Finset ι)
    (f : ι → Tensor0SSpace s I b) :
    Tensor0SSpace.toModel (∑ i ∈ fs, f i) = ∑ i ∈ fs, Tensor0SSpace.toModel (f i) :=
  map_sum (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) s b) f fs

set_option linter.unusedSectionVars false in
private lemma armResidual_model_slot0_linear {s : ℕ} {ι : Type*} (fs : Finset ι)
    (T : Tensor0SBundle.Tensor0SModel (s + 1) ℝ E) (c : ι → ℝ) (f : ι → E)
    (rest : Fin s → E) :
    T (Fin.cons (∑ j ∈ fs, c j • f j) rest) = ∑ j ∈ fs, c j * T (Fin.cons (f j) rest) := by
  have h : ∀ u : E, T (Fin.cons u rest) =
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s + 1) => E) ℝ) T u) rest := by
    intro u
    rw [continuousMultilinearCurryLeftEquiv_apply]
  rw [h, map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul, ← h]

set_option linter.unusedSectionVars false in
private lemma armResidual_model_slot1_linear {s : ℕ} {ι : Type*} (fs : Finset ι)
    (T : Tensor0SBundle.Tensor0SModel (s + 1 + 1) ℝ E) (a : E) (c : ι → ℝ) (f : ι → E)
    (rest : Fin s → E) :
    T (Fin.cons a (Fin.cons (∑ j ∈ fs, c j • f j) rest)) =
      ∑ j ∈ fs, c j * T (Fin.cons a (Fin.cons (f j) rest)) := by
  have hcur : ∀ w : Fin (s + 1) → E,
      T (Fin.cons a w) =
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s + 1 + 1) => E) ℝ) T a) w := by
    intro w
    rw [continuousMultilinearCurryLeftEquiv_apply]
  rw [hcur,
    armResidual_model_slot0_linear (E := E) fs
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s + 1 + 1) => E) ℝ) T a)
      c f rest]
  exact Finset.sum_congr rfl fun j _ => by rw [hcur]

set_option linter.unusedSectionVars false in
private lemma armResidual_orthoFrame_expansion (g₀ : SmoothRiemannianMetric I M) (b : M)
    (u : TangentSpace I b) :
    u = ∑ i : Fin (Module.finrank ℝ E),
      g₀.inner b u (smoothOrthoFrame (I := I) g₀ b i b) •
        smoothOrthoFrame (I := I) g₀ b i b := by
  classical
  have horth : ∀ a c : Fin (Module.finrank ℝ E),
      g₀.inner b (smoothOrthoFrame (I := I) g₀ b a b)
        (smoothOrthoFrame (I := I) g₀ b c b) = if a = c then 1 else 0 :=
    fun a c => smoothOrthoFrame_orthonormal_at_center (I := I) g₀ b a c
  have he_li : LinearIndependent ℝ (fun i => smoothOrthoFrame (I := I) g₀ b i b) := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g₀.inner b (smoothOrthoFrame (I := I) g₀ b k b)
        (∑ j ∈ fs, c j • smoothOrthoFrame (I := I) g₀ b j b) = 0 := by
      rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs, g₀.inner b (smoothOrthoFrame (I := I) g₀ b k b)
        (c j • smoothOrthoFrame (I := I) g₀ b j b) =
        c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [(g₀.inner b (smoothOrthoFrame (I := I) g₀ b k b)).map_smul (c j),
        smul_eq_mul, horth k j]
    rw [Finset.sum_congr rfl h_pull, Finset.sum_eq_single_of_mem k hk_mem] at h_zero
    · rwa [if_pos rfl, mul_one] at h_zero
    · intro j _ hjk
      rw [if_neg (fun h => hjk h.symm), mul_zero]
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) = Module.finrank ℝ E :=
    Fintype.card_fin _
  set bse := basisOfLinearIndependentOfCardEqFinrank he_li hcard with hbse_def
  have hbse : ∀ i, bse i = smoothOrthoFrame (I := I) g₀ b i b :=
    fun i => congrFun (coe_basisOfLinearIndependentOfCardEqFinrank he_li hcard) i
  have hcoeff : ∀ j : Fin (Module.finrank ℝ E),
      g₀.inner b u (smoothOrthoFrame (I := I) g₀ b j b) = bse.repr u j := by
    intro j
    rw [g₀.symm b u (smoothOrthoFrame (I := I) g₀ b j b)]
    conv_lhs => rw [← bse.sum_repr u]
    rw [map_sum]
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => by
      rw [(g₀.inner b (smoothOrthoFrame (I := I) g₀ b j b)).map_smul (bse.repr u i),
        smul_eq_mul, hbse i, horth j i])]
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
    · rw [if_pos rfl, mul_one]
    · intro i _ hij
      rw [if_neg (fun h => hij h.symm), mul_zero]
  calc u = ∑ i : Fin (Module.finrank ℝ E), bse.repr u i • bse i := (bse.sum_repr u).symm
    _ = ∑ i : Fin (Module.finrank ℝ E),
        g₀.inner b u (smoothOrthoFrame (I := I) g₀ b i b) •
          smoothOrthoFrame (I := I) g₀ b i b := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcoeff i, hbse i]

set_option linter.unusedSectionVars false in
private lemma armResidual_toModel_contract_covariant (s : ℕ) (b : M) (v : TangentSpace I b)
    (A : TensorRSSpace 0 (s + 1) I b) (D : Tensor0SSpace 0 I b) (m : Fin s → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace s I b from
          Tensor0SBundle.contract_covariant 0 s b v A) D) m =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (s + 1) I b from A) D)
        (Fin.cons ((v : TangentSpace I b) : E) m) :=
  rfl

set_option linter.unusedSectionVars false in
private lemma armResidual_covDivergence_toSection (g₀ : SmoothRiemannianMetric I M)
    (s : ℕ) (V : SmoothCcTensor g₀ 0 (s + 1)) (b : M) :
    ((covDivergence (I := I) (M := M) g₀ s V).toSection b : TensorRSSpace 0 s I b) =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SBundle.contract_covariant 0 s b (smoothOrthoFrame (I := I) g₀ b i b)
          (tensorCovDerivAt (I := I) (M := M) g₀ 0 (s + 1) V b
            (smoothOrthoFrame (I := I) g₀ b i b)) := by
  classical
  rw [covDivergence_toSection_apply (I := I) (M := M) g₀ s V b]
  rw [covDivergenceRaw]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hSmooth_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun z : M => TotalSpace.mk' E (E := fun w : M => TangentSpace I w) z
        (smoothOrthoFrame (I := I) g₀ b i z)) b :=
    (smoothOrthoFrame_smooth (I := I) g₀ b i).contMDiffAt.mdifferentiableAt (by simp)
  rw [codiffPsi_apply (I := I) (M := M) g₀ s V b hSmooth_at hSmooth_at]
  rw [tensorCovDerivAt_def (I := I) (M := M) g₀ 0 (s + 1) V b
    (smoothOrthoFrame (I := I) g₀ b i b)]

set_option linter.unusedSectionVars false in
private lemma armResidual_toModel_doubleTraceFib (g₀ : SmoothRiemannianMetric I M) (b : M)
    (W : Tensor0SSpace (2 + 2) I b) (m : Fin 2 → E) :
    Tensor0SSpace.toModel (DeTurck.cometricDoubleTraceFib (I := I) g₀ 2 b W) m =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel W
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E) m)) := by
  classical
  rw [DeTurck.cometricDoubleTraceFib_eq_orthoFrame_diag (I := I) g₀ 2 b
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) b) W]
  rw [armResidual_toModel_sum (I := I) (M := M) b Finset.univ
    (fun i => Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 b
      (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (2 + 1) b W
        (smoothOrthoFrame (I := I) g₀ b i b))
      (smoothOrthoFrame (I := I) g₀ b i b))]
  rw [ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (2 + 1) b W
      (smoothOrthoFrame (I := I) g₀ b i b))
    (v0 := ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E)) (vs := m)]
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (T := W)
    (v0 := ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E))
    (vs := Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E) m)]

set_option linter.unusedSectionVars false in
private lemma armResidual_slot01_transpose (g₀ g₁ : SmoothRiemannianMetric I M) (b : M)
    (T : Tensor0SBundle.Tensor0SModel (2 + 1 + 1) ℝ E) (m : Fin 2 → E) :
    (∑ i : Fin (Module.finrank ℝ E),
        T (Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E)
            (Fin.cons ((gInvDiffRaisedEndo (I := I) g₀ g₁ b
                (smoothOrthoFrame (I := I) g₀ b i b) : TangentSpace I b) : E) m))) =
      ∑ i : Fin (Module.finrank ℝ E),
        T (Fin.cons ((gInvDiffRaisedEndo (I := I) g₀ g₁ b
              (smoothOrthoFrame (I := I) g₀ b i b) : TangentSpace I b) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E) m)) := by
  classical
  set e : Fin (Module.finrank ℝ E) → TangentSpace I b :=
    fun i => smoothOrthoFrame (I := I) g₀ b i b with he
  set Λ : TangentSpace I b →L[ℝ] TangentSpace I b :=
    gInvDiffRaisedEndo (I := I) g₀ g₁ b with hΛ
  have hadj : ∀ a c : TangentSpace I b, g₀.inner b (Λ a) c = g₀.inner b a (Λ c) :=
    fun a c => gInvDiffRaisedEndo_g0_self_adjoint (I := I) g₀ g₁ b a c
  have hexp : ∀ v : TangentSpace I b,
      v = ∑ j : Fin (Module.finrank ℝ E), g₀.inner b v (e j) • e j :=
    fun v => armResidual_orthoFrame_expansion (I := I) (M := M) g₀ b v
  have hL : ∀ i : Fin (Module.finrank ℝ E),
      T (Fin.cons ((e i : TangentSpace I b) : E)
          (Fin.cons ((Λ (e i) : TangentSpace I b) : E) m)) =
        ∑ j : Fin (Module.finrank ℝ E), g₀.inner b (Λ (e i)) (e j) *
          T (Fin.cons ((e i : TangentSpace I b) : E)
              (Fin.cons ((e j : TangentSpace I b) : E) m)) := by
    intro i
    conv_lhs => rw [hexp (Λ (e i))]
    exact armResidual_model_slot1_linear (E := E) Finset.univ T ((e i : TangentSpace I b) : E)
      (fun j => g₀.inner b (Λ (e i)) (e j)) (fun j => ((e j : TangentSpace I b) : E)) m
  have hR : ∀ i : Fin (Module.finrank ℝ E),
      T (Fin.cons ((Λ (e i) : TangentSpace I b) : E)
          (Fin.cons ((e i : TangentSpace I b) : E) m)) =
        ∑ j : Fin (Module.finrank ℝ E), g₀.inner b (Λ (e i)) (e j) *
          T (Fin.cons ((e j : TangentSpace I b) : E)
              (Fin.cons ((e i : TangentSpace I b) : E) m)) := by
    intro i
    conv_lhs => rw [hexp (Λ (e i))]
    exact armResidual_model_slot0_linear (E := E) Finset.univ T
      (fun j => g₀.inner b (Λ (e i)) (e j)) (fun j => ((e j : TangentSpace I b) : E))
      (Fin.cons ((e i : TangentSpace I b) : E) m)
  rw [Finset.sum_congr rfl (fun i _ => hL i), Finset.sum_congr rfl (fun i _ => hR i)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hco : g₀.inner b (Λ (e j)) (e i) = g₀.inner b (Λ (e i)) (e j) := by
    rw [hadj (e j) (e i), g₀.symm b (e j) (Λ (e i))]
  rw [hco]

set_option linter.unusedSectionVars false in
private lemma armResidual_covGrad_eval (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (W : SmoothCcTensor g₀ 0 s) (b : M) (D : Tensor0SSpace 0 I b)
    (v0 : E) (vs : Fin s → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (s + 1) I b from
          (covGrad (I := I) (M := M) g₀ 0 s W).toSection b) D) (Fin.cons v0 vs) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace s I b from
          tensorCovDerivAt (I := I) (M := M) g₀ 0 s W b v0) D) vs := by
  have h := covGrad_toSection_apply_eval (I := I) (M := M) g₀ 0 s W b D (Fin.cons v0 vs)
  have ht : Matrix.vecTail (Fin.cons v0 vs : Fin (s + 1) → TangentSpace I b) = vs := by
    funext j
    rfl
  exact h.trans (congrArg (fun w : Fin s → E =>
    Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace s I b from
        tensorCovDerivAt (I := I) (M := M) g₀ 0 s W b v0) D) w) ht)

set_option linter.unusedSectionVars false in
private lemma armResidual_contract_term_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (u₀ : SmoothCcTensor g₀ 0 2) (b : M) (D : Tensor0SSpace 0 I b) (m : Fin 2 → E)
    (i : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from
          Tensor0SBundle.contract_covariant 0 2 b (smoothOrthoFrame (I := I) g₀ b i b)
            (tensorCovDerivAt (I := I) (M := M) g₀ 0 (2 + 1)
              (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 1)
                (slotInsertEndoCc (I := I) (M := M) g₀ 2
                  (gInvDiffRaisedEndoField (I := I) g₀ g₁))
                (covGrad (I := I) (M := M) g₀ 0 2 u₀)) b
              (smoothOrthoFrame (I := I) g₀ b i b))) D) m =
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
            (covGrad (I := I) (M := M) g₀ 0 2 u₀).toSection b) D)
          (Fin.cons
            ((((endoCovariantDerivative (I := I) (M := M) g₀)
                  (gInvDiffRaisedEndoField (I := I) g₀ g₁) b
                  (smoothOrthoFrame (I := I) g₀ b i b))
                (smoothOrthoFrame (I := I) g₀ b i b) : TangentSpace I b) : E) m) +
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace ((2 + 1) + 1) I b from
            (covGrad (I := I) (M := M) g₀ 0 (2 + 1)
              (covGrad (I := I) (M := M) g₀ 0 2 u₀)).toSection b) D)
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E)
            (Fin.cons ((gInvDiffRaisedEndo (I := I) g₀ g₁ b
                (smoothOrthoFrame (I := I) g₀ b i b) : TangentSpace I b) : E) m)) := by
  classical
  set ei : TangentSpace I b := smoothOrthoFrame (I := I) g₀ b i b with hei
  set Du : SmoothCcTensor g₀ 0 (2 + 1) := covGrad (I := I) (M := M) g₀ 0 2 u₀ with hDu
  set Λf := gInvDiffRaisedEndoField (I := I) g₀ g₁ with hΛf
  rw [armResidual_toModel_contract_covariant (I := I) (M := M) 2 b ei _ D m]
  have hderiv := tensorCovDerivAt_appCc_eq (I := I) (M := M) g₀ (2 + 1) (2 + 1)
    (slotInsertEndoCc (I := I) (M := M) g₀ 2 Λf) Du b ((ei : TangentSpace I b) : E)
  rw [hderiv]
  rw [show ((((show Tensor0SSpace (2 + 1) I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
          tensorCovDerivAt (I := I) (M := M) g₀ (2 + 1) (2 + 1)
            (slotInsertEndoCc (I := I) (M := M) g₀ 2 Λf) b ((ei : TangentSpace I b) : E)).comp
          (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from Du.toSection b) +
        (show Tensor0SSpace (2 + 1) I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
          (slotInsertEndoCc (I := I) (M := M) g₀ 2 Λf).toSection b).comp
          (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
            tensorCovDerivAt (I := I) (M := M) g₀ 0 (2 + 1) Du b
              ((ei : TangentSpace I b) : E))) : TensorRSSpace 0 (2 + 1) I b)) D =
      (show Tensor0SSpace (2 + 1) I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
          tensorCovDerivAt (I := I) (M := M) g₀ (2 + 1) (2 + 1)
            (slotInsertEndoCc (I := I) (M := M) g₀ 2 Λf) b ((ei : TangentSpace I b) : E))
        ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from Du.toSection b) D) +
      (show Tensor0SSpace (2 + 1) I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
          (slotInsertEndoCc (I := I) (M := M) g₀ 2 Λf).toSection b)
        ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
          tensorCovDerivAt (I := I) (M := M) g₀ 0 (2 + 1) Du b
            ((ei : TangentSpace I b) : E)) D) from rfl]
  rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
  congr 1
  · rw [tensorCovDerivAt_slotInsertEndoCc_eq (I := I) (M := M) g₀ 2 Λf b
      ((ei : TangentSpace I b) : E)]
    rw [slotInsertEndoFib_apply_eval (I := I) (M := M) (2 + 1) 0 b
      ((endoCovariantDerivative (I := I) (M := M) g₀) Λf b ((ei : TangentSpace I b) : E))
      ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from Du.toSection b) D)
      (Fin.cons ((ei : TangentSpace I b) : E) m)]
    rw [Fin.cons_zero, Fin.update_cons_zero]
  · rw [slotInsertEndoCc_toSection (I := I) (M := M) g₀ 2 Λf b]
    rw [slotInsertEndoFib_apply_eval (I := I) (M := M) (2 + 1) 0 b (Λf b)
      ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
        tensorCovDerivAt (I := I) (M := M) g₀ 0 (2 + 1) Du b
          ((ei : TangentSpace I b) : E)) D)
      (Fin.cons ((ei : TangentSpace I b) : E) m)]
    rw [Fin.cons_zero, Fin.update_cons_zero]
    exact (armResidual_covGrad_eval (I := I) (M := M) g₀ (2 + 1) Du b D
      ((ei : TangentSpace I b) : E)
      (Fin.cons ((Λf b (ei : TangentSpace I b) : TangentSpace I b) : E) m)).symm

set_option linter.unusedSectionVars false in
private lemma armResidual_arm_toModel_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (u₀ : SmoothCcTensor g₀ 0 2) (b : M) (D : Tensor0SSpace 0 I b) (m : Fin 2 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from
          (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toSection b) D) m =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace ((2 + 1) + 1) I b from
            (covGrad (I := I) (M := M) g₀ 0 (2 + 1)
              (covGrad (I := I) (M := M) g₀ 0 2 u₀)).toSection b) D)
          (Fin.cons ((gInvDiffRaisedEndo (I := I) g₀ g₁ b
              (smoothOrthoFrame (I := I) g₀ b i b) : TangentSpace I b) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E) m)) := by
  classical
  rw [deTurckPrincipalCometricArm,
    deTurckPrincipalCometricCoeff_eq_appCcRS_doubleTrace_slotInsertEndo (I := I) (M := M) g₀ g₁]
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from
        (appCc (I := I) (M := M) g₀ 4 2
          (DifferentialGeometry.Integral.Connection.appCcRS (I := I) (M := M) g₀ 4 4 2
            (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
            (DifferentialGeometry.Integral.Connection.slotInsertEndoCc (I := I) (M := M) g₀ 3
              (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
          (iteratedCovGrad (I := I) g₀ 0 2 2 u₀)).toSection b) D) m =
    Tensor0SSpace.toModel
      (DeTurck.cometricDoubleTraceFib (I := I) g₀ 2 b
        (slotInsertEndoFib (I := I) (M := M) (3 + 1) 0 b
          (gInvDiffRaisedEndoField (I := I) g₀ g₁ b)
          ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 4 I b from
            (iteratedCovGrad (I := I) g₀ 0 2 2 u₀).toSection b) D))) m from rfl]
  rw [armResidual_toModel_doubleTraceFib (I := I) (M := M) g₀ b
    (slotInsertEndoFib (I := I) (M := M) (3 + 1) 0 b
      (gInvDiffRaisedEndoField (I := I) g₀ g₁ b)
      ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 4 I b from
        (iteratedCovGrad (I := I) g₀ 0 2 2 u₀).toSection b) D)) m]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [slotInsertEndoFib_apply_eval (I := I) (M := M) (3 + 1) 0 b
    (gInvDiffRaisedEndoField (I := I) g₀ g₁ b)
    ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 4 I b from
      (iteratedCovGrad (I := I) g₀ 0 2 2 u₀).toSection b) D)
    (Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E)
      (Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E) m))]
  rw [Fin.cons_zero, Fin.update_cons_zero]
  rfl

set_option linter.unusedSectionVars false in
private lemma armResidual_gTerm_toModel_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (u₀ : SmoothCcTensor g₀ 0 2) (b : M) (D : Tensor0SSpace 0 I b) (m : Fin 2 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from
          (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 0)
            (appCcRS (I := I) (M := M) g₀ (2 + 1) ((2 + 1) + 1) (2 + 0)
              (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
              (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
                (slotInsertEndoCc (I := I) (M := M) g₀ 2
                  (gInvDiffRaisedEndoField (I := I) g₀ g₁))))
            (covGrad (I := I) (M := M) g₀ 0 2 u₀)).toSection b) D) m =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
            (covGrad (I := I) (M := M) g₀ 0 2 u₀).toSection b) D)
          (Fin.cons
            ((((endoCovariantDerivative (I := I) (M := M) g₀)
                  (gInvDiffRaisedEndoField (I := I) g₀ g₁) b
                  (smoothOrthoFrame (I := I) g₀ b i b))
                (smoothOrthoFrame (I := I) g₀ b i b) : TangentSpace I b) : E) m) := by
  classical
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from
        (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 0)
          (appCcRS (I := I) (M := M) g₀ (2 + 1) ((2 + 1) + 1) (2 + 0)
            (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
            (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 2
                (gInvDiffRaisedEndoField (I := I) g₀ g₁))))
          (covGrad (I := I) (M := M) g₀ 0 2 u₀)).toSection b) D) m =
    Tensor0SSpace.toModel
      (DeTurck.cometricDoubleTraceFib (I := I) g₀ 2 b
        ((show Tensor0SSpace (2 + 1) I b →L[ℝ] Tensor0SSpace ((2 + 1) + 1) I b from
          (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
            (slotInsertEndoCc (I := I) (M := M) g₀ 2
              (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection b)
          ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
            (covGrad (I := I) (M := M) g₀ 0 2 u₀).toSection b) D))) m from rfl]
  rw [armResidual_toModel_doubleTraceFib (I := I) (M := M) g₀ b
    ((show Tensor0SSpace (2 + 1) I b →L[ℝ] Tensor0SSpace ((2 + 1) + 1) I b from
      (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ 2
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection b)
      ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
        (covGrad (I := I) (M := M) g₀ 0 2 u₀).toSection b) D)) m]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hstep : Tensor0SSpace.toModel
      ((show Tensor0SSpace (2 + 1) I b →L[ℝ] Tensor0SSpace ((2 + 1) + 1) I b from
        (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ 2
            (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection b)
        ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
          (covGrad (I := I) (M := M) g₀ 0 2 u₀).toSection b) D))
      (Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E)
        (Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E) m)) =
      Tensor0SSpace.toModel
        (slotInsertEndoFib (I := I) (M := M) (2 + 1) 0 b
          ((endoCovariantDerivative (I := I) (M := M) g₀)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁) b
            (smoothOrthoFrame (I := I) g₀ b i b))
          ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
            (covGrad (I := I) (M := M) g₀ 0 2 u₀).toSection b) D))
        (Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E) m) := by
    have h := covGrad_slotInsertEndoCc_toSection_eq (I := I) (M := M) g₀ 2
      (gInvDiffRaisedEndoField (I := I) g₀ g₁) b
      ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
        (covGrad (I := I) (M := M) g₀ 0 2 u₀).toSection b) D)
      (Fin.cons (smoothOrthoFrame (I := I) g₀ b i b)
        (Fin.cons (smoothOrthoFrame (I := I) g₀ b i b) m))
    have ht : Matrix.vecTail (Fin.cons (smoothOrthoFrame (I := I) g₀ b i b)
        (Fin.cons (smoothOrthoFrame (I := I) g₀ b i b) m) :
          Fin (2 + 1 + 1) → TangentSpace I b) =
        (Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E) m :
          Fin (2 + 1) → E) := by
      funext j
      refine Fin.cases ?_ (fun j' => ?_) j
      · rfl
      · rfl
    exact h.trans (congrArg (fun w : Fin (2 + 1) → E =>
      Tensor0SSpace.toModel
        (slotInsertEndoFib (I := I) (M := M) (2 + 1) 0 b
          ((endoCovariantDerivative (I := I) (M := M) g₀)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁) b
            (smoothOrthoFrame (I := I) g₀ b i b))
          ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
            (covGrad (I := I) (M := M) g₀ 0 2 u₀).toSection b) D)) w) ht)
  rw [hstep]
  have happ : Tensor0SSpace.toModel
      (slotInsertEndoFib (I := I) (M := M) (2 + 1) 0 b
        ((endoCovariantDerivative (I := I) (M := M) g₀)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁) b
          (smoothOrthoFrame (I := I) g₀ b i b))
        ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
          (covGrad (I := I) (M := M) g₀ 0 2 u₀).toSection b) D))
      (Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E) m) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (2 + 1) I b from
          (covGrad (I := I) (M := M) g₀ 0 2 u₀).toSection b) D)
        (Function.update
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E) m) 0
          (((endoCovariantDerivative (I := I) (M := M) g₀)
              (gInvDiffRaisedEndoField (I := I) g₀ g₁) b
              (smoothOrthoFrame (I := I) g₀ b i b))
            ((Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E) m :
              Fin (2 + 1) → E) 0))) :=
    slotInsertEndoFib_apply_eval (I := I) (M := M) (2 + 1) 0 b _ _ _
  rw [happ]
  rw [show ((Fin.cons ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E) m :
      Fin (2 + 1) → E) 0) = ((smoothOrthoFrame (I := I) g₀ b i b : TangentSpace I b) : E)
    from rfl]
  rw [Fin.update_cons_zero]

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
private theorem armResidual_covDivergence_split (g₀ g₁ : SmoothRiemannianMetric I M)
    (u₀ : SmoothCcTensor g₀ 0 2) :
    covDivergence (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ 2 (gInvDiffRaisedEndoField (I := I) g₀ g₁))
          (covGrad (I := I) (M := M) g₀ 0 2 u₀)) =
      deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀ +
        appCc (I := I) (M := M) g₀ (2 + 1) (2 + 0)
          (appCcRS (I := I) (M := M) g₀ (2 + 1) ((2 + 1) + 1) (2 + 0)
            (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
            (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 2
                (gInvDiffRaisedEndoField (I := I) g₀ g₁))))
          (covGrad (I := I) (M := M) g₀ 0 2 u₀) := by
  classical
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro b
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext fun m => ?_
  beta_reduce
  set P : SmoothCcTensor g₀ 0 (2 + 1) :=
    appCc (I := I) (M := M) g₀ (2 + 1) (2 + 1)
      (slotInsertEndoCc (I := I) (M := M) g₀ 2 (gInvDiffRaisedEndoField (I := I) g₀ g₁))
      (covGrad (I := I) (M := M) g₀ 0 2 u₀) with hP
  set Garm : SmoothCcTensor g₀ 0 (2 + 0) :=
    appCc (I := I) (M := M) g₀ (2 + 1) (2 + 0)
      (appCcRS (I := I) (M := M) g₀ (2 + 1) ((2 + 1) + 1) (2 + 0)
        (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
        (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ 2
            (gInvDiffRaisedEndoField (I := I) g₀ g₁))))
      (covGrad (I := I) (M := M) g₀ 0 2 u₀) with hGarm
  rw [show ((deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀ + Garm).toSection b :
      TensorRSSpace 0 2 I b) =
    ((deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toSection b :
      TensorRSSpace 0 2 I b) + (Garm.toSection b : TensorRSSpace 0 2 I b) from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [show ((((deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toSection b :
        TensorRSSpace 0 2 I b) + (Garm.toSection b : TensorRSSpace 0 2 I b) :
        TensorRSSpace 0 2 I b)) D =
    (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from
      (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toSection b) D +
    (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from Garm.toSection b) D from rfl]
  rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
  rw [armResidual_covDivergence_toSection (I := I) (M := M) g₀ 2 P b]
  rw [show ((∑ i : Fin (Module.finrank ℝ E),
      Tensor0SBundle.contract_covariant 0 2 b (smoothOrthoFrame (I := I) g₀ b i b)
        (tensorCovDerivAt (I := I) (M := M) g₀ 0 (2 + 1) P b
          (smoothOrthoFrame (I := I) g₀ b i b)) : TensorRSSpace 0 2 I b)) D =
    ∑ i : Fin (Module.finrank ℝ E),
      (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from
        Tensor0SBundle.contract_covariant 0 2 b (smoothOrthoFrame (I := I) g₀ b i b)
          (tensorCovDerivAt (I := I) (M := M) g₀ 0 (2 + 1) P b
            (smoothOrthoFrame (I := I) g₀ b i b))) D from by
    exact ContinuousLinearMap.sum_apply _ _ _]
  rw [armResidual_toModel_sum (I := I) (M := M) b Finset.univ
    (fun i => (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from
      Tensor0SBundle.contract_covariant 0 2 b (smoothOrthoFrame (I := I) g₀ b i b)
        (tensorCovDerivAt (I := I) (M := M) g₀ 0 (2 + 1) P b
          (smoothOrthoFrame (I := I) g₀ b i b))) D)]
  rw [ContinuousMultilinearMap.sum_apply]
  rw [hP]
  rw [Finset.sum_congr rfl (fun i _ =>
    armResidual_contract_term_eq (I := I) (M := M) g₀ g₁ u₀ b D m i)]
  rw [Finset.sum_add_distrib]
  rw [armResidual_arm_toModel_eq (I := I) (M := M) g₀ g₁ u₀ b D m]
  rw [hGarm]
  rw [armResidual_gTerm_toModel_eq (I := I) (M := M) g₀ g₁ u₀ b D m]
  rw [armResidual_slot01_transpose (I := I) (M := M) g₀ g₁ b
    (Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace ((2 + 1) + 1) I b from
        (covGrad (I := I) (M := M) g₀ 0 (2 + 1)
          (covGrad (I := I) (M := M) g₀ 0 2 u₀)).toSection b) D)) m]
  exact add_comm _ _

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
              (iteratedCovGrad (I := I) g₀ 0 2 1 u₀)⟫_ℝ : ℝ) := by
  classical
  refine ⟨-(appCcRS (I := I) (M := M) g₀ (2 + 1) ((2 + 1) + 1) (2 + 0)
      (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
      (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ 2
          (gInvDiffRaisedEndoField (I := I) g₀ g₁)))), fun u₀ => ?_⟩
  set G₀ : SmoothCcTensor g₀ (2 + 1) (2 + 0) :=
    appCcRS (I := I) (M := M) g₀ (2 + 1) ((2 + 1) + 1) (2 + 0)
      (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
      (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ 2
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))) with hG₀
  set Du : SmoothCcTensor g₀ 0 (2 + 1) := covGrad (I := I) (M := M) g₀ 0 2 u₀ with hDu
  set P : SmoothCcTensor g₀ 0 (2 + 1) :=
    appCc (I := I) (M := M) g₀ (2 + 1) (2 + 1)
      (slotInsertEndoCc (I := I) (M := M) g₀ 2 (gInvDiffRaisedEndoField (I := I) g₀ g₁))
      Du with hP
  rw [armPrincipalSlotPairing_eq_neg_inner (I := I) (M := M) g₀ g₁ 0 u₀, sub_neg_eq_add,
    oneMinusConnLapSmoothIter_zero]
  have hslot : (⟪iteratedCovGrad (I := I) g₀ 0 2 (0 + 1) u₀,
      appCc (I := I) (M := M) g₀ ((2 + 0) + 1) ((2 + 0) + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ (2 + 0)
          (gInvDiffRaisedEndoField (I := I) (M := M) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (0 + 1) u₀)⟫_ℝ : ℝ) =
      tensorL2Inner (I := I) (M := M) g₀ 0 (2 + 1) Du.toFun P.toFun := by
    rw [hDu, hP]
    exact SmoothCcTensor.inner_def (I := I) (M := M)
      (iteratedCovGrad (I := I) g₀ 0 2 (0 + 1) u₀)
      (appCc (I := I) (M := M) g₀ ((2 + 0) + 1) ((2 + 0) + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ (2 + 0)
          (gInvDiffRaisedEndoField (I := I) (M := M) g₀ g₁))
        (iteratedCovGrad (I := I) g₀ 0 2 (0 + 1) u₀))
  rw [hslot]
  have hgreen := tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence
    (I := I) (M := M) g₀ 2 u₀ P
  have hsplit := armResidual_covDivergence_split (I := I) (M := M) g₀ g₁ u₀
  have hfun : (covDivergence (I := I) (M := M) g₀ 2 P).toFun =
      (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toFun +
        (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 0) G₀ Du).toFun := by
    rw [hP, hDu, hG₀, hsplit, SmoothCcTensor.toFun_add]
  rw [hfun] at hgreen
  rw [tensorL2Inner_add_right (I := I) (M := M) g₀ 0 2 u₀.toFun
    (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀).toFun
    (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 0) G₀ Du).toFun
    (DifferentialGeometry.Integral.L2.SmoothCcTensor.integrable_inner_cross
      (I := I) (M := M) u₀ (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ u₀))
    (DifferentialGeometry.Integral.L2.SmoothCcTensor.integrable_inner_cross
      (I := I) (M := M) u₀ (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 0) G₀ Du))] at hgreen
  have hrhs : (⟪iteratedCovGrad (I := I) g₀ 0 2 0 u₀,
      appCc (I := I) (M := M) g₀ (2 + 1) (2 + 0) (-G₀)
        (iteratedCovGrad (I := I) g₀ 0 2 1 u₀)⟫_ℝ : ℝ) =
      - tensorL2Inner (I := I) (M := M) g₀ 0 (2 + 0) u₀.toFun
        (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 0) G₀ Du).toFun := by
    have hinner := SmoothCcTensor.inner_def (I := I) (M := M)
      (iteratedCovGrad (I := I) g₀ 0 2 0 u₀)
      (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 0) (-G₀)
        (iteratedCovGrad (I := I) g₀ 0 2 1 u₀))
    rw [hinner]
    rw [show (iteratedCovGrad (I := I) g₀ 0 2 1 u₀ : SmoothCcTensor g₀ 0 (2 + 1)) = Du from rfl]
    rw [appCc_neg_left (I := I) (M := M) g₀ (2 + 1) (2 + 0) G₀ Du,
      SmoothCcTensor.toFun_neg]
    rw [show (-(appCc (I := I) (M := M) g₀ (2 + 1) (2 + 0) G₀ Du).toFun) =
        (-1 : ℝ) • (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 0) G₀ Du).toFun from by
      funext x
      rw [Pi.neg_apply, Pi.smul_apply, neg_one_smul]]
    rw [tensorL2Inner_smul_right]
    rw [show (iteratedCovGrad (I := I) g₀ 0 2 0 u₀).toFun = u₀.toFun from rfl]
    ring
  rw [hrhs]
  have hDuFun : Du.toFun = (covGrad (I := I) (M := M) g₀ 0 2 u₀).toFun := rfl
  rw [hDuFun]
  have hY : tensorL2Inner (I := I) (M := M) g₀ 0 (2 + 0) u₀.toFun
      (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 0) G₀ Du).toFun =
    tensorL2Inner (I := I) (M := M) g₀ 0 2 u₀.toFun
      (appCc (I := I) (M := M) g₀ (2 + 1) (2 + 0) G₀ Du).toFun := rfl
  linarith [hgreen, hY]

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
