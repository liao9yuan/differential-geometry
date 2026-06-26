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

noncomputable section

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

private noncomputable def armPrincipalSlotPairing
    (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ) (u₀ : SmoothCcTensor g₀ 0 2) : ℝ :=
  tensorL2Inner (I := I) (M := M) g₀ 0 ((2 + n) + 1)
    (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E)
      ((iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀).toSection x))
    (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E)
      (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvDiffSlotApplied
        (I := I) g₀ g₁ (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (n + 1) u₀).toSection x)))

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
          rem u₀ ≤ Clower * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2 :=
  sorry

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
          (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvDiffSlotApplied
            (I := I) g₀ g₁ (2 + n) x (A.toSection x)) := by
    intro x
    rfl
  have hWS_int : Integrable
      (fun x => tensorInnerPointwise (I := I) (M := M) g₀ 0 ((2 + n) + 1) x
        (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (A.toSection x))
        (TensorRSSpace.toModel (𝕜 := ℝ) (E := E)
          (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvDiffSlotApplied
            (I := I) g₀ g₁ (2 + n) x (A.toSection x))))
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    have hcross := DifferentialGeometry.Integral.L2.SmoothCcTensor.integrable_inner_cross
      (I := I) (M := M) (g := g₀) (r := 0) (s := (2 + n) + 1) A B
    refine hcross.congr ?_
    filter_upwards with x
    rw [hBfun x]
    rfl
  have hWW_int : Integrable
      (fun x => tensorInnerPointwise (I := I) (M := M) g₀ 0 ((2 + n) + 1) x
        (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (A.toSection x))
        (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (A.toSection x)))
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    DifferentialGeometry.Integral.L2.SmoothCcTensor.integrable_inner_cross
      (I := I) (M := M) (g := g₀) (r := 0) (s := (2 + n) + 1) A A
  have htool := DifferentialGeometry.Analysis.Sobolev.TensorHilbert.tensorL2Inner_gInvDiffSlot_le
    (I := I) (M := M) g₀ g₁ h htie hδ_lt hδ_nn hδ (2 + n)
    (fun x => A.toSection x) hWS_int hWW_int
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
  sorry

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
            (δ / (1 - δ)) *
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
  have hMn_nn : 0 ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2 :=
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
  nlinarith [hstep, hr, hMn_nn]

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
            2 * (δ / (1 - δ)) *
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
      2 * (δ / (1 - δ)) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((n : ℕ) : ℝ) + 1) u₀‖ ^ 2 +
          2 * Clower * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((n : ℕ) : ℝ) u₀‖ ^ 2 =
        2 * ((δ / (1 - δ)) *
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
            2 * (δ / (1 - δ)) *
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

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
