import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralPouNormEquiv
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.AllOrderGardingConstant
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs

noncomputable section

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private theorem covGrad_rawConnLapIter_l2NormSq_eq_tsum
    (g₀ : SmoothRiemannianMetric I M) (i : ℕ) (S : SmoothCcTensor g₀ 0 2) :
    ‖covGrad (I := I) (M := M) g₀ 0 2
        (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖ ^ 2 =
      ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 2,
        (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
            (I := I) (M := M) m) ^ (2 * i + 1) *
          (tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (SmoothCcTensor.toL2 S) m) ^ 2 := by
  classical
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
    with hcompact_def
  set U : SmoothCcTensor g₀ 0 2 := rawTensorConnLapIter (I := I) g₀ 0 2 i S with hU_def
  have hnorm_sq : ‖covGrad (I := I) (M := M) g₀ 0 2 U‖ ^ 2 =
      tensorL2Inner (I := I) (M := M) g₀ 0 3
        (covGrad (I := I) (M := M) g₀ 0 2 U).toFun
        (covGrad (I := I) (M := M) g₀ 0 2 U).toFun := by
    rw [SmoothCcTensor.norm_def (covGrad (I := I) (M := M) g₀ 0 2 U)]
    exact tensorL2Norm_sq_toFun (I := I) (M := M) g₀ 0 3 (covGrad (I := I) (M := M) g₀ 0 2 U)
  rw [hnorm_sq,
    tensorL2Inner_covGrad_self_eq_neg_rawConnLap_inner_gen (I := I) (M := M) g₀ 2 U]
  have hraw_eq : rawTensorConnLapSmooth (I := I) g₀ 0 2 U =
      rawTensorConnLapIter (I := I) g₀ 0 2 (i + 1) S := by
    rw [hU_def, rawTensorConnLapIter_succ]
  rw [hraw_eq]
  have hinner :
      tensorL2Inner (I := I) (M := M) g₀ 0 2
          (rawTensorConnLapIter (I := I) g₀ 0 2 (i + 1) S).toFun U.toFun =
        ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g₀ 0 2,
          tensorL2Coeff (I := I) (M := M) h_compact
              (SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 2 (i + 1) S)) m *
            tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 U) m := by
    have hsymm := SmoothCcTensor.inner_def (I := I) (M := M)
      (rawTensorConnLapIter (I := I) g₀ 0 2 (i + 1) S) U
    rw [← hsymm]
    rw [← SmoothCcTensor.inner_toL2 (I := I) (M := M)
      (rawTensorConnLapIter (I := I) g₀ 0 2 (i + 1) S) U]
    set b := tensorResolventHilbertEigenbasisSigma (I := I) (M := M) h_compact with hb_def
    have h_par := b.tsum_inner_mul_inner
      (SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 2 (i + 1) S))
      (SmoothCcTensor.toL2 U)
    rw [← h_par]
    refine tsum_congr (fun m => ?_)
    rw [tensorL2Coeff_eq_inner (I := I) (M := M) h_compact
        (SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 2 (i + 1) S)) m,
      tensorL2Coeff_eq_inner (I := I) (M := M) h_compact (SmoothCcTensor.toL2 U) m]
    rw [show (⟪SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 2 (i + 1) S), b m⟫_ℝ : ℝ) =
        ⟪b m, SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 2 (i + 1) S)⟫_ℝ from
      real_inner_comm _ _]
  rw [hinner, ← tsum_neg]
  refine tsum_congr (fun m => ?_)
  rw [tensorL2Coeff_ofCompact_rawTensorConnLapIter (I := I) (M := M) g₀ h_compact S m (i + 1),
    hU_def,
    tensorL2Coeff_ofCompact_rawTensorConnLapIter (I := I) (M := M) g₀ h_compact S m i]
  set c := tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m with hc_def
  set L := DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
    (I := I) (M := M) m with hL_def
  have hpow : ((-L) ^ (i + 1) * c) * ((-L) ^ i * c) = (-L) ^ (2 * i + 1) * c ^ 2 := by
    rw [show (2 * i + 1) = (i + 1) + i by ring, pow_add]
    ring
  rw [hpow, (odd_two_mul_add_one i).neg_pow L]
  ring

private theorem covGrad_rawConnLapIter_l2_le_ccSpectralEmbed_odd
    (g₀ : SmoothRiemannianMetric I M) (i : ℕ) (S : SmoothCcTensor g₀ 0 2) :
    ‖covGrad (I := I) (M := M) g₀ 0 2
        (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖ ≤
      ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * i + 1 : ℕ) : ℝ) S‖ := by
  classical
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
    with hcompact_def
  have hnn : 0 ≤ ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * i + 1 : ℕ) : ℝ) S‖ :=
    norm_nonneg _
  have hsq :
      ‖covGrad (I := I) (M := M) g₀ 0 2
          (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖ ^ 2 ≤
        ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * i + 1 : ℕ) : ℝ) S‖ ^ 2 := by
    rw [covGrad_rawConnLapIter_l2NormSq_eq_tsum (I := I) (M := M) g₀ i S,
      ccSpectralEmbed_norm_sq_eq_tsum]
    refine Summable.tsum_le_tsum ?_ ?_ ?_
    · intro m
      set c := tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m with hc_def
      have hbase_nn : (0 : ℝ) ≤
          DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
            (I := I) (M := M) m :=
        tensor_lambda_nonneg (I := I) (M := M) m
      have hbase_le :
          DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
              (I := I) (M := M) m ≤
            1 +
              DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
                (I := I) (M := M) m := by linarith
      have hweight_eq : tensorSobolevWeight (I := I) (M := M) m ((2 * i + 1 : ℕ) : ℝ) =
          (1 +
              DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
                (I := I) (M := M) m) ^ (2 * i + 1) := by
        unfold tensorSobolevWeight
        rw [Real.rpow_natCast]
      rw [hweight_eq]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hbase_nn hbase_le (2 * i + 1)) (sq_nonneg c)
    · have hsummable := (ccSpectralEmbed (I := I) (M := M) g₀
        ((2 * i + 1 : ℕ) : ℝ) S).weighted_summable
      refine Summable.of_nonneg_of_le ?_ ?_ hsummable
      · intro m
        have hbase_nn : (0 : ℝ) ≤
            DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
              (I := I) (M := M) m :=
          tensor_lambda_nonneg (I := I) (M := M) m
        positivity
      · intro m
        have hbase_nn : (0 : ℝ) ≤
            DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
              (I := I) (M := M) m :=
          tensor_lambda_nonneg (I := I) (M := M) m
        have hbase_le :
            DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
                (I := I) (M := M) m ≤
              1 +
                DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
                  (I := I) (M := M) m := by linarith
        have hweight_eq : tensorSobolevWeight (I := I) (M := M) m ((2 * i + 1 : ℕ) : ℝ) =
            (1 +
                DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
                  (I := I) (M := M) m) ^ (2 * i + 1) := by
          unfold tensorSobolevWeight
          rw [Real.rpow_natCast]
        rw [hweight_eq]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ hbase_nn hbase_le (2 * i + 1)) (sq_nonneg _)
    · exact (ccSpectralEmbed (I := I) (M := M) g₀ ((2 * i + 1 : ℕ) : ℝ) S).weighted_summable
  exact le_of_sq_le_sq hsq hnn

private theorem norm_iteratedCovGrad_comp
    (g₀ : SmoothRiemannianMetric I M) (s j i : ℕ) (S : SmoothCcTensor g₀ 0 s) :
    ‖iteratedCovGrad (I := I) g₀ 0 (s + j) i (iteratedCovGrad (I := I) g₀ 0 s j S)‖ =
      ‖iteratedCovGrad (I := I) g₀ 0 s (j + i) S‖ := by
  have hsq :
      ‖iteratedCovGrad (I := I) g₀ 0 (s + j) i
          (iteratedCovGrad (I := I) g₀ 0 s j S)‖ ^ 2 =
        ‖iteratedCovGrad (I := I) g₀ 0 s (j + i) S‖ ^ 2 := by
    rw [← DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm
        (I := I) (M := M) g₀
        (iteratedCovGrad (I := I) g₀ 0 (s + j) i (iteratedCovGrad (I := I) g₀ 0 s j S)),
      ← DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm
        (I := I) (M := M) g₀
        (iteratedCovGrad (I := I) g₀ 0 s (j + i) S),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀
        ((s + j) + i) (iteratedCovGrad (I := I) g₀ 0 (s + j) i
          (iteratedCovGrad (I := I) g₀ 0 s j S)),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀
        (s + (j + i)) (iteratedCovGrad (I := I) g₀ 0 s (j + i) S)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact riemannianFiberNormSq_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 s j i S x
  have h1 : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 (s + j) i
      (iteratedCovGrad (I := I) g₀ 0 s j S)‖ := norm_nonneg _
  have h2 : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 s (j + i) S‖ := norm_nonneg _
  nlinarith [hsq, h1, h2]

private theorem norm_iteratedCovGrad_order_eq
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) {n n' : ℕ} (h : n = n')
    (S : SmoothCcTensor g₀ 0 s) :
    ‖iteratedCovGrad (I := I) g₀ 0 s n S‖ = ‖iteratedCovGrad (I := I) g₀ 0 s n' S‖ := by
  subst h
  rfl

private theorem jet_even
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

private theorem jet_odd
    (g₀ : SmoothRiemannianMetric I M) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g₀ 0 2,
        ∑ j ∈ Finset.range (2 * k + 1 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ ≤
          C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k + 1 : ℕ) : ℝ) S‖ := by
  classical
  obtain ⟨Clow, hClow_nn, hClow⟩ := jet_even (I := I) (M := M) g₀ k
  obtain ⟨Cgard, hCgard_nn, hCgard⟩ :=
    exists_iteratedCovGrad_l2Norm_le_sum_rawConnLapIter (I := I) g₀ 3 k
  obtain ⟨Ceven, hCeven_nn, hCeven⟩ := jet_even (I := I) (M := M) g₀ k
  have hcommfam : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g₀ 0 2,
        ‖rawTensorConnLapIter (I := I) g₀ 0 (2 + 1) i (covGrad (I := I) (M := M) g₀ 0 2 S) -
            covGrad (I := I) (M := M) g₀ 0 2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖ ≤
          C * ∑ a ∈ Finset.range (2 * i), ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖ :=
    fun i => exists_rawConnLapIter_covGrad_commutator_l2Norm_le (I := I) (M := M) g₀ 2 i
  set Ccomm : ℕ → ℝ := fun i => Classical.choose (hcommfam i) with hCcomm_def
  have hCcomm_nn : ∀ i, 0 ≤ Ccomm i := fun i => (Classical.choose_spec (hcommfam i)).1
  have hCcomm : ∀ i, ∀ S : SmoothCcTensor g₀ 0 2,
      ‖rawTensorConnLapIter (I := I) g₀ 0 (2 + 1) i (covGrad (I := I) (M := M) g₀ 0 2 S) -
          covGrad (I := I) (M := M) g₀ 0 2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖ ≤
        Ccomm i * ∑ a ∈ Finset.range (2 * i), ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖ :=
    fun i => (Classical.choose_spec (hcommfam i)).2
  set Ccommsum : ℝ := ∑ i ∈ Finset.range (k + 1), Ccomm i with hCcommsum_def
  have hCcommsum_nn : 0 ≤ Ccommsum :=
    Finset.sum_nonneg (fun i _ => hCcomm_nn i)
  refine ⟨Clow + Cgard * (((k + 1 : ℕ) : ℝ) + Ccommsum * Ceven), by positivity,
    fun S => ?_⟩
  set Nspec : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k + 1 : ℕ) : ℝ) S‖
    with hNspec_def
  have hNspec_nn : 0 ≤ Nspec := norm_nonneg _
  have hembed_eq : ccSpectralEmbed (I := I) (M := M) g₀ ((2 * k + 1 : ℕ) : ℝ) S =
      smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k + 1 : ℕ) : ℝ) S :=
    tensorHs.ext (funext (fun i => rfl))
  have hccmono : ∀ (σ : ℕ), σ ≤ 2 * k + 1 →
      ‖ccSpectralEmbed (I := I) (M := M) g₀ ((σ : ℕ) : ℝ) S‖ ≤ Nspec := by
    intro σ hσ
    rw [hNspec_def, ← hembed_eq]
    refine ccSpectralEmbed_norm_mono (I := I) (M := M) g₀ ?_ S
    have : (σ : ℕ) ≤ (2 * k + 1 : ℕ) := hσ
    exact_mod_cast this
  have hlow_le : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S‖ ≤ Nspec := by
    have hembed2k : smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S =
        ccSpectralEmbed (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S :=
      tensorHs.ext (funext (fun i => rfl))
    rw [hembed2k]
    exact hccmono (2 * k) (by omega)
  have hlowsum : ∑ j ∈ Finset.range (2 * k + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ ≤ Clow * Nspec := by
    refine le_trans (hClow S) ?_
    exact mul_le_mul_of_nonneg_left hlow_le hClow_nn
  have heven_le : ∑ j ∈ Finset.range (2 * k + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ ≤ Ceven * Nspec := by
    refine le_trans (hCeven S) ?_
    exact mul_le_mul_of_nonneg_left hlow_le hCeven_nn
  have hccoeff_le : ∀ i ∈ Finset.range (k + 1),
      ‖rawTensorConnLapIter (I := I) g₀ 0 3 i
          (covGrad (I := I) (M := M) g₀ 0 2 S)‖ ≤
        (1 + Ccomm i * Ceven) * Nspec := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hsplit :
        rawTensorConnLapIter (I := I) g₀ 0 3 i (covGrad (I := I) (M := M) g₀ 0 2 S) =
          covGrad (I := I) (M := M) g₀ 0 2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S) +
            (rawTensorConnLapIter (I := I) g₀ 0 (2 + 1) i (covGrad (I := I) (M := M) g₀ 0 2 S) -
              covGrad (I := I) (M := M) g₀ 0 2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S)) := by
      abel
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    have hmain : ‖covGrad (I := I) (M := M) g₀ 0 2
          (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖ ≤ Nspec := by
      refine le_trans
        (covGrad_rawConnLapIter_l2_le_ccSpectralEmbed_odd (I := I) (M := M) g₀ i S) ?_
      exact hccmono (2 * i + 1) (by omega)
    have hcomm := hCcomm i S
    have hsub_le : 2 * i ≤ 2 * k + 1 := by omega
    have hsubrange : ∑ a ∈ Finset.range (2 * i),
          ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖ ≤
        ∑ a ∈ Finset.range (2 * k + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (f := fun a => ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖)
        (Finset.range_mono hsub_le) (fun a _ _ => norm_nonneg _)
    have hcommterm :
        ‖rawTensorConnLapIter (I := I) g₀ 0 (2 + 1) i (covGrad (I := I) (M := M) g₀ 0 2 S) -
            covGrad (I := I) (M := M) g₀ 0 2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖ ≤
          Ccomm i * Ceven * Nspec := by
      calc ‖rawTensorConnLapIter (I := I) g₀ 0 (2 + 1) i
              (covGrad (I := I) (M := M) g₀ 0 2 S) -
              covGrad (I := I) (M := M) g₀ 0 2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖
          ≤ Ccomm i * ∑ a ∈ Finset.range (2 * i),
              ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖ := hcomm
        _ ≤ Ccomm i * ∑ a ∈ Finset.range (2 * k + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖ :=
            mul_le_mul_of_nonneg_left hsubrange (hCcomm_nn i)
        _ ≤ Ccomm i * (Ceven * Nspec) :=
            mul_le_mul_of_nonneg_left heven_le (hCcomm_nn i)
        _ = Ccomm i * Ceven * Nspec := by ring
    calc ‖covGrad (I := I) (M := M) g₀ 0 2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖ +
          ‖rawTensorConnLapIter (I := I) g₀ 0 (2 + 1) i (covGrad (I := I) (M := M) g₀ 0 2 S) -
            covGrad (I := I) (M := M) g₀ 0 2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖
        ≤ Nspec + Ccomm i * Ceven * Nspec :=
          add_le_add hmain hcommterm
      _ = (1 + Ccomm i * Ceven) * Nspec := by ring
  have htop_le : ‖iteratedCovGrad (I := I) g₀ 0 2 (2 * k + 1) S‖ ≤
      Cgard * (((k + 1 : ℕ) : ℝ) + Ccommsum * Ceven) * Nspec := by
    have hbridge : ‖iteratedCovGrad (I := I) g₀ 0 2 (2 * k + 1) S‖ =
        ‖iteratedCovGrad (I := I) g₀ 0 3 (2 * k) (covGrad (I := I) (M := M) g₀ 0 2 S)‖ := by
      have h := norm_iteratedCovGrad_comp (I := I) (M := M) g₀ 2 1 (2 * k) S
      have hcov : covGrad (I := I) (M := M) g₀ 0 2 S =
          iteratedCovGrad (I := I) g₀ 0 2 1 S := rfl
      have horder : ‖iteratedCovGrad (I := I) g₀ 0 2 (2 * k + 1) S‖ =
          ‖iteratedCovGrad (I := I) g₀ 0 2 (1 + 2 * k) S‖ :=
        norm_iteratedCovGrad_order_eq (I := I) (M := M) g₀ 2 (by omega) S
      rw [horder, ← h, hcov]
    rw [hbridge]
    have hgard := hCgard (2 * k) (le_refl _) (covGrad (I := I) (M := M) g₀ 0 2 S)
    have hgard' : ‖iteratedCovGrad (I := I) g₀ 0 3 (2 * k)
          (covGrad (I := I) (M := M) g₀ 0 2 S)‖ ≤
        Cgard * ∑ i ∈ Finset.range (k + 1),
          ‖rawTensorConnLapIter (I := I) g₀ 0 3 i (covGrad (I := I) (M := M) g₀ 0 2 S)‖ := by
      have heq1 : tensorL2Norm (I := I) (M := M) g₀ 0 (3 + 2 * k)
            (iteratedCovGrad (I := I) g₀ 0 3 (2 * k)
              (covGrad (I := I) (M := M) g₀ 0 2 S)).toFun =
          ‖iteratedCovGrad (I := I) g₀ 0 3 (2 * k) (covGrad (I := I) (M := M) g₀ 0 2 S)‖ :=
        DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm (I := I) (M := M) g₀
          (iteratedCovGrad (I := I) g₀ 0 3 (2 * k) (covGrad (I := I) (M := M) g₀ 0 2 S))
      rw [← heq1]
      refine le_trans hgard ?_
      refine mul_le_mul_of_nonneg_left (le_of_eq ?_) hCgard_nn
      refine Finset.sum_congr rfl (fun i _ => ?_)
      exact DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm
        (I := I) (M := M) g₀
        (rawTensorConnLapIter (I := I) g₀ 0 3 i (covGrad (I := I) (M := M) g₀ 0 2 S))
    have hsumcoeff : ∑ i ∈ Finset.range (k + 1),
          ‖rawTensorConnLapIter (I := I) g₀ 0 3 i (covGrad (I := I) (M := M) g₀ 0 2 S)‖ ≤
        (((k + 1 : ℕ) : ℝ) + Ccommsum * Ceven) * Nspec := by
      calc ∑ i ∈ Finset.range (k + 1),
            ‖rawTensorConnLapIter (I := I) g₀ 0 3 i (covGrad (I := I) (M := M) g₀ 0 2 S)‖
          ≤ ∑ i ∈ Finset.range (k + 1), (1 + Ccomm i * Ceven) * Nspec :=
            Finset.sum_le_sum hccoeff_le
        _ = ∑ i ∈ Finset.range (k + 1), (Nspec + (Ccomm i) * (Ceven * Nspec)) :=
            Finset.sum_congr rfl (fun i _ => by ring)
        _ = (((k + 1 : ℕ) : ℝ) + Ccommsum * Ceven) * Nspec := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
              ← Finset.sum_mul]
            rw [hCcommsum_def]
            ring
    calc ‖iteratedCovGrad (I := I) g₀ 0 3 (2 * k) (covGrad (I := I) (M := M) g₀ 0 2 S)‖
        ≤ Cgard * ∑ i ∈ Finset.range (k + 1),
            ‖rawTensorConnLapIter (I := I) g₀ 0 3 i (covGrad (I := I) (M := M) g₀ 0 2 S)‖ := hgard'
      _ ≤ Cgard * ((((k + 1 : ℕ) : ℝ) + Ccommsum * Ceven) * Nspec) :=
          mul_le_mul_of_nonneg_left hsumcoeff hCgard_nn
      _ = Cgard * (((k + 1 : ℕ) : ℝ) + Ccommsum * Ceven) * Nspec := by ring
  rw [Finset.sum_range_succ (fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖) (2 * k + 1)]
  calc ∑ j ∈ Finset.range (2 * k + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ +
        ‖iteratedCovGrad (I := I) g₀ 0 2 (2 * k + 1) S‖
      ≤ Clow * Nspec + Cgard * (((k + 1 : ℕ) : ℝ) + Ccommsum * Ceven) * Nspec :=
        add_le_add hlowsum htop_le
    _ = (Clow + Cgard * (((k + 1 : ℕ) : ℝ) + Ccommsum * Ceven)) * Nspec := by ring

theorem exists_iteratedCovGrad_sum_le_smoothCcToTensorHs
    (g₀ : SmoothRiemannianMetric I M) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g₀ 0 2,
        ∑ j ∈ Finset.range (n + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ ≤
          C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (n : ℝ) S‖ := by
  classical
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · obtain ⟨C, hC_nn, hC⟩ := jet_even (I := I) (M := M) g₀ k
    refine ⟨C, hC_nn, fun S => ?_⟩
    have hn2k : n = 2 * k := by omega
    subst hn2k
    exact hC S
  · obtain ⟨C, hC_nn, hC⟩ := jet_odd (I := I) (M := M) g₀ k
    refine ⟨C, hC_nn, fun S => ?_⟩
    have hn : n = 2 * k + 1 := by omega
    subst hn
    exact hC S

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
