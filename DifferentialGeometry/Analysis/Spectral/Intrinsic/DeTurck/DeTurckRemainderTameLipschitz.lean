import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Sobolev.MoserTameProduct
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.GagliardoNirenbergProductTwoArm
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovariantBilinearLeibniz
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqSmoothCcUniformBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqLeRawComponents
import DifferentialGeometry.Analysis.Integration.Measure.FamilyDecomposition
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RawComponentEuclideanBridge
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.ChartDeTurckRicciRHSRealizeJet
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RHSSectionChartComponentIdentity
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.ChartGeometry.GoodSetMeasure
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckMetricArmCoeffField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckCurvatureArmCoeffField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.AppCcDropIteratedGrid
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckLinearization
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRHSSectionRealizeUnitModel

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (covGrad unitModel smoothCcTensor_ext_of_unitModel unitTensor)
open DifferentialGeometry.PDE.DeTurck (deTurckVF)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private theorem riemannianFiberNormSq_neg_value
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (-v) =
      riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (-v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_neg]
  rw [← neg_one_smul ℝ (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
        (r := r) (s := s) (x := x) v),
    tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
  ring

private theorem rawTensorConnLapSmooth_fiberNormSq_le_secondCovGrad_jet
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ∀ (S : SmoothCcTensor g₀ 0 s) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x
            ((rawTensorConnLapSmooth (I := I) g₀ 0 s S).toSection x) ≤
          C * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + 2) x
            ((iteratedCovGrad (I := I) g₀ 0 s 2 S).toSection x) := by
  refine ⟨((Module.finrank ℝ E : ℝ)) ^ 2, by positivity, fun S x => ?_⟩
  have hbase := rawConnLap_fiberNormSq_le_secondCovGrad (I := I) (M := M) g₀ s S x
  
  
  simpa only [iteratedCovGrad_succ, iteratedCovGrad_zero] using hbase

private theorem pointwiseTensorCurv_iteratedCovGrad_fiberNormSq_jet_le
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ K : ℕ → ℝ, (∀ p, 0 ≤ K p) ∧
      ∀ (p : ℕ) (S : SmoothCcTensor g₀ 0 s) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + 1) + p) x
            ((iteratedCovGrad (I := I) g₀ 0 (s + 1) p
              (pointwiseTensorCurv (I := I) (M := M) g₀ s S)).toSection x) ≤
          K p * ∑ a ∈ Finset.range (p + 2),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + a) x
              ((iteratedCovGrad (I := I) g₀ 0 s a S).toSection x) := by
  classical
  obtain ⟨H_R, H_dR, hsec⟩ :=
    exists_pointwiseTensorCurv_firstOrder_homField_section (I := I) (M := M) g₀ s
  obtain ⟨ccR, hccR_nn, hccR⟩ :=
    exists_appFullSec_iteratedCovGrad_window_bound (I := I) (M := M) g₀ 0 (s + 1) (s + 1) H_R
  obtain ⟨ccdR, hccdR_nn, hccdR⟩ :=
    exists_appFullSec_iteratedCovGrad_window_bound (I := I) (M := M) g₀ 0 s (s + 1) H_dR
  refine ⟨fun p => 2 * ccR p + 2 * ccdR p,
    fun p => by have := hccR_nn p; have := hccdR_nn p; positivity, fun p S x => ?_⟩
  set rfnsS : ℕ → ℝ := fun a =>
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + a) x
      ((iteratedCovGrad (I := I) g₀ 0 s a S).toSection x) with hrfnsS_def
  have hrfnsS_nn : ∀ a, 0 ≤ rfnsS a := fun a =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (s + a) x _
  set FULL : ℝ := ∑ a ∈ Finset.range (p + 2), rfnsS a with hFULL_def
  have hFULL_nn : 0 ≤ FULL := Finset.sum_nonneg (fun a _ => hrfnsS_nn a)
  
  set AR : SmoothCcTensor g₀ 0 (s + 1) :=
    appFullSec (I := I) (M := M) g₀ 0 (s + 1) (s + 1) H_R (covGrad (I := I) (M := M) g₀ 0 s S)
    with hAR_def
  set AdR : SmoothCcTensor g₀ 0 (s + 1) :=
    appFullSec (I := I) (M := M) g₀ 0 s (s + 1) H_dR S with hAdR_def
  have hgradsplit :
      iteratedCovGrad (I := I) g₀ 0 (s + 1) p (pointwiseTensorCurv (I := I) (M := M) g₀ s S) =
        iteratedCovGrad (I := I) g₀ 0 (s + 1) p AR + iteratedCovGrad (I := I) g₀ 0 (s + 1) p AdR := by
    rw [hsec S, ← hAR_def, ← hAdR_def, iteratedCovGrad_add (I := I) (M := M) g₀ 0 (s + 1) p]
  have happ :
      (iteratedCovGrad (I := I) g₀ 0 (s + 1) p
          (pointwiseTensorCurv (I := I) (M := M) g₀ s S)).toSection x =
        (iteratedCovGrad (I := I) g₀ 0 (s + 1) p AR).toSection x +
          (iteratedCovGrad (I := I) g₀ 0 (s + 1) p AdR).toSection x := by
    rw [hgradsplit, SmoothCcTensor.toSection_add]; rfl
  rw [happ]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 ((s + 1) + p) x
    ((iteratedCovGrad (I := I) g₀ 0 (s + 1) p AR).toSection x)
    ((iteratedCovGrad (I := I) g₀ 0 (s + 1) p AdR).toSection x)) ?_
  
  have hAR_w :
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + 1) + p) x
          ((iteratedCovGrad (I := I) g₀ 0 (s + 1) p AR).toSection x) ≤
        ccR p * ∑ i ∈ Finset.range (p + 1), rfnsS (i + 1) := by
    
    have hcov1 : covGrad (I := I) (M := M) g₀ 0 s S = iteratedCovGrad (I := I) g₀ 0 s 1 S := rfl
    have h := hccR (iteratedCovGrad (I := I) g₀ 0 s 1 S) p x
    rw [hAR_def, hcov1]
    refine h.trans_eq ?_
    refine congrArg (ccR p * ·) (Finset.sum_congr rfl (fun i _ => ?_))
    have hcomp := rfns_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 s 1 i S x
    
    have harg : rfnsS (1 + i) = rfnsS (i + 1) := by rw [Nat.add_comm 1 i]
    rw [← harg, hrfnsS_def]
    exact hcomp
  have hAdR_w :
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + 1) + p) x
          ((iteratedCovGrad (I := I) g₀ 0 (s + 1) p AdR).toSection x) ≤
        ccdR p * ∑ i ∈ Finset.range (p + 1), rfnsS i := by
    have h := hccdR S p x
    rw [hAdR_def]
    exact h.trans_eq (by rw [hrfnsS_def])
  
  have hsubR : ∑ i ∈ Finset.range (p + 1), rfnsS (i + 1) ≤ FULL := by
    rw [hFULL_def]
    have hIco : ∑ i ∈ Finset.range (p + 1), rfnsS (i + 1) =
        ∑ a ∈ Finset.Ico 1 (1 + (p + 1)), rfnsS a := by
      rw [Finset.sum_Ico_eq_sum_range]
      refine Finset.sum_congr (by congr 1; omega) (fun i _ => by rw [Nat.add_comm 1 i])
    rw [hIco]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun a _ _ => hrfnsS_nn a)
    intro a ha; rw [Finset.mem_Ico] at ha; rw [Finset.mem_range]; omega
  have hsubdR : ∑ i ∈ Finset.range (p + 1), rfnsS i ≤ FULL := by
    rw [hFULL_def]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun a _ _ => hrfnsS_nn a)
    intro a ha; rw [Finset.mem_range] at ha ⊢; omega
  calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + 1) + p) x
            ((iteratedCovGrad (I := I) g₀ 0 (s + 1) p AR).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + 1) + p) x
            ((iteratedCovGrad (I := I) g₀ 0 (s + 1) p AdR).toSection x)
      ≤ 2 * (ccR p * ∑ i ∈ Finset.range (p + 1), rfnsS (i + 1)) +
          2 * (ccdR p * ∑ i ∈ Finset.range (p + 1), rfnsS i) :=
        add_le_add (by linarith [hAR_w]) (by linarith [hAdR_w])
    _ ≤ 2 * (ccR p * FULL) + 2 * (ccdR p * FULL) := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hsubR (hccR_nn p)) (by norm_num)
        · exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hsubdR (hccdR_nn p)) (by norm_num)
    _ = (2 * ccR p + 2 * ccdR p) * FULL := by ring

set_option linter.style.show false in

private theorem iteratedRoughLapGrad_commutator_fiberNormSq_jet_le_aux
    (g₀ : SmoothRiemannianMetric I M) (m : ℕ) :
    ∀ s : ℕ, ∃ Cfun : ℕ → ℝ, (∀ p, 0 ≤ Cfun p) ∧
      ∀ (p : ℕ) (S : SmoothCcTensor g₀ 0 s) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + m) + p) x
            ((iteratedCovGrad (I := I) g₀ 0 (s + m) p
              (rawTensorConnLapSmooth (I := I) g₀ 0 (s + m)
                  (iteratedCovGrad (I := I) g₀ 0 s m S) -
                iteratedCovGrad (I := I) g₀ 0 s m
                  (rawTensorConnLapSmooth (I := I) g₀ 0 s S))).toSection x) ≤
          Cfun p * ∑ a ∈ Finset.range (m + p + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + a) x
              ((iteratedCovGrad (I := I) g₀ 0 s a S).toSection x) := by
  induction m with
  | zero =>
    intro s
    refine ⟨fun _ => 0, fun _ => le_refl _, fun p S x => ?_⟩
    
    have hcomm0 :
        rawTensorConnLapSmooth (I := I) g₀ 0 (s + 0) (iteratedCovGrad (I := I) g₀ 0 s 0 S) -
            iteratedCovGrad (I := I) g₀ 0 s 0 (rawTensorConnLapSmooth (I := I) g₀ 0 s S) =
          (0 : SmoothCcTensor g₀ 0 (s + 0)) := by
      simp only [iteratedCovGrad_zero, Nat.add_zero, sub_self]
    rw [hcomm0]
    have hz : iteratedCovGrad (I := I) g₀ 0 (s + 0) p (0 : SmoothCcTensor g₀ 0 (s + 0)) =
        (0 : SmoothCcTensor g₀ 0 (s + 0 + p)) := by
      have := iteratedCovGrad_sub (I := I) (M := M) g₀ 0 (s + 0) p
        (0 : SmoothCcTensor g₀ 0 (s + 0)) (0 : SmoothCcTensor g₀ 0 (s + 0))
      simpa using this
    rw [hz]
    have hzero : ((0 : SmoothCcTensor g₀ 0 (s + 0 + p)).toSection x :
        TensorRSSpace 0 ((s + 0) + p) I x) = 0 := rfl
    rw [show ((0 : SmoothCcTensor g₀ 0 (s + 0 + p)).toSection x) =
        (0 : TensorRSSpace 0 ((s + 0) + p) I x) from hzero]
    rw [riemannianFiberNormSq_zero (I := I) (M := M) g₀ 0 ((s + 0) + p) x]
    exact mul_nonneg (le_refl 0)
      (Finset.sum_nonneg (fun a _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (s + a) x _))
  | succ m ih =>
    intro s
    obtain ⟨Cm, hCm_nn, hCm⟩ := ih s
    obtain ⟨K, hK_nn, hK⟩ :=
      pointwiseTensorCurv_iteratedCovGrad_fiberNormSq_jet_le (I := I) (M := M) g₀ (s + m)
    refine ⟨fun p => 2 * K p + 2 * Cm (p + 1),
      fun p => by have := hK_nn p; have := hCm_nn (p + 1); positivity, fun p S x => ?_⟩
    
    have hsplit :
        rawTensorConnLapSmooth (I := I) g₀ 0 (s + (m + 1))
              (iteratedCovGrad (I := I) g₀ 0 s (m + 1) S) -
            iteratedCovGrad (I := I) g₀ 0 s (m + 1)
              (rawTensorConnLapSmooth (I := I) g₀ 0 s S) =
          pointwiseTensorCurv (I := I) (M := M) g₀ (s + m) (iteratedCovGrad (I := I) g₀ 0 s m S) +
            covGrad (I := I) (M := M) g₀ 0 (s + m)
              (rawTensorConnLapSmooth (I := I) g₀ 0 (s + m) (iteratedCovGrad (I := I) g₀ 0 s m S) -
                iteratedCovGrad (I := I) g₀ 0 s m (rawTensorConnLapSmooth (I := I) g₀ 0 s S)) := by
      rw [iteratedCovGrad_succ (I := I) (M := M) g₀ 0 s m S,
        iteratedCovGrad_succ (I := I) (M := M) g₀ 0 s m
          (rawTensorConnLapSmooth (I := I) g₀ 0 s S)]
      show rawTensorConnLapSmooth (I := I) g₀ 0 (s + m + 1)
            (covGrad (I := I) (M := M) g₀ 0 (s + m) (iteratedCovGrad (I := I) g₀ 0 s m S)) -
          covGrad (I := I) (M := M) g₀ 0 (s + m)
            (iteratedCovGrad (I := I) g₀ 0 s m (rawTensorConnLapSmooth (I := I) g₀ 0 s S)) =
        pointwiseTensorCurv (I := I) (M := M) g₀ (s + m) (iteratedCovGrad (I := I) g₀ 0 s m S) +
          covGrad (I := I) (M := M) g₀ 0 (s + m)
            (rawTensorConnLapSmooth (I := I) g₀ 0 (s + m) (iteratedCovGrad (I := I) g₀ 0 s m S) -
              iteratedCovGrad (I := I) g₀ 0 s m (rawTensorConnLapSmooth (I := I) g₀ 0 s S))
      rw [pointwiseTensorCurv_commutator_eq (I := I) (M := M) g₀ (s + m)
          (iteratedCovGrad (I := I) g₀ 0 s m S),
        covGrad_sub (I := I) (M := M) g₀ 0 (s + m)]
      abel
    set comm_m : SmoothCcTensor g₀ 0 (s + m) :=
      rawTensorConnLapSmooth (I := I) g₀ 0 (s + m) (iteratedCovGrad (I := I) g₀ 0 s m S) -
        iteratedCovGrad (I := I) g₀ 0 s m (rawTensorConnLapSmooth (I := I) g₀ 0 s S) with hcomm_m
    set gradm : SmoothCcTensor g₀ 0 (s + m) := iteratedCovGrad (I := I) g₀ 0 s m S with hgradm
    set fullSum : ℝ := ∑ a ∈ Finset.range (m + 1 + p + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + a) x
        ((iteratedCovGrad (I := I) g₀ 0 s a S).toSection x) with hfullSum
    have hfullSum_nn : 0 ≤ fullSum :=
      Finset.sum_nonneg (fun a _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (s + a) x _)
    
    have happ :
        (iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
            (rawTensorConnLapSmooth (I := I) g₀ 0 (s + (m + 1))
                (iteratedCovGrad (I := I) g₀ 0 s (m + 1) S) -
              iteratedCovGrad (I := I) g₀ 0 s (m + 1)
                (rawTensorConnLapSmooth (I := I) g₀ 0 s S))).toSection x =
          (iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
              (pointwiseTensorCurv (I := I) (M := M) g₀ (s + m) gradm)).toSection x +
            (iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
              (covGrad (I := I) (M := M) g₀ 0 (s + m) comm_m)).toSection x := by
      rw [hsplit, iteratedCovGrad_add (I := I) (M := M) g₀ 0 (s + (m + 1)) p,
        SmoothCcTensor.toSection_add]
      rfl
    rw [happ]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 ((s + (m + 1)) + p) x
      ((iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
        (pointwiseTensorCurv (I := I) (M := M) g₀ (s + m) gradm)).toSection x)
      ((iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
        (covGrad (I := I) (M := M) g₀ 0 (s + m) comm_m)).toSection x)) ?_
    
    have harm1 :
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + (m + 1)) + p) x
            ((iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
              (pointwiseTensorCurv (I := I) (M := M) g₀ (s + m) gradm)).toSection x) ≤
          K p * fullSum := by
      have hKb := hK p gradm x
      
      have hreindex : ∀ a,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + m) + a) x
              ((iteratedCovGrad (I := I) g₀ 0 (s + m) a gradm).toSection x) =
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + (m + a)) x
              ((iteratedCovGrad (I := I) g₀ 0 s (m + a) S).toSection x) := by
        intro a
        rw [hgradm]
        exact rfns_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 s m a S x
      rw [Finset.sum_congr rfl (fun a _ => hreindex a)] at hKb
      
      refine hKb.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (hK_nn p)
      
      have hIco : ∑ a ∈ Finset.range (p + 2),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + (m + a)) x
              ((iteratedCovGrad (I := I) g₀ 0 s (m + a) S).toSection x) =
          ∑ b ∈ Finset.Ico m (m + (p + 2)),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + b) x
              ((iteratedCovGrad (I := I) g₀ 0 s b S).toSection x) := by
        rw [Finset.sum_Ico_eq_sum_range]
        refine Finset.sum_congr (by congr 1; omega) (fun a _ => by rw [show m + a = m + a from rfl])
      rw [hfullSum, hIco]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_
        (fun b _ _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (s + b) x _)
      intro b hb; rw [Finset.mem_Ico] at hb; rw [Finset.mem_range]; omega
    
    have harm2 :
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + (m + 1)) + p) x
            ((iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
              (covGrad (I := I) (M := M) g₀ 0 (s + m) comm_m)).toSection x) ≤
          Cm (p + 1) * fullSum := by
      
      have hCmb := hCm (p + 1) S x
      rw [← hcomm_m] at hCmb
      have hsum_eq : ∑ a ∈ Finset.range (m + (p + 1) + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + a) x
              ((iteratedCovGrad (I := I) g₀ 0 s a S).toSection x) = fullSum := by
        rw [hfullSum, show m + (p + 1) + 1 = m + 1 + p + 1 from by omega]
      rw [hsum_eq] at hCmb
      
      have h := rfns_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 (s + m) 1 p comm_m x
      rw [iteratedCovGrad_succ (I := I) (M := M) g₀ 0 (s + m) 0 comm_m,
        iteratedCovGrad_zero] at h
      
      
      rw [Nat.add_comm 1 p] at h
      exact h.trans_le hCmb
    
    calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + (m + 1)) + p) x
              ((iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
                (pointwiseTensorCurv (I := I) (M := M) g₀ (s + m) gradm)).toSection x) +
            2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((s + (m + 1)) + p) x
              ((iteratedCovGrad (I := I) g₀ 0 (s + (m + 1)) p
                (covGrad (I := I) (M := M) g₀ 0 (s + m) comm_m)).toSection x)
        ≤ 2 * (K p * fullSum) + 2 * (Cm (p + 1) * fullSum) :=
          add_le_add (mul_le_mul_of_nonneg_left harm1 (by norm_num))
            (mul_le_mul_of_nonneg_left harm2 (by norm_num))
      _ = (2 * K p + 2 * Cm (p + 1)) * fullSum := by ring

private theorem rawTensorConnLapSmooth_iteratedCovGrad_riemannianFiberNormSq_jet_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ∀ (W : SmoothCcTensor g₀ 0 2) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
            ((iteratedCovGrad (I := I) g₀ 0 2 a
              (rawTensorConnLapSmooth (I := I) g₀ 0 2 W)).toSection x) ≤
          C * ∑ q ∈ Finset.range (a + 2 + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
              ((iteratedCovGrad (I := I) g₀ 0 2 q W).toSection x) := by
  classical
  
  obtain ⟨Cpost, hCpost_nn, hCpost⟩ :=
    rawTensorConnLapSmooth_fiberNormSq_le_secondCovGrad_jet (I := I) (M := M) g₀ (2 + a)
  
  obtain ⟨Cfun, hCfun_nn, hCfun⟩ :=
    iteratedRoughLapGrad_commutator_fiberNormSq_jet_le_aux (I := I) (M := M) g₀ a 2
  refine ⟨2 * Cpost + 2 * Cfun 0, by have := hCfun_nn 0; positivity, fun W x => ?_⟩
  set Scol : ℝ := ∑ q ∈ Finset.range (a + 2 + 1),
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
      ((iteratedCovGrad (I := I) g₀ 0 2 q W).toSection x) with hScol_def
  have hScol_nn : 0 ≤ Scol :=
    Finset.sum_nonneg fun q _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + q) x _
  
  set Comm : SmoothCcTensor g₀ 0 (2 + a) :=
    rawTensorConnLapSmooth (I := I) g₀ 0 (2 + a) (iteratedCovGrad (I := I) g₀ 0 2 a W) -
      iteratedCovGrad (I := I) g₀ 0 2 a (rawTensorConnLapSmooth (I := I) g₀ 0 2 W) with hComm_def
  have hsplit :
      iteratedCovGrad (I := I) g₀ 0 2 a (rawTensorConnLapSmooth (I := I) g₀ 0 2 W) =
        rawTensorConnLapSmooth (I := I) g₀ 0 (2 + a) (iteratedCovGrad (I := I) g₀ 0 2 a W) +
          (-Comm) := by
    rw [hComm_def]; abel
  have hsec :
      (iteratedCovGrad (I := I) g₀ 0 2 a
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 W)).toSection x =
        (rawTensorConnLapSmooth (I := I) g₀ 0 (2 + a) (iteratedCovGrad (I := I) g₀ 0 2 a W)).toSection x +
          (-Comm).toSection x := by
    rw [hsplit, SmoothCcTensor.toSection_add]; rfl
  rw [hsec]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (2 + a) x
    ((rawTensorConnLapSmooth (I := I) g₀ 0 (2 + a) (iteratedCovGrad (I := I) g₀ 0 2 a W)).toSection x)
    ((-Comm).toSection x)) ?_
  
  have hΔarm :
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
          ((rawTensorConnLapSmooth (I := I) g₀ 0 (2 + a)
            (iteratedCovGrad (I := I) g₀ 0 2 a W)).toSection x) ≤ Cpost * Scol := by
    refine (hCpost (iteratedCovGrad (I := I) g₀ 0 2 a W) x).trans ?_
    
    have hreindex :
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + a) + 2) x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + a) 2 (iteratedCovGrad (I := I) g₀ 0 2 a W)).toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (a + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (a + 2) W).toSection x) :=
      rfns_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 2 a 2 W x
    rw [hreindex]
    refine mul_le_mul_of_nonneg_left ?_ hCpost_nn
    rw [hScol_def]
    refine Finset.single_le_sum
      (f := fun q => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
        ((iteratedCovGrad (I := I) g₀ 0 2 q W).toSection x))
      (fun q _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + q) x _) ?_
    rw [Finset.mem_range]; omega
  
  have hCommarm :
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x ((-Comm).toSection x) ≤
        Cfun 0 * Scol := by
    
    have hneg : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x ((-Comm).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x (Comm.toSection x) := by
      rw [SmoothCcTensor.toSection_neg]
      rw [show ((-Comm.toSection) x : TensorRSSpace 0 (2 + a) I x) = -(Comm.toSection x) from rfl]
      exact riemannianFiberNormSq_neg_value (I := I) (M := M) g₀ 0 (2 + a) x (Comm.toSection x)
    rw [hneg]
    
    have hC := hCfun 0 W x
    rw [iteratedCovGrad_zero] at hC
    refine hC.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (hCfun_nn 0)
    rw [hScol_def]
    
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_
      (fun q _ _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + q) x _)
    intro q hq; rw [Finset.mem_range] at hq ⊢; omega
  calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x
            ((rawTensorConnLapSmooth (I := I) g₀ 0 (2 + a)
              (iteratedCovGrad (I := I) g₀ 0 2 a W)).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x ((-Comm).toSection x)
      ≤ 2 * (Cpost * Scol) + 2 * (Cfun 0 * Scol) :=
        add_le_add (mul_le_mul_of_nonneg_left hΔarm (by norm_num))
          (mul_le_mul_of_nonneg_left hCommarm (by norm_num))
    _ = (2 * Cpost + 2 * Cfun 0) * Scol := by ring

private lemma norm_iteratedFDerivWithin_rawCompOnE_le_iteratedFDeriv_rawPullR
    (g : SmoothRiemannianMetric I M)
    (S : DifferentialGeometry.Integral.L2.SmoothCcTensor g 0 2) (α : M)
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) (m : ℕ) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    ‖iteratedFDerivWithin ℝ m
        (DeTurckCoefficients.rawCompOnE (I := I) (M := M) g S α Jdx)
        (interior (extChartAt I α).target) y‖ ≤
      ‖((toEuclidean (E := E)) : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖ ^ m *
        ‖iteratedFDeriv ℝ m (rawPullR (I := I) (M := M) g 0 2 S α
            (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx) ((toEuclidean (E := E)) y)‖ := by
  classical
  set e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := toEuclidean (E := E) with he_def
  set O : Set E := interior (extChartAt I α).target with hO_def
  have hO_open : IsOpen O := isOpen_interior
  have hUD : UniqueDiffOn ℝ O := hO_open.uniqueDiffOn
  
  have hcompose :
      DeTurckCoefficients.rawCompOnE (I := I) (M := M) g S α Jdx =
        rawPullR (I := I) (M := M) g 0 2 S α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx ∘ ⇑e := by
    have hpull := rawPullR_eq_rawCompOnE_comp (I := I) (M := M) g S α Jdx
    funext z
    have := congrArg (fun f => f (e z)) hpull
    simp only [Function.comp_apply, he_def, ContinuousLinearEquiv.symm_apply_apply] at this ⊢
    rw [← this]
  rw [hcompose]
  
  have himg_open : IsOpen (e '' O) := e.isOpenMap _ hO_open
  have hey_mem : e y ∈ e '' O := ⟨y, hy, rfl⟩
  have hOeq : O = e ⁻¹' (e '' O) := by
    ext z; constructor
    · intro hz; exact ⟨z, hz, rfl⟩
    · rintro ⟨w, hw, hwz⟩; rwa [e.injective hwz] at hw
  
  have hcomp := e.iteratedFDerivWithin_comp_right
    (f := rawPullR (I := I) (M := M) g 0 2 S α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx)
    himg_open.uniqueDiffOn (x := y) hey_mem m
  rw [← hOeq] at hcomp
  rw [hcomp]
  
  have hplain : iteratedFDerivWithin ℝ m
      (rawPullR (I := I) (M := M) g 0 2 S α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx)
      (e '' O) (e y) =
      iteratedFDeriv ℝ m
        (rawPullR (I := I) (M := M) g 0 2 S α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx) (e y) :=
    iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) m himg_open hey_mem
  rw [hplain]
  
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have he_norm : ‖(e : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖ =
      ‖((toEuclidean (E := E)) : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖ := rfl
  rw [he_norm, mul_comm]

private lemma bareChartJetContent_le_sqrt_fiberNormSq_sum_uniform
    (g : SmoothRiemannianMetric I M) (α : M) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (D : SmoothCcTensor g 0 2) {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))},
        y ∈ DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPouKernel (I := I) (M := M) α →
        bareChartJetContent (I := I) (M := M) g 0 2 D α N y ≤
          C * ∑ i ∈ Finset.range (N + 1),
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (2 + i)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
              ((iteratedCovGrad (I := I) g 0 2 i D).toSection
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  obtain ⟨Cpeel, hCpeel_nn, hCpeel⟩ :=
    DifferentialGeometry.PDE.RicciFlow.iteratedFDeriv_rawPullR_le_zeroContent_sum
      (I := I) (M := M) g 0 2 α N N (le_refl N)
  obtain ⟨Cfib0, hCfib0_nn, hCfib0⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_zeroContentR_le_fiberNorm_on_pouKernel
      (I := I) (M := M) g 0 2 α
  
  have h_fib : ∀ i : ℕ, ∃ Ci : ℝ, 0 ≤ Ci ∧
      ∀ (D : SmoothCcTensor g 0 2)
        {z : EuclideanSpace ℝ (Fin n)},
        z ∈ DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPouKernel (I := I) (M := M) α →
        zeroContentR (I := I) (M := M) g 0 (2 + i)
          (iteratedCovGrad (I := I) g 0 2 i D) α z ≤
          Ci * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (2 + i)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
            ((iteratedCovGrad (I := I) g 0 2 i D).toSection
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)))) := by
    intro i
    obtain ⟨Ci, hCi_nn, hCi⟩ :=
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_zeroContentR_le_fiberNorm_on_pouKernel
        (I := I) (M := M) g 0 (2 + i) α
    refine ⟨Ci, hCi_nn, fun D {z} hz => ?_⟩
    refine (hCi (iteratedCovGrad (I := I) g 0 2 i D) hz).trans ?_
    refine mul_le_mul_of_nonneg_left (le_of_eq ?_) hCi_nn
    letI : Bundle.RiemannianBundle (fun w : M => TensorRSSpace 0 (2 + i) I w) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 (2 + i)
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 (2 + i)
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
      ((iteratedCovGrad (I := I) g 0 2 i D).toSection
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)))]
    exact norm_eq_sqrt_tensorInnerPointwise (I := I) (M := M) g 0 (2 + i)
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
      ((iteratedCovGrad (I := I) g 0 2 i D).toSection
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)))
  choose Cfib hCfib_nn hCfib using h_fib
  set Cfibmax : ℝ := (Finset.range (N + 1)).sup' (by simp) Cfib with hCfibmax_def
  have hCfibmax_nn : 0 ≤ Cfibmax :=
    le_trans (hCfib_nn 0) (Finset.le_sup' Cfib (by simp))
  set Npair : ℝ := (Fintype.card ((Fin 0 → Fin n) × (Fin 2 → Fin n)) : ℝ) with hNpair_def
  have hNpair_nn : 0 ≤ Npair := by positivity
  refine ⟨Npair * (Cpeel * (((N : ℝ) + 1) * Cfibmax)), by positivity, ?_⟩
  intro D y hyK
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  set Fib : ℕ → ℝ := fun i => Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (2 + i) b
    ((iteratedCovGrad (I := I) g 0 2 i D).toSection b)) with hFib_def
  have hFib_nn : ∀ i, 0 ≤ Fib i := fun i => Real.sqrt_nonneg _
  set FibSum : ℝ := ∑ i ∈ Finset.range (N + 1), Fib i with hFibSum_def
  have hFibSum_nn : 0 ≤ FibSum := Finset.sum_nonneg fun i _ => hFib_nn i
  have hyK' : y ∈ DifferentialGeometry.Analysis.Sobolev.Chart.chartImagePOUTsupport
      (I := I) (M := M) α := hyK
  have h_zc : ∀ i ∈ Finset.range (N + 1),
      zeroContentR (I := I) (M := M) g 0 (2 + i)
        (iteratedCovGrad (I := I) g 0 2 i D) α y ≤ Cfibmax * Fib i := by
    intro i hi
    have hiN : i < N + 1 := Finset.mem_range.mp hi
    have hzc := hCfib i D hyK
    refine hzc.trans ?_
    rw [hFib_def, hb_def]
    exact mul_le_mul_of_nonneg_right
      (Finset.le_sup' Cfib (Finset.mem_range.mpr hiN)) (Real.sqrt_nonneg _)
  have h_each : ∀ q' : (Fin 0 → Fin n) × (Fin 2 → Fin n),
      (∑ m ∈ Finset.range (N + 1),
        ‖iteratedFDeriv ℝ m (rawPullR (I := I) (M := M) g 0 2 D α q'.1 q'.2) y‖) ≤
      (Cpeel * (((N : ℝ) + 1) * Cfibmax)) * FibSum := by
    intro q'
    have h_per : ∀ m ∈ Finset.range (N + 1),
        ‖iteratedFDeriv ℝ m (rawPullR (I := I) (M := M) g 0 2 D α q'.1 q'.2) y‖ ≤
          Cpeel * (Cfibmax * FibSum) := by
      intro m hm
      have hmN : m ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
      have hpeel := hCpeel D m hmN 0 (by omega) q'.1 q'.2 y hyK'
      have h0eq : (iteratedCovGrad (I := I) g 0 2 0 D) = D :=
        DifferentialGeometry.PDE.RicciFlow.iteratedCovGrad_zero (I := I) g 0 2 D
      rw [h0eq] at hpeel
      have hreindex : (∑ i ∈ Finset.range (m + 1),
            zeroContentR (I := I) (M := M) g 0 (2 + (0 + i))
              (iteratedCovGrad (I := I) g 0 2 (0 + i) D) α y) =
          ∑ i ∈ Finset.range (m + 1),
            zeroContentR (I := I) (M := M) g 0 (2 + i)
              (iteratedCovGrad (I := I) g 0 2 i D) α y := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        congr 1 <;> rw [Nat.zero_add]
      rw [hreindex] at hpeel
      refine hpeel.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hCpeel_nn
      calc (∑ i ∈ Finset.range (m + 1),
            zeroContentR (I := I) (M := M) g 0 (2 + i)
              (iteratedCovGrad (I := I) g 0 2 i D) α y)
          ≤ ∑ i ∈ Finset.range (m + 1), Cfibmax * Fib i :=
            Finset.sum_le_sum (fun i hi => h_zc i
              (Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi)
                (Nat.succ_le_succ hmN))))
        _ = Cfibmax * ∑ i ∈ Finset.range (m + 1), Fib i := by rw [Finset.mul_sum]
        _ ≤ Cfibmax * FibSum := by
            refine mul_le_mul_of_nonneg_left ?_ hCfibmax_nn
            rw [hFibSum_def]
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.range_mono (by omega)) (fun i _ _ => hFib_nn i)
    refine (Finset.sum_le_sum h_per).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  calc bareChartJetContent (I := I) (M := M) g 0 2 D α N y
      = ∑ q' : (Fin 0 → Fin n) × (Fin 2 → Fin n),
          ∑ m ∈ Finset.range (N + 1),
            ‖iteratedFDeriv ℝ m (rawPullR (I := I) (M := M) g 0 2 D α q'.1 q'.2) y‖ := rfl
    _ ≤ ∑ _q' : (Fin 0 → Fin n) × (Fin 2 → Fin n),
          (Cpeel * (((N : ℝ) + 1) * Cfibmax)) * FibSum :=
        Finset.sum_le_sum (fun q' _ => h_each q')
    _ = Npair * ((Cpeel * (((N : ℝ) + 1) * Cfibmax)) * FibSum) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hNpair_def]
    _ = (Npair * (Cpeel * (((N : ℝ) + 1) * Cfibmax))) * FibSum := by ring

private lemma tensorChartComponentRaw_toSection_congr
    (g g' : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (S' : SmoothCcTensor g' r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) (x : M)
    (hSS' : S.toSection x = S'.toSection x) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
        (I := I) (M := M) g r s S α Idx Jdx x =
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
          (I := I) (M := M) g' r s S' α Idx Jdx x := by
  unfold DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorTrivProj
  rw [hSS']

private lemma tensorChartComponentRaw_sub'
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) (x : M) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
        (I := I) (M := M) g r s (S₁ - S₂) α Idx Jdx x =
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
          (I := I) (M := M) g r s S₁ α Idx Jdx x -
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
          (I := I) (M := M) g r s S₂ α Idx Jdx x := by
  have hsub : S₁ - S₂ = S₁ + (-1 : ℝ) • S₂ := by
    rw [neg_one_smul]; abel
  rw [hsub,
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_add
      (I := I) (M := M) g r s S₁ ((-1 : ℝ) • S₂) α Idx Jdx x,
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_smul
      (I := I) (M := M) g r s (-1 : ℝ) S₂ α Idx Jdx x]
  rw [smul_eq_mul]; ring

private lemma deTurckRHSArm_toSection_eq
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ((deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
        deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') +
      rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T')).toSection =
      ((deTurckRHSSectionBg (I := I) g_bg
            (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)).toSection -
        (deTurckRHSSectionBg (I := I) g_bg
            (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ')).toSection) := by
  classical
  rw [SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_sub]
  rw [rawTensorConnLapSmooth_sub (I := I) g₀ 0 2 T T']
  
  change (((deTurckRHSSectionBg (I := I) g_bg
            (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)).toSection -
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T).toSection) -
      ((deTurckRHSSectionBg (I := I) g_bg
            (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ')).toSection -
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T').toSection)) +
      ((rawTensorConnLapSmooth (I := I) g₀ 0 2 T).toSection -
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T').toSection) =
      _
  abel

private lemma tensorChartComponentRaw_deTurckRHSArm_eq_chartDeTurckRicciRHS_diff
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (α : M) {b : M}
    (hb : b ∈ DifferentialGeometry.Integral.Connection.chartLeviCivitaGoodSet (I := I) α)
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
        (I := I) (M := M) g₀ 0 2
        ((deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
            deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') +
          rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T'))
        α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx b =
      DeTurckCoefficients.chartDeTurckRicciRHS (I := I)
          (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) g_bg α (Jdx 0) (Jdx 1)
          (extChartAt I α b) -
        DeTurckCoefficients.chartDeTurckRicciRHS (I := I)
          (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') g_bg α (Jdx 0) (Jdx 1)
          (extChartAt I α b) := by
  classical
  set g₁ := tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ with hg₁_def
  set g₂ := tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ' with hg₂_def
  set RHSarm : SmoothCcTensor g₀ 0 2 :=
    (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
        deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') +
      rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T') with hRHSarm_def
  set S₁ : SmoothCcTensor g₀ 0 2 :=
    { toSection := (deTurckRHSSectionBg (I := I) g_bg g₁).toSection
      hasCompactSupport := (deTurckRHSSectionBg (I := I) g_bg g₁).hasCompactSupport } with hS₁_def
  set S₂ : SmoothCcTensor g₀ 0 2 :=
    { toSection := (deTurckRHSSectionBg (I := I) g_bg g₂).toSection
      hasCompactSupport := (deTurckRHSSectionBg (I := I) g_bg g₂).hasCompactSupport } with hS₂_def
  
  have hsec : RHSarm.toSection = (S₁ - S₂).toSection := by
    rw [SmoothCcTensor.toSection_sub]
    exact deTurckRHSArm_toSection_eq (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
  have hRHSeq : RHSarm = S₁ - S₂ := by
    apply DifferentialGeometry.Integral.L2.SmoothCcTensor.ext
    exact hsec
  rw [hRHSeq]
  
  rw [tensorChartComponentRaw_sub' (I := I) (M := M) g₀ 0 2 S₁ S₂ α _ Jdx b]
  have hS₁comp : DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
        (I := I) (M := M) g₀ 0 2 S₁ α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx b =
      DeTurckCoefficients.chartDeTurckRicciRHS (I := I) g₁ g_bg α (Jdx 0) (Jdx 1)
        (extChartAt I α b) := by
    rw [tensorChartComponentRaw_toSection_congr (I := I) (M := M) g₀ g_bg 0 2 S₁
      (deTurckRHSSectionBg (I := I) g_bg g₁) α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx b rfl]
    rw [DeTurckCoefficients.chartDeTurckRicciRHS_def]
    rw [← DeTurckCoefficients.tensorChartComponentRaw_deTurckRHSSectionBg_eq_chartRicciLie
      (I := I) (M := M) g_bg g₁ α hb (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx]
  have hS₂comp : DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
        (I := I) (M := M) g₀ 0 2 S₂ α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx b =
      DeTurckCoefficients.chartDeTurckRicciRHS (I := I) g₂ g_bg α (Jdx 0) (Jdx 1)
        (extChartAt I α b) := by
    rw [tensorChartComponentRaw_toSection_congr (I := I) (M := M) g₀ g_bg 0 2 S₂
      (deTurckRHSSectionBg (I := I) g_bg g₂) α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx b rfl]
    rw [DeTurckCoefficients.chartDeTurckRicciRHS_def]
    rw [← DeTurckCoefficients.tensorChartComponentRaw_deTurckRHSSectionBg_eq_chartRicciLie
      (I := I) (M := M) g_bg g₂ α hb (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx]
  rw [hS₁comp, hS₂comp]

private def deTurckRHSArmG0 (g₀ g_bg : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ) :
    SmoothCcTensor g₀ 0 2 where
  toSection :=
    (deTurckRHSSection (I := I) g_bg
      (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)).toSection
  hasCompactSupport :=
    (deTurckRHSSection (I := I) g_bg
      (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)).hasCompactSupport

private theorem deTurckSmoothRemainder_eq_arm_sub_connLap
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ) :
    deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ =
      deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ -
        rawTensorConnLapSmooth (I := I) g₀ 0 2 T :=
  rfl

private theorem deTurckSmoothRemainderDiff_eq_armDiff_sub_connLapDiff
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
        deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ' =
      (deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ -
          deTurckRHSArmG0 (I := I) g₀ g_bg T' hδ'_lt hδ') -
        rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T') := by
  rw [deTurckSmoothRemainder_eq_arm_sub_connLap (I := I) g₀ g_bg T hδ_lt hδ,
    deTurckSmoothRemainder_eq_arm_sub_connLap (I := I) g₀ g_bg T' hδ'_lt hδ',
    rawTensorConnLapSmooth_sub (I := I) g₀ 0 2 T T']
  abel

private theorem l2RootSum_of_pointwise_iteratedCovGrad_jet
    (g₀ : SmoothRiemannianMetric I M) (q N : ℕ)
    (P W : SmoothCcTensor g₀ 0 2) (C : ℝ) (hC : 0 ≤ C)
    (hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
          ((iteratedCovGrad (I := I) g₀ 0 2 q P).toSection x) ≤
        C * ∑ i ∈ Finset.range (N + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i W).toSection x)) :
    ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ≤
      Real.sqrt C * Real.sqrt (∑ i ∈ Finset.range (N + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2) := by
  classical
  set μ := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ_def
  
  have hbridgeP : ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
        ((iteratedCovGrad (I := I) g₀ 0 2 q P).toSection x) ∂μ := by
    rw [SmoothCcTensor.norm_def (I := I) (M := M) (iteratedCovGrad (I := I) g₀ 0 2 q P), hμ_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ (2 + q)
      (iteratedCovGrad (I := I) g₀ 0 2 q P)
  have hbridgeW : ∀ i, ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 2 i W).toSection x) ∂μ := by
    intro i
    rw [SmoothCcTensor.norm_def (I := I) (M := M) (iteratedCovGrad (I := I) g₀ 0 2 i W), hμ_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ (2 + i)
      (iteratedCovGrad (I := I) g₀ 0 2 i W)
  
  have hintW : ∀ i, MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 2 i W).toSection x)) μ := by
    intro i; rw [hμ_def]
    exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (2 + i)
      (iteratedCovGrad (I := I) g₀ 0 2 i W)
  
  set Scol : ℝ := ∑ i ∈ Finset.range (N + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2
    with hScol_def
  have hScol_nn : 0 ≤ Scol := Finset.sum_nonneg fun i _ => sq_nonneg _
  
  set RHS : M → ℝ := fun x =>
    C * ∑ i ∈ Finset.range (N + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 2 i W).toSection x) with hRHS_def
  have hsum_int : MeasureTheory.Integrable
      (fun x => ∑ i ∈ Finset.range (N + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 2 i W).toSection x)) μ :=
    MeasureTheory.integrable_finset_sum (Finset.range (N + 1)) (fun i _ => hintW i)
  have hRHS_int : MeasureTheory.Integrable RHS μ := by
    rw [hRHS_def]; exact hsum_int.const_mul C
  have hP_nn_ae : (0 : M → ℝ) ≤ᵐ[μ]
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
        ((iteratedCovGrad (I := I) g₀ 0 2 q P).toSection x)) :=
    Filter.Eventually.of_forall (fun x =>
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + q) x _)
  
  have hint_le :
      (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
          ((iteratedCovGrad (I := I) g₀ 0 2 q P).toSection x) ∂μ) ≤
        ∫ x, RHS x ∂μ :=
    MeasureTheory.integral_mono_of_nonneg hP_nn_ae hRHS_int
      (Filter.Eventually.of_forall (fun x => by rw [hRHS_def]; exact hpt x))
  have hRHS_integral : (∫ x, RHS x ∂μ) = C * Scol := by
    rw [hRHS_def, MeasureTheory.integral_const_mul, hScol_def,
      MeasureTheory.integral_finset_sum (Finset.range (N + 1)) (fun i _ => hintW i)]
    refine congrArg (C * ·) (Finset.sum_congr rfl (fun i _ => (hbridgeW i).symm))
  
  have hsq : ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2 ≤ C * Scol := by
    rw [hbridgeP]; exact hint_le.trans_eq hRHS_integral
  
  have hPq_nn : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ := norm_nonneg _
  calc ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖
      = Real.sqrt (‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2) := (Real.sqrt_sq hPq_nn).symm
    _ ≤ Real.sqrt (C * Scol) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt C * Real.sqrt Scol := Real.sqrt_mul hC Scol

private theorem rawTensorConnLapSmooth_iteratedCovGrad_l2_tame
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (W : SmoothCcTensor g₀ 0 2) (q : ℕ), q ≤ a →
        ‖iteratedCovGrad (I := I) g₀ 0 2 q
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 W)‖ ≤
          C * Real.sqrt (∑ i ∈ Finset.range (a + 2 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2) := by
  classical
  
  choose Cfam hCfam_nn hCfam using
    (fun q : ℕ => rawTensorConnLapSmooth_iteratedCovGrad_riemannianFiberNormSq_jet_le
      (I := I) (M := M) g₀ q)
  set Cunif : ℝ := ∑ q ∈ Finset.range (a + 1), Cfam q with hCunif_def
  have hCunif_nn : 0 ≤ Cunif :=
    Finset.sum_nonneg fun q _ => hCfam_nn q
  refine ⟨Real.sqrt Cunif, Real.sqrt_nonneg _, fun W q hq => ?_⟩
  
  have hCfam_le_Cunif : Cfam q ≤ Cunif := by
    rw [hCunif_def]
    exact Finset.single_le_sum (f := Cfam) (fun i _ => hCfam_nn i)
      (Finset.mem_range.mpr (by omega))
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
          ((iteratedCovGrad (I := I) g₀ 0 2 q
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 W)).toSection x) ≤
        Cunif * ∑ i ∈ Finset.range (a + 2 + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i W).toSection x) := by
    intro x
    refine (hCfam q W x).trans ?_
    
    have hqle : q + 2 + 1 ≤ a + 2 + 1 := by omega
    have hwindow : (∑ i ∈ Finset.range (q + 2 + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i W).toSection x)) ≤
        ∑ i ∈ Finset.range (a + 2 + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i W).toSection x) :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono hqle)
        (fun i _ _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + i) x _)
    have hsum_nn : 0 ≤ ∑ i ∈ Finset.range (a + 2 + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 2 i W).toSection x) :=
      Finset.sum_nonneg fun i _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + i) x _
    calc Cfam q * ∑ i ∈ Finset.range (q + 2 + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 2 i W).toSection x)
        ≤ Cfam q * ∑ i ∈ Finset.range (a + 2 + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 2 i W).toSection x) :=
          mul_le_mul_of_nonneg_left hwindow (hCfam_nn q)
      _ ≤ Cunif * ∑ i ∈ Finset.range (a + 2 + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 2 i W).toSection x) :=
          mul_le_mul_of_nonneg_right hCfam_le_Cunif hsum_nn
  
  exact l2RootSum_of_pointwise_iteratedCovGrad_jet (I := I) g₀ q (a + 2)
    (rawTensorConnLapSmooth (I := I) g₀ 0 2 W) W Cunif hCunif_nn hpt

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

private theorem deTurckArmDiff_supercritical_pointwise_jet_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    ∃ Cemb : ℝ, 0 ≤ Cemb ∧
      ∀ (W : SmoothCcTensor g₀ 0 2) (x : M),
        (∑ q ∈ Finset.range 3,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
              ((iteratedCovGrad (I := I) g₀ 0 2 q W).toSection x)) ≤
          Cemb ^ 2 * ∑ i ∈ Finset.range (a + 2 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2 := by
  classical
  
  
  set k : ℕ := Module.finrank ℝ E / 2 + 3 with hk_def
  have hk_super : 2 * k > Module.finrank ℝ E + 4 := by rw [hk_def]; omega
  have h4k_le : 4 * k ≤ a + 2 := by rw [hk_def]; omega
  
  obtain ⟨Cc, hCc_pos, hCc⟩ :=
    iteratedCovGrad_toSobolev_embedding_C2_unconditional (I := I) (M := M) g₀ k hk_super
  obtain ⟨Ch, hCh_nn, hCh⟩ :=
    exists_toHs_norm_le_iteratedCovGrad_tensorL2Norm_sum (I := I) (M := M) g₀ 0 2 (2 * k)
  refine ⟨Real.sqrt (3 * Cc ^ 2 * Ch ^ 2 * ((4 * k + 1 : ℕ) : ℝ)), Real.sqrt_nonneg _,
    fun W x => ?_⟩
  set S : ℝ := ∑ i ∈ Finset.range (a + 2 + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2 with hS_def
  have hS_nn : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  
  set Mn : ℝ := ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
      (g := g₀) (r := 0) (s := 2) (2 * k) W‖ with hMn_def
  have hMn_nn : 0 ≤ Mn := norm_nonneg _
  have hCol := hCc W x
  
  have hHebey : Mn ≤ Ch * ∑ j ∈ Finset.range (2 * (2 * k) + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖ := by
    refine le_trans (hCh W) ?_
    refine mul_le_mul_of_nonneg_left ?_ hCh_nn
    refine le_of_eq (Finset.sum_congr rfl (fun j _ => ?_))
    exact (SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 2 j W)).symm
  
  
  set Jsum : ℝ := ∑ j ∈ Finset.range (2 * (2 * k) + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖ with hJsum_def
  have hJsum_nn : 0 ≤ Jsum := Finset.sum_nonneg fun j _ => norm_nonneg _
  have hwin : (2 * (2 * k) + 1) ≤ a + 2 + 1 := by omega
  have hcol_sq_le : (∑ j ∈ Finset.range (2 * (2 * k) + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖ ^ 2) ≤ S := by
    rw [hS_def]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hwin)
      (fun i _ _ => sq_nonneg _)
  have hJsq : Jsum ^ 2 ≤ ((4 * k + 1 : ℕ) : ℝ) * S := by
    have hcs : Jsum ^ 2 ≤
        ((2 * (2 * k) + 1 : ℕ) : ℝ) *
          ∑ j ∈ Finset.range (2 * (2 * k) + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖ ^ 2 := by
      rw [hJsum_def]
      have := sq_sum_le_card_mul_sum_sq (s := Finset.range (2 * (2 * k) + 1))
        (f := fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖)
      rw [Finset.card_range] at this
      exact_mod_cast this
    have hcard_eq : (2 * (2 * k) + 1 : ℕ) = (4 * k + 1 : ℕ) := by omega
    rw [hcard_eq] at hcs hcol_sq_le
    refine le_trans hcs ?_
    exact mul_le_mul_of_nonneg_left hcol_sq_le (by positivity)
  
  have hMn_sq : Mn ^ 2 ≤ Ch ^ 2 * (((4 * k + 1 : ℕ) : ℝ) * S) := by
    have hstep : Mn ^ 2 ≤ (Ch * Jsum) ^ 2 := pow_le_pow_left₀ hMn_nn hHebey 2
    calc Mn ^ 2 ≤ (Ch * Jsum) ^ 2 := hstep
      _ = Ch ^ 2 * Jsum ^ 2 := by ring
      _ ≤ Ch ^ 2 * (((4 * k + 1 : ℕ) : ℝ) * S) :=
          mul_le_mul_of_nonneg_left hJsq (by positivity)
  
  
  
  
  letI inst0 : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + 0) I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + 0)
  letI inst1 : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + 1) I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + 1)
  letI inst2 : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + 2) I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + 2)
  have hcolsq_le : (∑ q ∈ Finset.range 3,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
        ((iteratedCovGrad (I := I) g₀ 0 2 q W).toSection x)) ≤ 3 * (Cc * Mn) ^ 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add,
      riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g₀ 0 (2 + 0) x
        ((iteratedCovGrad (I := I) g₀ 0 2 0 W).toSection x),
      riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g₀ 0 (2 + 1) x
        ((iteratedCovGrad (I := I) g₀ 0 2 1 W).toSection x),
      riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g₀ 0 (2 + 2) x
        ((iteratedCovGrad (I := I) g₀ 0 2 2 W).toSection x)]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add] at hCol
    have h0 : 0 ≤ ‖(iteratedCovGrad (I := I) g₀ 0 2 0 W).toSection x‖ := norm_nonneg _
    have h1 : 0 ≤ ‖(iteratedCovGrad (I := I) g₀ 0 2 1 W).toSection x‖ := norm_nonneg _
    have h2 : 0 ≤ ‖(iteratedCovGrad (I := I) g₀ 0 2 2 W).toSection x‖ := norm_nonneg _
    nlinarith [hCol, h0, h1, h2, hMn_nn, hCc_pos.le, mul_nonneg hCc_pos.le hMn_nn]
  
  have hsqrt_sq : Real.sqrt (3 * Cc ^ 2 * Ch ^ 2 * ((4 * k + 1 : ℕ) : ℝ)) ^ 2 =
      3 * Cc ^ 2 * Ch ^ 2 * ((4 * k + 1 : ℕ) : ℝ) :=
    Real.sq_sqrt (by positivity)
  rw [hsqrt_sq]
  calc (∑ q ∈ Finset.range 3,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
            ((iteratedCovGrad (I := I) g₀ 0 2 q W).toSection x))
      ≤ 3 * (Cc * Mn) ^ 2 := hcolsq_le
    _ = 3 * Cc ^ 2 * Mn ^ 2 := by ring
    _ ≤ 3 * Cc ^ 2 * (Ch ^ 2 * (((4 * k + 1 : ℕ) : ℝ) * S)) :=
        mul_le_mul_of_nonneg_left hMn_sq (by positivity)
    _ = (3 * Cc ^ 2 * Ch ^ 2 * ((4 * k + 1 : ℕ) : ℝ)) * S := by ring

private lemma unitModel_sub_local (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S S' : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (S - S') x =
      unitModel (I := I) (M := M) g s S x - unitModel (I := I) (M := M) g s S' x := by
  rw [unitModel, unitModel, unitModel]
  have hsec : (S - S').toSection x = S.toSection x - S'.toSection x := by
    rw [SmoothCcTensor.toSection_sub]; rfl
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from (S - S').toSection x)
        (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S.toSection x)
          (unitTensor (I := I) (M := M) x) -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S'.toSection x)
          (unitTensor (I := I) (M := M) x) from by
    rw [hsec]; rfl]
  rw [Tensor0SSpace.toModel_sub]

private lemma unitModel_add_local (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S S' : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (S + S') x =
      unitModel (I := I) (M := M) g s S x + unitModel (I := I) (M := M) g s S' x := by
  rw [unitModel, unitModel, unitModel]
  have hsec : (S + S').toSection x = S.toSection x + S'.toSection x := by
    rw [SmoothCcTensor.toSection_add]; rfl
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from (S + S').toSection x)
        (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S.toSection x)
          (unitTensor (I := I) (M := M) x) +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S'.toSection x)
          (unitTensor (I := I) (M := M) x) from by
    rw [hsec]; rfl]
  rw [Tensor0SSpace.toModel_add]

private lemma threeArmCoeffSum_rfns_le (g₀ : SmoothRiemannianMetric I M) {r s : ℕ}
    (R L : SmoothCcTensor g₀ r s) (ΛR ΛL : ℝ) (x : M)
    (hR : riemannianFiberNormSq (I := I) (M := M) g₀ r s x (R.toSection x) ≤ ΛR ^ 2)
    (hL : riemannianFiberNormSq (I := I) (M := M) g₀ r s x (L.toSection x) ≤ ΛL ^ 2) :
    riemannianFiberNormSq (I := I) (M := M) g₀ r s x ((R + L).toSection x) ≤
      Real.sqrt (2 * ΛR ^ 2 + 2 * ΛL ^ 2) ^ 2 := by
  have hsqrt : Real.sqrt (2 * ΛR ^ 2 + 2 * ΛL ^ 2) ^ 2 = 2 * ΛR ^ 2 + 2 * ΛL ^ 2 := by
    refine Real.sq_sqrt ?_
    have := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ r s x (R.toSection x)
    have := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ r s x (L.toSection x)
    nlinarith [hR, hL]
  rw [hsqrt]
  have hsec : (R + L).toSection x = R.toSection x + L.toSection x := by
    rw [SmoothCcTensor.toSection_add]; rfl
  rw [hsec]
  have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ r s x
    (R.toSection x) (L.toSection x)
  nlinarith [hadd, hR, hL]

private theorem exists_ricciArmCoeff_ballUniform_C0_sup
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ ΛR : ℝ, 0 ≤ ΛR ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∃ (R₀ : SmoothCcTensor g₀ 2 2) (R₁ : SmoothCcTensor g₀ 3 2) (R₂ : SmoothCcTensor g₀ 4 2),
          (∀ (x : M) (v : Fin 2 → TangentSpace I x),
            ((-2 : ℝ) * ricciTensor (I := I)
                  (smoothRiemannianMetricToInfty (I := I)
                    (tensorSectionRealizeMetric (I := I) g₀ T (lt_of_le_of_lt hδ_le hδ₀) hδ)) x (v 0) (v 1)
                - (-2 : ℝ) * ricciTensor (I := I)
                    (smoothRiemannianMetricToInfty (I := I)
                      (tensorSectionRealizeMetric (I := I) g₀ T' (lt_of_le_of_lt hδ'_le hδ₀) hδ')) x (v 0) (v 1)) =
            unitModel (I := I) (M := M) g₀ 2
              (appCc (I := I) (M := M) g₀ 2 2 R₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
                appCc (I := I) (M := M) g₀ 3 2 R₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
                appCc (I := I) (M := M) g₀ 4 2 R₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (R₀.toSection x) ≤ ΛR ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x (R₁.toSection x) ≤ ΛR ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (R₂.toSection x) ≤ ΛR ^ 2) :=
  sorry

private theorem deTurckRicciArm_appCc_graded_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ ΛR : ℝ, 0 ≤ ΛR ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∃ (R₀ : SmoothCcTensor g₀ 2 2) (R₁ : SmoothCcTensor g₀ 3 2) (R₂ : SmoothCcTensor g₀ 4 2),
          (∀ (x : M) (v : Fin 2 → TangentSpace I x),
            (-2 : ℝ) •
                (ricciTensor (I := I)
                    (tensorSectionRealizeMetric (I := I) g₀ T (lt_of_le_of_lt hδ_le hδ₀) hδ) x (v 0) (v 1)
                  - ricciTensor (I := I)
                    (tensorSectionRealizeMetric (I := I) g₀ T' (lt_of_le_of_lt hδ'_le hδ₀) hδ') x (v 0) (v 1)) =
            unitModel (I := I) (M := M) g₀ 2
              (appCc (I := I) (M := M) g₀ 2 2 R₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
                appCc (I := I) (M := M) g₀ 3 2 R₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
                appCc (I := I) (M := M) g₀ 4 2 R₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (R₀.toSection x) ≤ ΛR ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x (R₁.toSection x) ≤ ΛR ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (R₂.toSection x) ≤ ΛR ^ 2) := by
  classical
  obtain ⟨ΛR, hΛR_nn, hsup⟩ :=
    exists_ricciArmCoeff_ballUniform_C0_sup (I := I) g₀ g_bg a ha_super hR hδ₀
  refine ⟨ΛR, hΛR_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball
  obtain ⟨R₀, R₁, R₂, hval, hR₀, hR₁, hR₂⟩ :=
    hsup T T' hδ_le hδ hδ'_le hδ' hTball hT'ball
  refine ⟨R₀, R₁, R₂, fun x v => ?_, hR₀, hR₁, hR₂⟩
  
  
  
  rw [smul_sub, smul_eq_mul, smul_eq_mul]
  exact hval x v

private theorem exists_lieArmCoeff_ballUniform_C0_sup
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ ΛL : ℝ, 0 ≤ ΛL ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∃ (L₀ : SmoothCcTensor g₀ 2 2) (L₁ : SmoothCcTensor g₀ 3 2) (L₂ : SmoothCcTensor g₀ 4 2),
          (∀ (x : M) (v : Fin 2 → TangentSpace I x),
            lieDerivMetricClm (I := I)
                  (tensorSectionRealizeMetric (I := I) g₀ T (lt_of_le_of_lt hδ_le hδ₀) hδ)
                  (deTurckVF (I := I)
                    (smoothRiemannianMetricToInfty (I := I)
                      (tensorSectionRealizeMetric (I := I) g₀ T (lt_of_le_of_lt hδ_le hδ₀) hδ))
                    (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1) -
                lieDerivMetricClm (I := I)
                  (tensorSectionRealizeMetric (I := I) g₀ T' (lt_of_le_of_lt hδ'_le hδ₀) hδ')
                  (deTurckVF (I := I)
                    (smoothRiemannianMetricToInfty (I := I)
                      (tensorSectionRealizeMetric (I := I) g₀ T' (lt_of_le_of_lt hδ'_le hδ₀) hδ'))
                    (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1) =
            unitModel (I := I) (M := M) g₀ 2
              (appCc (I := I) (M := M) g₀ 2 2 L₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
                appCc (I := I) (M := M) g₀ 3 2 L₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
                appCc (I := I) (M := M) g₀ 4 2 L₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (L₀.toSection x) ≤ ΛL ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x (L₁.toSection x) ≤ ΛL ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (L₂.toSection x) ≤ ΛL ^ 2) :=
  sorry

private theorem deTurckLieArm_appCc_graded_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ ΛL : ℝ, 0 ≤ ΛL ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∃ (L₀ : SmoothCcTensor g₀ 2 2) (L₁ : SmoothCcTensor g₀ 3 2) (L₂ : SmoothCcTensor g₀ 4 2),
          (∀ (x : M) (v : Fin 2 → TangentSpace I x),
            lieDerivMetricClm (I := I)
                  (tensorSectionRealizeMetric (I := I) g₀ T (lt_of_le_of_lt hδ_le hδ₀) hδ)
                  (deTurckVF (I := I)
                    (smoothRiemannianMetricToInfty (I := I)
                      (tensorSectionRealizeMetric (I := I) g₀ T (lt_of_le_of_lt hδ_le hδ₀) hδ))
                    (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1) -
                lieDerivMetricClm (I := I)
                  (tensorSectionRealizeMetric (I := I) g₀ T' (lt_of_le_of_lt hδ'_le hδ₀) hδ')
                  (deTurckVF (I := I)
                    (smoothRiemannianMetricToInfty (I := I)
                      (tensorSectionRealizeMetric (I := I) g₀ T' (lt_of_le_of_lt hδ'_le hδ₀) hδ'))
                    (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1) =
            unitModel (I := I) (M := M) g₀ 2
              (appCc (I := I) (M := M) g₀ 2 2 L₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
                appCc (I := I) (M := M) g₀ 3 2 L₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
                appCc (I := I) (M := M) g₀ 4 2 L₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (L₀.toSection x) ≤ ΛL ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x (L₁.toSection x) ≤ ΛL ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (L₂.toSection x) ≤ ΛL ^ 2) := by
  classical
  obtain ⟨ΛL, hΛL_nn, hsup⟩ :=
    exists_lieArmCoeff_ballUniform_C0_sup (I := I) g₀ g_bg a ha_super hR hδ₀
  refine ⟨ΛL, hΛL_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball
  obtain ⟨L₀, L₁, L₂, hval, hL₀, hL₁, hL₂⟩ :=
    hsup T T' hδ_le hδ hδ'_le hδ' hTball hT'ball
  exact ⟨L₀, L₁, L₂, hval, hL₀, hL₁, hL₂⟩

private theorem deTurckRHSArmDiff_threeArm_unitModel_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ ΛC : ℝ, 0 ≤ ΛC ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∃ (C₀ : SmoothCcTensor g₀ 2 2) (C₁ : SmoothCcTensor g₀ 3 2) (C₂ : SmoothCcTensor g₀ 4 2),
          (∀ (x : M) (v : Fin 2 → TangentSpace I x),
            unitModel (I := I) (M := M) g₀ 2
                (deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
                  deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ') x v =
            unitModel (I := I) (M := M) g₀ 2
              (appCc (I := I) (M := M) g₀ 2 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
                appCc (I := I) (M := M) g₀ 3 2 C₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
                appCc (I := I) (M := M) g₀ 4 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (C₀.toSection x) ≤ ΛC ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x (C₁.toSection x) ≤ ΛC ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (C₂.toSection x) ≤ ΛC ^ 2) := by
  classical
  
  
  
  obtain ⟨ΛR, hΛR_nn, hRicci⟩ :=
    deTurckRicciArm_appCc_graded_ballUniform (I := I) g₀ g_bg a ha_super hR hδ₀
  obtain ⟨ΛL, hΛL_nn, hLie⟩ :=
    deTurckLieArm_appCc_graded_ballUniform (I := I) g₀ g_bg a ha_super hR hδ₀
  
  
  refine ⟨Real.sqrt (2 * ΛR ^ 2 + 2 * ΛL ^ 2), Real.sqrt_nonneg _, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  obtain ⟨R₀, R₁, R₂, hRval, hR₀, hR₁, hR₂⟩ :=
    hRicci T T' hδ_le hδ hδ'_le hδ' hTball hT'ball
  obtain ⟨L₀, L₁, L₂, hLval, hL₀, hL₁, hL₂⟩ :=
    hLie T T' hδ_le hδ hδ'_le hδ' hTball hT'ball
  
  refine ⟨R₀ + L₀, R₁ + L₁, R₂ + L₂, ?_, ?_, ?_, ?_⟩
  · intro x v
    set g₁ := tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ with hg₁
    set g₁' := tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ' with hg₁'
    
    
    rw [unitModel_sub_local (I := I) g₀ 2 _ _ x, ContinuousMultilinearMap.sub_apply]
    rw [show (unitModel (I := I) (M := M) g₀ 2 (deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ) x) v =
          deTurckRicciRHS (I := I) g_bg g₁ x (v 0) (v 1) from
      unitModel_of_deTurckRHSSection_realize (I := I) g₀ g_bg T hδ_lt hδ
        (deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ) rfl x v]
    rw [show (unitModel (I := I) (M := M) g₀ 2 (deTurckRHSArmG0 (I := I) g₀ g_bg T' hδ'_lt hδ') x) v =
          deTurckRicciRHS (I := I) g_bg g₁' x (v 0) (v 1) from
      unitModel_of_deTurckRHSSection_realize (I := I) g₀ g_bg T' hδ'_lt hδ'
        (deTurckRHSArmG0 (I := I) g₀ g_bg T' hδ'_lt hδ') rfl x v]
    
    
    have hsplit : ∀ (g : SmoothRiemannianMetric I M),
        deTurckRicciRHS (I := I) g_bg g x (v 0) (v 1) =
          ((-2 : ℝ) • ricciTensor (I := I) g x (v 0) (v 1)) +
            lieDerivMetricClm (I := I) g
              (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g)
                (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1) := by
      intro g
      rw [deTurckRicciRHS, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply]
      rfl
    rw [hsplit g₁, hsplit g₁']
    
    rw [show ((-2 : ℝ) • ricciTensor (I := I) g₁ x (v 0) (v 1) +
            lieDerivMetricClm (I := I) g₁
              (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g₁)
                (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1)) -
          ((-2 : ℝ) • ricciTensor (I := I) g₁' x (v 0) (v 1) +
            lieDerivMetricClm (I := I) g₁'
              (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g₁')
                (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1)) =
        ((-2 : ℝ) • (ricciTensor (I := I) g₁ x (v 0) (v 1) -
            ricciTensor (I := I) g₁' x (v 0) (v 1))) +
          (lieDerivMetricClm (I := I) g₁
              (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g₁)
                (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1) -
            lieDerivMetricClm (I := I) g₁'
              (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g₁')
                (smoothRiemannianMetricToInfty (I := I) g_bg)) x (v 0) (v 1)) from by
      simp only [smul_sub]; ring]
    
    rw [hRval x v, hLval x v]
    
    
    
    set Rblk : SmoothCcTensor g₀ 0 2 :=
      appCc (I := I) (M := M) g₀ 2 2 R₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
        appCc (I := I) (M := M) g₀ 3 2 R₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
        appCc (I := I) (M := M) g₀ 4 2 R₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) with hRblk
    set Lblk : SmoothCcTensor g₀ 0 2 :=
      appCc (I := I) (M := M) g₀ 2 2 L₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
        appCc (I := I) (M := M) g₀ 3 2 L₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
        appCc (I := I) (M := M) g₀ 4 2 L₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) with hLblk
    have hcoeffSum :
        appCc (I := I) (M := M) g₀ 2 2 (R₀ + L₀) (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
          appCc (I := I) (M := M) g₀ 3 2 (R₁ + L₁) (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
          appCc (I := I) (M := M) g₀ 4 2 (R₂ + L₂) (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) =
        Rblk + Lblk := by
      rw [appCc_add_left (I := I) (M := M) g₀ 2 2 R₀ L₀,
        appCc_add_left (I := I) (M := M) g₀ 3 2 R₁ L₁,
        appCc_add_left (I := I) (M := M) g₀ 4 2 R₂ L₂, hRblk, hLblk]
      abel
    rw [hcoeffSum, unitModel_add_local (I := I) g₀ 2 Rblk Lblk x,
      ContinuousMultilinearMap.add_apply]
  · exact fun x => threeArmCoeffSum_rfns_le (I := I) g₀ R₀ L₀ ΛR ΛL x (hR₀ x) (hL₀ x)
  · exact fun x => threeArmCoeffSum_rfns_le (I := I) g₀ R₁ L₁ ΛR ΛL x (hR₁ x) (hL₁ x)
  · exact fun x => threeArmCoeffSum_rfns_le (I := I) g₀ R₂ L₂ ΛR ΛL x (hR₂ x) (hL₂ x)

private theorem deTurckRHSArmDiff_threeArm_coeffC0_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ ΛC : ℝ, 0 ≤ ΛC ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∃ (C₀ : SmoothCcTensor g₀ 2 2) (C₁ : SmoothCcTensor g₀ 3 2) (C₂ : SmoothCcTensor g₀ 4 2),
          (deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
              deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ') =
            (appCc (I := I) (M := M) g₀ 2 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
              appCc (I := I) (M := M) g₀ 3 2 C₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
              appCc (I := I) (M := M) g₀ 4 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (C₀.toSection x) ≤ ΛC ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x (C₁.toSection x) ≤ ΛC ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (C₂.toSection x) ≤ ΛC ^ 2) := by
  classical
  
  
  obtain ⟨ΛC, hΛC_nn, hgrade⟩ :=
    deTurckRHSArmDiff_threeArm_unitModel_ballUniform (I := I) g₀ g_bg a ha_super hR hδ₀
  refine ⟨ΛC, hΛC_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  obtain ⟨C₀, C₁, C₂, hval, hC₀, hC₁, hC₂⟩ :=
    hgrade T T' hδ_le hδ hδ'_le hδ' hTball hT'ball
  refine ⟨C₀, C₁, C₂, ?_, hC₀, hC₁, hC₂⟩
  
  
  apply smoothCcTensor_ext_of_unitModel
  intro x
  apply ContinuousMultilinearMap.ext
  intro v
  exact hval x v

set_option maxHeartbeats 800000 in

private theorem deTurckRHSArmDiff_order0_rfns_intrinsic_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λa : ℝ, 0 ≤ Λa ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
              ((deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
                  deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ').toSection x) ≤
            Λa ^ 2 * ∑ i ∈ Finset.range (a + 2 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 := by
  classical
  
  
  obtain ⟨ΛC, hΛC_nn, hcore⟩ :=
    deTurckRHSArmDiff_threeArm_coeffC0_ballUniform (I := I) g₀ g_bg a ha_super hR hδ₀
  
  
  obtain ⟨Cemb, hCemb_nn, hemb⟩ :=
    deTurckArmDiff_supercritical_pointwise_jet_le (I := I) g₀ a ha_super
  refine ⟨Real.sqrt (4 * 3) * (ΛC * Cemb), by positivity, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball x
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  obtain ⟨C₀, C₁, C₂, hid, hC₀, hC₁, hC₂⟩ :=
    hcore T T' hδ_le hδ hδ'_le hδ' hTball hT'ball
  set S : ℝ := ∑ i ∈ Finset.range (a + 2 + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 with hS_def
  have hS_nn : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  
  set A₀ := appCc (I := I) (M := M) g₀ 2 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) with hA₀
  set A₁ := appCc (I := I) (M := M) g₀ 3 2 C₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) with hA₁
  set A₂ := appCc (I := I) (M := M) g₀ 4 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) with hA₂
  
  set f : ℕ → ℝ := fun m =>
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
      ((iteratedCovGrad (I := I) g₀ 0 2 m (T - T')).toSection x) with hf_def
  have hf_nn : ∀ m, 0 ≤ f m := fun m =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + m) x _
  
  
  
  have h0 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (A₀.toSection x) ≤ ΛC ^ 2 * f 0 := by
    rw [hA₀, appCc_toSection (I := I) (M := M) g₀ 2 2 C₀
      (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) x]
    refine (riemannianFiberNormSq_comp_le_mul (I := I) (M := M) g₀ 2 2 x
      (C₀.toSection x) ((iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')).toSection x)).trans ?_
    exact mul_le_mul_of_nonneg_right (hC₀ x) (hf_nn 0)
  have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (A₁.toSection x) ≤ ΛC ^ 2 * f 1 := by
    rw [hA₁, appCc_toSection (I := I) (M := M) g₀ 3 2 C₁
      (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) x]
    refine (riemannianFiberNormSq_comp_le_mul (I := I) (M := M) g₀ 3 2 x
      (C₁.toSection x) ((iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')).toSection x)).trans ?_
    exact mul_le_mul_of_nonneg_right (hC₁ x) (hf_nn 1)
  have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (A₂.toSection x) ≤ ΛC ^ 2 * f 2 := by
    rw [hA₂, appCc_toSection (I := I) (M := M) g₀ 4 2 C₂
      (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) x]
    refine (riemannianFiberNormSq_comp_le_mul (I := I) (M := M) g₀ 4 2 x
      (C₂.toSection x) ((iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')).toSection x)).trans ?_
    exact mul_le_mul_of_nonneg_right (hC₂ x) (hf_nn 2)
  
  have hsub : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x ((A₀ + A₁ + A₂).toSection x) ≤
      4 * (riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (A₀.toSection x)
        + riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (A₁.toSection x)
        + riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (A₂.toSection x)) := by
    simp only [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
    have hadd1 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 2 x
      (A₀.toSection x + A₁.toSection x) (A₂.toSection x)
    have hadd2 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 2 x
      (A₀.toSection x) (A₁.toSection x)
    have h2nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 2 x (A₂.toSection x)
    nlinarith [hadd1, hadd2, h2nn]
  
  have hcol : f 0 + f 1 + f 2 ≤ Cemb ^ 2 * S := by
    have hemb' := hemb (T - T') x
    have hsum3 : (∑ q ∈ Finset.range 3,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
          ((iteratedCovGrad (I := I) g₀ 0 2 q (T - T')).toSection x)) = f 0 + f 1 + f 2 := by
      simp only [hf_def, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [hS_def]
    rw [hsum3] at hemb'
    exact hemb'
  
  have hΛsq : (Real.sqrt (4 * 3) * (ΛC * Cemb)) ^ 2 = (4 * 3) * (ΛC ^ 2 * Cemb ^ 2) := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4 * 3)]; ring
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          ((deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ -
              deTurckRHSArmG0 (I := I) g₀ g_bg T' hδ'_lt hδ').toSection x)
      = riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x ((A₀ + A₁ + A₂).toSection x) := by
        rw [hid]
    _ ≤ 4 * (riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (A₀.toSection x)
          + riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (A₁.toSection x)
          + riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (A₂.toSection x)) := hsub
    _ ≤ 4 * (ΛC ^ 2 * f 0 + ΛC ^ 2 * f 1 + ΛC ^ 2 * f 2) := by
        refine mul_le_mul_of_nonneg_left (add_le_add (add_le_add h0 h1) h2) (by norm_num)
    _ = (4 * ΛC ^ 2) * (f 0 + f 1 + f 2) := by ring
    _ ≤ (4 * ΛC ^ 2) * (Cemb ^ 2 * S) := by
        refine mul_le_mul_of_nonneg_left hcol (by positivity)
    _ ≤ (Real.sqrt (4 * 3) * (ΛC * Cemb)) ^ 2 * S := by
        rw [hΛsq]
        have : (4 * ΛC ^ 2) * (Cemb ^ 2 * S) ≤ ((4 * 3) * (ΛC ^ 2 * Cemb ^ 2)) * S := by
          nlinarith [hS_nn, sq_nonneg ΛC, sq_nonneg Cemb,
            mul_nonneg (sq_nonneg ΛC) (sq_nonneg Cemb)]
        linarith [this]

set_option linter.unusedSectionVars false in

private theorem mixed_continuous_rfns
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Integral.L2.SmoothCcTensor g r s) :
    Continuous (fun x => riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x)) := by
  have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M) S
  refine hc.congr (fun x => ?_)
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (S.toSection x),
    ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M) S x]

set_option linter.unusedSectionVars false in

private theorem mixed_real_holder_two_nonneg
    (g : SmoothRiemannianMetric I M) (φ ψ : M → ℝ)
    (hφc : Continuous φ) (hψc : Continuous ψ)
    (hφ0 : ∀ x, 0 ≤ φ x) (hψ0 : ∀ x, 0 ≤ ψ x)
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    ∫ x, φ x * ψ x ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
      (∫ x, φ x ^ p ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ^ (1 / p) *
      (∫ x, ψ x ^ q ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ^ (1 / q) := by
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  set μ : Measure M := riemannianVolumeMeasure (I := I) (M := M) g with hμ
  haveI : IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  have hp_pos : 0 < p := hpq.left_pos
  have hq_pos : 0 < q := hpq.right_pos
  have hφm : AEMeasurable (fun x => ENNReal.ofReal (φ x)) μ :=
    (hφc.measurable.ennreal_ofReal).aemeasurable
  have hψm : AEMeasurable (fun x => ENNReal.ofReal (ψ x)) μ :=
    (hψc.measurable.ennreal_ofReal).aemeasurable
  have hint_prod : Integrable (fun x => φ x * ψ x) μ :=
    (hφc.mul hψc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint_φp : Integrable (fun x => φ x ^ p) μ :=
    ((hφc.rpow_const (fun x => Or.inr hp_pos.le)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  have hint_ψq : Integrable (fun x => ψ x ^ q) μ :=
    ((hψc.rpow_const (fun x => Or.inr hq_pos.le)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  have hφp0 : ∀ x, 0 ≤ φ x ^ p := fun x => Real.rpow_nonneg (hφ0 x) _
  have hψq0 : ∀ x, 0 ≤ ψ x ^ q := fun x => Real.rpow_nonneg (hψ0 x) _
  have hIφp_nn : 0 ≤ ∫ x, φ x ^ p ∂μ := integral_nonneg hφp0
  have hIψq_nn : 0 ≤ ∫ x, ψ x ^ q ∂μ := integral_nonneg hψq0
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ := μ) hpq hφm hψm
  have hLHS_lint : (∫⁻ x, ((fun x => ENNReal.ofReal (φ x)) * (fun x => ENNReal.ofReal (ψ x))) x ∂μ)
      = ENNReal.ofReal (∫ x, φ x * ψ x ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint_prod
      (Eventually.of_forall (fun x => mul_nonneg (hφ0 x) (hψ0 x)))]
    refine lintegral_congr_ae (Eventually.of_forall (fun x => ?_))
    simp only [Pi.mul_apply]
    rw [ENNReal.ofReal_mul (hφ0 x)]
  have hφp_pt : ∀ x, (ENNReal.ofReal (φ x)) ^ p = ENNReal.ofReal (φ x ^ p) :=
    fun x => ENNReal.ofReal_rpow_of_nonneg (hφ0 x) hp_pos.le
  have hψq_pt : ∀ x, (ENNReal.ofReal (ψ x)) ^ q = ENNReal.ofReal (ψ x ^ q) :=
    fun x => ENNReal.ofReal_rpow_of_nonneg (hψ0 x) hq_pos.le
  have hφp_lint : (∫⁻ x, (ENNReal.ofReal (φ x)) ^ p ∂μ) = ENNReal.ofReal (∫ x, φ x ^ p ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint_φp (Eventually.of_forall hφp0)]
    exact lintegral_congr_ae (Eventually.of_forall hφp_pt)
  have hψq_lint : (∫⁻ x, (ENNReal.ofReal (ψ x)) ^ q ∂μ) = ENNReal.ofReal (∫ x, ψ x ^ q ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint_ψq (Eventually.of_forall hψq0)]
    exact lintegral_congr_ae (Eventually.of_forall hψq_pt)
  rw [hLHS_lint, hφp_lint, hψq_lint] at hHolder
  rw [ENNReal.ofReal_rpow_of_nonneg hIφp_nn (by positivity),
    ENNReal.ofReal_rpow_of_nonneg hIψq_nn (by positivity),
    ← ENNReal.ofReal_mul (by positivity)] at hHolder
  have hrhs_nn : 0 ≤ (∫ x, φ x ^ p ∂μ) ^ (1 / p) * (∫ x, ψ x ^ q ∂μ) ^ (1 / q) := by positivity
  exact (ENNReal.ofReal_le_ofReal_iff hrhs_nn).mp hHolder

set_option linter.unusedSectionVars false in

private theorem mixed_young_arm_split
    (wi wl CS CT ΛS ΛT NS NT Iφp Iψq : ℝ)
    (hwi_nn : 0 ≤ wi) (hwl_nn : 0 ≤ wl) (hwsum : wi + wl = 1)
    (hCS : 0 ≤ CS) (hCT : 0 ≤ CT) (hΛS : 0 ≤ ΛS) (hΛT : 0 ≤ ΛT)
    (hNS : 0 ≤ NS) (hNT : 0 ≤ NT) (_hIφp : 0 ≤ Iφp) (hIψq : 0 ≤ Iψq)
    (hS : Iφp ^ wi ≤ CS * ΛS ^ (2 * (1 - wi)) * NS ^ (2 * wi))
    (hT : Iψq ^ wl ≤ CT * ΛT ^ (2 * (1 - wl)) * NT ^ (2 * wl)) :
    Iφp ^ wi * Iψq ^ wl ≤
      CS * CT * (wi * (ΛT ^ 2 * NS ^ 2) + wl * (ΛS ^ 2 * NT ^ 2)) := by
  have hT_nn : 0 ≤ Iψq ^ wl := Real.rpow_nonneg hIψq _
  have hprod : Iφp ^ wi * Iψq ^ wl ≤
      (CS * ΛS ^ (2 * (1 - wi)) * NS ^ (2 * wi)) *
      (CT * ΛT ^ (2 * (1 - wl)) * NT ^ (2 * wl)) :=
    mul_le_mul hS hT hT_nn (by positivity)
  have h1wi : (1 : ℝ) - wi = wl := by rw [← hwsum]; ring
  have h1wl : (1 : ℝ) - wl = wi := by rw [← hwsum]; ring
  rw [h1wi, h1wl] at hprod
  have hsq_rpow : ∀ (b : ℝ), 0 ≤ b → ∀ w : ℝ, b ^ (2 * w) = (b ^ 2) ^ w := by
    intro b hb w
    rw [Real.rpow_mul hb 2 w, Real.rpow_two]
  have hregroup :
      (CS * ΛS ^ (2 * wl) * NS ^ (2 * wi)) * (CT * ΛT ^ (2 * wi) * NT ^ (2 * wl))
        = CS * CT * ((ΛT ^ 2 * NS ^ 2) ^ wi * (ΛS ^ 2 * NT ^ 2) ^ wl) := by
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity),
      hsq_rpow ΛS hΛS wl, hsq_rpow NS hNS wi, hsq_rpow ΛT hΛT wi, hsq_rpow NT hNT wl]
    ring
  rw [hregroup] at hprod
  have hyoung : (ΛT ^ 2 * NS ^ 2) ^ wi * (ΛS ^ 2 * NT ^ 2) ^ wl ≤
      wi * (ΛT ^ 2 * NS ^ 2) + wl * (ΛS ^ 2 * NT ^ 2) :=
    Real.geom_mean_le_arith_mean2_weighted hwi_nn hwl_nn (by positivity) (by positivity) hwsum
  calc Iφp ^ wi * Iψq ^ wl
      ≤ CS * CT * ((ΛT ^ 2 * NS ^ 2) ^ wi * (ΛS ^ 2 * NT ^ 2) ^ wl) := hprod
    _ ≤ CS * CT * (wi * (ΛT ^ 2 * NS ^ 2) + wl * (ΛS ^ 2 * NT ^ 2)) :=
        mul_le_mul_of_nonneg_left hyoung (by positivity)

open DifferentialGeometry.Analysis.Sobolev.Tensor in

private theorem appCc_integrated_grid_twoArm_mixed
    (g : SmoothRiemannianMetric I M) (r s₁ s₂ k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : Integral.L2.SmoothCcTensor g r s₁) (T : Integral.L2.SmoothCcTensor g 0 s₂)
        (ΛS ΛT : ℝ), 0 ≤ ΛS → 0 ≤ ΛT →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g r s₁ x (S.toSection x) ≤ ΛS ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 s₂ x (T.toSection x) ≤ ΛT ^ 2) →
        (∫ x, (∑ i ∈ Finset.range (k + 1),
            riemannianFiberNormSq (I := I) (M := M) g r (s₁ + i) x
                ((iteratedCovGrad (I := I) g r s₁ i S).toSection x)
              * ∑ l ∈ Finset.range (k + 1 - i),
                  riemannianFiberNormSq (I := I) (M := M) g 0 (s₂ + l) x
                    ((iteratedCovGrad (I := I) g 0 s₂ l T).toSection x))
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
          C * (ΛT ^ 2 * ∑ i ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g r s₁ i S‖ ^ 2
              + ΛS ^ 2 * ∑ l ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g 0 s₂ l T‖ ^ 2) := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  set CSf : ℕ → ℝ := fun m =>
    if h : 1 ≤ m then
      (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs (I := I) (M := M) g r s₁ m h).choose
    else 0 with hCSf
  set CTf : ℕ → ℝ := fun m =>
    if h : 1 ≤ m then
      (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs (I := I) (M := M) g 0 s₂ m h).choose
    else 0 with hCTf
  have hCSf_nn : ∀ m, 0 ≤ CSf m := by
    intro m; rw [hCSf]; dsimp only; split
    · rename_i h
      exact (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g r s₁ m h).choose_spec.1
    · exact le_refl 0
  have hCTf_nn : ∀ m, 0 ≤ CTf m := by
    intro m; rw [hCTf]; dsimp only; split
    · rename_i h
      exact (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g 0 s₂ m h).choose_spec.1
    · exact le_refl 0
  set Cbig : ℝ := 1 + ∑ m ∈ Finset.range (k + 1), CSf m * CTf m with hCbig
  have hCbig1 : (1 : ℝ) ≤ Cbig := by
    rw [hCbig]
    have : (0 : ℝ) ≤ ∑ m ∈ Finset.range (k + 1), CSf m * CTf m :=
      Finset.sum_nonneg (fun m _ => mul_nonneg (hCSf_nn m) (hCTf_nn m))
    linarith
  have hCbig_nn : (0 : ℝ) ≤ Cbig := le_trans zero_le_one hCbig1
  have hCSCT_le : ∀ m, m ≤ k → CSf m * CTf m ≤ Cbig := by
    intro m hm
    rw [hCbig]
    have hmem : m ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
    have hterm : CSf m * CTf m ≤ ∑ m' ∈ Finset.range (k + 1), CSf m' * CTf m' :=
      Finset.single_le_sum (fun m' _ => mul_nonneg (hCSf_nn m') (hCTf_nn m')) hmem
    linarith
  refine ⟨(k + 1) ^ 2 * Cbig, by positivity, ?_⟩
  intro S T ΛS ΛT hΛS hΛT hSsup hTsup
  set μ : Measure M := riemannianVolumeMeasure (I := I) (M := M) g with hμ
  set Sj : ℕ → M → ℝ := fun a x =>
    riemannianFiberNormSq (I := I) (M := M) g r (s₁ + a) x
      ((iteratedCovGrad (I := I) g r s₁ a S).toSection x) with hSj
  set Tj : ℕ → M → ℝ := fun b x =>
    riemannianFiberNormSq (I := I) (M := M) g 0 (s₂ + b) x
      ((iteratedCovGrad (I := I) g 0 s₂ b T).toSection x) with hTj
  have hSnorm : ∀ a, ∫ x, Sj a x ∂μ =
      ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2 := by
    intro a
    rw [hSj, hμ,
      ← (show Integral.L2.tensorL2Norm (I := I) (M := M) g r (s₁ + a)
            (iteratedCovGrad (I := I) g r s₁ a S).toFun ^ 2 =
          ∫ x, riemannianFiberNormSq (I := I) (M := M) g r (s₁ + a) x
            ((iteratedCovGrad (I := I) g r s₁ a S).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) from by
        have hfun : (iteratedCovGrad (I := I) g r s₁ a S).toFun =
            fun x => Tensor0SBundle.TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I)
              (M := M) (r := r) (s := s₁ + a) (x := x)
              ((iteratedCovGrad (I := I) g r s₁ a S).toSection x) := rfl
        rw [hfun]
        exact tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g r (s₁ + a) _),
      ← Integral.L2.SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g r s₁ a S)]
  have hTnorm : ∀ b, ∫ x, Tj b x ∂μ =
      ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2 := by
    intro b
    rw [hTj, hμ,
      ← (show Integral.L2.tensorL2Norm (I := I) (M := M) g 0 (s₂ + b)
            (iteratedCovGrad (I := I) g 0 s₂ b T).toFun ^ 2 =
          ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 (s₂ + b) x
            ((iteratedCovGrad (I := I) g 0 s₂ b T).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) from by
        have hfun : (iteratedCovGrad (I := I) g 0 s₂ b T).toFun =
            fun x => Tensor0SBundle.TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I)
              (M := M) (r := 0) (s := s₂ + b) (x := x)
              ((iteratedCovGrad (I := I) g 0 s₂ b T).toSection x) := rfl
        rw [hfun]
        exact tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g 0 (s₂ + b) _),
      ← Integral.L2.SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g 0 s₂ b T)]
  have hSj_cont : ∀ a, Continuous (Sj a) := fun a => by
    rw [hSj]; exact mixed_continuous_rfns g r (s₁ + a) _
  have hTj_cont : ∀ b, Continuous (Tj b) := fun b => by
    rw [hTj]; exact mixed_continuous_rfns g 0 (s₂ + b) _
  have hSj_nn : ∀ a x, 0 ≤ Sj a x := fun a x => by
    rw [hSj]; exact riemannianFiberNormSq_nonneg (I := I) (M := M) g r (s₁ + a) x _
  have hTj_nn : ∀ b x, 0 ≤ Tj b x := fun b x => by
    rw [hTj]; exact riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s₂ + b) x _
  have hSj_int : ∀ a, Integrable (Sj a) μ := fun a => by
    rw [hμ]; exact (hSj_cont a).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hTj_int : ∀ b, Integrable (Tj b) μ := fun b => by
    rw [hμ]; exact (hTj_cont b).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint_cell : ∀ a b, Integrable (fun x => Sj a x * Tj b x) μ := fun a b => by
    rw [hμ]
    exact ((hSj_cont a).mul (hTj_cont b)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hSsup0 : ∀ x, Sj 0 x ≤ ΛS ^ 2 := by
    intro x; rw [hSj]; dsimp only
    rw [iteratedCovGrad_zero (I := I) g r s₁ S]
    exact hSsup x
  have hTsup0 : ∀ x, Tj 0 x ≤ ΛT ^ 2 := by
    intro x; rw [hTj]; dsimp only
    rw [iteratedCovGrad_zero (I := I) g 0 s₂ T]
    exact hTsup x
  have hAS_nn : 0 ≤ ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
      ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2 := by positivity
  have hAT_nn : 0 ≤ ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
      ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2 := by positivity
  have hcell : ∀ i, i ≤ k → ∀ l, i + l ≤ k →
      ∫ x, Sj i x * Tj l x ∂μ ≤ Cbig *
        ((ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
            ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2)
          + (ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
            ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2)) := by
    intro i hik l hilk
    have hSi_in : ‖iteratedCovGrad (I := I) g r s₁ i S‖ ^ 2 ≤
        ∑ a ∈ Finset.range (k + 1),
          ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2 :=
      Finset.single_le_sum
        (f := fun a => ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2)
        (fun a _ => sq_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hik))
    have hTl_in : ‖iteratedCovGrad (I := I) g 0 s₂ l T‖ ^ 2 ≤
        ∑ b ∈ Finset.range (k + 1),
          ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2 :=
      Finset.single_le_sum
        (f := fun b => ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2)
        (fun b _ => sq_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le (by omega)))
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0
      have hbound : ∫ x, Sj 0 x * Tj l x ∂μ ≤ ΛS ^ 2 * ∫ x, Tj l x ∂μ := by
        rw [← integral_const_mul]
        refine integral_mono_of_nonneg (Eventually.of_forall (fun x => ?_)) ?_
          (Eventually.of_forall (fun x => ?_))
        · exact mul_nonneg (hSj_nn 0 x) (hTj_nn l x)
        · exact (hTj_int l).const_mul _
        · exact mul_le_mul_of_nonneg_right (hSsup0 x) (hTj_nn l x)
      rw [hTnorm l] at hbound
      calc ∫ x, Sj 0 x * Tj l x ∂μ
          ≤ ΛS ^ 2 * ‖iteratedCovGrad (I := I) g 0 s₂ l T‖ ^ 2 := hbound
        _ ≤ Cbig * (ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
              ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2) := by
              rw [← mul_assoc, mul_comm (Cbig) (ΛS ^ 2), mul_assoc]
              exact mul_le_mul_of_nonneg_left
                (le_trans hTl_in (le_mul_of_one_le_left (Finset.sum_nonneg
                  (fun b _ => sq_nonneg _)) hCbig1)) (by positivity)
        _ ≤ Cbig * ((ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
              ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2)
            + (ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
              ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2)) := by
              apply mul_le_mul_of_nonneg_left _ hCbig_nn
              linarith [hAS_nn]
    · rcases Nat.eq_zero_or_pos l with hl0 | hlpos
      · subst hl0
        have hbound : ∫ x, Sj i x * Tj 0 x ∂μ ≤ ΛT ^ 2 * ∫ x, Sj i x ∂μ := by
          rw [← integral_const_mul]
          refine integral_mono_of_nonneg (Eventually.of_forall (fun x => ?_)) ?_
            (Eventually.of_forall (fun x => ?_))
          · exact mul_nonneg (hSj_nn i x) (hTj_nn 0 x)
          · exact (hSj_int i).const_mul _
          · calc Sj i x * Tj 0 x
                ≤ Sj i x * ΛT ^ 2 := mul_le_mul_of_nonneg_left (hTsup0 x) (hSj_nn i x)
              _ = ΛT ^ 2 * Sj i x := mul_comm _ _
        rw [hSnorm i] at hbound
        calc ∫ x, Sj i x * Tj 0 x ∂μ
            ≤ ΛT ^ 2 * ‖iteratedCovGrad (I := I) g r s₁ i S‖ ^ 2 := hbound
          _ ≤ Cbig * (ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2) := by
                rw [← mul_assoc, mul_comm (Cbig) (ΛT ^ 2), mul_assoc]
                exact mul_le_mul_of_nonneg_left
                  (le_trans hSi_in (le_mul_of_one_le_left (Finset.sum_nonneg
                    (fun a _ => sq_nonneg _)) hCbig1)) (by positivity)
          _ ≤ Cbig * ((ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2)
              + (ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2)) := by
                apply mul_le_mul_of_nonneg_left _ hCbig_nn
                linarith [hAT_nn]
      · set m : ℕ := i + l with hm
        have hmk : m ≤ k := by rw [hm]; exact hilk
        have hm1 : 1 ≤ m := by omega
        have hmi : i < m := by omega
        have hml : l < m := by omega
        have hm_posR : 0 < (m : ℝ) := by positivity
        set wi : ℝ := (i : ℝ) / m with hwi
        set wl : ℝ := (l : ℝ) / m with hwl
        have hwi_nn : 0 ≤ wi := by rw [hwi]; positivity
        have hwl_nn : 0 ≤ wl := by rw [hwl]; positivity
        have hwsum : wi + wl = 1 := by
          rw [hwi, hwl, ← add_div, show (i : ℝ) + l = (m : ℝ) by push_cast [hm]; ring]
          exact div_self (ne_of_gt hm_posR)
        have hi_posR : 0 < (i : ℝ) := by exact_mod_cast hipos
        have hl_posR : 0 < (l : ℝ) := by exact_mod_cast hlpos
        set p : ℝ := (m : ℝ) / i with hp
        set q : ℝ := (m : ℝ) / l with hq
        have hp_one : 1 < p := by rw [hp, lt_div_iff₀ hi_posR, one_mul]; exact_mod_cast hmi
        have hpq : p.HolderConjugate q := by
          rw [Real.holderConjugate_iff]
          refine ⟨hp_one, ?_⟩
          rw [hp, hq, inv_div, inv_div, ← add_div,
            show (i : ℝ) + l = (m : ℝ) by push_cast [hm]; ring]
          exact div_self (ne_of_gt hm_posR)
        have hHolder := mixed_real_holder_two_nonneg g (Sj i) (Tj l)
          (hSj_cont i) (hTj_cont l) (hSj_nn i) (hTj_nn l) hpq
        have h1p : (1 : ℝ) / p = wi := by rw [hp, one_div_div, hwi]
        have h1q : (1 : ℝ) / q = wl := by rw [hq, one_div_div, hwl]
        rw [h1p, h1q] at hHolder
        have hSe := (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
          (I := I) (M := M) g r s₁ m hm1).choose_spec.2 S ΛS hΛS hSsup i hipos hmi
        have hTe := (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
          (I := I) (M := M) g 0 s₂ m hm1).choose_spec.2 T ΛT hΛT hTsup l hlpos hml
        have hCSf_m : (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
            (I := I) (M := M) g r s₁ m hm1).choose = CSf m := by
          simp only [hCSf, dif_pos hm1]
        have hCTf_m : (exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
            (I := I) (M := M) g 0 s₂ m hm1).choose = CTf m := by
          simp only [hCTf, dif_pos hm1]
        rw [hCSf_m] at hSe
        rw [hCTf_m] at hTe
        rw [mul_div_assoc 2 (i : ℝ) m, ← hwi] at hSe
        rw [mul_div_assoc 2 (l : ℝ) m, ← hwl] at hTe
        rw [show Integral.L2.tensorL2Norm (I := I) g r (s₁ + m)
              (iteratedCovGrad (I := I) g r s₁ m S).toFun =
              ‖iteratedCovGrad (I := I) g r s₁ m S‖ from
            (Integral.L2.SmoothCcTensor.norm_def
              (iteratedCovGrad (I := I) g r s₁ m S)).symm] at hSe
        rw [show Integral.L2.tensorL2Norm (I := I) g 0 (s₂ + m)
              (iteratedCovGrad (I := I) g 0 s₂ m T).toFun =
              ‖iteratedCovGrad (I := I) g 0 s₂ m T‖ from
            (Integral.L2.SmoothCcTensor.norm_def
              (iteratedCovGrad (I := I) g 0 s₂ m T)).symm] at hTe
        set Iφp : ℝ := ∫ x, Sj i x ^ p ∂μ with hIφp
        set Iψq : ℝ := ∫ x, Tj l x ^ q ∂μ with hIψq
        have hIφp_nn : 0 ≤ Iφp := by
          rw [hIφp]; exact integral_nonneg (fun x => Real.rpow_nonneg (hSj_nn i x) _)
        have hIψq_nn : 0 ≤ Iψq := by
          rw [hIψq]; exact integral_nonneg (fun x => Real.rpow_nonneg (hTj_nn l x) _)
        have hys := mixed_young_arm_split wi wl (CSf m) (CTf m) ΛS ΛT
          ‖iteratedCovGrad (I := I) g r s₁ m S‖
          ‖iteratedCovGrad (I := I) g 0 s₂ m T‖
          Iφp Iψq hwi_nn hwl_nn hwsum (hCSf_nn m) (hCTf_nn m) hΛS hΛT
          (norm_nonneg _) (norm_nonneg _) hIφp_nn hIψq_nn hSe hTe
        have hNS_sum : ‖iteratedCovGrad (I := I) g r s₁ m S‖ ^ 2 ≤
            ∑ a ∈ Finset.range (k + 1),
              ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2 :=
          Finset.single_le_sum
            (f := fun a => ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2)
            (fun a _ => sq_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hmk))
        have hNT_sum : ‖iteratedCovGrad (I := I) g 0 s₂ m T‖ ^ 2 ≤
            ∑ b ∈ Finset.range (k + 1),
              ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2 :=
          Finset.single_le_sum
            (f := fun b => ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2)
            (fun b _ => sq_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hmk))
        have hwi_le1 : wi ≤ 1 := by rw [← hwsum]; linarith
        have hwl_le1 : wl ≤ 1 := by rw [← hwsum]; linarith
        calc ∫ x, Sj i x * Tj l x ∂μ
            ≤ Iφp ^ wi * Iψq ^ wl := hHolder
          _ ≤ CSf m * CTf m * (wi * (ΛT ^ 2 *
                ‖iteratedCovGrad (I := I) g r s₁ m S‖ ^ 2)
              + wl * (ΛS ^ 2 *
                ‖iteratedCovGrad (I := I) g 0 s₂ m T‖ ^ 2)) := hys
          _ ≤ Cbig * ((ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2)
              + (ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2)) := by
              refine le_trans (mul_le_mul_of_nonneg_right (hCSCT_le m hmk) ?_) ?_
              · have : 0 ≤ wi * (ΛT ^ 2 *
                    ‖iteratedCovGrad (I := I) g r s₁ m S‖ ^ 2)
                  + wl * (ΛS ^ 2 *
                    ‖iteratedCovGrad (I := I) g 0 s₂ m T‖ ^ 2) := by positivity
                exact this
              · refine mul_le_mul_of_nonneg_left ?_ hCbig_nn
                have harm1 : wi * (ΛT ^ 2 *
                    ‖iteratedCovGrad (I := I) g r s₁ m S‖ ^ 2) ≤
                    ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
                      ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2 := by
                  calc wi * (ΛT ^ 2 *
                        ‖iteratedCovGrad (I := I) g r s₁ m S‖ ^ 2)
                      ≤ 1 * (ΛT ^ 2 *
                        ‖iteratedCovGrad (I := I) g r s₁ m S‖ ^ 2) :=
                        mul_le_mul_of_nonneg_right hwi_le1 (by positivity)
                    _ = ΛT ^ 2 *
                        ‖iteratedCovGrad (I := I) g r s₁ m S‖ ^ 2 := one_mul _
                    _ ≤ ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
                          ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2 :=
                        mul_le_mul_of_nonneg_left hNS_sum (by positivity)
                have harm2 : wl * (ΛS ^ 2 *
                    ‖iteratedCovGrad (I := I) g 0 s₂ m T‖ ^ 2) ≤
                    ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
                      ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2 := by
                  calc wl * (ΛS ^ 2 *
                        ‖iteratedCovGrad (I := I) g 0 s₂ m T‖ ^ 2)
                      ≤ 1 * (ΛS ^ 2 *
                        ‖iteratedCovGrad (I := I) g 0 s₂ m T‖ ^ 2) :=
                        mul_le_mul_of_nonneg_right hwl_le1 (by positivity)
                    _ = ΛS ^ 2 *
                        ‖iteratedCovGrad (I := I) g 0 s₂ m T‖ ^ 2 := one_mul _
                    _ ≤ ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
                          ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2 :=
                        mul_le_mul_of_nonneg_left hNT_sum (by positivity)
                linarith
  have hrw : (∫ x, ∑ i ∈ Finset.range (k + 1), Sj i x *
        ∑ l ∈ Finset.range (k + 1 - i), Tj l x ∂μ)
      = ∑ i ∈ Finset.range (k + 1), ∑ l ∈ Finset.range (k + 1 - i),
          ∫ x, Sj i x * Tj l x ∂μ := by
    rw [MeasureTheory.integral_finset_sum _
      (fun i _ => by
        rw [hμ]
        exact ((hSj_cont i).mul (continuous_finset_sum _
          (fun l _ => hTj_cont l))).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show (∫ x, Sj i x * ∑ l ∈ Finset.range (k + 1 - i), Tj l x ∂μ)
          = ∫ x, ∑ l ∈ Finset.range (k + 1 - i), Sj i x * Tj l x ∂μ from by
        simp only [Finset.mul_sum],
      MeasureTheory.integral_finset_sum _ (fun l _ => hint_cell i l)]
  rw [hrw]
  have hsum_le : ∑ i ∈ Finset.range (k + 1), ∑ l ∈ Finset.range (k + 1 - i),
        ∫ x, Sj i x * Tj l x ∂μ ≤
      ∑ i ∈ Finset.range (k + 1), ∑ l ∈ Finset.range (k + 1 - i),
        Cbig * ((ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
            ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2)
          + (ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
            ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2)) := by
    refine Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun l hl => ?_))
    have hik : i ≤ k := by rw [Finset.mem_range] at hi; omega
    have hilk : i + l ≤ k := by
      rw [Finset.mem_range] at hi hl; omega
    exact hcell i hik l hilk
  refine le_trans hsum_le ?_
  set c : ℝ := Cbig * ((ΛT ^ 2 * ∑ a ∈ Finset.range (k + 1),
      ‖iteratedCovGrad (I := I) g r s₁ a S‖ ^ 2)
    + (ΛS ^ 2 * ∑ b ∈ Finset.range (k + 1),
      ‖iteratedCovGrad (I := I) g 0 s₂ b T‖ ^ 2)) with hc
  have hc_nn : 0 ≤ c := by
    rw [hc]; exact mul_nonneg hCbig_nn (by linarith [hAS_nn, hAT_nn])
  have hinner : ∀ i ∈ Finset.range (k + 1),
      (∑ _l ∈ Finset.range (k + 1 - i), c) ≤ (k + 1 : ℝ) * c := by
    intro i _
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le (k + 1) i) hc_nn
  have hdouble : (∑ i ∈ Finset.range (k + 1), ∑ _l ∈ Finset.range (k + 1 - i), c)
      ≤ (k + 1 : ℝ) * ((k + 1 : ℝ) * c) := by
    calc (∑ i ∈ Finset.range (k + 1), ∑ _l ∈ Finset.range (k + 1 - i), c)
        ≤ ∑ _i ∈ Finset.range (k + 1), (k + 1 : ℝ) * c := Finset.sum_le_sum hinner
      _ = (k + 1 : ℝ) * ((k + 1 : ℝ) * c) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]; push_cast; ring
  refine le_trans hdouble (le_of_eq ?_)
  rw [hc]
  ring

private theorem appCc_topOrder_l2_twoArm_mixed_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (b₀ s₀ k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g₀ b₀ s₀) (W : SmoothCcTensor g₀ 0 b₀) (ΛΦ ΛW : ℝ),
        0 ≤ ΛΦ → 0 ≤ ΛW →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ b₀ s₀ x (Φ.toSection x) ≤ ΛΦ ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 b₀ x (W.toSection x) ≤ ΛW ^ 2) →
        ‖iteratedCovGrad (I := I) g₀ 0 s₀ k
            (appCc (I := I) (M := M) g₀ b₀ s₀ Φ W)‖ ^ 2 ≤
          C * (ΛW ^ 2 * ∑ i ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ‖ ^ 2
              + ΛΦ ^ 2 * ∑ l ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ^ 2) := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  
  obtain ⟨Cgrid, hCgrid_nn, hCgrid⟩ :=
    appCc_integrated_grid_twoArm_mixed (I := I) g₀ b₀ s₀ b₀ k
  
  set Gk : ℝ := appCcGdiag (E := E) k with hGk
  have hGk_nn : 0 ≤ Gk := appCcGdiag_nonneg (E := E) k
  refine ⟨Gk * Cgrid, by positivity, ?_⟩
  intro Φ W ΛΦ ΛW hΛΦ hΛW hΦsup hWsup
  set μ : Measure M := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ
  set P : SmoothCcTensor g₀ 0 s₀ := appCc (I := I) (M := M) g₀ b₀ s₀ Φ W with hP
  
  have hLHS_eq : ‖iteratedCovGrad (I := I) g₀ 0 s₀ k P‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₀ + k) x
        ((iteratedCovGrad (I := I) g₀ 0 s₀ k P).toSection x) ∂μ := by
    rw [hμ, Integral.L2.SmoothCcTensor.norm_def
        (iteratedCovGrad (I := I) g₀ 0 s₀ k P)]
    have hfun : (iteratedCovGrad (I := I) g₀ 0 s₀ k P).toFun =
        fun x => Tensor0SBundle.TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I)
          (M := M) (r := 0) (s := s₀ + k) (x := x)
          ((iteratedCovGrad (I := I) g₀ 0 s₀ k P).toSection x) := rfl
    rw [hfun]
    exact tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₀ + k) _
  
  set grid : M → ℝ := fun x => ∑ i ∈ Finset.range (k + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ b₀ (s₀ + i) x
          ((iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ).toSection x)
        * ∑ l ∈ Finset.range (k + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (b₀ + l) x
              ((iteratedCovGrad (I := I) g₀ 0 b₀ l W).toSection x) with hgrid
  
  have hptwise : ∀ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₀ + k) x
        ((iteratedCovGrad (I := I) g₀ 0 s₀ k P).toSection x) ≤ Gk * grid x := by
    intro x
    rw [hGk, hgrid, hP]
    exact appCc_iteratedCovGrad_diagonalProductGrid_le (I := I) g₀ b₀ s₀ Φ W k x
  
  have hgrid_cont : Continuous grid := by
    rw [hgrid]
    refine continuous_finset_sum _ (fun i _ => (mixed_continuous_rfns g₀ b₀ (s₀ + i) _).mul ?_)
    exact continuous_finset_sum _ (fun l _ => mixed_continuous_rfns g₀ 0 (b₀ + l) _)
  have hgrid_int : Integrable grid μ := by
    rw [hμ]; exact hgrid_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  
  have hmono : ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₀ + k) x
        ((iteratedCovGrad (I := I) g₀ 0 s₀ k P).toSection x) ∂μ ≤
      Gk * ∫ x, grid x ∂μ := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall (fun x =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (s₀ + k) x _)) ?_
      (Eventually.of_forall hptwise)
    exact hgrid_int.const_mul _
  
  have hgrid_bound := hCgrid Φ W ΛΦ ΛW hΛΦ hΛW hΦsup hWsup
  rw [hLHS_eq]
  calc ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s₀ + k) x
        ((iteratedCovGrad (I := I) g₀ 0 s₀ k P).toSection x) ∂μ
      ≤ Gk * ∫ x, grid x ∂μ := hmono
    _ ≤ Gk * (Cgrid * (ΛW ^ 2 * ∑ i ∈ Finset.range (k + 1),
            ‖iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ‖ ^ 2
          + ΛΦ ^ 2 * ∑ l ∈ Finset.range (k + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ hGk_nn
        rw [hgrid]; exact hgrid_bound
    _ = Gk * Cgrid * (ΛW ^ 2 * ∑ i ∈ Finset.range (k + 1),
            ‖iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ‖ ^ 2
          + ΛΦ ^ 2 * ∑ l ∈ Finset.range (k + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ^ 2) := by ring

private theorem deTurckRHSArmDiff_threeArm_coeffC0_jetL2_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ ΛC Γ : ℝ, 0 ≤ ΛC ∧ 0 ≤ Γ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∃ (C₀ : SmoothCcTensor g₀ 2 2) (C₁ : SmoothCcTensor g₀ 3 2) (C₂ : SmoothCcTensor g₀ 4 2),
          (deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
              deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ') =
            (appCc (I := I) (M := M) g₀ 2 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
              appCc (I := I) (M := M) g₀ 3 2 C₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
              appCc (I := I) (M := M) g₀ 4 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (C₀.toSection x) ≤ ΛC ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x (C₁.toSection x) ≤ ΛC ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (C₂.toSection x) ≤ ΛC ^ 2) ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i C₀‖ ^ 2) ≤ Γ ^ 2 ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 3 2 i C₁‖ ^ 2) ≤ Γ ^ 2 ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i C₂‖ ^ 2) ≤ Γ ^ 2 :=
  sorry

private theorem deTurckRHSArmDiff_topOrder_l2_intrinsic_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λc : ℝ, 0 ≤ Λc ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ‖iteratedCovGrad (I := I) g₀ 0 2 a
            (deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
              deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ')‖ ≤
          Λc * Real.sqrt (∑ i ∈ Finset.range (a + 2 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) := by
  classical
  
  
  
  
  
  
  obtain ⟨ΛC, Γ, hΛC_nn, hΓ_nn, hcoeff⟩ :=
    deTurckRHSArmDiff_threeArm_coeffC0_jetL2_ballUniform (I := I) g₀ g_bg a ha_super hR hδ₀
  
  obtain ⟨K₀, hK₀_nn, hK₀⟩ := appCc_topOrder_l2_twoArm_mixed_ballUniform (I := I) g₀ 2 2 a
  obtain ⟨K₁, hK₁_nn, hK₁⟩ := appCc_topOrder_l2_twoArm_mixed_ballUniform (I := I) g₀ 3 2 a
  obtain ⟨K₂, hK₂_nn, hK₂⟩ := appCc_topOrder_l2_twoArm_mixed_ballUniform (I := I) g₀ 4 2 a
  
  obtain ⟨Cemb, hCemb_nn, hemb⟩ :=
    deTurckArmDiff_supercritical_pointwise_jet_le (I := I) g₀ a ha_super
  
  
  
  
  set Kmax : ℝ := max K₀ (max K₁ K₂) with hKmax_def
  have hKmax_nn : 0 ≤ Kmax := le_trans hK₀_nn (le_max_left _ _)
  have hK₀_le : K₀ ≤ Kmax := le_max_left _ _
  have hK₁_le : K₁ ≤ Kmax := le_trans (le_max_left _ _) (le_max_right _ _)
  have hK₂_le : K₂ ≤ Kmax := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨Real.sqrt (9 * (Kmax * (Cemb ^ 2 * Γ ^ 2 + ΛC ^ 2))), Real.sqrt_nonneg _, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  set S : ℝ := ∑ i ∈ Finset.range (a + 2 + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 with hS_def
  have hS_nn : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  
  obtain ⟨C₀, C₁, C₂, hid, hC₀sup, hC₁sup, hC₂sup, hC₀jet, hC₁jet, hC₂jet⟩ :=
    hcoeff T T' hδ_le hδ hδ'_le hδ' hTball hT'ball
  
  
  have hWsup : ∀ (m : ℕ), m ≤ 2 → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 m (T - T')).toSection x) ≤
        (Real.sqrt (Cemb ^ 2 * S)) ^ 2 := by
    intro m hm x
    rw [Real.sq_sqrt (by positivity)]
    have hembx := hemb (T - T') x
    rw [hS_def]
    have hmem : m ∈ Finset.range 3 := Finset.mem_range.mpr (by omega)
    refine le_trans (Finset.single_le_sum
      (f := fun q => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
        ((iteratedCovGrad (I := I) g₀ 0 2 q (T - T')).toSection x))
      (fun q _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + q) x _) hmem) ?_
    exact hembx
  
  have hWjet : ∀ (m : ℕ), m ≤ 2 →
      (∑ l ∈ Finset.range (a + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
          (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2) ≤ S := by
    intro m hm
    
    have hcomp : ∀ l : ℕ,
        ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
            (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2 =
          ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) (T - T')‖ ^ 2 := by
      intro l
      have hbridgeL : ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
            (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2 =
          ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l
              (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
        rw [SmoothCcTensor.norm_def]
        exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ ((2 + m) + l)
          (iteratedCovGrad (I := I) g₀ 0 (2 + m) l (iteratedCovGrad (I := I) g₀ 0 2 m (T - T')))
      have hbridgeR : ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) (T - T')‖ ^ 2 =
          ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (m + l)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (m + l) (T - T')).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
        rw [SmoothCcTensor.norm_def]
        exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ (2 + (m + l))
          (iteratedCovGrad (I := I) g₀ 0 2 (m + l) (T - T'))
      rw [hbridgeL, hbridgeR]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      have hrw := rfns_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 2 m l (T - T') x
      
      simpa only [Nat.add_assoc] using hrw
    
    rw [show (∑ l ∈ Finset.range (a + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
            (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2) =
        ∑ l ∈ Finset.range (a + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) (T - T')‖ ^ 2 from
      Finset.sum_congr rfl (fun l _ => hcomp l)]
    rw [hS_def]
    
    set f : ℕ → ℝ := fun i => ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 with hf_def
    have hf_nn : ∀ i, 0 ≤ f i := fun i => sq_nonneg _
    have himg : (Finset.range (a + 1)).image (fun l => m + l) ⊆ Finset.range (a + 2 + 1) := by
      intro i hi
      rw [Finset.mem_image] at hi
      obtain ⟨l, hl, rfl⟩ := hi
      rw [Finset.mem_range] at hl ⊢
      omega
    have hinj : ∀ l₁ ∈ Finset.range (a + 1), ∀ l₂ ∈ Finset.range (a + 1),
        m + l₁ = m + l₂ → l₁ = l₂ := fun l₁ _ l₂ _ h => by omega
    calc (∑ l ∈ Finset.range (a + 1), f (m + l))
        = ∑ i ∈ (Finset.range (a + 1)).image (fun l => m + l), f i :=
          (Finset.sum_image hinj).symm
      _ ≤ ∑ i ∈ Finset.range (a + 2 + 1), f i :=
          Finset.sum_le_sum_of_subset_of_nonneg himg (fun i _ _ => hf_nn i)
  
  have harm : ∀ (m : ℕ) (hm : m ≤ 2) (Cm : SmoothCcTensor g₀ (2 + m) 2) (Km : ℝ)
      (hKm_le : Km ≤ Kmax)
      (hKm : ∀ (Φ : SmoothCcTensor g₀ (2 + m) 2) (W : SmoothCcTensor g₀ 0 (2 + m)) (ΛΦ ΛW : ℝ),
        0 ≤ ΛΦ → 0 ≤ ΛW →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) 2 x (Φ.toSection x) ≤ ΛΦ ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x (W.toSection x) ≤ ΛW ^ 2) →
        ‖iteratedCovGrad (I := I) g₀ 0 2 a (appCc (I := I) (M := M) g₀ (2 + m) 2 Φ W)‖ ^ 2 ≤
          Km * (ΛW ^ 2 * ∑ i ∈ Finset.range (a + 1),
                ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Φ‖ ^ 2
              + ΛΦ ^ 2 * ∑ l ∈ Finset.range (a + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖ ^ 2))
      (hCmsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) 2 x (Cm.toSection x) ≤ ΛC ^ 2)
      (hCmjet : (∑ i ∈ Finset.range (a + 1),
          ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2) ≤ Γ ^ 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 a
          (appCc (I := I) (M := M) g₀ (2 + m) 2 Cm
            (iteratedCovGrad (I := I) g₀ 0 2 m (T - T')))‖ ^ 2 ≤
        Kmax * (Cemb ^ 2 * Γ ^ 2 + ΛC ^ 2) * S := by
    intro m hm Cm Km hKm_le hKm hCmsup hCmjet
    have htame := hKm Cm (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))
      ΛC (Real.sqrt (Cemb ^ 2 * S)) hΛC_nn (Real.sqrt_nonneg _) hCmsup (hWsup m hm)
    refine htame.trans ?_
    
    have hcoeffjet := hCmjet
    have hwjet := hWjet m hm
    have hΛWsq : (Real.sqrt (Cemb ^ 2 * S)) ^ 2 = Cemb ^ 2 * S := Real.sq_sqrt (by positivity)
    rw [hΛWsq]
    
    have hcjsum_nn : 0 ≤ ∑ i ∈ Finset.range (a + 1),
        ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    have hwjsum_nn : 0 ≤ ∑ l ∈ Finset.range (a + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
          (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2 :=
      Finset.sum_nonneg fun l _ => sq_nonneg _
    have ha1 : (Cemb ^ 2 * S) * ∑ i ∈ Finset.range (a + 1),
          ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2 ≤ (Cemb ^ 2 * S) * Γ ^ 2 :=
      mul_le_mul_of_nonneg_left hcoeffjet (by positivity)
    have ha2 : ΛC ^ 2 * ∑ l ∈ Finset.range (a + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
            (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2 ≤ ΛC ^ 2 * S :=
      mul_le_mul_of_nonneg_left hwjet (sq_nonneg _)
    have hinner :
        (Cemb ^ 2 * S) * ∑ i ∈ Finset.range (a + 1),
            ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2
          + ΛC ^ 2 * ∑ l ∈ Finset.range (a + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
              (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2
        ≤ Cemb ^ 2 * Γ ^ 2 * S + ΛC ^ 2 * S := by nlinarith [ha1, ha2]
    have hinner_nn : 0 ≤ (Cemb ^ 2 * S) * ∑ i ∈ Finset.range (a + 1),
            ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2
          + ΛC ^ 2 * ∑ l ∈ Finset.range (a + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
              (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2 := by
      have : 0 ≤ (Cemb ^ 2 * S) := by positivity
      have : 0 ≤ ΛC ^ 2 := sq_nonneg _
      positivity
    calc Km * ((Cemb ^ 2 * S) * ∑ i ∈ Finset.range (a + 1),
              ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2
            + ΛC ^ 2 * ∑ l ∈ Finset.range (a + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
                (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2)
        ≤ Kmax * (Cemb ^ 2 * Γ ^ 2 * S + ΛC ^ 2 * S) :=
          mul_le_mul hKm_le hinner hinner_nn hKmax_nn
      _ = Kmax * (Cemb ^ 2 * Γ ^ 2 + ΛC ^ 2) * S := by ring
  
  have ha0 := harm 0 (by norm_num) C₀ K₀ hK₀_le hK₀ hC₀sup hC₀jet
  have ha1 := harm 1 (by norm_num) C₁ K₁ hK₁_le hK₁ hC₁sup hC₁jet
  have ha2 := harm 2 (by norm_num) C₂ K₂ hK₂_le hK₂ hC₂sup hC₂jet
  
  set A₀ := appCc (I := I) (M := M) g₀ 2 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) with hA₀
  set A₁ := appCc (I := I) (M := M) g₀ 3 2 C₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) with hA₁
  set A₂ := appCc (I := I) (M := M) g₀ 4 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) with hA₂
  have hN_split : deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ -
      deTurckRHSArmG0 (I := I) g₀ g_bg T' hδ'_lt hδ' = A₀ + A₁ + A₂ := by
    rw [hA₀, hA₁, hA₂]; exact hid
  set base : ℝ := Kmax * (Cemb ^ 2 * Γ ^ 2 + ΛC ^ 2) with hbase_def
  have hbase_nn : 0 ≤ base := by rw [hbase_def]; positivity
  
  have hnorm0 : ‖iteratedCovGrad (I := I) g₀ 0 2 a A₀‖ ≤ Real.sqrt (base * S) := by
    rw [show ‖iteratedCovGrad (I := I) g₀ 0 2 a A₀‖ =
        Real.sqrt (‖iteratedCovGrad (I := I) g₀ 0 2 a A₀‖ ^ 2) from
      (Real.sqrt_sq (norm_nonneg _)).symm]
    exact Real.sqrt_le_sqrt (by rw [hbase_def]; exact ha0)
  have hnorm1 : ‖iteratedCovGrad (I := I) g₀ 0 2 a A₁‖ ≤ Real.sqrt (base * S) := by
    rw [show ‖iteratedCovGrad (I := I) g₀ 0 2 a A₁‖ =
        Real.sqrt (‖iteratedCovGrad (I := I) g₀ 0 2 a A₁‖ ^ 2) from
      (Real.sqrt_sq (norm_nonneg _)).symm]
    exact Real.sqrt_le_sqrt (by rw [hbase_def]; exact ha1)
  have hnorm2 : ‖iteratedCovGrad (I := I) g₀ 0 2 a A₂‖ ≤ Real.sqrt (base * S) := by
    rw [show ‖iteratedCovGrad (I := I) g₀ 0 2 a A₂‖ =
        Real.sqrt (‖iteratedCovGrad (I := I) g₀ 0 2 a A₂‖ ^ 2) from
      (Real.sqrt_sq (norm_nonneg _)).symm]
    exact Real.sqrt_le_sqrt (by rw [hbase_def]; exact ha2)
  
  rw [hN_split, iteratedCovGrad_add (I := I) g₀ 0 2 a (A₀ + A₁) A₂,
    iteratedCovGrad_add (I := I) g₀ 0 2 a A₀ A₁]
  have htri : ‖iteratedCovGrad (I := I) g₀ 0 2 a A₀ +
        iteratedCovGrad (I := I) g₀ 0 2 a A₁ +
        iteratedCovGrad (I := I) g₀ 0 2 a A₂‖ ≤
      Real.sqrt (base * S) + Real.sqrt (base * S) + Real.sqrt (base * S) := by
    refine le_trans (norm_add_le _ _) ?_
    refine add_le_add (le_trans (norm_add_le _ _) (add_le_add hnorm0 hnorm1)) hnorm2
  refine htri.trans ?_
  
  rw [show Real.sqrt (base * S) = Real.sqrt base * Real.sqrt S from Real.sqrt_mul hbase_nn S]
  rw [show Real.sqrt (9 * base) = Real.sqrt 9 * Real.sqrt base from Real.sqrt_mul (by norm_num) base]
  rw [show Real.sqrt (9 : ℝ) = 3 from by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact le_of_eq (by ring)

private theorem deTurckRHSArmDiff_endpoints_l2_tame_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ₀ : ℝ, 0 ≤ Λ₀ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
                ((deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
                    deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ').toSection x) ≤
              Λ₀ ^ 2 * ∑ i ∈ Finset.range (a + 2 + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) ∧
          ‖deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
              deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ'‖ ≤
            Λ₀ * Real.sqrt (∑ i ∈ Finset.range (a + 2 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) ∧
          ‖iteratedCovGrad (I := I) g₀ 0 2 a
              (deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
                deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ')‖ ≤
            Λ₀ * Real.sqrt (∑ i ∈ Finset.range (a + 2 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) := by
  classical
  
  
  
  obtain ⟨Λa, hΛa_nn, hΛa⟩ :=
    deTurckRHSArmDiff_order0_rfns_intrinsic_ballUniform (I := I) g₀ g_bg a ha_super hR hδ₀
  obtain ⟨Λc, hΛc_nn, hΛc⟩ :=
    deTurckRHSArmDiff_topOrder_l2_intrinsic_ballUniform (I := I) g₀ g_bg a ha_super hR hδ₀
  
  
  haveI : MeasureTheory.IsFiniteMeasure
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g₀
  set vol : ℝ := (riemannianVolumeMeasure (I := I) (M := M) g₀).real Set.univ with hvol_def
  have hvol_nn : 0 ≤ vol := by rw [hvol_def]; exact MeasureTheory.measureReal_nonneg
  
  refine ⟨Λa * Real.sqrt (vol + 1) + Λc,
    by positivity, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  set N : SmoothCcTensor g₀ 0 2 :=
    deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ -
      deTurckRHSArmG0 (I := I) g₀ g_bg T' hδ'_lt hδ' with hN_def
  set S : ℝ := ∑ i ∈ Finset.range (a + 2 + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 with hS_def
  have hS_nn : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsqrtS_nn : 0 ≤ Real.sqrt S := Real.sqrt_nonneg _
  set Λ₀ : ℝ := Λa * Real.sqrt (vol + 1) + Λc with hΛ₀_def
  have hΛ₀_nn : 0 ≤ Λ₀ := by rw [hΛ₀_def]; positivity
  
  have hsqrt_ge_one : (1 : ℝ) ≤ Real.sqrt (vol + 1) :=
    Real.one_le_sqrt.mpr (by linarith)
  have hΛa_le : Λa ≤ Λ₀ := by
    rw [hΛ₀_def]
    have h1 : Λa ≤ Λa * Real.sqrt (vol + 1) := by
      nlinarith [hΛa_nn, hsqrt_ge_one]
    linarith [hΛc_nn]
  have hΛc_le : Λc ≤ Λ₀ := by rw [hΛ₀_def]; nlinarith [hΛa_nn, hsqrt_ge_one]
  
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (N.toSection x) ≤ Λa ^ 2 * S := by
    intro x
    rw [hN_def, hS_def]
    exact hΛa T T' hδ_le hδ hδ'_le hδ' hTball hT'ball x
  have hC0 : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (N.toSection x) ≤ Λ₀ ^ 2 * S := by
    intro x
    refine (hpt x).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ hS_nn
    exact pow_le_pow_left₀ hΛa_nn hΛa_le 2
  
  
  have hL0 : ‖N‖ ≤ Λ₀ * Real.sqrt S := by
    
    have hnormsq : ‖N‖ ^ 2 ≤ vol * (Λa ^ 2 * S) := by
      rw [SmoothCcTensor.norm_def,
        tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ 2 N]
      have hint_le :
          (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (N.toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            ∫ _x, Λa ^ 2 * S ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
        refine MeasureTheory.integral_mono_of_nonneg ?_ (MeasureTheory.integrable_const _) ?_
        · exact MeasureTheory.ae_of_all _ fun x =>
            riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 2 x _
        · exact MeasureTheory.ae_of_all _ fun x => hpt x
      rw [MeasureTheory.integral_const, smul_eq_mul, ← hvol_def] at hint_le
      exact hint_le
    
    have hnorm_nn : 0 ≤ ‖N‖ := norm_nonneg _
    have hrhs_nn : 0 ≤ vol * (Λa ^ 2 * S) := by positivity
    have hsqrt_le : ‖N‖ ≤ Real.sqrt (vol * (Λa ^ 2 * S)) := by
      rw [show ‖N‖ = Real.sqrt (‖N‖ ^ 2) from (Real.sqrt_sq hnorm_nn).symm]
      exact Real.sqrt_le_sqrt hnormsq
    refine hsqrt_le.trans ?_
    
    have hfac : Real.sqrt (vol * (Λa ^ 2 * S)) = Λa * (Real.sqrt vol * Real.sqrt S) := by
      rw [show vol * (Λa ^ 2 * S) = Λa ^ 2 * (vol * S) by ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hΛa_nn,
        Real.sqrt_mul hvol_nn]
    rw [hfac, hΛ₀_def, add_mul]
    have hvol_le : Real.sqrt vol ≤ Real.sqrt (vol + 1) :=
      Real.sqrt_le_sqrt (by linarith)
    calc Λa * (Real.sqrt vol * Real.sqrt S)
        = (Λa * Real.sqrt vol) * Real.sqrt S := by ring
      _ ≤ (Λa * Real.sqrt (vol + 1)) * Real.sqrt S := by
          refine mul_le_mul_of_nonneg_right ?_ hsqrtS_nn
          exact mul_le_mul_of_nonneg_left hvol_le hΛa_nn
      _ ≤ Λa * Real.sqrt (vol + 1) * Real.sqrt S + Λc * Real.sqrt S := by
          have : 0 ≤ Λc * Real.sqrt S := mul_nonneg hΛc_nn hsqrtS_nn
          linarith
  
  have hLa : ‖iteratedCovGrad (I := I) g₀ 0 2 a N‖ ≤ Λ₀ * Real.sqrt S := by
    have hbase : ‖iteratedCovGrad (I := I) g₀ 0 2 a N‖ ≤ Λc * Real.sqrt S := by
      rw [hN_def, hS_def]
      exact hΛc T T' hδ_le hδ hδ'_le hδ' hTball hT'ball
    refine hbase.trans ?_
    exact mul_le_mul_of_nonneg_right hΛc_le hsqrtS_nn
  exact ⟨hC0, hL0, hLa⟩

private theorem deTurckRHSArmDiff_iteratedCovGrad_l2_tame_ballUniform
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
              (deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
                deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ')‖ ≤
            C * Real.sqrt (∑ i ∈ Finset.range (a + 2 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) := by
  classical
  
  obtain ⟨Λ₀, hΛ₀_nn, hEnd⟩ :=
    deTurckRHSArmDiff_endpoints_l2_tame_ballUniform (I := I) g₀ g_bg a ha_super hR hδ₀
  
  rcases Nat.eq_zero_or_pos a with ha0 | hapos
  · subst ha0
    refine ⟨Λ₀, hΛ₀_nn, ?_⟩
    intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball q hq
    obtain rfl : q = 0 := Nat.le_zero.mp hq
    have hEnd' := hEnd T T' hδ_le hδ hδ'_le hδ' hTball hT'ball
    simpa using hEnd'.2.1
  · obtain ⟨Cgn, hCgn_nn, hGN⟩ :=
      DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_l2Norm_le
        (I := I) (M := M) g₀ 2 a hapos
    refine ⟨(Cgn + 1) * (Λ₀ + 1), by positivity, ?_⟩
    intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball q hq
    have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
    have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
    set N : SmoothCcTensor g₀ 0 2 :=
      deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ -
        deTurckRHSArmG0 (I := I) g₀ g_bg T' hδ'_lt hδ' with hN_def
    set S : ℝ := ∑ i ∈ Finset.range (a + 2 + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 with hS_def
    have hS_nn : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hsqrtS_nn : 0 ≤ Real.sqrt S := Real.sqrt_nonneg _
    obtain ⟨hC0, hL0, hLa⟩ := hEnd T T' hδ_le hδ hδ'_le hδ' hTball hT'ball
    
    have hC0' : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (N.toSection x) ≤
        (Λ₀ * Real.sqrt S) ^ 2 := by
      intro x
      have hx := hC0 x
      rw [mul_pow, Real.sq_sqrt hS_nn]
      exact hx
    have hL0' : ‖N‖ ≤ Λ₀ * Real.sqrt S := by rw [hN_def, hS_def]; exact hL0
    have hLa' : ‖iteratedCovGrad (I := I) g₀ 0 2 a N‖ ≤ Λ₀ * Real.sqrt S := by
      rw [hN_def, hS_def]; exact hLa
    
    have hN_norm_nn : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 a N‖ := norm_nonneg _
    have hΛ₀S_nn : 0 ≤ Λ₀ * Real.sqrt S := mul_nonneg hΛ₀_nn hsqrtS_nn
    
    suffices hgoal : ‖iteratedCovGrad (I := I) g₀ 0 2 q N‖ ≤
        ((Cgn + 1) * (Λ₀ + 1)) * Real.sqrt S by
      rw [hN_def, hS_def] at hgoal; exact hgoal
    rcases Nat.eq_zero_or_pos q with hq0 | hqpos
    · subst hq0
      have h0 : ‖iteratedCovGrad (I := I) g₀ 0 2 0 N‖ = ‖N‖ := by simp
      rw [h0]
      refine hL0'.trans ?_
      refine mul_le_mul_of_nonneg_right ?_ hsqrtS_nn
      nlinarith [hCgn_nn, hΛ₀_nn]
    · rcases lt_or_eq_of_le hq with hqlt | hqeq
      · have hGNq := hGN N (Λ₀ * Real.sqrt S) hΛ₀S_nn hC0' q hqpos hqlt
        
        set e : ℝ := (q : ℝ) / a with he_def
        have he_nn : 0 ≤ e := by
          rw [he_def]; positivity
        have he_lt_one : e < 1 := by
          rw [he_def]
          rw [div_lt_one (by exact_mod_cast hapos)]
          exact_mod_cast hqlt
        have h1me_nn : 0 ≤ 1 - e := by linarith
        
        have hak_mono : (‖iteratedCovGrad (I := I) g₀ 0 2 a N‖) ^ e ≤
            (Λ₀ * Real.sqrt S) ^ e :=
          Real.rpow_le_rpow hN_norm_nn hLa' he_nn
        
        have hrhs_eq : Cgn * (Λ₀ * Real.sqrt S) ^ (1 - e) * (Λ₀ * Real.sqrt S) ^ e =
            Cgn * (Λ₀ * Real.sqrt S) := by
          rcases eq_or_lt_of_le hΛ₀S_nn with hzero | hpos
          · rw [← hzero, Real.zero_rpow (ne_of_gt (by linarith [he_lt_one] : (0 : ℝ) < 1 - e))]
            simp
          · rw [mul_assoc, ← Real.rpow_add hpos, sub_add_cancel, Real.rpow_one]
        calc ‖iteratedCovGrad (I := I) g₀ 0 2 q N‖
            ≤ Cgn * (Λ₀ * Real.sqrt S) ^ (1 - e) *
                (‖iteratedCovGrad (I := I) g₀ 0 2 a N‖) ^ e := by
              simpa only [he_def] using hGNq
          _ ≤ Cgn * (Λ₀ * Real.sqrt S) ^ (1 - e) * (Λ₀ * Real.sqrt S) ^ e := by
              refine mul_le_mul_of_nonneg_left hak_mono ?_
              exact mul_nonneg hCgn_nn (Real.rpow_nonneg hΛ₀S_nn _)
          _ = Cgn * (Λ₀ * Real.sqrt S) := hrhs_eq
          _ = (Cgn * Λ₀) * Real.sqrt S := by ring
          _ ≤ ((Cgn + 1) * (Λ₀ + 1)) * Real.sqrt S := by
              refine mul_le_mul_of_nonneg_right ?_ hsqrtS_nn
              nlinarith [hCgn_nn, hΛ₀_nn]
      · subst hqeq
        refine hLa'.trans ?_
        refine mul_le_mul_of_nonneg_right ?_ hsqrtS_nn
        nlinarith [hCgn_nn, hΛ₀_nn]

private theorem deTurckSmoothRemainderDiff_iteratedCovGrad_l2_tame_ballUniform
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
            C * Real.sqrt (∑ i ∈ Finset.range (a + 2 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) := by
  classical
  
  obtain ⟨Cn, hCn_nn, hCn⟩ :=
    deTurckRHSArmDiff_iteratedCovGrad_l2_tame_ballUniform (I := I) g₀ g_bg a ha_super hR hδ₀
  
  obtain ⟨Cl, hCl_nn, hCl⟩ :=
    rawTensorConnLapSmooth_iteratedCovGrad_l2_tame (I := I) g₀ a
  refine ⟨Cn + Cl, by positivity, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball q hq
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  
  set S : ℝ := ∑ i ∈ Finset.range (a + 2 + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 with hS_def
  have hS_nn : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsqrtS_nn : 0 ≤ Real.sqrt S := Real.sqrt_nonneg _
  
  set N : SmoothCcTensor g₀ 0 2 :=
    deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ -
      deTurckRHSArmG0 (I := I) g₀ g_bg T' hδ'_lt hδ' with hN_def
  
  
  have hjet_split :
      iteratedCovGrad (I := I) g₀ 0 2 q
          (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
            deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') =
        iteratedCovGrad (I := I) g₀ 0 2 q N -
          iteratedCovGrad (I := I) g₀ 0 2 q
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T')) := by
    rw [deTurckSmoothRemainderDiff_eq_armDiff_sub_connLapDiff
      (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ', ← hN_def, iteratedCovGrad_sub]
  
  have htri :
      ‖iteratedCovGrad (I := I) g₀ 0 2 q
          (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
            deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ')‖ ≤
        ‖iteratedCovGrad (I := I) g₀ 0 2 q N‖ +
          ‖iteratedCovGrad (I := I) g₀ 0 2 q
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T'))‖ := by
    rw [hjet_split]; exact norm_sub_le _ _
  
  have hNarm : ‖iteratedCovGrad (I := I) g₀ 0 2 q N‖ ≤ Cn * Real.sqrt S := by
    rw [hN_def, hS_def]
    exact hCn T T' hδ_le hδ hδ'_le hδ' hTball hT'ball q hq
  have hLarm : ‖iteratedCovGrad (I := I) g₀ 0 2 q
      (rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T'))‖ ≤ Cl * Real.sqrt S := by
    rw [hS_def]; exact hCl (T - T') q hq
  calc ‖iteratedCovGrad (I := I) g₀ 0 2 q
          (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
            deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ')‖
      ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 q N‖ +
          ‖iteratedCovGrad (I := I) g₀ 0 2 q
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T'))‖ := htri
    _ ≤ Cn * Real.sqrt S + Cl * Real.sqrt S := add_le_add hNarm hLarm
    _ = (Cn + Cl) * Real.sqrt S := by ring

private theorem deTurckSmoothRemainderDiff_threeArm_coeffC0_jetL2_weighted_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (hδ₀_nn : 0 ≤ δ₀) :
    ∃ ΛC Γ : ℝ, 0 ≤ ΛC ∧ 0 ≤ Γ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∃ (C₀ : SmoothCcTensor g₀ 2 2) (C₁ : SmoothCcTensor g₀ 3 2) (C₂ : SmoothCcTensor g₀ 4 2),
          (deTurckSmoothRemainder (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
              deTurckSmoothRemainder (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ') =
            (appCc (I := I) (M := M) g₀ 2 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
              appCc (I := I) (M := M) g₀ 3 2 C₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
              appCc (I := I) (M := M) g₀ 4 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (C₀.toSection x) ≤ ΛC ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x (C₁.toSection x) ≤ ΛC ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (C₂.toSection x) ≤
            (ΛC * δ₀) ^ 2) ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i C₀‖ ^ 2) ≤ Γ ^ 2 ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 3 2 i C₁‖ ^ 2) ≤ Γ ^ 2 ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i C₂‖ ^ 2) ≤ Γ ^ 2 :=
  sorry

private theorem deTurckArmDiff_supercritical_pointwise_jet_le_lowerWindow
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    ∃ Cemb : ℝ, 0 ≤ Cemb ∧
      ∀ (W : SmoothCcTensor g₀ 0 2) (x : M),
        (∑ q ∈ Finset.range 3,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
              ((iteratedCovGrad (I := I) g₀ 0 2 q W).toSection x)) ≤
          Cemb ^ 2 * ∑ i ∈ Finset.range (a + 1 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2 :=
  sorry

private theorem appCc_topOrder_l2_twoArm_mixed_ballUniform_qUniform
    (g₀ : SmoothRiemannianMetric I M) (b₀ s₀ a : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (q : ℕ), q ≤ a →
      ∀ (Φ : SmoothCcTensor g₀ b₀ s₀) (W : SmoothCcTensor g₀ 0 b₀) (ΛΦ ΛW : ℝ),
        0 ≤ ΛΦ → 0 ≤ ΛW →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ b₀ s₀ x (Φ.toSection x) ≤ ΛΦ ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 b₀ x (W.toSection x) ≤ ΛW ^ 2) →
        ‖iteratedCovGrad (I := I) g₀ 0 s₀ q
            (appCc (I := I) (M := M) g₀ b₀ s₀ Φ W)‖ ^ 2 ≤
          C * (ΛW ^ 2 * ∑ i ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ‖ ^ 2
              + ΛΦ ^ 2 * ∑ l ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ^ 2) := by
  classical
  set Kf : ℕ → ℝ := fun k => (appCc_topOrder_l2_twoArm_mixed_ballUniform (I := I) g₀ b₀ s₀ k).choose
    with hKf_def
  have hKf_nn : ∀ k, 0 ≤ Kf k := fun k =>
    (appCc_topOrder_l2_twoArm_mixed_ballUniform (I := I) g₀ b₀ s₀ k).choose_spec.1
  have hKf_spec : ∀ k, ∀ (Φ : SmoothCcTensor g₀ b₀ s₀) (W : SmoothCcTensor g₀ 0 b₀) (ΛΦ ΛW : ℝ),
        0 ≤ ΛΦ → 0 ≤ ΛW →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ b₀ s₀ x (Φ.toSection x) ≤ ΛΦ ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 b₀ x (W.toSection x) ≤ ΛW ^ 2) →
        ‖iteratedCovGrad (I := I) g₀ 0 s₀ k
            (appCc (I := I) (M := M) g₀ b₀ s₀ Φ W)‖ ^ 2 ≤
          Kf k * (ΛW ^ 2 * ∑ i ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ‖ ^ 2
              + ΛΦ ^ 2 * ∑ l ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ^ 2) := fun k =>
    (appCc_topOrder_l2_twoArm_mixed_ballUniform (I := I) g₀ b₀ s₀ k).choose_spec.2
  refine ⟨(Finset.range (a + 1)).sup' (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero a)) Kf,
    le_trans (hKf_nn 0) (Finset.le_sup' Kf (Finset.mem_range.mpr (Nat.succ_pos a))), ?_⟩
  intro q hq Φ W ΛΦ ΛW hΛΦ hΛW hΦsup hWsup
  have hqmem : q ∈ Finset.range (a + 1) := Finset.mem_range.mpr (by omega)
  have hKq_le : Kf q ≤
      (Finset.range (a + 1)).sup' (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero a)) Kf :=
    Finset.le_sup' Kf hqmem
  refine le_trans (hKf_spec q Φ W ΛΦ ΛW hΛΦ hΛW hΦsup hWsup) ?_
  refine mul_le_mul_of_nonneg_right hKq_le ?_
  have h1 : 0 ≤ ΛW ^ 2 * ∑ i ∈ Finset.range (q + 1),
      ‖iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ‖ ^ 2 := by positivity
  have h2 : 0 ≤ ΛΦ ^ 2 * ∑ l ∈ Finset.range (q + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ^ 2 := by positivity
  linarith

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem deTurckSmoothRemainderDiff_iteratedCovGrad_l2_weighted_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (hδ₀_nn : 0 ≤ δ₀) :
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
            C * (δ₀ * Real.sqrt (∑ i ∈ Finset.range (a + 2 + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) +
              Real.sqrt (∑ i ∈ Finset.range (a + 1 + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2)) := by
  classical
  obtain ⟨ΛC, Γ, hΛC_nn, hΓ_nn, hcoeff⟩ :=
    deTurckSmoothRemainderDiff_threeArm_coeffC0_jetL2_weighted_ballUniform
      (I := I) g₀ g_bg a ha_super hR hδ₀ hδ₀_nn
  obtain ⟨K₀, hK₀_nn, hK₀⟩ := appCc_topOrder_l2_twoArm_mixed_ballUniform_qUniform (I := I) g₀ 2 2 a
  obtain ⟨K₁, hK₁_nn, hK₁⟩ := appCc_topOrder_l2_twoArm_mixed_ballUniform_qUniform (I := I) g₀ 3 2 a
  obtain ⟨K₂, hK₂_nn, hK₂⟩ := appCc_topOrder_l2_twoArm_mixed_ballUniform_qUniform (I := I) g₀ 4 2 a
  obtain ⟨Cemb2, hCemb2_nn, -⟩ :=
    deTurckArmDiff_supercritical_pointwise_jet_le (I := I) g₀ a ha_super
  obtain ⟨Cemb1, hCemb1_nn, hemb1⟩ :=
    deTurckArmDiff_supercritical_pointwise_jet_le_lowerWindow (I := I) g₀ a ha_super
  set Kmax : ℝ := max K₀ (max K₁ K₂) with hKmax_def
  have hKmax_nn : 0 ≤ Kmax := le_trans hK₀_nn (le_max_left _ _)
  have hK₀_le : K₀ ≤ Kmax := le_max_left _ _
  have hK₁_le : K₁ ≤ Kmax := le_trans (le_max_left _ _) (le_max_right _ _)
  have hK₂_le : K₂ ≤ Kmax := le_trans (le_max_right _ _) (le_max_right _ _)
  set base : ℝ := Kmax * ((Cemb2 ^ 2 + Cemb1 ^ 2 + 1) * (Γ ^ 2 + ΛC ^ 2 + 1)) with hbase_def
  have hbase_nn : 0 ≤ base := by rw [hbase_def]; positivity
  refine ⟨3 * Real.sqrt base, by positivity, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball q hq
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  set S₂ : ℝ := ∑ i ∈ Finset.range (a + 2 + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 with hS₂_def
  set S₁ : ℝ := ∑ i ∈ Finset.range (a + 1 + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 with hS₁_def
  have hS₂_nn : 0 ≤ S₂ := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hS₁_nn : 0 ≤ S₁ := Finset.sum_nonneg fun i _ => sq_nonneg _
  obtain ⟨C₀, C₁, C₂, hid, hC₀sup, hC₁sup, hC₂sup, hC₀jet, hC₁jet, hC₂jet⟩ :=
    hcoeff T T' hδ_le hδ hδ'_le hδ' hTball hT'ball
  set A₀ := appCc (I := I) (M := M) g₀ 2 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) with hA₀
  set A₁ := appCc (I := I) (M := M) g₀ 3 2 C₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) with hA₁
  set A₂ := appCc (I := I) (M := M) g₀ 4 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) with hA₂
  have hN_split : deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
      deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ' = A₀ + A₁ + A₂ := by
    rw [hA₀, hA₁, hA₂]; exact hid
  have hWsup1 : ∀ (m : ℕ), m ≤ 2 → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 m (T - T')).toSection x) ≤
        (Real.sqrt (Cemb1 ^ 2 * S₁)) ^ 2 := by
    intro m hm x
    rw [Real.sq_sqrt (by positivity)]
    have hembx := hemb1 (T - T') x
    rw [hS₁_def]
    have hmem : m ∈ Finset.range 3 := Finset.mem_range.mpr (by omega)
    refine le_trans (Finset.single_le_sum
      (f := fun qq => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + qq) x
        ((iteratedCovGrad (I := I) g₀ 0 2 qq (T - T')).toSection x))
      (fun qq _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + qq) x _) hmem) ?_
    exact hembx
  have hWjet : ∀ (m : ℕ), m ≤ 2 →
      (∑ l ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
          (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2) ≤
        ∑ i ∈ Finset.range (a + m + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 := by
    intro m hm
    have hcomp : ∀ l : ℕ,
        ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
            (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2 =
          ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) (T - T')‖ ^ 2 := by
      intro l
      have hbridgeL : ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
            (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2 =
          ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l
              (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
        rw [SmoothCcTensor.norm_def]
        exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ ((2 + m) + l)
          (iteratedCovGrad (I := I) g₀ 0 (2 + m) l (iteratedCovGrad (I := I) g₀ 0 2 m (T - T')))
      have hbridgeR : ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) (T - T')‖ ^ 2 =
          ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (m + l)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (m + l) (T - T')).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
        rw [SmoothCcTensor.norm_def]
        exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ (2 + (m + l))
          (iteratedCovGrad (I := I) g₀ 0 2 (m + l) (T - T'))
      rw [hbridgeL, hbridgeR]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      have hrw := rfns_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 2 m l (T - T') x
      simpa only [Nat.add_assoc] using hrw
    rw [show (∑ l ∈ Finset.range (q + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
            (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2) =
        ∑ l ∈ Finset.range (q + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) (T - T')‖ ^ 2 from
      Finset.sum_congr rfl (fun l _ => hcomp l)]
    set f : ℕ → ℝ := fun i => ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 with hf_def
    have hf_nn : ∀ i, 0 ≤ f i := fun i => sq_nonneg _
    have himg : (Finset.range (q + 1)).image (fun l => m + l) ⊆ Finset.range (a + m + 1) := by
      intro i hi
      rw [Finset.mem_image] at hi
      obtain ⟨l, hl, rfl⟩ := hi
      rw [Finset.mem_range] at hl ⊢
      omega
    have hinj : ∀ l₁ ∈ Finset.range (q + 1), ∀ l₂ ∈ Finset.range (q + 1),
        m + l₁ = m + l₂ → l₁ = l₂ := fun l₁ _ l₂ _ h => by omega
    calc (∑ l ∈ Finset.range (q + 1), f (m + l))
        = ∑ i ∈ (Finset.range (q + 1)).image (fun l => m + l), f i :=
          (Finset.sum_image hinj).symm
      _ ≤ ∑ i ∈ Finset.range (a + m + 1), f i :=
          Finset.sum_le_sum_of_subset_of_nonneg himg (fun i _ _ => hf_nn i)
  have hcoeffjet_le : ∀ (m : ℕ) (Cm : SmoothCcTensor g₀ (2 + m) 2) (bnd : ℝ),
      0 ≤ bnd →
      (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2) ≤ bnd →
      (∑ i ∈ Finset.range (q + 1), ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2) ≤ bnd := by
    intro m Cm bnd hbnd_nn hjet
    refine le_trans ?_ hjet
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => sq_nonneg _)
    exact Finset.range_mono (by omega)
  have harmTop : ‖iteratedCovGrad (I := I) g₀ 0 2 q A₂‖ ≤
      Real.sqrt base * (Real.sqrt S₁ + δ₀ * Real.sqrt S₂) := by
    have htame := hK₂ q hq C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))
      (ΛC * δ₀) (Real.sqrt (Cemb1 ^ 2 * S₁)) (mul_nonneg hΛC_nn hδ₀_nn) (Real.sqrt_nonneg _)
      hC₂sup (hWsup1 2 (by norm_num))
    have hΛWsq : (Real.sqrt (Cemb1 ^ 2 * S₁)) ^ 2 = Cemb1 ^ 2 * S₁ := Real.sq_sqrt (by positivity)
    have hcjet : (∑ i ∈ Finset.range (q + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i C₂‖ ^ 2) ≤
        Γ ^ 2 :=
      hcoeffjet_le 2 C₂ (Γ ^ 2) (sq_nonneg _) hC₂jet
    have hwjet : (∑ l ∈ Finset.range (q + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 4 l (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))‖ ^ 2) ≤
        S₂ := by
      have h := hWjet 2 (by norm_num)
      rw [hS₂_def]
      exact h
    have hsq : ‖iteratedCovGrad (I := I) g₀ 0 2 q A₂‖ ^ 2 ≤ base * (S₁ + δ₀ ^ 2 * S₂) := by
      rw [hA₂]
      refine le_trans htame ?_
      rw [hΛWsq]
      have ha1 : (Cemb1 ^ 2 * S₁) * ∑ i ∈ Finset.range (q + 1),
            ‖iteratedCovGrad (I := I) g₀ 4 2 i C₂‖ ^ 2 ≤ (Cemb1 ^ 2 * S₁) * Γ ^ 2 :=
        mul_le_mul_of_nonneg_left hcjet (by positivity)
      have ha2 : (ΛC * δ₀) ^ 2 * ∑ l ∈ Finset.range (q + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 4 l
              (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))‖ ^ 2 ≤ (ΛC * δ₀) ^ 2 * S₂ :=
        mul_le_mul_of_nonneg_left hwjet (sq_nonneg _)
      have hinner :
          (Cemb1 ^ 2 * S₁) * ∑ i ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ 4 2 i C₂‖ ^ 2
            + (ΛC * δ₀) ^ 2 * ∑ l ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 4 l
                (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))‖ ^ 2
          ≤ (Cemb2 ^ 2 + Cemb1 ^ 2 + 1) * (Γ ^ 2 + ΛC ^ 2 + 1) * (S₁ + δ₀ ^ 2 * S₂) := by
        have hsum_le :
            (Cemb1 ^ 2 * S₁) * Γ ^ 2 + (ΛC * δ₀) ^ 2 * S₂ ≤
              (Cemb2 ^ 2 + Cemb1 ^ 2 + 1) * (Γ ^ 2 + ΛC ^ 2 + 1) * (S₁ + δ₀ ^ 2 * S₂) := by
          have hcoeff_le : Cemb1 ^ 2 * Γ ^ 2 ≤
              (Cemb2 ^ 2 + Cemb1 ^ 2 + 1) * (Γ ^ 2 + ΛC ^ 2 + 1) := by
            nlinarith [sq_nonneg Cemb1, sq_nonneg Cemb2, sq_nonneg Γ, sq_nonneg ΛC,
              mul_nonneg (sq_nonneg Cemb1) (sq_nonneg ΛC),
              mul_nonneg (sq_nonneg Cemb2) (sq_nonneg Γ)]
          have hΛC_le : ΛC ^ 2 ≤
              (Cemb2 ^ 2 + Cemb1 ^ 2 + 1) * (Γ ^ 2 + ΛC ^ 2 + 1) := by
            nlinarith [sq_nonneg Cemb1, sq_nonneg Cemb2, sq_nonneg Γ, sq_nonneg ΛC,
              mul_nonneg (sq_nonneg Cemb2) (sq_nonneg ΛC),
              mul_nonneg (sq_nonneg Cemb1) (sq_nonneg ΛC)]
          set B : ℝ := (Cemb2 ^ 2 + Cemb1 ^ 2 + 1) * (Γ ^ 2 + ΛC ^ 2 + 1) with hB_def
          have hB_nn : 0 ≤ B := by rw [hB_def]; positivity
          have hterm1 : (Cemb1 ^ 2 * S₁) * Γ ^ 2 ≤ B * S₁ := by
            rw [show (Cemb1 ^ 2 * S₁) * Γ ^ 2 = (Cemb1 ^ 2 * Γ ^ 2) * S₁ by ring]
            exact mul_le_mul_of_nonneg_right hcoeff_le hS₁_nn
          have hterm2 : (ΛC * δ₀) ^ 2 * S₂ ≤ B * (δ₀ ^ 2 * S₂) := by
            rw [show (ΛC * δ₀) ^ 2 * S₂ = ΛC ^ 2 * (δ₀ ^ 2 * S₂) by ring]
            exact mul_le_mul_of_nonneg_right hΛC_le (by positivity)
          calc (Cemb1 ^ 2 * S₁) * Γ ^ 2 + (ΛC * δ₀) ^ 2 * S₂
              ≤ B * S₁ + B * (δ₀ ^ 2 * S₂) := add_le_add hterm1 hterm2
            _ = B * (S₁ + δ₀ ^ 2 * S₂) := by ring
        linarith [ha1, ha2, hsum_le]
      have hinner_nn : 0 ≤ (Cemb1 ^ 2 * S₁) * ∑ i ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ 4 2 i C₂‖ ^ 2
            + (ΛC * δ₀) ^ 2 * ∑ l ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 4 l
                (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))‖ ^ 2 := by positivity
      calc K₂ * ((Cemb1 ^ 2 * S₁) * ∑ i ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ 4 2 i C₂‖ ^ 2
              + (ΛC * δ₀) ^ 2 * ∑ l ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 4 l
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))‖ ^ 2)
          ≤ Kmax * ((Cemb2 ^ 2 + Cemb1 ^ 2 + 1) * (Γ ^ 2 + ΛC ^ 2 + 1) * (S₁ + δ₀ ^ 2 * S₂)) :=
            mul_le_mul hK₂_le hinner hinner_nn hKmax_nn
        _ = base * (S₁ + δ₀ ^ 2 * S₂) := by rw [hbase_def]; ring
    have hfinal : ‖iteratedCovGrad (I := I) g₀ 0 2 q A₂‖ ≤
        Real.sqrt base * (Real.sqrt S₁ + δ₀ * Real.sqrt S₂) := by
      have hsqrt_le : ‖iteratedCovGrad (I := I) g₀ 0 2 q A₂‖ ≤
          Real.sqrt (base * (S₁ + δ₀ ^ 2 * S₂)) := by
        rw [show ‖iteratedCovGrad (I := I) g₀ 0 2 q A₂‖ =
            Real.sqrt (‖iteratedCovGrad (I := I) g₀ 0 2 q A₂‖ ^ 2) from
          (Real.sqrt_sq (norm_nonneg _)).symm]
        exact Real.sqrt_le_sqrt hsq
      refine hsqrt_le.trans ?_
      have hrhs_nn : 0 ≤ Real.sqrt base * (Real.sqrt S₁ + δ₀ * Real.sqrt S₂) := by
        have : 0 ≤ Real.sqrt S₁ + δ₀ * Real.sqrt S₂ := by
          have := mul_nonneg hδ₀_nn (Real.sqrt_nonneg S₂)
          have := Real.sqrt_nonneg S₁
          linarith
        exact mul_nonneg (Real.sqrt_nonneg _) this
      have hsq_rhs : (Real.sqrt base * (Real.sqrt S₁ + δ₀ * Real.sqrt S₂)) ^ 2 =
          base * (S₁ + δ₀ ^ 2 * S₂ + 2 * δ₀ * (Real.sqrt S₁ * Real.sqrt S₂)) := by
        rw [mul_pow, Real.sq_sqrt hbase_nn, add_sq, mul_pow,
          Real.sq_sqrt hS₁_nn, Real.sq_sqrt hS₂_nn]
        ring
      have hle_sq : base * (S₁ + δ₀ ^ 2 * S₂) ≤
          (Real.sqrt base * (Real.sqrt S₁ + δ₀ * Real.sqrt S₂)) ^ 2 := by
        rw [hsq_rhs]
        have hcross_nn : 0 ≤ 2 * δ₀ * (Real.sqrt S₁ * Real.sqrt S₂) := by
          have := mul_nonneg (Real.sqrt_nonneg S₁) (Real.sqrt_nonneg S₂)
          have := mul_nonneg (by linarith : (0:ℝ) ≤ 2 * δ₀) this
          linarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hδ₀_nn)
            (mul_nonneg (Real.sqrt_nonneg S₁) (Real.sqrt_nonneg S₂))]
        nlinarith [hbase_nn, hcross_nn,
          mul_nonneg hbase_nn hcross_nn]
      calc Real.sqrt (base * (S₁ + δ₀ ^ 2 * S₂))
          ≤ Real.sqrt ((Real.sqrt base * (Real.sqrt S₁ + δ₀ * Real.sqrt S₂)) ^ 2) :=
            Real.sqrt_le_sqrt hle_sq
        _ = Real.sqrt base * (Real.sqrt S₁ + δ₀ * Real.sqrt S₂) := Real.sqrt_sq hrhs_nn
    exact hfinal
  have harmLow : ∀ (m : ℕ) (hm : m ≤ 1) (Cm : SmoothCcTensor g₀ (2 + m) 2) (Km : ℝ)
      (hKm_le : Km ≤ Kmax)
      (hKm : ∀ (Φ : SmoothCcTensor g₀ (2 + m) 2) (W : SmoothCcTensor g₀ 0 (2 + m)) (ΛΦ ΛW : ℝ),
        0 ≤ ΛΦ → 0 ≤ ΛW →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) 2 x (Φ.toSection x) ≤ ΛΦ ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x (W.toSection x) ≤ ΛW ^ 2) →
        ‖iteratedCovGrad (I := I) g₀ 0 2 q (appCc (I := I) (M := M) g₀ (2 + m) 2 Φ W)‖ ^ 2 ≤
          Km * (ΛW ^ 2 * ∑ i ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Φ‖ ^ 2
              + ΛΦ ^ 2 * ∑ l ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖ ^ 2))
      (hCmsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) 2 x (Cm.toSection x) ≤ ΛC ^ 2)
      (hCmjet : (∑ i ∈ Finset.range (a + 1),
          ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2) ≤ Γ ^ 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 q
          (appCc (I := I) (M := M) g₀ (2 + m) 2 Cm
            (iteratedCovGrad (I := I) g₀ 0 2 m (T - T')))‖ ≤ Real.sqrt (base * S₁) := by
    intro m hm Cm Km hKm_le hKm hCmsup hCmjet
    have htame := hKm Cm (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))
      ΛC (Real.sqrt (Cemb1 ^ 2 * S₁)) hΛC_nn (Real.sqrt_nonneg _) hCmsup
      (hWsup1 m (by omega))
    have hΛWsq : (Real.sqrt (Cemb1 ^ 2 * S₁)) ^ 2 = Cemb1 ^ 2 * S₁ := Real.sq_sqrt (by positivity)
    have hcjet : (∑ i ∈ Finset.range (q + 1), ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2) ≤
        Γ ^ 2 := hcoeffjet_le m Cm (Γ ^ 2) (sq_nonneg _) hCmjet
    have hwjet : (∑ l ∈ Finset.range (q + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
            (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2) ≤ S₁ := by
      have h := hWjet m (by omega)
      refine le_trans h ?_
      rw [hS₁_def]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        (fun i _ _ => sq_nonneg _)
    have hsq : ‖iteratedCovGrad (I := I) g₀ 0 2 q
        (appCc (I := I) (M := M) g₀ (2 + m) 2 Cm
          (iteratedCovGrad (I := I) g₀ 0 2 m (T - T')))‖ ^ 2 ≤ base * S₁ := by
      refine le_trans htame ?_
      rw [hΛWsq]
      have ha1 : (Cemb1 ^ 2 * S₁) * ∑ i ∈ Finset.range (q + 1),
            ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2 ≤ (Cemb1 ^ 2 * S₁) * Γ ^ 2 :=
        mul_le_mul_of_nonneg_left hcjet (by positivity)
      have ha2 : ΛC ^ 2 * ∑ l ∈ Finset.range (q + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
              (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2 ≤ ΛC ^ 2 * S₁ :=
        mul_le_mul_of_nonneg_left hwjet (sq_nonneg _)
      have hinner :
          (Cemb1 ^ 2 * S₁) * ∑ i ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2
            + ΛC ^ 2 * ∑ l ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
                (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2
          ≤ (Cemb2 ^ 2 + Cemb1 ^ 2 + 1) * (Γ ^ 2 + ΛC ^ 2 + 1) * S₁ := by
        have hsum_le : (Cemb1 ^ 2 * S₁) * Γ ^ 2 + ΛC ^ 2 * S₁ ≤
            (Cemb2 ^ 2 + Cemb1 ^ 2 + 1) * (Γ ^ 2 + ΛC ^ 2 + 1) * S₁ := by
          have hfactor : (Cemb1 ^ 2 * S₁) * Γ ^ 2 + ΛC ^ 2 * S₁ =
              (Cemb1 ^ 2 * Γ ^ 2 + ΛC ^ 2) * S₁ := by ring
          rw [hfactor]
          refine mul_le_mul_of_nonneg_right ?_ hS₁_nn
          nlinarith [sq_nonneg Cemb1, sq_nonneg Cemb2, sq_nonneg Γ, sq_nonneg ΛC,
            mul_nonneg (sq_nonneg Cemb2) (sq_nonneg ΛC),
            mul_nonneg (sq_nonneg Cemb1) (sq_nonneg Γ),
            mul_nonneg (sq_nonneg Cemb1) (sq_nonneg ΛC)]
        linarith [ha1, ha2, hsum_le]
      have hinner_nn : 0 ≤ (Cemb1 ^ 2 * S₁) * ∑ i ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2
            + ΛC ^ 2 * ∑ l ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
                (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2 := by positivity
      calc Km * ((Cemb1 ^ 2 * S₁) * ∑ i ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2
              + ΛC ^ 2 * ∑ l ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
                  (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2)
          ≤ Kmax * ((Cemb2 ^ 2 + Cemb1 ^ 2 + 1) * (Γ ^ 2 + ΛC ^ 2 + 1) * S₁) :=
            mul_le_mul hKm_le hinner hinner_nn hKmax_nn
        _ = base * S₁ := by rw [hbase_def]; ring
    rw [show ‖iteratedCovGrad (I := I) g₀ 0 2 q
          (appCc (I := I) (M := M) g₀ (2 + m) 2 Cm
            (iteratedCovGrad (I := I) g₀ 0 2 m (T - T')))‖ =
        Real.sqrt (‖iteratedCovGrad (I := I) g₀ 0 2 q
          (appCc (I := I) (M := M) g₀ (2 + m) 2 Cm
            (iteratedCovGrad (I := I) g₀ 0 2 m (T - T')))‖ ^ 2) from
      (Real.sqrt_sq (norm_nonneg _)).symm]
    exact Real.sqrt_le_sqrt hsq
  have ha0 := harmLow 0 (by norm_num) C₀ K₀ hK₀_le (hK₀ q hq) hC₀sup hC₀jet
  have ha1 := harmLow 1 (by norm_num) C₁ K₁ hK₁_le (hK₁ q hq) hC₁sup hC₁jet
  have hnorm0 : ‖iteratedCovGrad (I := I) g₀ 0 2 q A₀‖ ≤ Real.sqrt (base * S₁) := by
    rw [hA₀]; exact ha0
  have hnorm1 : ‖iteratedCovGrad (I := I) g₀ 0 2 q A₁‖ ≤ Real.sqrt (base * S₁) := by
    rw [hA₁]; exact ha1
  rw [hN_split, iteratedCovGrad_add (I := I) g₀ 0 2 q (A₀ + A₁) A₂,
    iteratedCovGrad_add (I := I) g₀ 0 2 q A₀ A₁]
  have hsqrt_lowfac : Real.sqrt (base * S₁) = Real.sqrt base * Real.sqrt S₁ :=
    Real.sqrt_mul hbase_nn S₁
  have htri : ‖iteratedCovGrad (I := I) g₀ 0 2 q A₀ +
        iteratedCovGrad (I := I) g₀ 0 2 q A₁ +
        iteratedCovGrad (I := I) g₀ 0 2 q A₂‖ ≤
      Real.sqrt (base * S₁) + Real.sqrt (base * S₁) +
        Real.sqrt base * (Real.sqrt S₁ + δ₀ * Real.sqrt S₂) := by
    refine le_trans (norm_add_le _ _) ?_
    refine add_le_add (le_trans (norm_add_le _ _) (add_le_add hnorm0 hnorm1)) harmTop
  refine htri.trans ?_
  rw [hsqrt_lowfac]
  have hsb_nn : 0 ≤ Real.sqrt base := Real.sqrt_nonneg _
  have hs1_nn : 0 ≤ Real.sqrt S₁ := Real.sqrt_nonneg _
  have hs2_nn : 0 ≤ Real.sqrt S₂ := Real.sqrt_nonneg _
  nlinarith [hsb_nn, hs1_nn, hs2_nn, hδ₀_nn,
    mul_nonneg hsb_nn hs1_nn, mul_nonneg hsb_nn hs2_nn,
    mul_nonneg (mul_nonneg hδ₀_nn hsb_nn) hs2_nn]

theorem deTurckRemainderDiff_iteratedCovGradSum_ballLipschitz
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
        (∑ q ∈ Finset.range (a + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 q
              (deTurckSmoothRemainder (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
                deTurckSmoothRemainder (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ')‖ ^ 2) ≤
          C * ∑ i ∈ Finset.range (a + 2 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 := by
  classical
  
  
  
  obtain ⟨C, hC_nn, hC⟩ :=
    deTurckSmoothRemainderDiff_iteratedCovGrad_l2_tame_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  refine ⟨(a + 1 : ℕ) * C ^ 2, by positivity, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  set D : SmoothCcTensor g₀ 0 2 :=
    deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
      deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ' with hD_def
  
  set Scol : ℝ := ∑ i ∈ Finset.range (a + 2 + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 with hScol_def
  have hScol_nn : 0 ≤ Scol :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  
  have hsqrt_sq : Real.sqrt Scol ^ 2 = Scol := Real.sq_sqrt hScol_nn
  
  
  have hper : ∀ q ∈ Finset.range (a + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ ^ 2 ≤ C ^ 2 * Scol := by
    intro q hq
    have hqa : q ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
    have hbound : ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ ≤ C * Real.sqrt Scol := by
      rw [hD_def, hScol_def]
      exact hC T T' hδ_le hδ hδ'_le hδ' hTball hT'ball q hqa
    have hnn : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ := norm_nonneg _
    calc ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ ^ 2
        ≤ (C * Real.sqrt Scol) ^ 2 := pow_le_pow_left₀ hnn hbound 2
      _ = C ^ 2 * Scol := by rw [mul_pow, hsqrt_sq]
  
  calc (∑ q ∈ Finset.range (a + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ ^ 2)
      ≤ ∑ _q ∈ Finset.range (a + 1), C ^ 2 * Scol := Finset.sum_le_sum hper
    _ = (a + 1 : ℕ) * C ^ 2 * Scol := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
