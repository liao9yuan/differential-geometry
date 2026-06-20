import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.IntegratedOrder2Garding
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.IntegratedCurvatureCrossBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapIterL2WtwokTwoBound
import DifferentialGeometry.Geometry.Connection.Laplacian.RoughLaplacianSecondCovGradL2Bound
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingReverseHebey
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Geometry.Connection.TensorNabla.HomFieldActionIteratedCovGradWindow
import DifferentialGeometry.Analysis.Sobolev.Embedding.RawConnLapToHsOrderDropping
import DifferentialGeometry.Geometry.Curvature.Bochner.PointwiseTensorCurvFirstOrderSection

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

set_option linter.unusedSectionVars false in

theorem exists_secondCovGrad_l2NormSq_le_rawConnLap_rankGen
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧
      ∀ S : SmoothCcTensor g 0 s,
        tensorL2Norm (I := I) (M := M) g 0 (s + 1 + 1)
            (covGrad (I := I) (M := M) g 0 (s + 1)
              (covGrad (I := I) (M := M) g 0 s S)).toFun ^ 2 ≤
          Cg *
            (tensorL2Norm (I := I) (M := M) g 0 s
                (rawTensorConnLapSmooth (I := I) g 0 s S).toFun ^ 2 +
              tensorL2Norm (I := I) (M := M) g 0 s S.toFun ^ 2) := by
  obtain ⟨Ccross, hCcross, hcross⟩ := exists_integrated_curvatureCrossBound (I := I) (M := M) g s
  refine ⟨2 + 2 * Ccross, by positivity, fun S => ?_⟩
  exact secondCovGrad_l2NormSq_le_of_cross_bound (I := I) (M := M) g s S Ccross hCcross (hcross S)

private theorem norm_iteratedCovGrad_comp
    (g : SmoothRiemannianMetric I M) (s j i : ℕ) (S : SmoothCcTensor g 0 s) :
    ‖iteratedCovGrad g 0 (s + j) i (iteratedCovGrad g 0 s j S)‖ =
      ‖iteratedCovGrad g 0 s (j + i) S‖ := by
  have hsq :
      ‖iteratedCovGrad g 0 (s + j) i (iteratedCovGrad g 0 s j S)‖ ^ 2 =
        ‖iteratedCovGrad g 0 s (j + i) S‖ ^ 2 := by
    rw [← tensorL2Norm_toFun_eq_norm (I := I) (M := M) g
        (iteratedCovGrad g 0 (s + j) i (iteratedCovGrad g 0 s j S)),
      ← tensorL2Norm_toFun_eq_norm (I := I) (M := M) g (iteratedCovGrad g 0 s (j + i) S),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g
        ((s + j) + i) (iteratedCovGrad g 0 (s + j) i (iteratedCovGrad g 0 s j S)),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g
        (s + (j + i)) (iteratedCovGrad g 0 s (j + i) S)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact rfns_iteratedCovGrad_comp (I := I) (M := M) g 0 s j i S x
  have h1 : 0 ≤ ‖iteratedCovGrad g 0 (s + j) i (iteratedCovGrad g 0 s j S)‖ := norm_nonneg _
  have h2 : 0 ≤ ‖iteratedCovGrad g 0 s (j + i) S‖ := norm_nonneg _
  nlinarith [hsq, h1, h2]

theorem exists_iteratedCovGrad_pointwiseTensorCurv_l2Norm_le
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ K : ℕ → ℝ, (∀ p, 0 ≤ K p) ∧
      ∀ (p : ℕ) (S : SmoothCcTensor g 0 s),
        ‖iteratedCovGrad g 0 (s + 1) p (pointwiseTensorCurv (I := I) (M := M) g s S)‖ ≤
          K p * ∑ a ∈ Finset.range (p + 2), ‖iteratedCovGrad g 0 s a S‖ := by
  classical
  
  obtain ⟨H_R, H_dR, hsec⟩ :=
    exists_pointwiseTensorCurv_firstOrder_homField_section (I := I) (M := M) g s
  
  
  
  obtain ⟨ccR, hccR_nn, hccR⟩ :=
    exists_appFullSec_on_jet_iteratedCovGrad_window_bound (I := I) (M := M) g 0 s 1 (s + 1) H_R
  obtain ⟨ccdR, hccdR_nn, hccdR⟩ :=
    exists_appFullSec_on_jet_iteratedCovGrad_window_bound (I := I) (M := M) g 0 s 0 (s + 1) H_dR
  
  refine ⟨fun p => Real.sqrt (2 * ccR p + 2 * ccdR p), fun p => Real.sqrt_nonneg _,
    fun p S => ?_⟩
  set Kp : ℝ := Real.sqrt (2 * ccR p + 2 * ccdR p) with hKp_def
  have hKp_nn : 0 ≤ Kp := Real.sqrt_nonneg _
  have hKp_sq : Kp ^ 2 = 2 * ccR p + 2 * ccdR p := by
    rw [hKp_def, Real.sq_sqrt (by have := hccR_nn p; have := hccdR_nn p; linarith)]
  
  set rfnsS : ℕ → M → ℝ := fun a x =>
    riemannianFiberNormSq (I := I) (M := M) g 0 (s + a) x ((iteratedCovGrad g 0 s a S).toSection x)
    with hrfnsS_def
  have hrfnsS_nn : ∀ a x, 0 ≤ rfnsS a x := fun a x =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + a) x _
  
  set AR : SmoothCcTensor g 0 (s + 1) :=
    appFullSec (I := I) (M := M) g 0 (s + 1) (s + 1) H_R (covGrad (I := I) (M := M) g 0 s S)
    with hAR_def
  set AdR : SmoothCcTensor g 0 (s + 1) :=
    appFullSec (I := I) (M := M) g 0 s (s + 1) H_dR S with hAdR_def
  
  have hgradsplit :
      iteratedCovGrad g 0 (s + 1) p (pointwiseTensorCurv (I := I) (M := M) g s S) =
        iteratedCovGrad g 0 (s + 1) p AR + iteratedCovGrad g 0 (s + 1) p AdR := by
    rw [hsec S, ← hAR_def, ← hAdR_def, iteratedCovGrad_add (I := I) (M := M) g 0 (s + 1) p]
  
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 ((s + 1) + p) x
          ((iteratedCovGrad g 0 (s + 1) p (pointwiseTensorCurv (I := I) (M := M) g s S)).toSection x) ≤
        Kp ^ 2 * ∑ a ∈ Finset.range (p + 2), rfnsS a x := by
    intro x
    
    have happ :
        (iteratedCovGrad g 0 (s + 1) p (pointwiseTensorCurv (I := I) (M := M) g s S)).toSection x =
          (iteratedCovGrad g 0 (s + 1) p AR).toSection x +
            (iteratedCovGrad g 0 (s + 1) p AdR).toSection x := by
      rw [hgradsplit, SmoothCcTensor.toSection_add]; rfl
    rw [happ]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g 0 ((s + 1) + p) x
      ((iteratedCovGrad g 0 (s + 1) p AR).toSection x)
      ((iteratedCovGrad g 0 (s + 1) p AdR).toSection x)) ?_
    
    have hAR_w : riemannianFiberNormSq (I := I) (M := M) g 0 ((s + 1) + p) x
          ((iteratedCovGrad g 0 (s + 1) p AR).toSection x) ≤
        ccR p * ∑ i ∈ Finset.range (1 + p), rfnsS (i + 1) x := by
      have h := hccR S p x
      rw [hrfnsS_def]
      simpa only [hAR_def] using h
    
    have hAdR_w : riemannianFiberNormSq (I := I) (M := M) g 0 ((s + 1) + p) x
          ((iteratedCovGrad g 0 (s + 1) p AdR).toSection x) ≤
        ccdR p * ∑ i ∈ Finset.range (1 + p), rfnsS i x := by
      have h := hccdR S p x
      have hreidx : ∀ i, riemannianFiberNormSq (I := I) (M := M) g 0 (s + (i + 0)) x
            ((iteratedCovGrad g 0 s (i + 0) S).toSection x) = rfnsS i x := by
        intro i; rw [hrfnsS_def]; simp only [Nat.add_zero]
      rw [Finset.sum_congr rfl (fun i _ => hreidx i)] at h
      simpa only [hAdR_def] using h
    
    have hsubR : ∑ i ∈ Finset.range (1 + p), rfnsS (i + 1) x ≤
        ∑ a ∈ Finset.range (p + 2), rfnsS a x := by
      have hIco : ∑ i ∈ Finset.range (1 + p), rfnsS (i + 1) x =
          ∑ a ∈ Finset.Ico 1 (1 + (1 + p)), rfnsS a x := by
        rw [Finset.sum_Ico_eq_sum_range]
        refine Finset.sum_congr (by congr 1; omega) (fun i _ => by rw [Nat.add_comm 1 i])
      rw [hIco]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun a _ _ => hrfnsS_nn a x)
      intro a ha
      rw [Finset.mem_Ico] at ha; rw [Finset.mem_range]; omega
    
    have hsubdR : ∑ i ∈ Finset.range (1 + p), rfnsS i x ≤
        ∑ a ∈ Finset.range (p + 2), rfnsS a x := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun a _ _ => hrfnsS_nn a x)
      intro a ha
      rw [Finset.mem_range] at ha ⊢; omega
    
    set FULL : ℝ := ∑ a ∈ Finset.range (p + 2), rfnsS a x with hFULL_def
    have hFULL_nn : 0 ≤ FULL := Finset.sum_nonneg (fun a _ => hrfnsS_nn a x)
    rw [hKp_sq]
    calc 2 * riemannianFiberNormSq (I := I) (M := M) g 0 ((s + 1) + p) x
              ((iteratedCovGrad g 0 (s + 1) p AR).toSection x) +
            2 * riemannianFiberNormSq (I := I) (M := M) g 0 ((s + 1) + p) x
              ((iteratedCovGrad g 0 (s + 1) p AdR).toSection x)
        ≤ 2 * (ccR p * ∑ i ∈ Finset.range (1 + p), rfnsS (i + 1) x) +
            2 * (ccdR p * ∑ i ∈ Finset.range (1 + p), rfnsS i x) :=
          add_le_add (by linarith [hAR_w]) (by linarith [hAdR_w])
      _ ≤ 2 * (ccR p * FULL) + 2 * (ccdR p * FULL) := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hsubR (hccR_nn p)) (by norm_num)
          · exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hsubdR (hccdR_nn p)) (by norm_num)
      _ = (2 * ccR p + 2 * ccdR p) * FULL := by ring
  
  have hL2 := tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum (I := I) (M := M) g
    (c := (s + 1) + p) (p + 2) (fun a => s + a) (fun a => iteratedCovGrad g 0 s a S)
    (iteratedCovGrad g 0 (s + 1) p (pointwiseTensorCurv (I := I) (M := M) g s S)) Kp hKp_nn
    (fun x => by simpa only [hrfnsS_def] using hpt x)
  simpa only using hL2

set_option linter.style.show false in

private theorem iteratedRoughLapGrad_commutator_l2Norm_le_aux
    (g : SmoothRiemannianMetric I M) (m : ℕ) :
    ∀ s : ℕ, ∃ Cfun : ℕ → ℝ, (∀ p, 0 ≤ Cfun p) ∧
      ∀ (p : ℕ) (S : SmoothCcTensor g 0 s),
        ‖iteratedCovGrad g 0 (s + m) p
            (rawTensorConnLapSmooth (I := I) g 0 (s + m) (iteratedCovGrad g 0 s m S) -
              iteratedCovGrad g 0 s m (rawTensorConnLapSmooth (I := I) g 0 s S))‖ ≤
          Cfun p * ∑ a ∈ Finset.range (m + p + 1), ‖iteratedCovGrad g 0 s a S‖ := by
  induction m with
  | zero =>
    intro s
    refine ⟨fun _ => 0, fun _ => le_refl _, fun p S => ?_⟩
    
    have hcomm0 :
        rawTensorConnLapSmooth (I := I) g 0 (s + 0) (iteratedCovGrad g 0 s 0 S) -
            iteratedCovGrad g 0 s 0 (rawTensorConnLapSmooth (I := I) g 0 s S) =
          (0 : SmoothCcTensor g 0 (s + 0)) := by
      simp only [iteratedCovGrad_zero, Nat.add_zero, sub_self]
    rw [hcomm0]
    have hz : iteratedCovGrad g 0 (s + 0) p (0 : SmoothCcTensor g 0 (s + 0)) =
        (0 : SmoothCcTensor g 0 (s + 0 + p)) := by
      have := iteratedCovGrad_sub (I := I) (M := M) g 0 (s + 0) p
        (0 : SmoothCcTensor g 0 (s + 0)) (0 : SmoothCcTensor g 0 (s + 0))
      simpa using this
    rw [hz, norm_zero]
    exact mul_nonneg (le_refl 0) (Finset.sum_nonneg (fun a _ => norm_nonneg _))
  | succ m ih =>
    intro s
    
    
    obtain ⟨Cm, hCm_nn, hCm⟩ := ih s
    obtain ⟨K, hK_nn, hK⟩ :=
      exists_iteratedCovGrad_pointwiseTensorCurv_l2Norm_le (I := I) (M := M) g (s + m)
    refine ⟨fun p => K p + Cm (p + 1), fun p => add_nonneg (hK_nn p) (hCm_nn (p + 1)),
      fun p S => ?_⟩
    
    
    have hsplit :
        rawTensorConnLapSmooth (I := I) g 0 (s + (m + 1)) (iteratedCovGrad g 0 s (m + 1) S) -
            iteratedCovGrad g 0 s (m + 1) (rawTensorConnLapSmooth (I := I) g 0 s S) =
          pointwiseTensorCurv (I := I) (M := M) g (s + m) (iteratedCovGrad g 0 s m S) +
            covGrad (I := I) (M := M) g 0 (s + m)
              (rawTensorConnLapSmooth (I := I) g 0 (s + m) (iteratedCovGrad g 0 s m S) -
                iteratedCovGrad g 0 s m (rawTensorConnLapSmooth (I := I) g 0 s S)) := by
      rw [iteratedCovGrad_succ (I := I) (M := M) g 0 s m S,
        iteratedCovGrad_succ (I := I) (M := M) g 0 s m
          (rawTensorConnLapSmooth (I := I) g 0 s S)]
      show rawTensorConnLapSmooth (I := I) g 0 (s + m + 1)
            (covGrad (I := I) (M := M) g 0 (s + m) (iteratedCovGrad g 0 s m S)) -
          covGrad (I := I) (M := M) g 0 (s + m)
            (iteratedCovGrad g 0 s m (rawTensorConnLapSmooth (I := I) g 0 s S)) =
        pointwiseTensorCurv (I := I) (M := M) g (s + m) (iteratedCovGrad g 0 s m S) +
          covGrad (I := I) (M := M) g 0 (s + m)
            (rawTensorConnLapSmooth (I := I) g 0 (s + m) (iteratedCovGrad g 0 s m S) -
              iteratedCovGrad g 0 s m (rawTensorConnLapSmooth (I := I) g 0 s S))
      rw [pointwiseTensorCurv_commutator_eq (I := I) (M := M) g (s + m)
          (iteratedCovGrad g 0 s m S),
        covGrad_sub (I := I) (M := M) g 0 (s + m)]
      abel
    
    set comm_m : SmoothCcTensor g 0 (s + m) :=
      rawTensorConnLapSmooth (I := I) g 0 (s + m) (iteratedCovGrad g 0 s m S) -
        iteratedCovGrad g 0 s m (rawTensorConnLapSmooth (I := I) g 0 s S) with hcomm_m
    set gradm : SmoothCcTensor g 0 (s + m) := iteratedCovGrad g 0 s m S with hgradm
    set fullSum : ℝ := ∑ a ∈ Finset.range (m + 1 + p + 1),
      ‖iteratedCovGrad g 0 s a S‖ with hfullSum
    have hfullSum_nn : 0 ≤ fullSum :=
      Finset.sum_nonneg (fun a _ => norm_nonneg _)
    
    rw [hsplit, iteratedCovGrad_add (I := I) (M := M) g 0 (s + (m + 1)) p]
    
    refine le_trans (norm_add_le _ _) ?_
    
    have harm1 :
        ‖iteratedCovGrad g 0 (s + (m + 1)) p
            (pointwiseTensorCurv (I := I) (M := M) g (s + m) gradm)‖ ≤
          K p * fullSum := by
      have hKb := hK p gradm
      
      have hreindex : ∀ a, ‖iteratedCovGrad g 0 (s + m) a gradm‖ =
          ‖iteratedCovGrad g 0 s (m + a) S‖ := by
        intro a
        rw [hgradm, norm_iteratedCovGrad_comp (I := I) (M := M) g s m a S]
      rw [Finset.sum_congr rfl (fun a _ => hreindex a)] at hKb
      
      have hsub : ∑ a ∈ Finset.range (p + 2), ‖iteratedCovGrad g 0 s (m + a) S‖ ≤ fullSum := by
        rw [hfullSum]
        have hIco : ∑ a ∈ Finset.range (p + 2), ‖iteratedCovGrad g 0 s (m + a) S‖ =
            ∑ b ∈ Finset.Ico m (m + (p + 2)), ‖iteratedCovGrad g 0 s b S‖ := by
          rw [Finset.sum_Ico_eq_sum_range]
          refine Finset.sum_congr ?_ (fun a _ => rfl)
          congr 1
          omega
        rw [hIco]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun b _ _ => norm_nonneg _)
        intro b hb
        rw [Finset.mem_Ico] at hb
        rw [Finset.mem_range]
        omega
      calc ‖iteratedCovGrad g 0 (s + (m + 1)) p
              (pointwiseTensorCurv (I := I) (M := M) g (s + m) gradm)‖
          ≤ K p * ∑ a ∈ Finset.range (p + 2), ‖iteratedCovGrad g 0 s (m + a) S‖ := hKb
        _ ≤ K p * fullSum := mul_le_mul_of_nonneg_left hsub (hK_nn p)
    
    have harm2 :
        ‖iteratedCovGrad g 0 (s + (m + 1)) p
            (covGrad (I := I) (M := M) g 0 (s + m) comm_m)‖ ≤
          Cm (p + 1) * fullSum := by
      
      have hcomp :
          ‖iteratedCovGrad g 0 (s + (m + 1)) p
              (covGrad (I := I) (M := M) g 0 (s + m) comm_m)‖ =
            ‖iteratedCovGrad g 0 (s + m) (p + 1) comm_m‖ := by
        have h := norm_iteratedCovGrad_comp (I := I) (M := M) g (s + m) 1 p comm_m
        rw [Nat.add_comm 1 p] at h
        exact h
      rw [hcomp]
      have hCmb := hCm (p + 1) S
      rw [← hcomm_m] at hCmb
      
      have hsum_eq : ∑ a ∈ Finset.range (m + (p + 1) + 1), ‖iteratedCovGrad g 0 s a S‖ = fullSum := by
        rw [hfullSum, show m + (p + 1) + 1 = m + 1 + p + 1 from by omega]
      rw [hsum_eq] at hCmb
      exact hCmb
    
    have hfinal : K p * fullSum + Cm (p + 1) * fullSum =
        (K p + Cm (p + 1)) * fullSum := by ring
    calc ‖iteratedCovGrad g 0 (s + (m + 1)) p
            (pointwiseTensorCurv (I := I) (M := M) g (s + m) gradm)‖ +
          ‖iteratedCovGrad g 0 (s + (m + 1)) p
            (covGrad (I := I) (M := M) g 0 (s + m) comm_m)‖
        ≤ K p * fullSum + Cm (p + 1) * fullSum := add_le_add harm1 harm2
      _ = (K p + Cm (p + 1)) * fullSum := hfinal

theorem exists_iteratedRoughLapGrad_commutator_l2Norm_le
    (g : SmoothRiemannianMetric I M) (s m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g 0 s,
        ‖rawTensorConnLapSmooth (I := I) g 0 (s + m) (iteratedCovGrad g 0 s m S) -
            iteratedCovGrad g 0 s m (rawTensorConnLapSmooth (I := I) g 0 s S)‖ ≤
          C * ∑ a ∈ Finset.range (m + 1), ‖iteratedCovGrad g 0 s a S‖ := by
  obtain ⟨Cfun, _hCfun_nn, hbound⟩ :=
    iteratedRoughLapGrad_commutator_l2Norm_le_aux (I := I) (M := M) g m s
  refine ⟨Cfun 0, _hCfun_nn 0, fun S => ?_⟩
  have h := hbound 0 S
  simpa only [iteratedCovGrad_zero, Nat.add_zero, Nat.add_zero] using h

private theorem rawTensorConnLapIter_rawTensorConnLapSmooth
    (g : SmoothRiemannianMetric I M) (s : ℕ) (i : ℕ) (S : SmoothCcTensor g 0 s) :
    rawTensorConnLapIter (I := I) g 0 s i (rawTensorConnLapSmooth (I := I) g 0 s S) =
      rawTensorConnLapIter (I := I) g 0 s (i + 1) S := by
  induction i with
  | zero => rfl
  | succ n ih =>
    rw [rawTensorConnLapIter_succ (I := I) g 0 s n
          (rawTensorConnLapSmooth (I := I) g 0 s S),
        ih, rawTensorConnLapIter_succ (I := I) g 0 s (n + 1) S]

private theorem covGrad_norm_sq_le_rawConnLap_mul_self
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    ‖covGrad (I := I) (M := M) g 0 s S‖ ^ 2 ≤
      ‖rawTensorConnLapSmooth (I := I) g 0 s S‖ * ‖S‖ := by
  have h := covGrad_l2NormSq_le_rawConnLap_mul_self_gen (I := I) (M := M) g s S
  rwa [tensorL2Norm_toFun_eq_norm (I := I) (M := M) g (covGrad (I := I) (M := M) g 0 s S),
    tensorL2Norm_toFun_eq_norm (I := I) (M := M) g (rawTensorConnLapSmooth (I := I) g 0 s S),
    tensorL2Norm_toFun_eq_norm (I := I) (M := M) g S] at h

private theorem exists_secondCovGrad_norm_sq_le_rawConnLap
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧
      ∀ S : SmoothCcTensor g 0 s,
        ‖covGrad (I := I) (M := M) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S)‖ ^ 2 ≤
          Cg * (‖rawTensorConnLapSmooth (I := I) g 0 s S‖ ^ 2 + ‖S‖ ^ 2) := by
  obtain ⟨Cg, hCg, hbound⟩ := exists_secondCovGrad_l2NormSq_le_rawConnLap_rankGen (I := I) (M := M) g s
  refine ⟨Cg, hCg, fun S => ?_⟩
  have h := hbound S
  rwa [tensorL2Norm_toFun_eq_norm (I := I) (M := M) g
        (covGrad (I := I) (M := M) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S)),
      tensorL2Norm_toFun_eq_norm (I := I) (M := M) g (rawTensorConnLapSmooth (I := I) g 0 s S),
      tensorL2Norm_toFun_eq_norm (I := I) (M := M) g S] at h

private theorem covGrad_covGrad_eq_iteratedCovGrad_two
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    covGrad (I := I) (M := M) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s S) =
      iteratedCovGrad g 0 s 2 S := rfl

private theorem iteratedCovGrad_add_two
    (g : SmoothRiemannianMetric I M) (s j : ℕ) (S : SmoothCcTensor g 0 s) :
    iteratedCovGrad g 0 s (j + 2) S =
      covGrad (I := I) (M := M) g 0 (s + j + 1)
        (covGrad (I := I) (M := M) g 0 (s + j) (iteratedCovGrad g 0 s j S)) := rfl

private theorem rawConnLap_iteratedCovGrad_eq_iteratedCovGrad_rawConnLap_add_comm
    (g : SmoothRiemannianMetric I M) (s m : ℕ) (S : SmoothCcTensor g 0 s) :
    rawTensorConnLapSmooth (I := I) g 0 (s + m) (iteratedCovGrad g 0 s m S) =
      iteratedCovGrad g 0 s m (rawTensorConnLapSmooth (I := I) g 0 s S) +
        (rawTensorConnLapSmooth (I := I) g 0 (s + m) (iteratedCovGrad g 0 s m S) -
          iteratedCovGrad g 0 s m (rawTensorConnLapSmooth (I := I) g 0 s S)) := by
  abel

theorem exists_iteratedCovGrad_l2Norm_le_sum_rawConnLapIter
    (g : SmoothRiemannianMetric I M) (s k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (j : ℕ), j ≤ 2 * k → ∀ S : SmoothCcTensor g 0 s,
        tensorL2Norm (I := I) (M := M) g 0 (s + j)
            (iteratedCovGrad g 0 s j S).toFun ≤
          C * ∑ i ∈ Finset.range (k + 1),
            tensorL2Norm (I := I) (M := M) g 0 s
              (rawTensorConnLapIter (I := I) g 0 s i S).toFun := by
  classical
  
  
  
  suffices h : ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (j : ℕ), j ≤ 2 * k → ∀ S : SmoothCcTensor g 0 s,
        ‖iteratedCovGrad g 0 s j S‖ ≤
          C * ∑ i ∈ Finset.range (k + 1), ‖rawTensorConnLapIter (I := I) g 0 s i S‖ by
    obtain ⟨C, hC, hbound⟩ := h s
    refine ⟨C, hC, fun j hj S => ?_⟩
    have hb := hbound j hj S
    rw [tensorL2Norm_toFun_eq_norm (I := I) (M := M) g (iteratedCovGrad g 0 s j S)]
    refine le_trans hb (le_of_eq ?_)
    simp only [tensorL2Norm_toFun_eq_norm (I := I) (M := M) g]
  
  
  induction k with
  | zero =>
    intro s
    refine ⟨1, by norm_num, fun j hj S => ?_⟩
    have hj0 : j = 0 := by omega
    subst hj0
    rw [iteratedCovGrad_zero, Finset.sum_range_one, rawTensorConnLapIter_zero, one_mul]
  | succ n ih =>
    intro s
    
    set lapSum : ∀ r : ℕ, SmoothCcTensor g 0 s → ℝ :=
      fun r S => ∑ i ∈ Finset.range (r + 1), ‖rawTensorConnLapIter (I := I) g 0 s i S‖
      with hlapSum_def
    
    obtain ⟨Cn, hCn_nn, hCn⟩ := ih s
    
    
    obtain ⟨Cg, hCg_nn, hgard⟩ := exists_secondCovGrad_norm_sq_le_rawConnLap (I := I) (M := M) g (s + 2 * n)
    obtain ⟨Ccomm, hCcomm_nn, hcomm⟩ :=
      exists_iteratedRoughLapGrad_commutator_l2Norm_le (I := I) (M := M) g s (2 * n)
    
    set P : ℝ := Cn + Ccomm * ((2 * n + 1 : ℕ) : ℝ) * Cn with hP_def
    have hP_nn : 0 ≤ P := by
      have : 0 ≤ Ccomm * ((2 * n + 1 : ℕ) : ℝ) * Cn :=
        mul_nonneg (mul_nonneg hCcomm_nn (by positivity)) hCn_nn
      positivity
    set C2 : ℝ := Real.sqrt (Cg * (P ^ 2 + Cn ^ 2)) with hC2_def
    set C1 : ℝ := Real.sqrt (P * Cn) with hC1_def
    refine ⟨max Cn (max C2 C1), le_trans hCn_nn (le_max_left _ _), fun j hj S => ?_⟩
    
    have hlapSum_nn : ∀ r, 0 ≤ lapSum r S := fun r =>
      Finset.sum_nonneg (fun i _ => norm_nonneg _)
    
    have hlapSum_mono : lapSum n S ≤ lapSum (n + 1) S := by
      simp only [hlapSum_def]
      rw [Finset.sum_range_succ
        (fun i => ‖rawTensorConnLapIter (I := I) g 0 s i S‖) (n + 1)]
      have := norm_nonneg (rawTensorConnLapIter (I := I) g 0 s (n + 1) S)
      linarith
    
    have hgrad_le : ∀ i : ℕ, i ≤ 2 * n → ‖iteratedCovGrad g 0 s i S‖ ≤ Cn * lapSum n S := by
      intro i hi
      have := hCn i hi S
      rwa [hlapSum_def]
    
    
    have hgrad_lap_le :
        ‖iteratedCovGrad g 0 s (2 * n) (rawTensorConnLapSmooth (I := I) g 0 s S)‖ ≤
          Cn * lapSum (n + 1) S := by
      have hih := hCn (2 * n) (le_refl _) (rawTensorConnLapSmooth (I := I) g 0 s S)
      
      have hreindex :
          ∑ i ∈ Finset.range (n + 1),
              ‖rawTensorConnLapIter (I := I) g 0 s i (rawTensorConnLapSmooth (I := I) g 0 s S)‖ ≤
            lapSum (n + 1) S := by
        have hterm : ∀ i ∈ Finset.range (n + 1),
            ‖rawTensorConnLapIter (I := I) g 0 s i (rawTensorConnLapSmooth (I := I) g 0 s S)‖ =
              ‖rawTensorConnLapIter (I := I) g 0 s (i + 1) S‖ := by
          intro i _
          rw [rawTensorConnLapIter_rawTensorConnLapSmooth (I := I) (M := M) g s i S]
        rw [Finset.sum_congr rfl hterm]
        rw [hlapSum_def]
        simp only
        
        rw [Finset.sum_range_succ' (fun i => ‖rawTensorConnLapIter (I := I) g 0 s i S‖) (n + 1)]
        have : (0 : ℝ) ≤ ‖rawTensorConnLapIter (I := I) g 0 s 0 S‖ := norm_nonneg _
        linarith
      calc ‖iteratedCovGrad g 0 s (2 * n) (rawTensorConnLapSmooth (I := I) g 0 s S)‖
          ≤ Cn * ∑ i ∈ Finset.range (n + 1),
              ‖rawTensorConnLapIter (I := I) g 0 s i (rawTensorConnLapSmooth (I := I) g 0 s S)‖ := hih
        _ ≤ Cn * lapSum (n + 1) S := by
            exact mul_le_mul_of_nonneg_left hreindex hCn_nn
    
    have hcomm_le :
        ‖rawTensorConnLapSmooth (I := I) g 0 (s + 2 * n) (iteratedCovGrad g 0 s (2 * n) S) -
            iteratedCovGrad g 0 s (2 * n) (rawTensorConnLapSmooth (I := I) g 0 s S)‖ ≤
          Ccomm * ((2 * n + 1 : ℕ) : ℝ) * Cn * lapSum (n + 1) S := by
      have hc := hcomm S
      
      have hsum_le :
          ∑ a ∈ Finset.range (2 * n + 1), ‖iteratedCovGrad g 0 s a S‖ ≤
            ((2 * n + 1 : ℕ) : ℝ) * (Cn * lapSum n S) := by
        calc ∑ a ∈ Finset.range (2 * n + 1), ‖iteratedCovGrad g 0 s a S‖
            ≤ ∑ _a ∈ Finset.range (2 * n + 1), (Cn * lapSum n S) :=
              Finset.sum_le_sum (fun a ha =>
                hgrad_le a (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)))
          _ = ((2 * n + 1 : ℕ) : ℝ) * (Cn * lapSum n S) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      calc ‖rawTensorConnLapSmooth (I := I) g 0 (s + 2 * n) (iteratedCovGrad g 0 s (2 * n) S) -
              iteratedCovGrad g 0 s (2 * n) (rawTensorConnLapSmooth (I := I) g 0 s S)‖
          ≤ Ccomm * ∑ a ∈ Finset.range (2 * n + 1), ‖iteratedCovGrad g 0 s a S‖ := hc
        _ ≤ Ccomm * (((2 * n + 1 : ℕ) : ℝ) * (Cn * lapSum n S)) :=
            mul_le_mul_of_nonneg_left hsum_le hCcomm_nn
        _ ≤ Ccomm * ((2 * n + 1 : ℕ) : ℝ) * Cn * lapSum (n + 1) S := by
            have hmono := mul_le_mul_of_nonneg_left hlapSum_mono
              (by positivity : (0 : ℝ) ≤ Ccomm * ((2 * n + 1 : ℕ) : ℝ) * Cn)
            nlinarith [hmono, mul_nonneg (mul_nonneg hCcomm_nn
              (by positivity : (0 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ))) hCn_nn]
    
    have hrawlap_grad_le :
        ‖rawTensorConnLapSmooth (I := I) g 0 (s + 2 * n) (iteratedCovGrad g 0 s (2 * n) S)‖ ≤
          P * lapSum (n + 1) S := by
      have hsplit := rawConnLap_iteratedCovGrad_eq_iteratedCovGrad_rawConnLap_add_comm
        (I := I) (M := M) g s (2 * n) S
      rw [hsplit]
      refine le_trans (norm_add_le _ _) ?_
      have := add_le_add hgrad_lap_le hcomm_le
      rw [hP_def]
      calc ‖iteratedCovGrad g 0 s (2 * n) (rawTensorConnLapSmooth (I := I) g 0 s S)‖ +
            ‖rawTensorConnLapSmooth (I := I) g 0 (s + 2 * n) (iteratedCovGrad g 0 s (2 * n) S) -
              iteratedCovGrad g 0 s (2 * n) (rawTensorConnLapSmooth (I := I) g 0 s S)‖
          ≤ Cn * lapSum (n + 1) S +
              Ccomm * ((2 * n + 1 : ℕ) : ℝ) * Cn * lapSum (n + 1) S := this
        _ = (Cn + Ccomm * ((2 * n + 1 : ℕ) : ℝ) * Cn) * lapSum (n + 1) S := by ring
    
    have hgrad2n_le : ‖iteratedCovGrad g 0 s (2 * n) S‖ ≤ Cn * lapSum (n + 1) S :=
      le_trans (hgrad_le (2 * n) (le_refl _))
        (mul_le_mul_of_nonneg_left hlapSum_mono hCn_nn)
    
    rcases Nat.lt_or_ge j (2 * n + 1) with hjlt | hjge
    · have hjle : j ≤ 2 * n := Nat.lt_succ_iff.mp hjlt
      calc ‖iteratedCovGrad g 0 s j S‖
          ≤ Cn * lapSum n S := hgrad_le j hjle
        _ ≤ Cn * lapSum (n + 1) S := mul_le_mul_of_nonneg_left hlapSum_mono hCn_nn
        _ = Cn * ∑ i ∈ Finset.range (n + 1 + 1), ‖rawTensorConnLapIter (I := I) g 0 s i S‖ := by
            simp only [hlapSum_def]
        _ ≤ max Cn (max C2 C1) *
              ∑ i ∈ Finset.range (n + 1 + 1), ‖rawTensorConnLapIter (I := I) g 0 s i S‖ :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    · have hjcase : j = 2 * n + 1 ∨ j = 2 * n + 2 := by omega
      rcases hjcase with hj1 | hj2
      · subst hj1
        
        
        have heq : iteratedCovGrad g 0 s (2 * n + 1) S =
            covGrad (I := I) (M := M) g 0 (s + 2 * n) (iteratedCovGrad g 0 s (2 * n) S) := rfl
        have hord1 := covGrad_norm_sq_le_rawConnLap_mul_self (I := I) (M := M) g (s + 2 * n)
          (iteratedCovGrad g 0 s (2 * n) S)
        
        have hsq : ‖iteratedCovGrad g 0 s (2 * n + 1) S‖ ^ 2 ≤
            (P * Cn) * lapSum (n + 1) S ^ 2 := by
          rw [heq]
          refine le_trans hord1 ?_
          have h1 := hrawlap_grad_le
          have h2 := hgrad2n_le
          have hL := hlapSum_nn (n + 1)
          nlinarith [mul_nonneg (norm_nonneg
            (rawTensorConnLapSmooth (I := I) g 0 (s + 2 * n) (iteratedCovGrad g 0 s (2 * n) S)))
            (norm_nonneg (iteratedCovGrad g 0 s (2 * n) S)),
            mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg hP_nn hL),
            mul_nonneg hP_nn hL, mul_nonneg hCn_nn hL]
        
        have hle : ‖iteratedCovGrad g 0 s (2 * n + 1) S‖ ≤ C1 * lapSum (n + 1) S := by
          rw [hC1_def]
          have hfinal : ‖iteratedCovGrad g 0 s (2 * n + 1) S‖ ^ 2 ≤
              (Real.sqrt (P * Cn) * lapSum (n + 1) S) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt (mul_nonneg hP_nn hCn_nn)]
            exact hsq
          exact le_of_sq_le_sq hfinal
            (mul_nonneg (Real.sqrt_nonneg _) (hlapSum_nn (n + 1)))
        calc ‖iteratedCovGrad g 0 s (2 * n + 1) S‖
            ≤ C1 * lapSum (n + 1) S := hle
          _ ≤ max Cn (max C2 C1) * lapSum (n + 1) S :=
              mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) (le_max_right _ _))
                (hlapSum_nn (n + 1))
          _ = max Cn (max C2 C1) *
                ∑ i ∈ Finset.range (n + 1 + 1), ‖rawTensorConnLapIter (I := I) g 0 s i S‖ := by
              simp only [hlapSum_def]
      · subst hj2
        
        
        have heq : iteratedCovGrad g 0 s (2 * n + 2) S =
            covGrad (I := I) (M := M) g 0 (s + 2 * n + 1)
              (covGrad (I := I) (M := M) g 0 (s + 2 * n) (iteratedCovGrad g 0 s (2 * n) S)) :=
          iteratedCovGrad_add_two (I := I) (M := M) g s (2 * n) S
        have hord2 := hgard (iteratedCovGrad g 0 s (2 * n) S)
        
        have hsq : ‖iteratedCovGrad g 0 s (2 * n + 2) S‖ ^ 2 ≤
            (Cg * (P ^ 2 + Cn ^ 2)) * lapSum (n + 1) S ^ 2 := by
          rw [heq]
          refine le_trans hord2 ?_
          have h1 := hrawlap_grad_le
          have h2 := hgrad2n_le
          have hL := hlapSum_nn (n + 1)
          have hb1 : ‖rawTensorConnLapSmooth (I := I) g 0 (s + 2 * n)
              (iteratedCovGrad g 0 s (2 * n) S)‖ ^ 2 ≤ P ^ 2 * lapSum (n + 1) S ^ 2 := by
            have hnn := norm_nonneg (rawTensorConnLapSmooth (I := I) g 0 (s + 2 * n)
              (iteratedCovGrad g 0 s (2 * n) S))
            nlinarith [h1, mul_nonneg hP_nn hL]
          have hb2 : ‖iteratedCovGrad g 0 s (2 * n) S‖ ^ 2 ≤ Cn ^ 2 * lapSum (n + 1) S ^ 2 := by
            have hnn := norm_nonneg (iteratedCovGrad g 0 s (2 * n) S)
            nlinarith [h2, mul_nonneg hCn_nn hL]
          nlinarith [hb1, hb2, hCg_nn, mul_nonneg hCg_nn
            (add_nonneg (sq_nonneg P) (sq_nonneg Cn))]
        have hle : ‖iteratedCovGrad g 0 s (2 * n + 2) S‖ ≤ C2 * lapSum (n + 1) S := by
          rw [hC2_def]
          have hfinal : ‖iteratedCovGrad g 0 s (2 * n + 2) S‖ ^ 2 ≤
              (Real.sqrt (Cg * (P ^ 2 + Cn ^ 2)) * lapSum (n + 1) S) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt
              (mul_nonneg hCg_nn (add_nonneg (sq_nonneg P) (sq_nonneg Cn)))]
            exact hsq
          exact le_of_sq_le_sq hfinal
            (mul_nonneg (Real.sqrt_nonneg _) (hlapSum_nn (n + 1)))
        calc ‖iteratedCovGrad g 0 s (2 * n + 2) S‖
            ≤ C2 * lapSum (n + 1) S := hle
          _ ≤ max Cn (max C2 C1) * lapSum (n + 1) S :=
              mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_right _ _))
                (hlapSum_nn (n + 1))
          _ = max Cn (max C2 C1) *
                ∑ i ∈ Finset.range (n + 1 + 1), ‖rawTensorConnLapIter (I := I) g 0 s i S‖ := by
              simp only [hlapSum_def]

set_option linter.unusedSectionVars false in

theorem exists_tensorPouSobolevHsNorm_k_le_sum_rawConnLapIter
    (g : SmoothRiemannianMetric I M) (s k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : SmoothCcTensor g 0 s,
        (tensorPouSobolevHsNorm (I := I) (M := M) g k T).toReal ≤
          C * ∑ j ∈ Finset.range (k + 1),
            ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g 0 s j T)‖ := by
  classical
  obtain ⟨Cb, hCb, hbridge⟩ :=
    exists_tensorPouSobolevHsNorm_toReal_le_iteratedCovGrad_tensorL2Norm_sum
      (I := I) (M := M) g 0 s k
  obtain ⟨Cg, hCg, hgrad⟩ :=
    exists_iteratedCovGrad_l2Norm_le_sum_rawConnLapIter (I := I) (M := M) g s k
  refine ⟨Cb * ((2 * k + 1 : ℕ) : ℝ) * Cg, by positivity, fun T => ?_⟩
  
  set LapSum : ℝ := ∑ i ∈ Finset.range (k + 1),
    tensorL2Norm (I := I) (M := M) g 0 s
      (rawTensorConnLapIter (I := I) g 0 s i T).toFun with hLapSum_def
  set toL2Sum : ℝ := ∑ j ∈ Finset.range (k + 1),
    ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g 0 s j T)‖ with htoL2Sum_def
  have hLapSum_nn : 0 ≤ LapSum :=
    Finset.sum_nonneg (fun i _ => tensorL2Norm_nonneg (I := I) (M := M) g 0 s _)
  
  have hsum_eq : LapSum = toL2Sum := by
    rw [hLapSum_def, htoL2Sum_def]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [SmoothCcTensor.norm_toL2,
      tensorL2Norm_toFun_eq_norm (I := I) (M := M) g (rawTensorConnLapIter (I := I) g 0 s i T)]
  
  set Gsum : ℝ := ∑ j ∈ Finset.range (2 * k + 1),
    tensorL2Norm (I := I) (M := M) g 0 (s + j) (iteratedCovGrad g 0 s j T).toFun with hGsum_def
  have hbridge_T : (tensorPouSobolevHsNorm (I := I) (M := M) g k T).toReal ≤ Cb * Gsum :=
    hbridge T
  
  have hterm_le : ∀ j ∈ Finset.range (2 * k + 1),
      tensorL2Norm (I := I) (M := M) g 0 (s + j) (iteratedCovGrad g 0 s j T).toFun ≤
        Cg * LapSum := by
    intro j hj
    have hjle : j ≤ 2 * k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [hLapSum_def]
    exact hgrad j hjle T
  
  have hGsum_le : Gsum ≤ ((2 * k + 1 : ℕ) : ℝ) * (Cg * LapSum) := by
    calc Gsum ≤ ∑ _j ∈ Finset.range (2 * k + 1), (Cg * LapSum) :=
            Finset.sum_le_sum hterm_le
      _ = (Finset.range (2 * k + 1)).card • (Cg * LapSum) := by rw [Finset.sum_const]
      _ = ((2 * k + 1 : ℕ) : ℝ) * (Cg * LapSum) := by
            rw [Finset.card_range, nsmul_eq_mul]
  
  calc (tensorPouSobolevHsNorm (I := I) (M := M) g k T).toReal
      ≤ Cb * Gsum := hbridge_T
    _ ≤ Cb * (((2 * k + 1 : ℕ) : ℝ) * (Cg * LapSum)) :=
        mul_le_mul_of_nonneg_left hGsum_le hCb
    _ = Cb * ((2 * k + 1 : ℕ) : ℝ) * Cg * LapSum := by ring
    _ = Cb * ((2 * k + 1 : ℕ) : ℝ) * Cg * toL2Sum := by rw [hsum_eq]

end Connection
end Integral
end DifferentialGeometry

end
