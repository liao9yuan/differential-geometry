import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SmoothParametricCoeffIntegral
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Algebra
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqTensorInnerBridge
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Seminorm

noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open MeasureTheory Set Filter Bundle Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace L2

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (pathIntegralCoeffField
  pathIntegralCoeffField_toSection pathIntegralFib pathIntegralFib_toModel)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

theorem tensorPointwiseNorm_add_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (S T : TensorRSModel r s ℝ E) :
    tensorPointwiseNorm (I := I) (M := M) g r s x (S + T) ≤
      tensorPointwiseNorm (I := I) (M := M) g r s x S +
        tensorPointwiseNorm (I := I) (M := M) g r s x T := by
  unfold tensorPointwiseNorm
  set qSS := tensorInnerPointwise (I := I) (M := M) g r s x S S with hqSS
  set qTT := tensorInnerPointwise (I := I) (M := M) g r s x T T with hqTT
  set qST := tensorInnerPointwise (I := I) (M := M) g r s x S T with hqST
  have hSS_nn : 0 ≤ qSS := tensorInnerPointwise_nonneg (I := I) (M := M) g r s x S
  have hTT_nn : 0 ≤ qTT := tensorInnerPointwise_nonneg (I := I) (M := M) g r s x T
  have hexpand : tensorInnerPointwise (I := I) (M := M) g r s x (S + T) (S + T) =
      qSS + qST + (qST + qTT) := by
    rw [tensorInnerPointwise_add_left, tensorInnerPointwise_add_right,
      tensorInnerPointwise_add_right]
    have hcomm : tensorInnerPointwise (I := I) (M := M) g r s x T S = qST := by
      rw [hqST, tensorInnerPointwise_symm]
    rw [hcomm]
  have hcs : |qST| ≤ Real.sqrt qSS * Real.sqrt qTT := by
    have := abs_tensorInnerPointwise_le_mul (I := I) (M := M) g r s x S T
    simpa only [tensorPointwiseNorm] using this
  have hqST_le : qST ≤ Real.sqrt qSS * Real.sqrt qTT :=
    le_trans (le_abs_self qST) hcs
  have hsumeq : Real.sqrt qSS + Real.sqrt qTT =
      Real.sqrt ((Real.sqrt qSS + Real.sqrt qTT) ^ 2) :=
    (Real.sqrt_sq (by positivity)).symm
  rw [hexpand, hsumeq]
  refine Real.sqrt_le_sqrt ?_
  have hsq : (Real.sqrt qSS + Real.sqrt qTT) ^ 2 =
      qSS + 2 * (Real.sqrt qSS * Real.sqrt qTT) + qTT := by
    rw [add_pow_two, Real.sq_sqrt hSS_nn, Real.sq_sqrt hTT_nn]; ring
  rw [hsq]
  nlinarith [hqST_le]

theorem tensorPointwiseNorm_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (a : ℝ) (S : TensorRSModel r s ℝ E) :
    tensorPointwiseNorm (I := I) (M := M) g r s x (a • S) =
      |a| * tensorPointwiseNorm (I := I) (M := M) g r s x S := by
  haveI : NormedSpace ℝ (TensorRSModel r s ℝ E) :=
    Tensor0SBundle.tensorRSModel_normedSpace r s
  unfold tensorPointwiseNorm
  rw [tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
  rw [show a * (a * tensorInnerPointwise (I := I) (M := M) g r s x S S) =
      a ^ 2 * tensorInnerPointwise (I := I) (M := M) g r s x S S from by ring]
  rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]

theorem tensorPointwiseNorm_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (S : TensorRSModel r s ℝ E) :
    0 ≤ tensorPointwiseNorm (I := I) (M := M) g r s x S :=
  Real.sqrt_nonneg _

def tensorPointwiseSeminorm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) :
    Seminorm ℝ (TensorRSModel r s ℝ E) :=
  Seminorm.of (tensorPointwiseNorm (I := I) (M := M) g r s x)
    (tensorPointwiseNorm_add_le (I := I) (M := M) g r s x)
    (fun a S => by
      rw [tensorPointwiseNorm_smul (I := I) (M := M) g r s x a S, Real.norm_eq_abs])

@[simp] theorem tensorPointwiseSeminorm_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (S : TensorRSModel r s ℝ E) :
    tensorPointwiseSeminorm (I := I) (M := M) g r s x S =
      tensorPointwiseNorm (I := I) (M := M) g r s x S := rfl

theorem tensorPointwiseNorm_continuous
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) :
    Continuous (tensorPointwiseNorm (I := I) (M := M) g r s x) :=
  sorry

theorem tensorPointwiseNorm_intervalIntegral_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (f : ℝ → TensorRSModel r s ℝ E)
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1)) :
    tensorPointwiseNorm (I := I) (M := M) g r s x (∫ t in (0 : ℝ)..1, f t) ≤
      ∫ t in (0 : ℝ)..1, tensorPointwiseNorm (I := I) (M := M) g r s x (f t) := by
  classical
  set p : Seminorm ℝ (TensorRSModel r s ℝ E) :=
    tensorPointwiseSeminorm (I := I) (M := M) g r s x with hp_def
  have hp_cont : Continuous (p : TensorRSModel r s ℝ E → ℝ) := by
    have hpeq : (p : TensorRSModel r s ℝ E → ℝ) =
        tensorPointwiseNorm (I := I) (M := M) g r s x := rfl
    rw [hpeq]; exact tensorPointwiseNorm_continuous (I := I) (M := M) g r s x
  haveI hprob : IsProbabilityMeasure (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc]
    norm_num
  have hf_meas : ContinuousOn f (Set.Ioc (0 : ℝ) 1) := hf.mono Set.Ioc_subset_Icc_self
  have hf_int : Integrable f (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    (hf.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hpf_int : Integrable (fun t => p (f t)) (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    ((hp_cont.comp_continuousOn hf).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hjensen :
      p (∫ t, f t ∂(volume.restrict (Set.Ioc (0:ℝ) 1))) ≤
        ∫ t, p (f t) ∂(volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    p.convexOn.map_integral_le hp_cont.continuousOn isClosed_univ
      (Filter.Eventually.of_forall (fun _ => Set.mem_univ _)) hf_int hpf_int
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact hjensen

theorem riemannianFiberNormSq_pathIntegralCoeffField_le_sq
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ) (hS : IsOpen S)
    (hSI : Set.uIcc (0:ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (x : M) (Λ : ℝ) (hΛ_nn : 0 ≤ Λ)
    (hcont : ContinuousOn (fun t : ℝ => TensorRSSpace.toModel ((Φ t).toSection x))
      (Set.Icc (0 : ℝ) 1))
    (hsup : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ r s x ((Φ t).toSection x)) ≤ Λ) :
    riemannianFiberNormSq (I := I) (M := M) g₀ r s x
        ((pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint).toSection x) ≤ Λ ^ 2 := by
  classical
  set f : ℝ → TensorRSModel r s ℝ E :=
    fun t => TensorRSSpace.toModel ((Φ t).toSection x) with hf_def
  have hfns : riemannianFiberNormSq (I := I) (M := M) g₀ r s x
      ((pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint).toSection x) =
      tensorPointwiseNorm (I := I) (M := M) g₀ r s x (∫ t in (0 : ℝ)..1, f t) ^ 2 := by
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise]
    rw [pathIntegralCoeffField_toSection, pathIntegralFib_toModel]
    unfold tensorPointwiseNorm
    rw [Real.sq_sqrt (tensorInnerPointwise_nonneg (I := I) (M := M) g₀ r s x _)]
  rw [hfns]
  have hbound :
      tensorPointwiseNorm (I := I) (M := M) g₀ r s x (∫ t in (0 : ℝ)..1, f t) ≤ Λ := by
    refine le_trans (tensorPointwiseNorm_intervalIntegral_le (I := I) (M := M) g₀ r s x f hcont) ?_
    have hpt : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        tensorPointwiseNorm (I := I) (M := M) g₀ r s x (f t) ≤ Λ := by
      intro t ht
      have hfns_t : tensorPointwiseNorm (I := I) (M := M) g₀ r s x (f t) =
          Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ r s x ((Φ t).toSection x)) := by
        rw [riemannianFiberNormSq_eq_tensorInnerPointwise]; rfl
      rw [hfns_t]; exact hsup t ht
    have hle : (∫ t in (0 : ℝ)..1, tensorPointwiseNorm (I := I) (M := M) g₀ r s x (f t)) ≤
        ∫ _t in (0 : ℝ)..1, Λ := by
      refine intervalIntegral.integral_mono_on (by norm_num) ?_ intervalIntegrable_const ?_
      · exact ((tensorPointwiseNorm_continuous (I := I) (M := M) g₀ r s x).comp_continuousOn
          hcont).intervalIntegrable_of_Icc (by norm_num)
      · exact fun t ht => hpt t ht
    refine le_trans hle ?_
    rw [intervalIntegral.integral_const]; simp
  have hsqnn : 0 ≤ tensorPointwiseNorm (I := I) (M := M) g₀ r s x (∫ t in (0 : ℝ)..1, f t) :=
    tensorPointwiseNorm_nonneg (I := I) (M := M) g₀ r s x _
  nlinarith [hbound, hsqnn, hΛ_nn]

end L2
end Integral
end DifferentialGeometry

end
