import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CometricTraceSelfBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckPrincipalCometricExtraction

/-!
# Dimension-only principal coefficient bounds

This module replaces the metricwise compactness constants in the principal
Ricci--DeTurck coefficient estimates by explicit constants depending only on
the model-space dimension.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- Dimension-only coefficient for the DeTurck principal jet of order `i`. -/
def pccJetC (i : ℕ) : ℝ :=
  appCcGdiag (E := E) i * (Module.finrank ℝ E : ℝ) ^ 8

/-- Dimension-only coefficient for the Ricci principal-difference jet of order `i`. -/
def ricciJetC (i : ℕ) : ℝ := (10 / 4 : ℝ) * pccJetC (E := E) i

/-- The DeTurck dimension-only jet coefficient is nonnegative. -/
theorem pccJetC_nonneg (i : ℕ) : 0 ≤ pccJetC (E := E) i := by
  exact mul_nonneg (appCcGdiag_nonneg (E := E) i) (by positivity)

/-- The Ricci dimension-only jet coefficient is nonnegative. -/
theorem ricciJetC_nonneg (i : ℕ) : 0 ≤ ricciJetC (E := E) i := by
  exact mul_nonneg (by norm_num) (pccJetC_nonneg (E := E) i)

/-- The DeTurck principal coefficient has a pointwise jet bound whose constant
depends only on dimension. -/
theorem pcc_rfns_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)).toSection x) ≤
      pccJetC (E := E) i * ∑ j ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 2 2 j
            (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) := by
  have h := pcc_rfns_of_bound (I := I) (M := M) g₀ g₁
    (K := (Module.finrank ℝ E : ℝ) ^ 6) (by positivity)
    (fun b => cometricTrace_rfns (I := I) (M := M) g₀ b) i x
  convert h using 1
  simp only [pccJetC]
  ring

/-- The Ricci principal-coefficient difference has a pointwise jet bound whose
constant depends only on dimension. -/
theorem ricci_rfns_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 4 2 i
          (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
            - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)).toSection x) ≤
      ricciJetC (E := E) i * ∑ j ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 2 2 j
            (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) := by
  refine (ricci_sub_rfns (I := I) (M := M) g₀ g₁ i x).trans ?_
  calc
    _ ≤ (10 / 4 : ℝ) * (pccJetC (E := E) i *
          ∑ j ∈ Finset.range (i + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 2 2 j
                (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x)) :=
      mul_le_mul_of_nonneg_left (pcc_rfns_le (I := I) (M := M) g₀ g₁ i x) (by norm_num)
    _ = ricciJetC (E := E) i * ∑ j ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 2 2 j
              (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) := by
      simp only [ricciJetC]
      ring

set_option linter.style.setOption false in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
/-- The trace-Hessian coefficient difference is the canonical slot reindexing
of the DeTurck principal coefficient. -/
theorem traceCoeff_sub_eq
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    traceHessianCoeff (I := I) (M := M) g₀ g₁ -
        traceHessianCoeff (I := I) (M := M) g₀ g₀ =
      reindexCoeffGen (I := I) (M := M) g₀ 4 2
        (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)
        traceHessianSlotPerm := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    traceHessianCoeff_toSection, traceHessianCoeff_toSection,
    reindexCoeffGen_toSection]
  apply ContinuousLinearMap.ext
  intro D
  rw [ContinuousLinearMap.sub_apply, reindexCoeffFibGen_apply,
    deTurckPrincipalCometricCoeff_toSection_clm_eq,
    ContinuousLinearMap.sub_apply, traceHessianFib, traceHessianFib,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    domDomCongrFib_apply]

/-- The trace-Hessian coefficient difference has the same dimension-only
pointwise jet bound as the DeTurck principal coefficient. -/
theorem trace_rfns_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 4 2 i
          (traceHessianCoeff (I := I) (M := M) g₀ g₁ -
            traceHessianCoeff (I := I) (M := M) g₀ g₀)).toSection x) ≤
      pccJetC (E := E) i * ∑ j ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 2 2 j
            (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) := by
  rw [traceCoeff_sub_eq (I := I) (M := M) g₀ g₁,
    rfns_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 4 2
      (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)
      traceHessianSlotPerm i x]
  exact pcc_rfns_le (I := I) (M := M) g₀ g₁ i x

private theorem jetL2_of_rfns
    (g : SmoothRiemannianMetric I M) (A : SmoothCcTensor g 4 2)
    (B : SmoothCcTensor g 2 2) (C : ℝ) (i : ℕ)
    (h : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 4 (2 + i) x
          ((iteratedCovGrad (I := I) g 4 2 i A).toSection x) ≤
        C * ∑ j ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g 2 (2 + j) x
            ((iteratedCovGrad (I := I) g 2 2 j B).toSection x)) :
    ‖iteratedCovGrad (I := I) g 4 2 i A‖ ^ 2 ≤
      C * ∑ j ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g 2 2 j B‖ ^ 2 := by
  have hF_int : MeasureTheory.Integrable
      (fun x => C * ∑ j ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g 2 (2 + j) x
          ((iteratedCovGrad (I := I) g 2 2 j B).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    (MeasureTheory.integrable_finset_sum (Finset.range (i + 1))
      (fun j _ => integrable_riemannianFiberNormSq_toSection
        (I := I) (M := M) g 2 (2 + j)
        (iteratedCovGrad (I := I) g 2 2 j B))).const_mul C
  have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g 4 (2 + i) (iteratedCovGrad (I := I) g 4 2 i A)
    (fun x => C * ∑ j ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g 2 (2 + j) x
        ((iteratedCovGrad (I := I) g 2 2 j B).toSection x)) hF_int h
  refine le_trans key (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul]
  congr 1
  rw [MeasureTheory.integral_finset_sum (Finset.range (i + 1))
    (fun j _ => integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g 2 (2 + j)
      (iteratedCovGrad (I := I) g 2 2 j B))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [SmoothCcTensor.norm_def (I := I) (M := M)
    (iteratedCovGrad (I := I) g 2 2 j B)]
  exact (tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
    (I := I) (M := M) g 2 (2 + j)
    (iteratedCovGrad (I := I) g 2 2 j B)).symm

/-- The DeTurck principal coefficient has an `L²` jet bound whose coefficient
depends only on dimension. -/
theorem pcc_l2_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 4 2 i
        (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
      pccJetC (E := E) i * ∑ j ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 2 2 j
          (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 :=
  jetL2_of_rfns (I := I) (M := M) g₀
    (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)
    (gInvDiffSlotCoeff (I := I) g₀ g₁) (pccJetC (E := E) i) i
    (pcc_rfns_le (I := I) (M := M) g₀ g₁ i)

/-- The Ricci principal-coefficient difference has an `L²` jet bound whose
coefficient depends only on dimension. -/
theorem ricci_l2_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 4 2 i
        (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤
      ricciJetC (E := E) i * ∑ j ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 2 2 j
          (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 :=
  jetL2_of_rfns (I := I) (M := M) g₀
    (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁ -
      ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)
    (gInvDiffSlotCoeff (I := I) g₀ g₁) (ricciJetC (E := E) i) i
    (ricci_rfns_le (I := I) (M := M) g₀ g₁ i)

/-- The trace-Hessian coefficient difference has an `L²` jet bound whose
coefficient depends only on dimension. -/
theorem trace_l2_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 4 2 i
        (traceHessianCoeff (I := I) (M := M) g₀ g₁ -
          traceHessianCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤
      pccJetC (E := E) i * ∑ j ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 2 2 j
          (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 :=
  jetL2_of_rfns (I := I) (M := M) g₀
    (traceHessianCoeff (I := I) (M := M) g₀ g₁ -
      traceHessianCoeff (I := I) (M := M) g₀ g₀)
    (gInvDiffSlotCoeff (I := I) g₀ g₁) (pccJetC (E := E) i) i
    (trace_rfns_le (I := I) (M := M) g₀ g₁ i)

end DifferentialGeometry.Integral.Connection

end
