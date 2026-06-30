import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmAppCc
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciDeTurckArmCoeffPerOrderJetTower
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RemainderCoeffPerOrderJetEnvelopes
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckPrincipalCometricExtraction

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (linearizedRicciArm0BaseCoeff linearizedRicciArm1BaseCoeff ricciArmPrincipalCoeff
    traceHessianCoeff traceHessianCoeff_toSection traceHessianFib traceHessianSlotPerm
    domDomCongrFib domDomCongrFib_apply deTurckPrincipalCometricCoeff
    deTurckPrincipalCometricCoeff_toSection_clm_eq
    deTurckPrincipalCometricCoeff_perOrder_rfns_le_gInvDiffSlotCoeff
    reindexCoeffGen reindexCoeffGen_toSection reindexCoeffFibGen_apply)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (realizedFam)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem linearizedRicciArm0BaseCoeff_realizedFam_jetL2_perOrder_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s)‖ ^ 2 ≤ P i :=
  sorry

theorem linearizedRicciArm1BaseCoeff_realizedFam_jetL2_perOrder_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s)‖ ^ 2 ≤ P i :=
  sorry

theorem ricciArmPrincipalCoeff_sub_background_perOrder_rfns_le_gInvDiffSlotCoeff_rfns
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 4 2 i
              (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
                - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)).toSection x) ≤
          C i * ∑ j ∈ Finset.range (i + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) :=
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeff_sub_perOrder_rfns_le_gInvDiffSlotCoeff
    g₀

theorem ricciArmPrincipalCoeff_sub_background_jetL2_le_gInvDiffSlotCoeff_jetL2
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (i : ℕ),
        ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
              - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤
          C i * ∑ j ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 := by
  obtain ⟨C, hC_nn, hP⟩ :=
    ricciArmPrincipalCoeff_sub_background_perOrder_rfns_le_gInvDiffSlotCoeff_rfns
      (I := I) (M := M) g₀
  refine ⟨C, hC_nn, ?_⟩
  intro g₁ i
  have hF_int : MeasureTheory.Integrable
      (fun x => C i * ∑ j ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (MeasureTheory.integrable_finset_sum (Finset.range (i + 1))
      (fun j _ => integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 2 (2 + j)
        (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)))).const_mul (C i)
  have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 4 (2 + i)
    (iteratedCovGrad (I := I) g₀ 4 2 i
      (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
        - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀))
    (fun x => C i * ∑ j ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x))
    hF_int (fun x => hP g₁ i x)
  refine le_trans key (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul]
  congr 1
  rw [MeasureTheory.integral_finset_sum (Finset.range (i + 1))
    (fun j _ => integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 2 (2 + j)
      (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [SmoothCcTensor.norm_def (I := I) (M := M)
    (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁))]
  exact (tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 2 (2 + j)
    (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁))).symm

set_option linter.unusedVariables false in
theorem ricciArmPrincipalCoeff_realizedFam_sub_background_jetL2_perOrder_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ D : ℕ → ℝ, (∀ i, 0 ≤ D i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (ricciArmPrincipalCoeff (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s)
                - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤ D i := by
  obtain ⟨K, hK_nn, hK⟩ :=
    gInvDiffSlotCoeff_realizedFam_perOrder_l2_ballUniform (I := I) g₀ a ha_super hR hδ₀
  obtain ⟨C, hC_nn, hC⟩ :=
    ricciArmPrincipalCoeff_sub_background_jetL2_le_gInvDiffSlotCoeff_jetL2 (I := I) (M := M) g₀
  refine ⟨fun i => C i * ∑ j ∈ Finset.range (i + 1), K j,
    fun i => mul_nonneg (hC_nn i) (Finset.sum_nonneg fun j _ => hK_nn j), ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i hi s hs
  calc ‖iteratedCovGrad (I := I) g₀ 4 2 i
          (ricciArmPrincipalCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s)
            - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2
      ≤ C i * ∑ j ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 2 2 j
            (gInvDiffSlotCoeff (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 :=
        hC (realizedFam (I := I) g₀ T T' hδ hδ' s) i
    _ ≤ C i * ∑ j ∈ Finset.range (i + 1), K j := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum ?_) (hC_nn i)
        intro j hj
        exact hK T T' hδ_le hδ hδ'_le hδ' hTball hT'ball j
          (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hi) s hs

set_option linter.unusedVariables false in
theorem ricciArmPrincipalCoeff_realizedFam_jetL2_perOrder_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (ricciArmPrincipalCoeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 ≤ P i := by
  obtain ⟨D, hD_nn, hD⟩ :=
    ricciArmPrincipalCoeff_realizedFam_sub_background_jetL2_perOrder_ballUniform
      (I := I) g₀ a ha_super hR hδ₀
  refine ⟨fun i => 2 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
        (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 + 2 * D i,
    fun i => add_nonneg (by positivity) (by linarith [hD_nn i]), ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i hi s hs
  have hq2 := hD T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i hi s hs
  set A := ricciArmPrincipalCoeff (I := I) (M := M) g₀
    (realizedFam (I := I) g₀ T T' hδ hδ' s) with hA
  set B := ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀ with hB
  have hgrad : iteratedCovGrad (I := I) g₀ 4 2 i A
      = iteratedCovGrad (I := I) g₀ 4 2 i B + iteratedCovGrad (I := I) g₀ 4 2 i (A - B) := by
    have h := iteratedCovGrad_add (I := I) g₀ 4 2 i B (A - B)
    have hBA : B + (A - B) = A := by abel
    rw [hBA] at h
    exact h
  have htri : ‖iteratedCovGrad (I := I) g₀ 4 2 i A‖ ≤
      ‖iteratedCovGrad (I := I) g₀ 4 2 i B‖ + ‖iteratedCovGrad (I := I) g₀ 4 2 i (A - B)‖ := by
    rw [hgrad]
    exact norm_add_le _ _
  have hp_nn : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 4 2 i B‖ := norm_nonneg _
  have hq_nn : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 4 2 i (A - B)‖ := norm_nonneg _
  have hA_nn : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 4 2 i A‖ := norm_nonneg _
  nlinarith [htri, hq2, hp_nn, hq_nn, hA_nn,
    sq_nonneg (‖iteratedCovGrad (I := I) g₀ 4 2 i B‖
      - ‖iteratedCovGrad (I := I) g₀ 4 2 i (A - B)‖),
    mul_le_mul htri htri hA_nn (add_nonneg hp_nn hq_nn)]

set_option linter.style.setOption false in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem traceHessianCoeff_sub_eq_reindex_deTurckPrincipalCometricCoeff
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

theorem traceHessianCoeff_sub_background_perOrder_rfns_le_gInvDiffSlotCoeff_rfns
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 4 2 i
              (traceHessianCoeff (I := I) (M := M) g₀ g₁
                - traceHessianCoeff (I := I) (M := M) g₀ g₀)).toSection x) ≤
          C i * ∑ j ∈ Finset.range (i + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) := by
  obtain ⟨C, hC_nn, hC⟩ :=
    deTurckPrincipalCometricCoeff_perOrder_rfns_le_gInvDiffSlotCoeff (I := I) (M := M) g₀
  refine ⟨C, hC_nn, ?_⟩
  intro g₁ i x
  rw [traceHessianCoeff_sub_eq_reindex_deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁,
    rfns_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 4 2
      (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁) traceHessianSlotPerm i x]
  exact hC g₁ i x

theorem traceHessianCoeff_sub_background_jetL2_le_gInvDiffSlotCoeff_jetL2
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (i : ℕ),
        ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (traceHessianCoeff (I := I) (M := M) g₀ g₁
              - traceHessianCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤
          C i * ∑ j ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 := by
  obtain ⟨C, hC_nn, hP⟩ :=
    traceHessianCoeff_sub_background_perOrder_rfns_le_gInvDiffSlotCoeff_rfns
      (I := I) (M := M) g₀
  refine ⟨C, hC_nn, ?_⟩
  intro g₁ i
  have hF_int : MeasureTheory.Integrable
      (fun x => C i * ∑ j ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (MeasureTheory.integrable_finset_sum (Finset.range (i + 1))
      (fun j _ => integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 2 (2 + j)
        (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)))).const_mul (C i)
  have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 4 (2 + i)
    (iteratedCovGrad (I := I) g₀ 4 2 i
      (traceHessianCoeff (I := I) (M := M) g₀ g₁
        - traceHessianCoeff (I := I) (M := M) g₀ g₀))
    (fun x => C i * ∑ j ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x))
    hF_int (fun x => hP g₁ i x)
  refine le_trans key (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul]
  congr 1
  rw [MeasureTheory.integral_finset_sum (Finset.range (i + 1))
    (fun j _ => integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 2 (2 + j)
      (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [SmoothCcTensor.norm_def (I := I) (M := M)
    (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁))]
  exact (tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 2 (2 + j)
    (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁))).symm

set_option linter.unusedVariables false in
theorem traceHessianCoeff_realizedFam_sub_background_jetL2_perOrder_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ D : ℕ → ℝ, (∀ i, 0 ≤ D i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (traceHessianCoeff (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s)
                - traceHessianCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤ D i := by
  obtain ⟨K, hK_nn, hK⟩ :=
    gInvDiffSlotCoeff_realizedFam_perOrder_l2_ballUniform (I := I) g₀ a ha_super hR hδ₀
  obtain ⟨C, hC_nn, hC⟩ :=
    traceHessianCoeff_sub_background_jetL2_le_gInvDiffSlotCoeff_jetL2 (I := I) (M := M) g₀
  refine ⟨fun i => C i * ∑ j ∈ Finset.range (i + 1), K j,
    fun i => mul_nonneg (hC_nn i) (Finset.sum_nonneg fun j _ => hK_nn j), ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i hi s hs
  calc ‖iteratedCovGrad (I := I) g₀ 4 2 i
          (traceHessianCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s)
            - traceHessianCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2
      ≤ C i * ∑ j ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 2 2 j
            (gInvDiffSlotCoeff (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 :=
        hC (realizedFam (I := I) g₀ T T' hδ hδ' s) i
    _ ≤ C i * ∑ j ∈ Finset.range (i + 1), K j := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum ?_) (hC_nn i)
        intro j hj
        exact hK T T' hδ_le hδ hδ'_le hδ' hTball hT'ball j
          (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hi) s hs

set_option linter.unusedVariables false in
theorem traceHessianCoeff_realizedFam_jetL2_perOrder_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (traceHessianCoeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 ≤ P i := by
  obtain ⟨D, hD_nn, hD⟩ :=
    traceHessianCoeff_realizedFam_sub_background_jetL2_perOrder_ballUniform
      (I := I) g₀ a ha_super hR hδ₀
  refine ⟨fun i => 2 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
        (traceHessianCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 + 2 * D i,
    fun i => add_nonneg (by positivity) (by linarith [hD_nn i]), ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i hi s hs
  have hq2 := hD T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i hi s hs
  set A := traceHessianCoeff (I := I) (M := M) g₀
    (realizedFam (I := I) g₀ T T' hδ hδ' s) with hA
  set B := traceHessianCoeff (I := I) (M := M) g₀ g₀ with hB
  have hgrad : iteratedCovGrad (I := I) g₀ 4 2 i A
      = iteratedCovGrad (I := I) g₀ 4 2 i B + iteratedCovGrad (I := I) g₀ 4 2 i (A - B) := by
    have h := iteratedCovGrad_add (I := I) g₀ 4 2 i B (A - B)
    have hBA : B + (A - B) = A := by abel
    rw [hBA] at h
    exact h
  have htri : ‖iteratedCovGrad (I := I) g₀ 4 2 i A‖ ≤
      ‖iteratedCovGrad (I := I) g₀ 4 2 i B‖ + ‖iteratedCovGrad (I := I) g₀ 4 2 i (A - B)‖ := by
    rw [hgrad]
    exact norm_add_le _ _
  have hp_nn : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 4 2 i B‖ := norm_nonneg _
  have hq_nn : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 4 2 i (A - B)‖ := norm_nonneg _
  have hA_nn : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 4 2 i A‖ := norm_nonneg _
  nlinarith [htri, hq2, hp_nn, hq_nn, hA_nn,
    sq_nonneg (‖iteratedCovGrad (I := I) g₀ 4 2 i B‖
      - ‖iteratedCovGrad (I := I) g₀ 4 2 i (A - B)‖),
    mul_le_mul htri htri hA_nn (add_nonneg hp_nn hq_nn)]

end DifferentialGeometry.Integral.Connection

end
