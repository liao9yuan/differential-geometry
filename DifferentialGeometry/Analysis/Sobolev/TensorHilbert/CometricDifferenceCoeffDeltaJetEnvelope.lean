import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciDeTurckArmCoeffPerOrderJetTower
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckPrincipalCometricExtraction

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (ricciArmPrincipalCoeffPure deTurckPrincipalCometricCoeff
    riemannianFiberNormSq_deTurckPrincipalCometricCoeff_le)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option linter.unusedVariables false in
theorem deTurckPrincipalCometricCoeff_realizedFam_perOrder_rfns_pointwise_singleOrder
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_le : δ ≤ δ₀)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (hTball : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R)
    (hT'ball : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R)
    (i : ℕ) (hi : i ≤ a) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s))).toSection x) ≤
      coeffPerOrderJetBound (E := E) R δ₀ 4 i :=
  sorry

set_option linter.unusedVariables false in
theorem exists_cometricDoubleTraceDiff_delta_jetL2_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (hδ₀_nn : 0 ≤ δ₀) :
    ∃ ΛC Γ : ℝ, 0 ≤ ΛC ∧ 0 ≤ Γ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
        (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T x v w = ccTensorBilin (I := I) g₀ T x w v)
        (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T' x v w = ccTensorBilin (I := I) g₀ T' x w v),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
              ((ricciArmPrincipalCoeffPure (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s)
                - ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₀).toSection x) ≤
            (ΛC * δ₀) ^ 2) ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s)
                - ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤ Γ ^ 2) := by
  classical
  have hpos : (0 : ℝ) < 1 - δ₀ := by linarith
  refine ⟨(Module.finrank ℝ E : ℝ) ^ 2 / (1 - δ₀),
    Real.sqrt ((∑ i ∈ Finset.range (a + 1), coeffPerOrderJetBound (E := E) R δ₀ 4 i) *
      (riemannianVolumeMeasure (I := I) (M := M) g₀ Set.univ).toReal),
    ?_, ?_, ?_⟩
  · exact div_nonneg (by positivity) hpos.le
  · exact Real.sqrt_nonneg _
  · intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTsymm hT'symm hTball hT'ball s hs
    have hs0 : (0 : ℝ) ≤ s := hs.1
    have hs1 : s ≤ 1 := hs.2
    have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
    have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
    have hrfl : (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s)
        - ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₀) =
        deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) := rfl
    refine ⟨?_, ?_⟩
    · intro x
      rw [hrfl]
      have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
        Icc_subset_realizedSmallSet hδ_lt hδ'_lt hs
      have htie : ∀ (y : M) (v w : TangentSpace I y),
          (realizedFam (I := I) g₀ T T' hδ hδ' s).inner y v w =
            g₀.inner y v w +
              ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) y v w :=
        fun y v w => realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ' hs_mem y v w
      have hbnd0 : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s))
          ((1 - s) * δ' + s * δ) :=
        convexPerturbation_gFibreOpBound (I := I) g₀ T T' hδ hδ' hs0 hs1
      have hδs_le : (1 - s) * δ' + s * δ ≤ δ₀ := by
        have h1ms : (0 : ℝ) ≤ 1 - s := by linarith
        nlinarith [mul_nonneg h1ms (sub_nonneg.mpr hδ'_le),
          mul_nonneg hs0 (sub_nonneg.mpr hδ_le)]
      have hbnd : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s)) δ₀ := by
        intro y v w
        refine le_trans (hbnd0 y v w) ?_
        have hsv : (0 : ℝ) ≤ Real.sqrt (g₀.inner y v v) := Real.sqrt_nonneg _
        have hsw : (0 : ℝ) ≤ Real.sqrt (g₀.inner y w w) := Real.sqrt_nonneg _
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hδs_le hsv) hsw
      have hbrick := riemannianFiberNormSq_deTurckPrincipalCometricCoeff_le (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s)
        (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s))
        htie hδ₀ hδ₀_nn hbnd x
      refine le_trans hbrick ?_
      have hfr_pos : 0 < Module.finrank ℝ E := Nat.pos_of_ne_zero (NeZero.ne _)
      have hn1 : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by exact_mod_cast hfr_pos
      have hn0 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := le_trans zero_le_one hn1
      have hn34 : (Module.finrank ℝ E : ℝ) ^ 3 ≤ (Module.finrank ℝ E : ℝ) ^ 4 := by
        nlinarith [pow_nonneg hn0 3, hn1]
      have heq : ((Module.finrank ℝ E : ℝ) ^ 2 / (1 - δ₀) * δ₀) ^ 2 =
          (Module.finrank ℝ E : ℝ) ^ 4 * (δ₀ / (1 - δ₀)) ^ 2 := by
        ring
      rw [heq]
      exact mul_le_mul_of_nonneg_right hn34 (sq_nonneg _)
    · simp only [hrfl]
      set C : SmoothCcTensor g₀ 4 2 :=
        deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) with hC
      have hFULL_nn : (0 : ℝ) ≤
          (∑ i ∈ Finset.range (a + 1), coeffPerOrderJetBound (E := E) R δ₀ 4 i) *
            (riemannianVolumeMeasure (I := I) (M := M) g₀ Set.univ).toReal :=
        mul_nonneg
          (Finset.sum_nonneg (fun i _ => coeffPerOrderJetBound_nonneg R δ₀ hR hδ₀ 4 i))
          ENNReal.toReal_nonneg
      rw [Real.sq_sqrt hFULL_nn]
      have hterm : ∀ i ∈ Finset.range (a + 1),
          ‖iteratedCovGrad (I := I) g₀ 4 2 i C‖ ^ 2 ≤
            coeffPerOrderJetBound (E := E) R δ₀ 4 i *
              (riemannianVolumeMeasure (I := I) (M := M) g₀ Set.univ).toReal := by
        intro i hi
        have hi_le : i ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hpt : ∀ y : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) y
            ((iteratedCovGrad (I := I) g₀ 4 2 i C).toSection y) ≤
              coeffPerOrderJetBound (E := E) R δ₀ 4 i := by
          intro y
          rw [hC]
          exact deTurckPrincipalCometricCoeff_realizedFam_perOrder_rfns_pointwise_singleOrder
            (I := I) g₀ a ha_super hR hδ₀ T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i hi_le s hs y
        exact l2_of_pointwise_rfns_iteratedCovGrad_perOrder (I := I) g₀ 4 i C
          (coeffPerOrderJetBound (E := E) R δ₀ 4 i) hpt
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum hterm

end DifferentialGeometry.Integral.Connection

end
