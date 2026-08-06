import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitz.TameL2

/-!
# Supercritical jet embedding and the covariant-L2 tame remainder chain

Chunk of `DeTurckRemainderTameLipschitz`, split out of the former
46927-line monolith (no longer elaborable in a single Lean
process).  Every declaration is verbatim.  Chunk map, dependency
graph and measured peaks: `DeTurckRemainderTameLipschitz.md`.
-/

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

open DifferentialGeometry.Integral.DivergenceTheorem (chartRiemannTensor extChartAt_target_subset_interior_of_boundaryless)

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (covGrad unitModel smoothCcTensor_ext_of_unitModel unitTensor pathIntegralCoeffField pathIntegralCoeffField_appCc_eq pathIntegralCoeffField_toSection linearizedRicciThreeArmHjoint linearizedRicciThreeArmHcont linearizedRicciThreeArmHjoint_zero exists_linearizedRicci_threeArm_coeffFields ricciTensor_realize_sub_eq_threeArm_appCc linearizedRicciArm0Field linearizedRicciArm1Field linearizedRicciArm2FieldLichnerowicz linearizedRicciArm0BaseCoeff linearizedRicciArm0CorrField linearizedRicciArm1BaseCoeff linearizedRicciArm1CorrField ricciArmPrincipalCoeff traceHessianCoeff linearizedRicci_arm0Field_jointSmooth linearizedRicci_arm1Field_jointSmooth linearizedRicci_arm2FieldLichnerowicz_jointSmooth ricciArmOrder1KoszulCoeff exists_arm1Koszul_realizedFam_rfns_ballUniform cmm_two_basis_expand unitModel_basis_expand_two unitModel_eq_ccTensorBilin_local appCc_zero_left_local symmS symmS_sub ccTensorBilin_symmS iteratedCovGrad_symmS_eq domDomCongrSection riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection)

open DifferentialGeometry.PDE.DeTurck (deTurckVF)

open DifferentialGeometry.PDE.DeTurck.RicciLinearization (realizedSmallSet realizedSmallSet_isOpen Icc_subset_realizedSmallSet linearizedRicciAt ricciTensor_realized_sub_eq_integral_linearizedRicci linearizedRicciAt_eq_deriv_chartSum_on_Ioo realizedRicciChartSum jointContMDiff_toModel_continuous_slice hasDerivAt_realizedRicciChartSum_general realizedFam)

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (symmAbsorbedCoeff symmAbsorbedCoeff_appCc_eq exists_iteratedCovGrad_unitModel_domDomCongrSection symmAbsorbedCoeff_rfns_le symmAbsorbedCoeff_jet_le)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance instCompleteSpaceE_tame : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

namespace DeTurckRemainderTameLipschitz
end DeTurckRemainderTameLipschitz

open DeTurckRemainderTameLipschitz

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem deTurckArmDiff_supercritical_pointwise_jet_le_lowerWindow
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    ∃ Cemb : ℝ, 0 ≤ Cemb ∧
      ∀ (W : SmoothCcTensor g₀ 0 2) (x : M),
        (∑ q ∈ Finset.range 3,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
              ((iteratedCovGrad (I := I) g₀ 0 2 q W).toSection x)) ≤
          Cemb ^ 2 * ∑ i ∈ Finset.range (a + 1 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2 := by
  classical
  set K : ℕ := Module.finrank ℝ E / 2 + 1 with hK_def
  have hK_super : 2 * K > Module.finrank ℝ E + 2 * 0 := by rw [hK_def]; omega
  set L : ℕ := 4 * K + 4 with hL_def
  have hL_le : L ≤ a + 1 := by rw [hL_def, hK_def]; omega
  have hperdeg : ∀ q : ℕ, q ≤ 2 → ∃ Dq : ℝ, 0 ≤ Dq ∧
      ∀ (W : SmoothCcTensor g₀ 0 2) (x : M),
        (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + q) I b) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + q)
        ‖(iteratedCovGrad (I := I) g₀ 0 2 q W).toSection x‖) ≤
          Dq * ∑ j ∈ Finset.range (L + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖ := by
    intro q hq
    obtain ⟨Cemb, hCemb_pos, hCemb⟩ :=
      tensorPouSobolevHilbert_embedding_Ck_gNorm (I := I) (M := M) g₀ 0 (2 + q) K 0 hK_super
    obtain ⟨Cit, hCit_nn, hCit⟩ :=
      iteratedCovGrad_toHs_norm_le (I := I) (M := M) g₀ 0 2 q (2 * K)
    obtain ⟨Crev, hCrev_nn, hCrev⟩ :=
      exists_toHs_norm_le_iteratedCovGrad_tensorL2Norm_sum (I := I) (M := M) g₀ 0 2 (2 * K + q)
    refine ⟨Cemb * Cit * Crev, by positivity, fun W x => ?_⟩
    have hwin : 2 * (2 * K + q) + 1 ≤ L + 1 := by rw [hL_def]; omega
    have hrev : ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2)
        (2 * K + q) W‖ ≤
        Crev * ∑ j ∈ Finset.range (L + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖ := by
      refine le_trans (hCrev W) ?_
      refine mul_le_mul_of_nonneg_left ?_ hCrev_nn
      have hcongr : (∑ j ∈ Finset.range (2 * (2 * K + q) + 1),
          tensorL2Norm (I := I) (M := M) g₀ 0 (2 + j)
            (iteratedCovGrad (I := I) g₀ 0 2 j W).toFun) =
          ∑ j ∈ Finset.range (2 * (2 * K + q) + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖ :=
        Finset.sum_congr rfl
          (fun j _ => (SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 2 j W)).symm)
      rw [hcongr]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hwin)
        (fun j _ _ => norm_nonneg _)
    have hit : ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2 + q)
        (2 * K) (iteratedCovGrad (I := I) g₀ 0 2 q W)‖ ≤
        Cit * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2)
          (2 * K + q) W‖ := hCit W
    have hemb := hCemb (iteratedCovGrad (I := I) g₀ 0 2 q W) x
    calc (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + q) I b) :=
            Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + q)
          ‖(iteratedCovGrad (I := I) g₀ 0 2 q W).toSection x‖)
        ≤ Cemb * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2 + q)
            (2 * K) (iteratedCovGrad (I := I) g₀ 0 2 q W)‖ := hemb
      _ ≤ Cemb * (Cit * ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2)
            (2 * K + q) W‖) := mul_le_mul_of_nonneg_left hit hCemb_pos.le
      _ ≤ Cemb * (Cit * (Crev * ∑ j ∈ Finset.range (L + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hrev hCit_nn) hCemb_pos.le
      _ = Cemb * Cit * Crev * ∑ j ∈ Finset.range (L + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖ := by ring
  choose Dfun hDfun_nn hDfun using hperdeg
  set D : ℝ := max (Dfun 0 (by norm_num))
    (max (Dfun 1 (by norm_num)) (Dfun 2 (by norm_num))) with hD_def
  have hD_nn : 0 ≤ D := le_trans (hDfun_nn 0 (by norm_num)) (le_max_left _ _)
  have hD0 : Dfun 0 (by norm_num) ≤ D := le_max_left _ _
  have hD1 : Dfun 1 (by norm_num) ≤ D := le_trans (le_max_left _ _) (le_max_right _ _)
  have hD2 : Dfun 2 (by norm_num) ≤ D := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨Real.sqrt (3 * D ^ 2 * ((L + 1 : ℕ) : ℝ)), Real.sqrt_nonneg _, fun W x => ?_⟩
  set Ssum : ℝ := ∑ j ∈ Finset.range (L + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖
    with hSsum_def
  have hSsum_nn : 0 ≤ Ssum := Finset.sum_nonneg fun j _ => norm_nonneg _
  letI inst0 : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + 0) I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + 0)
  letI inst1 : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + 1) I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + 1)
  letI inst2 : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + 2) I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + 2)
  have hptdeg : ∀ q : ℕ, q ≤ 2 →
      (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + q) I b) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + q)
      ‖(iteratedCovGrad (I := I) g₀ 0 2 q W).toSection x‖) ≤ D * Ssum := by
    intro q hq
    interval_cases q
    · exact le_trans (hDfun 0 (by norm_num) W x)
        (mul_le_mul_of_nonneg_right hD0 hSsum_nn)
    · exact le_trans (hDfun 1 (by norm_num) W x)
        (mul_le_mul_of_nonneg_right hD1 hSsum_nn)
    · exact le_trans (hDfun 2 (by norm_num) W x)
        (mul_le_mul_of_nonneg_right hD2 hSsum_nn)
  have hcs : Ssum ^ 2 ≤ ((L + 1 : ℕ) : ℝ) *
      ∑ j ∈ Finset.range (L + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖ ^ 2 := by
    rw [hSsum_def]
    have := sq_sum_le_card_mul_sum_sq (s := Finset.range (L + 1))
      (f := fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖)
    rw [Finset.card_range] at this
    exact_mod_cast this
  have hwin2 : (∑ j ∈ Finset.range (L + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖ ^ 2) ≤
      ∑ i ∈ Finset.range (a + 1 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (by omega)) (fun i _ _ => sq_nonneg _)
  have hsqrt_sq : Real.sqrt (3 * D ^ 2 * ((L + 1 : ℕ) : ℝ)) ^ 2 =
      3 * D ^ 2 * ((L + 1 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
  rw [hsqrt_sq]
  set RHS : ℝ := ∑ i ∈ Finset.range (a + 1 + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2 with hRHS_def
  have hRHS_nn : 0 ≤ RHS := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hpt0 := hptdeg 0 (by norm_num)
  have hpt1 := hptdeg 1 (by norm_num)
  have hpt2 := hptdeg 2 (by norm_num)
  have hcolsq_le : (∑ q ∈ Finset.range 3,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
        ((iteratedCovGrad (I := I) g₀ 0 2 q W).toSection x)) ≤
      3 * (D * Ssum) ^ 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add,
      riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g₀ 0 (2 + 0) x
        ((iteratedCovGrad (I := I) g₀ 0 2 0 W).toSection x),
      riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g₀ 0 (2 + 1) x
        ((iteratedCovGrad (I := I) g₀ 0 2 1 W).toSection x),
      riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g₀ 0 (2 + 2) x
        ((iteratedCovGrad (I := I) g₀ 0 2 2 W).toSection x)]
    have hDS_nn : 0 ≤ D * Ssum := mul_nonneg hD_nn hSsum_nn
    nlinarith [hpt0, hpt1, hpt2,
      norm_nonneg ((iteratedCovGrad (I := I) g₀ 0 2 0 W).toSection x),
      norm_nonneg ((iteratedCovGrad (I := I) g₀ 0 2 1 W).toSection x),
      norm_nonneg ((iteratedCovGrad (I := I) g₀ 0 2 2 W).toSection x), hDS_nn]
  calc (∑ q ∈ Finset.range 3,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x
            ((iteratedCovGrad (I := I) g₀ 0 2 q W).toSection x))
      ≤ 3 * (D * Ssum) ^ 2 := hcolsq_le
    _ = 3 * D ^ 2 * Ssum ^ 2 := by ring
    _ ≤ 3 * D ^ 2 * (((L + 1 : ℕ) : ℝ) * RHS) := by
        rw [hRHS_def]
        exact mul_le_mul_of_nonneg_left
          (le_trans hcs (mul_le_mul_of_nonneg_left hwin2 (by positivity))) (by positivity)
    _ = (3 * D ^ 2 * ((L + 1 : ℕ) : ℝ)) * RHS := by ring

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

set_option maxHeartbeats 1000000 in
private theorem deTurckRHSArmDiff_threeArm_coeffC0_jetL2_crude_ballUniform
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
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i C₂‖ ^ 2) ≤ Γ ^ 2 := by
  classical
  obtain ⟨ΛC, Γ, hΛC_nn, hΓ_nn, hsymm⟩ :=
    deTurckRHSArmDiff_threeArm_coeffC0_jetL2_ballUniform (I := I) g₀ g_bg a ha_super hR hδ₀
  refine ⟨ΛC, Γ, hΛC_nn, hΓ_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball
  have hδ_s : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (symmS (I := I) g₀ T)) δ :=
    gFibreOpBound_ccTensorBilinSymm_symmS g₀ T hδ
  have hδ'_s : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (symmS (I := I) g₀ T')) δ' :=
    gFibreOpBound_ccTensorBilinSymm_symmS g₀ T' hδ'
  obtain ⟨C₀, C₁, C₂, hid, h0s, h1s, h2s, h0j, h1j, h2j⟩ :=
    hsymm (symmS (I := I) g₀ T) (symmS (I := I) g₀ T') hδ_le hδ_s hδ'_le hδ'_s
      (ccTensorBilin_symmS_symm g₀ T) (ccTensorBilin_symmS_symm g₀ T')
      (fun j hj => le_trans (tensorL2Norm_iteratedCovGrad_symmS_le g₀ T j) (hTball j hj))
      (fun j hj => le_trans (tensorL2Norm_iteratedCovGrad_symmS_le g₀ T' j) (hT'ball j hj))
  obtain ⟨σ'₀, hσ'₀⟩ :=
    exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) (T - T') 0
  obtain ⟨σ'₁, hσ'₁⟩ :=
    exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) (T - T') 1
  obtain ⟨σ'₂, hσ'₂⟩ :=
    exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) (T - T') 2
  refine ⟨symmAbsorbedCoeff (I := I) (M := M) g₀ 0 C₀ σ'₀,
    symmAbsorbedCoeff (I := I) (M := M) g₀ 1 C₁ σ'₁,
    symmAbsorbedCoeff (I := I) (M := M) g₀ 2 C₂ σ'₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have he0 : appCc (I := I) (M := M) g₀ 2 2
          (symmAbsorbedCoeff (I := I) (M := M) g₀ 0 C₀ σ'₀)
          (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) =
        appCc (I := I) (M := M) g₀ 2 2 C₀
          (iteratedCovGrad (I := I) g₀ 0 2 0 (symmS (I := I) g₀ (T - T'))) := by
      apply smoothCcTensor_ext_of_unitModel
      intro x
      apply ContinuousMultilinearMap.ext
      intro v
      exact symmAbsorbedCoeff_appCc_eq (I := I) (M := M) g₀ 0 (T - T') C₀ σ'₀ hσ'₀ x v
    have he1 : appCc (I := I) (M := M) g₀ 3 2
          (symmAbsorbedCoeff (I := I) (M := M) g₀ 1 C₁ σ'₁)
          (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) =
        appCc (I := I) (M := M) g₀ 3 2 C₁
          (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) g₀ (T - T'))) := by
      apply smoothCcTensor_ext_of_unitModel
      intro x
      apply ContinuousMultilinearMap.ext
      intro v
      exact symmAbsorbedCoeff_appCc_eq (I := I) (M := M) g₀ 1 (T - T') C₁ σ'₁ hσ'₁ x v
    have he2 : appCc (I := I) (M := M) g₀ 4 2
          (symmAbsorbedCoeff (I := I) (M := M) g₀ 2 C₂ σ'₂)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) =
        appCc (I := I) (M := M) g₀ 4 2 C₂
          (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) g₀ (T - T'))) := by
      apply smoothCcTensor_ext_of_unitModel
      intro x
      apply ContinuousMultilinearMap.ext
      intro v
      exact symmAbsorbedCoeff_appCc_eq (I := I) (M := M) g₀ 2 (T - T') C₂ σ'₂ hσ'₂ x v
    rw [he0, he1, he2, symmS_sub g₀ T T',
      ← deTurckRHSArmG0_symmS_eq g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ
        (lt_of_le_of_lt hδ_le hδ₀) hδ_s,
      ← deTurckRHSArmG0_symmS_eq g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ'
        (lt_of_le_of_lt hδ'_le hδ₀) hδ'_s]
    exact hid
  · intro x
    exact (symmAbsorbedCoeff_rfns_le g₀ 0 C₀ σ'₀ x).trans (h0s x)
  · intro x
    exact (symmAbsorbedCoeff_rfns_le g₀ 1 C₁ σ'₁ x).trans (h1s x)
  · intro x
    exact (symmAbsorbedCoeff_rfns_le g₀ 2 C₂ σ'₂ x).trans (h2s x)
  · exact (symmAbsorbedCoeff_jet_le g₀ 0 (a + 1) C₀ σ'₀).trans h0j
  · exact (symmAbsorbedCoeff_jet_le g₀ 1 (a + 1) C₁ σ'₁).trans h1j
  · exact (symmAbsorbedCoeff_jet_le g₀ 2 (a + 1) C₂ σ'₂).trans h2j

set_option linter.unusedVariables false in
set_option maxHeartbeats 1000000 in
private theorem deTurckSmoothRemainderDiff_connLapResidual_topCoeff_crude_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {ΛC Γ : ℝ} (hΛC_nn : 0 ≤ ΛC) (hΓ_nn : 0 ≤ Γ)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λw Γw : ℝ, 0 ≤ Λw ∧ 0 ≤ Γw ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (C₀ : SmoothCcTensor g₀ 2 2) (C₁ : SmoothCcTensor g₀ 3 2) (C₂arm : SmoothCcTensor g₀ 4 2),
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (C₂arm.toSection x) ≤ ΛC ^ 2) →
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i C₂arm‖ ^ 2) ≤ Γ ^ 2 →
          (deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
              deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ') =
            (appCc (I := I) (M := M) g₀ 2 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
              appCc (I := I) (M := M) g₀ 3 2 C₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
              appCc (I := I) (M := M) g₀ 4 2 C₂arm (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) →
          ∃ C₂' : SmoothCcTensor g₀ 4 2,
            (deTurckSmoothRemainder (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
                deTurckSmoothRemainder (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ') =
              (appCc (I := I) (M := M) g₀ 2 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
                appCc (I := I) (M := M) g₀ 3 2 C₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
                appCc (I := I) (M := M) g₀ 4 2 C₂' (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) ∧
            (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (C₂'.toSection x) ≤ Λw ^ 2) ∧
            (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i C₂'‖ ^ 2) ≤ Γw ^ 2 := by
  classical
  obtain ⟨Λpure, Γpure, hΛpure_nn, hΓpure_nn, hpuresup, hpurejet⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_ricciArmPrincipalCoeffPure_self_fibre_jetL2_bound
      (I := I) (M := M) g₀ a
  refine ⟨Real.sqrt (2 * ΛC ^ 2 + 2 * Λpure ^ 2), Real.sqrt (2 * Γ ^ 2 + 2 * Γpure ^ 2),
    Real.sqrt_nonneg _, Real.sqrt_nonneg _, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball C₀ C₁ C₂arm hC₂armsup hC₂armjet hidArm
  refine ⟨C₂arm - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
      (I := I) (M := M) g₀ g₀, ?_, ?_, ?_⟩
  · have hlift : rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T') =
        appCc (I := I) (M := M) g₀ 4 2
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
            (I := I) (M := M) g₀ g₀)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) := by
      apply smoothCcTensor_ext_of_unitModel
      intro x
      apply ContinuousMultilinearMap.ext
      intro v
      exact
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.rawTensorConnLapSmooth_eq_appCc_cometricDoubleTrace
          (I := I) (M := M) g₀ (T - T') x v
    rw [deTurckSmoothRemainderDiff_eq_armDiff_sub_connLapDiff (I := I) g₀ g_bg T T'
        (lt_of_le_of_lt hδ_le hδ₀) hδ (lt_of_le_of_lt hδ'_le hδ₀) hδ', hidArm, hlift,
      appCc_sub_left]
    abel
  · intro x
    rw [Real.sq_sqrt (by positivity)]
    have hsec : (C₂arm -
          DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
            (I := I) (M := M) g₀ g₀).toSection x =
        C₂arm.toSection x -
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
            (I := I) (M := M) g₀ g₀).toSection x := by
      have h1 := smoothCcTensor_toSection_add_apply g₀ C₂arm
        (-(DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
          (I := I) (M := M) g₀ g₀)) x
      rw [smoothCcTensor_toSection_neg_apply, ← sub_eq_add_neg, ← sub_eq_add_neg] at h1
      exact h1
    rw [hsec]
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
            (C₂arm.toSection x -
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
                (I := I) (M := M) g₀ g₀).toSection x)
        ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (C₂arm.toSection x) +
            2 * riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
              ((DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
                (I := I) (M := M) g₀ g₀).toSection x) :=
          riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 4 2 x _ _
      _ ≤ 2 * ΛC ^ 2 + 2 * Λpure ^ 2 := by
          have h1 := hC₂armsup x
          have h2 := hpuresup x
          linarith [h1, h2]
  · rw [Real.sq_sqrt (by positivity)]
    have hpi : ∀ i ∈ Finset.range (a + 1),
        ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (C₂arm -
              DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
                (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤
          2 * ‖iteratedCovGrad (I := I) g₀ 4 2 i C₂arm‖ ^ 2 +
            2 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
                (I := I) (M := M) g₀ g₀)‖ ^ 2 := by
      intro i _
      have h := normSq_iteratedCovGrad_sub_smul_le_tame (I := I) g₀ 4 2 i C₂arm
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
          (I := I) (M := M) g₀ g₀) 1
        (‖iteratedCovGrad (I := I) g₀ 4 2 i C₂arm‖ ^ 2)
        (‖iteratedCovGrad (I := I) g₀ 4 2 i
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
            (I := I) (M := M) g₀ g₀)‖ ^ 2) (le_refl _) (le_refl _)
      rw [one_smul] at h
      simp only [one_pow, mul_one] at h
      linarith [h]
    calc (∑ i ∈ Finset.range (a + 1),
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (C₂arm -
              DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
                (I := I) (M := M) g₀ g₀)‖ ^ 2)
        ≤ ∑ i ∈ Finset.range (a + 1),
            (2 * ‖iteratedCovGrad (I := I) g₀ 4 2 i C₂arm‖ ^ 2 +
              2 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
                (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
                  (I := I) (M := M) g₀ g₀)‖ ^ 2) := Finset.sum_le_sum hpi
      _ = 2 * (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i C₂arm‖ ^ 2) +
            2 * (∑ i ∈ Finset.range (a + 1),
              ‖iteratedCovGrad (I := I) g₀ 4 2 i
                (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
                  (I := I) (M := M) g₀ g₀)‖ ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ 2 * Γ ^ 2 + 2 * Γpure ^ 2 := by linarith [hC₂armjet, hpurejet]

set_option maxHeartbeats 1000000 in
private theorem deTurckSmoothRemainderDiff_intrinsicPalatini_coeffC0_jetL2_crude_ballUniform
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
          (deTurckSmoothRemainder (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
              deTurckSmoothRemainder (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ') =
            (appCc (I := I) (M := M) g₀ 2 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
              appCc (I := I) (M := M) g₀ 3 2 C₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
              appCc (I := I) (M := M) g₀ 4 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (C₀.toSection x) ≤ ΛC ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x (C₁.toSection x) ≤ ΛC ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (C₂.toSection x) ≤ ΛC ^ 2) ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i C₀‖ ^ 2) ≤ Γ ^ 2 ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 3 2 i C₁‖ ^ 2) ≤ Γ ^ 2 ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i C₂‖ ^ 2) ≤ Γ ^ 2 := by
  classical
  obtain ⟨ΛC, Γ, hΛC_nn, hΓ_nn, harm⟩ :=
    deTurckRHSArmDiff_threeArm_coeffC0_jetL2_crude_ballUniform (I := I) g₀ g_bg a ha_super hR hδ₀
  obtain ⟨Λw, Γw, hΛw_nn, hΓw_nn, hresid⟩ :=
    deTurckSmoothRemainderDiff_connLapResidual_topCoeff_crude_ballUniform
      (I := I) g₀ g_bg a ha_super hR hΛC_nn hΓ_nn hδ₀
  refine ⟨max ΛC Λw, max Γ Γw, le_trans hΛC_nn (le_max_left _ _),
    le_trans hΓ_nn (le_max_left _ _), ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball
  obtain ⟨C₀, C₁, C₂arm, hidArm, hC₀sup, hC₁sup, hC₂armsup, hC₀jet, hC₁jet, hC₂armjet⟩ :=
    harm T T' hδ_le hδ hδ'_le hδ' hTball hT'ball
  obtain ⟨C₂', hidRem, hC₂'sup, hC₂'jet⟩ :=
    hresid T T' hδ_le hδ hδ'_le hδ' hTball hT'ball C₀ C₁ C₂arm hC₂armsup hC₂armjet hidArm
  have hΛCsq : ΛC ^ 2 ≤ max ΛC Λw ^ 2 := by
    have h1 : ΛC ≤ max ΛC Λw := le_max_left _ _
    nlinarith [h1, hΛC_nn]
  have hΛwsq : Λw ^ 2 ≤ max ΛC Λw ^ 2 := by
    have h2 : Λw ≤ max ΛC Λw := le_max_right _ _
    nlinarith [h2, hΛw_nn]
  have hΓsq : Γ ^ 2 ≤ max Γ Γw ^ 2 := by
    have h1 : Γ ≤ max Γ Γw := le_max_left _ _
    nlinarith [h1, hΓ_nn]
  have hΓwsq : Γw ^ 2 ≤ max Γ Γw ^ 2 := by
    have h2 : Γw ≤ max Γ Γw := le_max_right _ _
    nlinarith [h2, hΓw_nn]
  exact ⟨C₀, C₁, C₂', hidRem, fun x => le_trans (hC₀sup x) hΛCsq,
    fun x => le_trans (hC₁sup x) hΛCsq, fun x => le_trans (hC₂'sup x) hΛwsq,
    le_trans hC₀jet hΓsq, le_trans hC₁jet hΓsq, le_trans hC₂'jet hΓwsq⟩

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem deTurckSmoothRemainderDiff_iteratedCovGrad_l2_tame_intrinsic_ballUniform
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
  obtain ⟨ΛC, Γ, hΛC_nn, hΓ_nn, hcoeff⟩ :=
    deTurckSmoothRemainderDiff_intrinsicPalatini_coeffC0_jetL2_crude_ballUniform
      (I := I) g₀ g_bg a ha_super hR hδ₀
  obtain ⟨K₀, hK₀_nn, hK₀⟩ := appCc_topOrder_l2_twoArm_mixed_ballUniform_qUniform (I := I) g₀ 2 2 a
  obtain ⟨K₁, hK₁_nn, hK₁⟩ := appCc_topOrder_l2_twoArm_mixed_ballUniform_qUniform (I := I) g₀ 3 2 a
  obtain ⟨K₂, hK₂_nn, hK₂⟩ := appCc_topOrder_l2_twoArm_mixed_ballUniform_qUniform (I := I) g₀ 4 2 a
  obtain ⟨Cemb1, hCemb1_nn, hemb1⟩ :=
    deTurckArmDiff_supercritical_pointwise_jet_le_lowerWindow (I := I) g₀ a ha_super
  set Kmax : ℝ := max K₀ (max K₁ K₂) with hKmax_def
  have hKmax_nn : 0 ≤ Kmax := le_trans hK₀_nn (le_max_left _ _)
  have hK₀_le : K₀ ≤ Kmax := le_max_left _ _
  have hK₁_le : K₁ ≤ Kmax := le_trans (le_max_left _ _) (le_max_right _ _)
  have hK₂_le : K₂ ≤ Kmax := le_trans (le_max_right _ _) (le_max_right _ _)
  set base : ℝ := Kmax * (Cemb1 ^ 2 * Γ ^ 2 + ΛC ^ 2) with hbase_def
  have hbase_nn : 0 ≤ base := by
    rw [hbase_def]; exact mul_nonneg hKmax_nn (by positivity)
  refine ⟨3 * Real.sqrt base, by positivity, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball q hq
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  set S₂ : ℝ := ∑ i ∈ Finset.range (a + 2 + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 with hS₂_def
  have hS₂_nn : 0 ≤ S₂ := Finset.sum_nonneg fun i _ => sq_nonneg _
  obtain ⟨C₀, C₁, C₂, hid, hC₀sup, hC₁sup, hC₂sup, hC₀jet, hC₁jet, hC₂jet⟩ :=
    hcoeff T T' hδ_le hδ hδ'_le hδ' hTball hT'ball
  set A₀ := appCc (I := I) (M := M) g₀ 2 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) with hA₀
  set A₁ := appCc (I := I) (M := M) g₀ 3 2 C₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) with hA₁
  set A₂ := appCc (I := I) (M := M) g₀ 4 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) with hA₂
  have hN_split : deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
      deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ' = A₀ + A₁ + A₂ := by
    rw [hA₀, hA₁, hA₂]; exact hid
  have hWsup : ∀ (m : ℕ), m ≤ 2 → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 m (T - T')).toSection x) ≤
        (Real.sqrt (Cemb1 ^ 2 * S₂)) ^ 2 := by
    intro m hm x
    rw [Real.sq_sqrt (by positivity)]
    have hembx := hemb1 (T - T') x
    have hmem : m ∈ Finset.range 3 := Finset.mem_range.mpr (by omega)
    refine le_trans (Finset.single_le_sum
      (f := fun qq => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + qq) x
        ((iteratedCovGrad (I := I) g₀ 0 2 qq (T - T')).toSection x))
      (fun qq _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + qq) x _) hmem) ?_
    refine le_trans hembx ?_
    rw [hS₂_def]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg Cemb1)
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun i _ _ => sq_nonneg _)
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
  have harm : ∀ (m : ℕ) (hm : m ≤ 2) (Cm : SmoothCcTensor g₀ (2 + m) 2) (Km : ℝ)
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
      (hCmsup : ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) 2 x (Cm.toSection x) ≤ ΛC ^ 2)
      (hCmjet : (∑ i ∈ Finset.range (a + 1),
          ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2) ≤ Γ ^ 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 q
          (appCc (I := I) (M := M) g₀ (2 + m) 2 Cm
            (iteratedCovGrad (I := I) g₀ 0 2 m (T - T')))‖ ≤ Real.sqrt (base * S₂) := by
    intro m hm Cm Km hKm_le hKm hCmsup hCmjet
    have htame := hKm Cm (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))
      ΛC (Real.sqrt (Cemb1 ^ 2 * S₂)) hΛC_nn (Real.sqrt_nonneg _) hCmsup
      (hWsup m hm)
    have hΛWsq : (Real.sqrt (Cemb1 ^ 2 * S₂)) ^ 2 = Cemb1 ^ 2 * S₂ := Real.sq_sqrt (by positivity)
    have hcjet : (∑ i ∈ Finset.range (q + 1), ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2) ≤
        Γ ^ 2 := hcoeffjet_le m Cm (Γ ^ 2) (sq_nonneg _) hCmjet
    have hwjet : (∑ l ∈ Finset.range (q + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
            (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2) ≤ S₂ := by
      refine le_trans (hWjet m hm) ?_
      rw [hS₂_def]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        (fun i _ _ => sq_nonneg _)
    have hsq : ‖iteratedCovGrad (I := I) g₀ 0 2 q
        (appCc (I := I) (M := M) g₀ (2 + m) 2 Cm
          (iteratedCovGrad (I := I) g₀ 0 2 m (T - T')))‖ ^ 2 ≤ base * S₂ := by
      refine le_trans htame ?_
      rw [hΛWsq]
      have ha1 : (Cemb1 ^ 2 * S₂) * ∑ i ∈ Finset.range (q + 1),
            ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2 ≤ (Cemb1 ^ 2 * S₂) * Γ ^ 2 :=
        mul_le_mul_of_nonneg_left hcjet (by positivity)
      have ha2 : ΛC ^ 2 * ∑ l ∈ Finset.range (q + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
              (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2 ≤ ΛC ^ 2 * S₂ :=
        mul_le_mul_of_nonneg_left hwjet (sq_nonneg _)
      have hinner :
          (Cemb1 ^ 2 * S₂) * ∑ i ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2
            + ΛC ^ 2 * ∑ l ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
                (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2
          ≤ (Cemb1 ^ 2 * Γ ^ 2 + ΛC ^ 2) * S₂ := by
        calc (Cemb1 ^ 2 * S₂) * ∑ i ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2
              + ΛC ^ 2 * ∑ l ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
                  (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2
            ≤ (Cemb1 ^ 2 * S₂) * Γ ^ 2 + ΛC ^ 2 * S₂ := add_le_add ha1 ha2
          _ = (Cemb1 ^ 2 * Γ ^ 2 + ΛC ^ 2) * S₂ := by ring
      have hinner_nn : 0 ≤ (Cemb1 ^ 2 * S₂) * ∑ i ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2
            + ΛC ^ 2 * ∑ l ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
                (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2 := by positivity
      calc Km * ((Cemb1 ^ 2 * S₂) * ∑ i ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2
              + ΛC ^ 2 * ∑ l ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
                  (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2)
          ≤ Kmax * ((Cemb1 ^ 2 * Γ ^ 2 + ΛC ^ 2) * S₂) :=
            mul_le_mul hKm_le hinner hinner_nn hKmax_nn
        _ = base * S₂ := by rw [hbase_def]; ring
    rw [show ‖iteratedCovGrad (I := I) g₀ 0 2 q
          (appCc (I := I) (M := M) g₀ (2 + m) 2 Cm
            (iteratedCovGrad (I := I) g₀ 0 2 m (T - T')))‖ =
        Real.sqrt (‖iteratedCovGrad (I := I) g₀ 0 2 q
          (appCc (I := I) (M := M) g₀ (2 + m) 2 Cm
            (iteratedCovGrad (I := I) g₀ 0 2 m (T - T')))‖ ^ 2) from
      (Real.sqrt_sq (norm_nonneg _)).symm]
    exact Real.sqrt_le_sqrt hsq
  have ha0 := harm 0 (by norm_num) C₀ K₀ hK₀_le (hK₀ q hq) hC₀sup hC₀jet
  have ha1 := harm 1 (by norm_num) C₁ K₁ hK₁_le (hK₁ q hq) hC₁sup hC₁jet
  have ha2 := harm 2 (by norm_num) C₂ K₂ hK₂_le (hK₂ q hq) hC₂sup hC₂jet
  have hnorm0 : ‖iteratedCovGrad (I := I) g₀ 0 2 q A₀‖ ≤ Real.sqrt (base * S₂) := by
    rw [hA₀]; exact ha0
  have hnorm1 : ‖iteratedCovGrad (I := I) g₀ 0 2 q A₁‖ ≤ Real.sqrt (base * S₂) := by
    rw [hA₁]; exact ha1
  have hnorm2 : ‖iteratedCovGrad (I := I) g₀ 0 2 q A₂‖ ≤ Real.sqrt (base * S₂) := by
    rw [hA₂]; exact ha2
  have hsqrt_fac : Real.sqrt (base * S₂) = Real.sqrt base * Real.sqrt S₂ :=
    Real.sqrt_mul hbase_nn S₂
  have hgoal : ‖iteratedCovGrad (I := I) g₀ 0 2 q
      (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
        deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ')‖ ≤
      3 * Real.sqrt base * Real.sqrt S₂ := by
    rw [hN_split, iteratedCovGrad_add (I := I) g₀ 0 2 q (A₀ + A₁) A₂,
      iteratedCovGrad_add (I := I) g₀ 0 2 q A₀ A₁]
    have htri : ‖iteratedCovGrad (I := I) g₀ 0 2 q A₀ +
          iteratedCovGrad (I := I) g₀ 0 2 q A₁ +
          iteratedCovGrad (I := I) g₀ 0 2 q A₂‖ ≤
        Real.sqrt (base * S₂) + Real.sqrt (base * S₂) + Real.sqrt (base * S₂) := by
      refine le_trans (norm_add_le _ _) ?_
      exact add_le_add (le_trans (norm_add_le _ _) (add_le_add hnorm0 hnorm1)) hnorm2
    refine htri.trans (le_of_eq ?_)
    rw [hsqrt_fac]; ring
  exact hgoal

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
    deTurckSmoothRemainderDiff_iteratedCovGrad_l2_tame_intrinsic_ballUniform (I := I) (M := M) g₀ g_bg a
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

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck (cometricLmodel)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private lemma unitModel_zero_fw (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) :
    unitModel (I := I) (M := M) g s (0 : SmoothCcTensor g 0 s) x = 0 := by
  have h := unitModel_sub_local (I := I) g s 0 0 x
  rw [sub_zero] at h
  rw [h, sub_self]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
theorem deTurckPhiMetTotal_background_appCc_eq_zero_of_slot01Symm
    (g₀ g_bg : SmoothRiemannianMetric I M) (W : SmoothCcTensor g₀ 0 4)
    (hWsymm : ∀ (x : M) (u₀ u₁ u₂ u₃ : TangentSpace I x),
      unitModel (I := I) (M := M) g₀ 4 W x ![u₀, u₁, u₂, u₃] =
        unitModel (I := I) (M := M) g₀ 4 W x ![u₁, u₀, u₂, u₃]) :
    appCc (I := I) (M := M) g₀ 4 2
        (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀
          - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
              (I := I) (M := M) g₀ g₀) W = 0 := by
  classical
  apply smoothCcTensor_ext_of_unitModel
  intro x
  apply ContinuousMultilinearMap.ext
  intro v
  rw [unitModel_zero_fw, ContinuousMultilinearMap.zero_apply]
  rw [deTurckPhiMetTotal, appCc_sub_left, appCc_sub_left, appCc_add_left, appCc_add_left]
  rw [unitModel_sub_local, unitModel_sub_local, unitModel_add_local, unitModel_add_local,
    ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.sub_apply,
    ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.add_apply]
  have hLie :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieArm2PrincipalCoeff_appCc_eq
      (I := I) g₀ g₀ g_bg W x v
  have hTHraw :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceHessianCoeff_appCc_eq
      (I := I) (M := M) g₀ g₀ W x v
  have hRACraw :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeff_appCc_eq_combinedTrace
      (I := I) (M := M) g₀ g₀ W x v
  have hPure :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure_appCc_eq_roughLaplacian
      (I := I) (M := M) g₀ g₀ W x v
  have hTH : unitModel (I := I) (M := M) g₀ 2
      (appCc (I := I) (M := M) g₀ 4 2 (traceHessianCoeff (I := I) (M := M) g₀ g₀) W) x v =
      ∑ k : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 4 W x
          ![v 0, v 1,
            cometricLmodel (I := I) g₀ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            (Module.finBasis ℝ E) k] := by
    rw [hTHraw]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    exact congrArg (fun t : Fin 4 → E => unitModel (I := I) (M := M) g₀ 4 W x t)
      (by funext i; fin_cases i <;> rfl)
  have hRAC : unitModel (I := I) (M := M) g₀ 2
      (appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀) W) x v =
      (1 / 2 : ℝ) *
        ((∑ k : Fin (Module.finrank ℝ E),
            unitModel (I := I) (M := M) g₀ 4 W x
              ![cometricLmodel (I := I) g₀ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)),
                v 0, v 1, (Module.finBasis ℝ E) k]
          + ∑ k : Fin (Module.finrank ℝ E),
              unitModel (I := I) (M := M) g₀ 4 W x
                ![cometricLmodel (I := I) g₀ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)),
                  v 1, v 0, (Module.finBasis ℝ E) k])
        - ∑ k : Fin (Module.finrank ℝ E),
            unitModel (I := I) (M := M) g₀ 4 W x
              (Fin.cons (cometricLmodel (I := I) g₀ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)))
                (Fin.cons ((Module.finBasis ℝ E) k) v))) := by
    rw [hRACraw, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    refine congrArg (fun t : ℝ => (1 / 2 : ℝ) * t) ?_
    refine congrArg₂ (fun a b : ℝ => a - b) (congrArg₂ (fun a b : ℝ => a + b) ?_ ?_) rfl
    · refine Finset.sum_congr rfl fun k _ => ?_
      exact congrArg (fun t : Fin 4 → E => unitModel (I := I) (M := M) g₀ 4 W x t)
        (by funext i; fin_cases i <;> rfl)
    · refine Finset.sum_congr rfl fun k _ => ?_
      exact congrArg (fun t : Fin 4 → E => unitModel (I := I) (M := M) g₀ 4 W x t)
        (by funext i; fin_cases i <;> rfl)
  rw [hLie, hTH, hRAC, hPure]
  have hswapA : ∑ k : Fin (Module.finrank ℝ E),
      unitModel (I := I) (M := M) g₀ 4 W x
        ![v 0,
          cometricLmodel (I := I) g₀ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)),
          v 1, (Module.finBasis ℝ E) k] =
      ∑ k : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 4 W x
          ![cometricLmodel (I := I) g₀ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            v 0, v 1, (Module.finBasis ℝ E) k] :=
    Finset.sum_congr rfl fun k _ => hWsymm x (v 0)
      (cometricLmodel (I := I) g₀ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k)))
      (v 1) ((Module.finBasis ℝ E) k)
  have hswapB : ∑ k : Fin (Module.finrank ℝ E),
      unitModel (I := I) (M := M) g₀ 4 W x
        ![v 1,
          cometricLmodel (I := I) g₀ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)),
          v 0, (Module.finBasis ℝ E) k] =
      ∑ k : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 4 W x
          ![cometricLmodel (I := I) g₀ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            v 1, v 0, (Module.finBasis ℝ E) k] :=
    Finset.sum_congr rfl fun k _ => hWsymm x (v 1)
      (cometricLmodel (I := I) g₀ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k)))
      (v 0) ((Module.finBasis ℝ E) k)
  rw [hswapA, hswapB]
  ring

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private lemma deTurckPhiMetTotal_realizedFam_eq_lieSubLich
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) :
    deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg (realizedFam (I := I) g₀ T T' hδ hδ' s) =
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieArm2PrincipalCoeff
          (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
        - (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s
            + linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s) := by
  rw [deTurckPhiMetTotal, linearizedRicciArm2FieldLichnerowicz]
  set X : SmoothCcTensor g₀ 4 2 :=
    ricciArmPrincipalCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) with hX
  set Y : SmoothCcTensor g₀ 4 2 :=
    traceHessianCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) with hY
  have hhalf : (1 / 2 : ℝ) • Y + (1 / 2 : ℝ) • Y = Y := by
    rw [← add_smul]
    norm_num
  have hgrp : (X - (1 / 2 : ℝ) • Y) + (X - (1 / 2 : ℝ) • Y) =
      (X + X) - ((1 / 2 : ℝ) • Y + (1 / 2 : ℝ) • Y) := by abel
  rw [hgrp, hhalf]
  abel

namespace DeTurckRemainderTameLipschitz

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
theorem jointTotalSpaceRS_sub_fw {r s : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (B p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p - B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
    (fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hB p₀ hp₀)
  refine (hA'.2.sub hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_sub (A p) (B p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_sub
      (A p₀) (B p₀)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
theorem jointTotalSpaceRS_add_fw {r s : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (B p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p + B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
    (fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hB p₀ hp₀)
  refine (hA'.2.add hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_add (A p) (B p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_add
      (A p₀) (B p₀)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
theorem deTurckPhiMetTotal_realizedFam_jointSmooth
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4
      (fun s => deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
        (realizedFam (I := I) g₀ T T' hδ hδ' s)) (δ := δ) (δ' := δ') := by
  have hLie :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieArm2PrincipalCoeff_realizedFam_jointSmooth
      (I := I) g₀ T T' hδ hδ' g_bg
  have hLich := linearizedRicci_arm2FieldLichnerowicz_jointSmooth (I := I) g₀ T T' hδ hδ'
  have hadd := jointTotalSpaceRS_add_fw (I := I) (r := 4) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ =>
      (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' p.2).toSection p.1)
    (fun p : M × ℝ =>
      (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' p.2).toSection p.1)
    hLich hLich
  have hsub := jointTotalSpaceRS_sub_fw (I := I) (r := 4) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ =>
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieArm2PrincipalCoeff
        (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg).toSection p.1)
    (fun p : M × ℝ =>
      (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' p.2).toSection p.1
        + (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' p.2).toSection p.1)
    hLie hadd
  refine hsub.congr (fun p _ => ?_)
  beta_reduce
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1 t) ?_
  rw [deTurckPhiMetTotal_realizedFam_eq_lieSubLich (I := I) (M := M) g₀ g_bg T T' hδ hδ' p.2,
    SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]

end DeTurckRemainderTameLipschitz

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
def deTurckPhiTotPathIntegral (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    SmoothCcTensor g₀ 4 2 :=
  pathIntegralCoeffField (I := I) (M := M) g₀ 4 2
    (fun s => deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
      (realizedFam (I := I) g₀ T T' hδ hδ' s))
    (realizedSmallSet (δ := δ) (δ' := δ')) realizedSmallSet_isOpen
    (by rw [Set.uIcc_of_le zero_le_one]; exact Icc_subset_realizedSmallSet hδ_lt hδ'_lt)
    (deTurckPhiMetTotal_realizedFam_jointSmooth (I := I) (M := M) g₀ g_bg T T' hδ hδ')

namespace DeTurckRemainderTameLipschitz

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
lemma ccTensorBilin_sub_fw (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2) (x : M) (v w : TangentSpace I x) :
    ccTensorBilin (I := I) g₀ (T - T') x v w =
      ccTensorBilin (I := I) g₀ T x v w - ccTensorBilin (I := I) g₀ T' x v w := by
  rw [← unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ (T - T') x v w,
    ← unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ T x v w,
    ← unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ T' x v w,
    unitModel_sub_local, ContinuousMultilinearMap.sub_apply]

end DeTurckRemainderTameLipschitz

open DifferentialGeometry.PDE.DeTurck.RicciLinearization (lieDeTurckChartSlope deriv_realizedFam_chartLieDeTurckComp_eq_chartSlope)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (deTurckLieArm2PrincipalCoeff deTurckLieArm1Coeff deTurckLieCoeffField deTurckLieArm2PrincipalCoeff_realizedFam_jointSmooth deTurckLieArm1Coeff_realizedFam_jointSmooth deTurckLieCoeffField_realizedFam_jointSmooth)

namespace DeTurckRemainderTameLipschitz

lemma sq_bound_of_sqrt_le_fw {r Λv : ℝ} (hr : 0 ≤ r) (h : Real.sqrt r ≤ Λv) :
    r ≤ Λv ^ 2 := by
  nlinarith [Real.sq_sqrt hr, Real.sqrt_nonneg r]

end DeTurckRemainderTameLipschitz

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private lemma symmS_eq_self_of_symm_fw (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2)
    (hsymm : ∀ (x : M) (u w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ S x u w = ccTensorBilin (I := I) g₀ S x w u) :
    symmS (I := I) (M := M) g₀ S = S := by
  have hswap : domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) S = S := by
    refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀ (fun x => ?_)
    rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrSection_unitModel]
    refine ContinuousMultilinearMap.ext (fun v => ?_)
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    have hv : ∀ u w : TangentSpace I x,
        unitModel (I := I) (M := M) g₀ 2 S x ![u, w] =
          unitModel (I := I) (M := M) g₀ 2 S x ![w, u] := by
      intro u w
      rw [unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ S x u w,
        unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ S x w u]
      exact hsymm x u w
    have hveta : (fun i => v ((Equiv.swap (0 : Fin 2) 1) i)) = ![v 1, v 0] := by
      funext i
      fin_cases i <;> rfl
    have hveta' : v = ![v 0, v 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hveta]
    conv_rhs => rw [hveta']
    exact hv (v 1) (v 0)
  rw [symmS, hswap, ← two_smul ℝ S, smul_smul,
    show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul]

namespace DeTurckRemainderTameLipschitz

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
theorem threeArmHjoint_neg_two_smul_add_fw (g₀ : SmoothRiemannianMetric I M) (r : ℕ)
    (A B : ℝ → SmoothCcTensor g₀ r 2) {δ δ' : ℝ}
    (hA : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r A (δ := δ) (δ' := δ'))
    (hB : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r B (δ := δ) (δ' := δ')) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r
      (fun s => (-2 : ℝ) • A s + B s) (δ := δ) (δ' := δ') := by
  have hsmul := lieArm_jointRS_const_smul_local (I := I) (r := r) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) (-2 : ℝ)
    (fun p : M × ℝ => (A p.2).toSection p.1) hA
  have hadd := jointTotalSpaceRS_add_fw (I := I) (r := r) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => (-2 : ℝ) • (A p.2).toSection p.1)
    (fun p : M × ℝ => (B p.2).toSection p.1)
    hsmul hB
  refine hadd.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r 2 I z) p.1 t) ?_
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
lemma deTurckPhiMetTotal_realizedFam_eq_neg_two_smul_fw
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) :
    deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg (realizedFam (I := I) g₀ T T' hδ hδ' s) =
      (-2 : ℝ) • linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s
        + deTurckLieArm2PrincipalCoeff (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg := by
  rw [deTurckPhiMetTotal_realizedFam_eq_lieSubLich (I := I) (M := M) g₀ g_bg T T' hδ hδ' s]
  rw [show (-2 : ℝ) • linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s =
      -(linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s
        + linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s) from by
    rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, neg_smul, two_smul]]
  abel

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
theorem linearizedDeTurckLieAt_eq_threeArm_plain_of_symm_fw
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (hSsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ (T - T') x v w = ccTensorBilin (I := I) g₀ (T - T') x w v)
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) (x : M) (v : Fin 2 → TangentSpace I x) :
    linearizedDeTurckLieAt (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) s =
      unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2
            (deTurckLieCoeffField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
              + lieCorr0Field (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
            (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
          + appCc (I := I) (M := M) g₀ 3 2
            (deTurckLieArm1Coeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
            (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
          + appCc (I := I) (M := M) g₀ 4 2
            (deTurckLieArm2PrincipalCoeff (I := I) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  have hSsymmS : symmS (I := I) (M := M) g₀ (T - T') = T - T' :=
    symmS_eq_self_of_symm_fw (I := I) (M := M) g₀ (T - T') hSsymm
  rw [linearizedDeTurckLieAt_eq_deriv_chartSum_on_Ioo (I := I) g₀ g_bg T T'
    hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) hs]
  rw [(hasDerivAt_realizedDeTurckLieChartSum_general (I := I) g₀ g_bg T T'
    hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) hs).deriv]
  have hcomp : ∀ i j : Fin (Module.finrank ℝ E),
      deriv (fun s : ℝ =>
        DeTurckCoefficients.chartLieDeTurckComp (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i j (extChartAt I x x)) s =
      unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2
            (deTurckLieCoeffField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
              + lieCorr0Field (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
            (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
          + appCc (I := I) (M := M) g₀ 3 2
            (deTurckLieArm1Coeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
            (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
          + appCc (I := I) (M := M) g₀ 4 2
            (deTurckLieArm2PrincipalCoeff (I := I) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x
        ![(chartModelBasis E) i, (chartModelBasis E) j] := by
    intro i j
    rw [deriv_realizedFam_chartLieDeTurckComp_eq_chartSlope (I := I) g₀ T T'
      hδ_lt hδ hδ'_lt hδ' g_bg x i j hs]
    have h := lieArm_chartSlope_center_value_eq_threeArm (I := I) g₀ g_bg T T'
      hδ_lt hδ hδ'_lt hδ' s x i j
    rw [hSsymmS] at h
    exact h
  set Wbase : SmoothCcTensor g₀ 0 2 :=
    appCc (I := I) (M := M) g₀ 2 2
        (deTurckLieCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
          + lieCorr0Field (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
        (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
      + appCc (I := I) (M := M) g₀ 3 2
        (deTurckLieArm1Coeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
        (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
      + appCc (I := I) (M := M) g₀ 4 2
        (deTurckLieArm2PrincipalCoeff (I := I) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
        (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) with hWbase
  calc (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) j *
        deriv (fun s : ℝ =>
          DeTurckCoefficients.chartLieDeTurckComp (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i j (extChartAt I x x)) s)
      = ∑ j : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) j *
            deriv (fun s : ℝ =>
              DeTurckCoefficients.chartLieDeTurckComp (I := I)
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i j (extChartAt I x x)) s :=
        Finset.sum_comm
    _ = ∑ j : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) j *
            unitModel (I := I) (M := M) g₀ 2 Wbase x
              ![(chartModelBasis E) i, (chartModelBasis E) j] := by
        refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
        rw [hcomp i j]
    _ = unitModel (I := I) (M := M) g₀ 2 Wbase x v :=
        unitModel_basis_expand_two (I := I) (M := M) g₀ Wbase x v

end DeTurckRemainderTameLipschitz

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
theorem deTurckRHSArmDiff_threeArm_canonicalTop_coeffC0_jetL2_ballUniform_of_symm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
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
        ∃ (C₀ : SmoothCcTensor g₀ 2 2) (C₁ : SmoothCcTensor g₀ 3 2),
          (deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
              deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ') =
            (appCc (I := I) (M := M) g₀ 2 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
              appCc (I := I) (M := M) g₀ 3 2 C₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
              appCc (I := I) (M := M) g₀ 4 2
                (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T T'
                  (lt_of_le_of_lt hδ_le hδ₀) hδ (lt_of_le_of_lt hδ'_le hδ₀) hδ')
                (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (C₀.toSection x) ≤ ΛC ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x (C₁.toSection x) ≤ ΛC ^ 2) ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i C₀‖ ^ 2) ≤ Γ ^ 2 ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 3 2 i C₁‖ ^ 2) ≤ Γ ^ 2 := by
  classical
  obtain ⟨ΛCr, hΛCr_nn, hC0r⟩ :=
    uniform_C0_bound_concrete_lichnerowicz_coeffFields (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  obtain ⟨Br, hBr_nn, hJr⟩ :=
    linearizedRicciArm_concreteField_jetL2_ballUniform (I := I) g₀ a ha_super hR hδ₀
  obtain ⟨ΛL0, hΛL0_nn, hL0r⟩ :=
    deTurckLieCoeffField_realizedFam_rfns_order0_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  obtain ⟨ΛLc, hΛLc_nn, hLcr⟩ :=
    lieCorr0Field_realizedFam_rfns_order0_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  obtain ⟨ΛL1, hΛL1_nn, hL1r⟩ :=
    deTurckLieArm1Coeff_realizedFam_rfns_order0_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  obtain ⟨P0, hP0_nn, hP0j⟩ :=
    deTurckLieCoeffField_realizedFam_jetL2_perOrder_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  obtain ⟨PL, hPL_nn, hPLj⟩ :=
    lieCorr0Field_realizedFam_jetL2_perOrder_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  obtain ⟨P1, hP1_nn, hP1j⟩ :=
    deTurckLieArm1Coeff_realizedFam_jetL2_perOrder_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  refine ⟨max (Real.sqrt (8 * ΛCr ^ 2 + 4 * ΛL0 + 4 * ΛLc)) (Real.sqrt (8 * ΛCr ^ 2 + 2 * ΛL1)),
    max (Real.sqrt (8 * Br ^ 2 + ∑ i ∈ Finset.range (a + 1), (4 * P0 i + 4 * PL i)))
      (Real.sqrt (8 * Br ^ 2 + 2 * ∑ i ∈ Finset.range (a + 1), P1 i)),
    le_trans (Real.sqrt_nonneg _) (le_max_left _ _),
    le_trans (Real.sqrt_nonneg _) (le_max_left _ _), ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTsymm hT'symm hTball hT'ball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  have hSsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ (T - T') x v w = ccTensorBilin (I := I) g₀ (T - T') x w v := by
    intro x v w
    rw [ccTensorBilin_sub_fw (I := I) (M := M) g₀ T T' x v w,
      ccTensorBilin_sub_fw (I := I) (M := M) g₀ T T' x w v, hTsymm x v w, hT'symm x v w]
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ') := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_realizedSmallSet hδ_lt hδ'_lt
  have hSopen : IsOpen (realizedSmallSet (δ := δ) (δ' := δ')) := realizedSmallSet_isOpen
  set Ψ₀ : ℝ → SmoothCcTensor g₀ 2 2 := fun s =>
    (-2 : ℝ) • linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s
      + (deTurckLieCoeffField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
        + lieCorr0Field (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) with hΨ₀def
  set Ψ₁ : ℝ → SmoothCcTensor g₀ 3 2 := fun s =>
    (-2 : ℝ) • linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s
      + deTurckLieArm1Coeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg with hΨ₁def
  set Ψ₂ : ℝ → SmoothCcTensor g₀ 4 2 := fun s =>
    deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
      (realizedFam (I := I) g₀ T T' hδ hδ' s) with hΨ₂def
  have hj0 : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 Ψ₀ (δ := δ) (δ' := δ') := by
    rw [hΨ₀def]
    exact threeArmHjoint_neg_two_smul_add_fw (I := I) (M := M) g₀ 2 _ _
      (linearizedRicci_arm0Field_jointSmooth (I := I) g₀ T T' hδ hδ')
      (lieCorr0Phi0b_jointSmooth (I := I) g₀ T T' hδ hδ' g_bg)
  have hj1 : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3 Ψ₁ (δ := δ) (δ' := δ') := by
    rw [hΨ₁def]
    exact threeArmHjoint_neg_two_smul_add_fw (I := I) (M := M) g₀ 3 _ _
      (linearizedRicci_arm1Field_jointSmooth (I := I) g₀ T T' hδ hδ')
      (deTurckLieArm1Coeff_realizedFam_jointSmooth (I := I) g₀ T T' hδ hδ' g_bg)
  have hj2 : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4 Ψ₂ (δ := δ) (δ' := δ') := by
    rw [hΨ₂def]
    exact deTurckPhiMetTotal_realizedFam_jointSmooth (I := I) (M := M) g₀ g_bg T T' hδ hδ'
  have hc0 : ∀ x : M, ContinuousOn (fun t : ℝ =>
      Tensor0SBundle.TensorRSSpace.toModel ((Ψ₀ t).toSection x))
      (realizedSmallSet (δ := δ) (δ' := δ')) := fun x =>
    jointContMDiff_toModel_continuous_slice (I := I) g₀ 2 2 Ψ₀
      (realizedSmallSet (δ := δ) (δ' := δ')) hj0 x
  have hc1 : ∀ x : M, ContinuousOn (fun t : ℝ =>
      Tensor0SBundle.TensorRSSpace.toModel ((Ψ₁ t).toSection x))
      (realizedSmallSet (δ := δ) (δ' := δ')) := fun x =>
    jointContMDiff_toModel_continuous_slice (I := I) g₀ 3 2 Ψ₁
      (realizedSmallSet (δ := δ) (δ' := δ')) hj1 x
  have hc2 : ∀ x : M, ContinuousOn (fun t : ℝ =>
      Tensor0SBundle.TensorRSSpace.toModel ((Ψ₂ t).toSection x))
      (realizedSmallSet (δ := δ) (δ' := δ')) := fun x =>
    jointContMDiff_toModel_continuous_slice (I := I) g₀ 4 2 Ψ₂
      (realizedSmallSet (δ := δ) (δ' := δ')) hj2 x
  set C₀ : SmoothCcTensor g₀ 2 2 := pathIntegralCoeffField (I := I) (M := M) g₀ 2 2 Ψ₀
    (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj0 with hC₀def
  set C₁ : SmoothCcTensor g₀ 3 2 := pathIntegralCoeffField (I := I) (M := M) g₀ 3 2 Ψ₁
    (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj1 with hC₁def
  have hPitop : deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T T'
      (lt_of_le_of_lt hδ_le hδ₀) hδ (lt_of_le_of_lt hδ'_le hδ₀) hδ' =
      pathIntegralCoeffField (I := I) (M := M) g₀ 4 2 Ψ₂
        (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj2 := rfl
  refine ⟨C₀, C₁, ?_, ?_, ?_, ?_, ?_⟩
  · apply smoothCcTensor_ext_of_unitModel
    intro x
    apply ContinuousMultilinearMap.ext
    intro v
    rw [hPitop]
    set g₁ := tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ with hg₁
    set g₁' := tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ' with hg₁'
    rw [unitModel_sub_local (I := I) g₀ 2 _ _ x, ContinuousMultilinearMap.sub_apply]
    rw [show (unitModel (I := I) (M := M) g₀ 2
          (deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ) x) v =
        deTurckRicciRHS (I := I) g_bg g₁ x (v 0) (v 1) from
      unitModel_of_deTurckRHSSection_realize (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ
        (deTurckRHSArmG0 (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ) rfl x v]
    rw [show (unitModel (I := I) (M := M) g₀ 2
          (deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ') x) v =
        deTurckRicciRHS (I := I) g_bg g₁' x (v 0) (v 1) from
      unitModel_of_deTurckRHSSection_realize (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ'
        (deTurckRHSArmG0 (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ') rfl x v]
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
    rw [hg₁, hg₁']
    rw [ricciTensor_realized_sub_eq_integral_linearizedRicci (I := I) g₀ T T'
      hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1)]
    rw [lieDerivMetricClm_realized_sub_eq_integral_linearizedDeTurckLie (I := I) g₀ g_bg T T'
      hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1)]
    rw [smul_eq_mul, ← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_add
      ((DifferentialGeometry.PDE.DeTurck.RicciLinearization.linearizedRicciAt_intervalIntegrable
        (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1)).const_mul (-2 : ℝ))
      (linearizedDeTurckLieAt_intervalIntegrable (I := I) g₀ g_bg T T'
        hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1))]
    have hintegrand : ∀ᵐ s ∂MeasureTheory.volume, s ∈ Set.uIoc (0 : ℝ) 1 →
        (-2 : ℝ) * linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) s
          + linearizedDeTurckLieAt (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) s =
        unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 2 2 (Ψ₀ s)
            (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))) x v
          + unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 3 2 (Ψ₁ s)
            (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))) x v
          + unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 4 2 (Ψ₂ s)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
      rw [MeasureTheory.ae_iff]
      have hnull : MeasureTheory.volume ({1} : Set ℝ) = 0 := by simp
      refine MeasureTheory.measure_mono_null (fun s hs => ?_) hnull
      rw [Set.mem_setOf_eq, Classical.not_imp] at hs
      obtain ⟨hsmem, hsneq⟩ := hs
      rw [Set.uIoc_of_le zero_le_one, Set.mem_Ioc] at hsmem
      rw [Set.mem_singleton_iff]
      by_contra hne
      have hsIoo : s ∈ Set.Ioo (0 : ℝ) 1 := ⟨hsmem.1, lt_of_le_of_ne hsmem.2 hne⟩
      refine hsneq ?_
      have hRid : linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) s =
          unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 2 2
                (linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s)
                (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
              + appCc (I := I) (M := M) g₀ 3 2
                (linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s)
                (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
              + appCc (I := I) (M := M) g₀ 4 2
                (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
                (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
        obtain ⟨_, _, _, hident, _, _⟩ :=
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_arm0_arm1_corrField_data
            (I := I) g₀ T T' hδ hδ').choose_spec.choose_spec
        exact hident hTsymm hT'symm s hsIoo x v hδ_lt hδ'_lt
      have hLid := linearizedDeTurckLieAt_eq_threeArm_plain_of_symm_fw (I := I) (M := M)
        g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' hSsymm hsIoo x v
      have hRid' : linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) s =
          unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 2 2
              (linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s)
              (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))) x v
            + unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 3 2
              (linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s)
              (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))) x v
            + unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 4 2
              (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
              (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
        rw [hRid, unitModel_add2_apply_tame, unitModel_add2_apply_tame]
      have hLid' : linearizedDeTurckLieAt (I := I) g₀ g_bg T T'
            hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) s =
          unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 2 2
              (deTurckLieCoeffField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
                + lieCorr0Field (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
              (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))) x v
            + unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 3 2
              (deTurckLieArm1Coeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
              (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))) x v
            + unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 4 2
              (deTurckLieArm2PrincipalCoeff (I := I) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
              (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
        rw [hLid, unitModel_add2_apply_tame, unitModel_add2_apply_tame]
      have e0 : unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 2 2 (Ψ₀ s)
            (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))) x v =
          (-2 : ℝ) * unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 2 2
              (linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s)
              (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))) x v
            + unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 2 2
              (deTurckLieCoeffField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
                + lieCorr0Field (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
              (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))) x v := by
        simp only [hΨ₀def]
        rw [appCc_add_left, unitModel_add2_apply_tame, unitModel_appCc_smul_left_apply_tame]
      have e1 : unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 3 2 (Ψ₁ s)
            (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))) x v =
          (-2 : ℝ) * unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 3 2
              (linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s)
              (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))) x v
            + unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 3 2
              (deTurckLieArm1Coeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
              (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))) x v := by
        simp only [hΨ₁def]
        rw [appCc_add_left, unitModel_add2_apply_tame, unitModel_appCc_smul_left_apply_tame]
      have e2 : unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 4 2 (Ψ₂ s)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v =
          (-2 : ℝ) * unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 4 2
              (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
              (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v
            + unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 4 2
              (deTurckLieArm2PrincipalCoeff (I := I) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
              (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
        simp only [hΨ₂def]
        rw [deTurckPhiMetTotal_realizedFam_eq_neg_two_smul_fw (I := I) (M := M)
          g₀ g_bg T T' hδ hδ' s]
        rw [appCc_add_left, unitModel_add2_apply_tame, unitModel_appCc_smul_left_apply_tame]
      rw [hRid', hLid', e0, e1, e2]
      ring
    rw [intervalIntegral.integral_congr_ae hintegrand]
    have hI0 : IntervalIntegrable (fun s : ℝ => unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2 (Ψ₀ s)
          (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))) x v) MeasureTheory.volume 0 1 :=
      threeArm_unitModel_appCc_intervalIntegrable_tame (I := I) g₀ 2 Ψ₀
        (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) hSI hc0 x v
    have hI1 : IntervalIntegrable (fun s : ℝ => unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 3 2 (Ψ₁ s)
          (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))) x v) MeasureTheory.volume 0 1 :=
      threeArm_unitModel_appCc_intervalIntegrable_tame (I := I) g₀ 3 Ψ₁
        (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) hSI hc1 x v
    have hI2 : IntervalIntegrable (fun s : ℝ => unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2 (Ψ₂ s)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v) MeasureTheory.volume 0 1 :=
      threeArm_unitModel_appCc_intervalIntegrable_tame (I := I) g₀ 4 Ψ₂
        (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) hSI hc2 x v
    rw [intervalIntegral.integral_add (hI0.add hI1) hI2, intervalIntegral.integral_add hI0 hI1]
    have he0 := pathIntegralCoeffField_appCc_eq (I := I) (M := M) g₀ 2 2 Ψ₀
      (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj0 hc0 x v
    have he1 := pathIntegralCoeffField_appCc_eq (I := I) (M := M) g₀ 3 2 Ψ₁
      (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj1 hc1 x v
    have he2 := pathIntegralCoeffField_appCc_eq (I := I) (M := M) g₀ 4 2 Ψ₂
      (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj2 hc2 x v
    rw [← hC₀def] at he0
    rw [← hC₁def] at he1
    rw [unitModel_add2_apply_tame, unitModel_add2_apply_tame, he0, he1, he2]
  · intro x
    have hsup : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x ((Ψ₀ t).toSection x)) ≤
          Real.sqrt (8 * ΛCr ^ 2 + 4 * ΛL0 + 4 * ΛLc) := by
      intro t ht
      refine Real.sqrt_le_sqrt ?_
      simp only [hΨ₀def]
      have hadd := lc0b_rfns_toSection_add_le (I := I) (M := M) g₀ 2 2
        ((-2 : ℝ) • linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' t)
        (deTurckLieCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' t) g_bg
          + lieCorr0Field (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' t) g_bg) x
      have hsm : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          (((-2 : ℝ) • linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' t).toSection x) =
          4 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' t).toSection x) := by
        rw [show (((-2 : ℝ) • linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' t).toSection x) =
            (-2 : ℝ) • ((linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' t).toSection x) from by
          rw [SmoothCcTensor.toSection_smul]; rfl]
        rw [riemannianFiberNormSq_smul_value_tame]
        norm_num
      have hR := sq_bound_of_sqrt_le_fw
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 2 x _)
        ((hC0r T T' hδ_le hδ hδ'_le hδ' hTball hT'ball t ht x).1)
      have haddL := lc0b_rfns_toSection_add_le (I := I) (M := M) g₀ 2 2
        (deTurckLieCoeffField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' t) g_bg)
        (lieCorr0Field (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' t) g_bg) x
      have hL0 := hL0r T T' hδ_le hδ hδ'_le hδ' hTball hT'ball t ht x
      have hLc := hLcr T T' hδ_le hδ hδ'_le hδ' hTball hT'ball t ht x
      linarith
    have htrans := riemannianFiberNormSq_pathIntegralCoeffField_le_sq (I := I) (M := M) g₀ 2 2 Ψ₀
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj0 x
      (Real.sqrt (8 * ΛCr ^ 2 + 4 * ΛL0 + 4 * ΛLc)) (Real.sqrt_nonneg _)
      ((hc0 x).mono (Icc_subset_realizedSmallSet hδ_lt hδ'_lt)) hsup
    rw [← hC₀def] at htrans
    refine le_trans htrans (pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_max_left _ _) 2)
  · intro x
    have hsup : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x ((Ψ₁ t).toSection x)) ≤
          Real.sqrt (8 * ΛCr ^ 2 + 2 * ΛL1) := by
      intro t ht
      refine Real.sqrt_le_sqrt ?_
      simp only [hΨ₁def]
      have hadd := lc0b_rfns_toSection_add_le (I := I) (M := M) g₀ 3 2
        ((-2 : ℝ) • linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' t)
        (deTurckLieArm1Coeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' t) g_bg) x
      have hsm : riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
          (((-2 : ℝ) • linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' t).toSection x) =
          4 * riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
            ((linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' t).toSection x) := by
        rw [show (((-2 : ℝ) • linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' t).toSection x) =
            (-2 : ℝ) • ((linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' t).toSection x) from by
          rw [SmoothCcTensor.toSection_smul]; rfl]
        rw [riemannianFiberNormSq_smul_value_tame]
        norm_num
      have hR := sq_bound_of_sqrt_le_fw
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 3 2 x _)
        ((hC0r T T' hδ_le hδ hδ'_le hδ' hTball hT'ball t ht x).2.1)
      have hL1 := hL1r T T' hδ_le hδ hδ'_le hδ' hTball hT'ball t ht x
      linarith
    have htrans := riemannianFiberNormSq_pathIntegralCoeffField_le_sq (I := I) (M := M) g₀ 3 2 Ψ₁
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj1 x
      (Real.sqrt (8 * ΛCr ^ 2 + 2 * ΛL1)) (Real.sqrt_nonneg _)
      ((hc1 x).mono (Icc_subset_realizedSmallSet hδ_lt hδ'_lt)) hsup
    rw [← hC₁def] at htrans
    refine le_trans htrans (pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_max_right _ _) 2)
  · have hnn : (0 : ℝ) ≤ 8 * Br ^ 2 + ∑ i ∈ Finset.range (a + 1), (4 * P0 i + 4 * PL i) := by
      have hsum : (0 : ℝ) ≤ ∑ i ∈ Finset.range (a + 1), (4 * P0 i + 4 * PL i) :=
        Finset.sum_nonneg fun i _ => by
          have := hP0_nn i; have := hPL_nn i; linarith
      nlinarith [sq_nonneg Br]
    have hjet : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i (Ψ₀ s)‖ ^ 2) ≤
          Real.sqrt (8 * Br ^ 2 + ∑ i ∈ Finset.range (a + 1), (4 * P0 i + 4 * PL i)) ^ 2 := by
      intro s hs
      rw [Real.sq_sqrt hnn]
      simp only [hΨ₀def]
      have htow := jetTowerSum_add_le (I := I) g₀ 2 2 (a + 1)
        ((-2 : ℝ) • linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s)
        (deTurckLieCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
          + lieCorr0Field (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
      have hsc : (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i
          ((-2 : ℝ) • linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s)‖ ^ 2) =
          4 * ∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s)‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [iteratedCovGrad_smul', norm_smul]
        rw [show ‖(-2 : ℝ)‖ = 2 by rw [Real.norm_eq_abs]; norm_num]
        ring
      have hRj := (hJr T T' hδ_le hδ hδ'_le hδ' hTball hT'ball).1 s hs
      have htowL := jetTowerSum_add_le (I := I) g₀ 2 2 (a + 1)
        (deTurckLieCoeffField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
        (lieCorr0Field (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
      have hLsum : (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (deTurckLieCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2) ≤
          ∑ i ∈ Finset.range (a + 1), P0 i :=
        Finset.sum_le_sum fun i hi =>
          hP0j T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i
            (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) s hs
      have hcsum : (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (lieCorr0Field (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2) ≤
          ∑ i ∈ Finset.range (a + 1), PL i :=
        Finset.sum_le_sum fun i hi =>
          hPLj T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i
            (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) s hs
      have hexpand : (∑ i ∈ Finset.range (a + 1), (4 * P0 i + 4 * PL i)) =
          4 * (∑ i ∈ Finset.range (a + 1), P0 i) + 4 * (∑ i ∈ Finset.range (a + 1), PL i) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      linarith
    have htower := armField_pathIntegral_jetL2_tower_le (I := I) g₀ 2 a Ψ₀ hSI hSopen hj0
      (Real.sqrt_nonneg _) hjet
    rw [← hC₀def] at htower
    refine le_trans htower (pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_max_left _ _) 2)
  · have hnn : (0 : ℝ) ≤ 8 * Br ^ 2 + 2 * ∑ i ∈ Finset.range (a + 1), P1 i := by
      have hsum : (0 : ℝ) ≤ ∑ i ∈ Finset.range (a + 1), P1 i :=
        Finset.sum_nonneg fun i _ => hP1_nn i
      nlinarith [sq_nonneg Br]
    have hjet : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 3 2 i (Ψ₁ s)‖ ^ 2) ≤
          Real.sqrt (8 * Br ^ 2 + 2 * ∑ i ∈ Finset.range (a + 1), P1 i) ^ 2 := by
      intro s hs
      rw [Real.sq_sqrt hnn]
      simp only [hΨ₁def]
      have htow := jetTowerSum_add_le (I := I) g₀ 3 2 (a + 1)
        ((-2 : ℝ) • linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s)
        (deTurckLieArm1Coeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
      have hsc : (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 3 2 i
          ((-2 : ℝ) • linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s)‖ ^ 2) =
          4 * ∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 3 2 i
            (linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s)‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [iteratedCovGrad_smul', norm_smul]
        rw [show ‖(-2 : ℝ)‖ = 2 by rw [Real.norm_eq_abs]; norm_num]
        ring
      have hRj := (hJr T T' hδ_le hδ hδ'_le hδ' hTball hT'ball).2.1 s hs
      have hLsum : (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 3 2 i
          (deTurckLieArm1Coeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2) ≤
          ∑ i ∈ Finset.range (a + 1), P1 i :=
        Finset.sum_le_sum fun i hi =>
          hP1j T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i
            (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) s hs
      linarith
    have htower := armField_pathIntegral_jetL2_tower_le (I := I) g₀ 3 a Ψ₁ hSI hSopen hj1
      (Real.sqrt_nonneg _) hjet
    rw [← hC₁def] at htower
    refine le_trans htower (pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_max_right _ _) 2)

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
theorem exists_iteratedCovGradTwo_gradSlotAntisym_curvatureCoeff
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : SmoothCcTensor g₀ 2 4,
      ∀ S : SmoothCcTensor g₀ 0 2,
        iteratedCovGrad (I := I) g₀ 0 2 2 S
            - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrSection (I := I)
                g₀ (Equiv.swap (0 : Fin 4) 1) (iteratedCovGrad (I := I) g₀ 0 2 2 S) =
          appCcRS (I := I) (M := M) g₀ 0 2 4 C S := by
  classical
  refine ⟨⟨⟨fun y : M =>
      (show Tensor0SBundle.TensorRSSpace 2 4 I y from
        TensorRSSpace.ofCLM (slotFreeCurvOpFib (I := I) (M := M) g₀ 2 y)),
      slotFreeCurvOpFib_contMDiff (I := I) (M := M) g₀ 2⟩,
    HasCompactSupport.of_compactSpace _⟩, ?_⟩
  intro S
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  apply ContinuousMultilinearMap.ext
  intro v
  rw [unitModel_sub_local (I := I) g₀ 4 _ _ x, ContinuousMultilinearMap.sub_apply,
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrSection_unitModel (I := I)
      g₀ (Equiv.swap (0 : Fin 4) 1) (iteratedCovGrad (I := I) g₀ 0 2 2 S) x,
    ContinuousMultilinearMap.domDomCongr_apply]
  set Xs : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x (v 0), smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩
    with hXs_def
  set Ys : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x (v 1), smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩
    with hYs_def
  have hXx : Xs x = v 0 := smoothExtensionTangent_eq (I := I) x (v 0)
  have hYx : Ys x = v 1 := smoothExtensionTangent_eq (I := I) x (v 1)
  set m : Fin 2 → TangentSpace I x := ![v 2, v 3] with hm_def
  have hv_eq : v = Fin.cons (Xs x) (Fin.cons (Ys x) m) := by
    rw [hXx, hYx, hm_def]
    funext i
    fin_cases i <;> rfl
  have hv_swap : (fun i => v ((Equiv.swap (0 : Fin 4) 1) i)) =
      Fin.cons (Ys x) (Fin.cons (Xs x) m) := by
    rw [hXx, hYx, hm_def]
    funext i
    fin_cases i <;> rfl
  have h1 : unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorSecondCovDeriv (I := I) g₀ 0 2 (fun b => Xs b) (fun b => Ys b)
            (fun y : M => S.toSection y) x)
          (unitZeroSec (I := I) (M := M) x)) m := by
    conv_lhs => rw [hv_eq]
    rw [unitModel]
    exact tensorSecondCovDeriv_eq_covGrad_succ_twoSlotEval_genVal (I := I) (M := M) g₀ 2 S
      Xs.contMDiff Ys.contMDiff x m
  have h2 : unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
        (fun i => v ((Equiv.swap (0 : Fin 4) 1) i)) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorSecondCovDeriv (I := I) g₀ 0 2 (fun b => Ys b) (fun b => Xs b)
            (fun y : M => S.toSection y) x)
          (unitZeroSec (I := I) (M := M) x)) m := by
    rw [hv_swap]
    rw [unitModel]
    exact tensorSecondCovDeriv_eq_covGrad_succ_twoSlotEval_genVal (I := I) (M := M) g₀ 2 S
      Ys.contMDiff Xs.contMDiff x m
  have h3 : tensorSecondCovDeriv (I := I) g₀ 0 2 (fun b => Xs b) (fun b => Ys b)
        (fun y : M => S.toSection y) x -
      tensorSecondCovDeriv (I := I) g₀ 0 2 (fun b => Ys b) (fun b => Xs b)
        (fun y : M => S.toSection y) x =
      riemannSec (tensorCov (I := I) g₀ 0 2) (fun b => Xs b) (fun b => Ys b)
        (fun y : M => S.toSection y) x :=
    tensorSecondCovDeriv_antisymm_eq_riemannSec (I := I) g₀ 0 2
      (fun y : M => S.toSection y)
      ((Xs.contMDiff x).mdifferentiableAt (by simp))
      ((Ys.contMDiff x).mdifferentiableAt (by simp))
  have h4 : Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorSecondCovDeriv (I := I) g₀ 0 2 (fun b => Xs b) (fun b => Ys b)
            (fun y : M => S.toSection y) x) (unitZeroSec (I := I) (M := M) x)) m -
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorSecondCovDeriv (I := I) g₀ 0 2 (fun b => Ys b) (fun b => Xs b)
            (fun y : M => S.toSection y) x) (unitZeroSec (I := I) (M := M) x)) m =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          riemannSec (tensorCov (I := I) g₀ 0 2) (fun b => Xs b) (fun b => Ys b)
            (fun y : M => S.toSection y) x) (unitZeroSec (I := I) (M := M) x)) m := by
    rw [← h3]
    rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorSecondCovDeriv (I := I) g₀ 0 2 (fun b => Xs b) (fun b => Ys b)
          (fun y : M => S.toSection y) x -
        tensorSecondCovDeriv (I := I) g₀ 0 2 (fun b => Ys b) (fun b => Xs b)
          (fun y : M => S.toSection y) x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorSecondCovDeriv (I := I) g₀ 0 2 (fun b => Xs b) (fun b => Ys b)
          (fun y : M => S.toSection y) x) -
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorSecondCovDeriv (I := I) g₀ 0 2 (fun b => Ys b) (fun b => Xs b)
          (fun y : M => S.toSection y) x) from rfl]
    rw [ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub,
      ContinuousMultilinearMap.sub_apply]
  have h5 := riemannSec_tensorCov_apply_eval (I := I) (M := M) g₀ 0 2 Xs Ys
    S.toSection (unitZeroSec (I := I) (M := M)) x m
  have h6 : riemannSec
      (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g₀))
      (fun b => Xs b) (fun b => Ys b) (fun b => unitZeroSec (I := I) (M := M) b) x = 0 :=
    riemannSec_tensor0SCov_zero_eq_zero (I := I) g₀ Xs Ys
      (fun b => unitZeroSec (I := I) (M := M) b) (contMDiff_unitZeroSection (I := I) (M := M)) x
  have h7 := riemannSec_tensorCov_baseSlot_eval (I := I) (M := M) g₀ 2 Xs Ys
    (fun b => (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from S.toSection b)
      (unitZeroSec (I := I) (M := M) b))
    (contMDiff_unitEvalSection (I := I) (M := M) g₀ 2 S) x m
  have h8 : ∀ u : TangentSpace I x, baseSlotCurv (I := I) g₀ Xs Ys x u =
      riemannOp (LeviCivita (I := I) g₀) x (v 0) (v 1) u := by
    intro u
    rw [show baseSlotCurv (I := I) g₀ Xs Ys x u =
        riemannSec (LeviCivita (I := I) g₀) (fun b => Xs b) (fun b => Ys b)
          (fun b => smoothExtensionTangent (I := I) x u b) x from rfl]
    rw [riemannSec_eq_riemannOp_smooth (cov := LeviCivita (I := I) g₀) Xs.contMDiff Ys.contMDiff
      (smoothExtensionTangent_contMDiff (I := I) x u)]
    rw [smoothExtensionTangent_eq (I := I) x u, hXx, hYx]
  have h9 := slotFreeCurvOpFib_apply_eval (I := I) (M := M) g₀ 2 x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from S.toSection x)
      (unitZeroSec (I := I) (M := M) x)) (v 0) (v 1) m
  have hv0 : v = Fin.cons (v 0) (Fin.cons (v 1) m) := by
    rw [hm_def]
    funext i
    fin_cases i <;> rfl
  rw [h1, h2, h4, h5, h6, map_zero, Tensor0SSpace.toModel_zero,
    ContinuousMultilinearMap.zero_apply, sub_zero, h7]
  rw [Finset.sum_congr rfl (fun k _ => by rw [h8 (m k)])]
  rw [← h9]
  conv_rhs => rw [unitModel, hv0]
  rfl

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem appCc_appCcRS_assoc_fw (g₀ : SmoothRiemannianMetric I M)
    (Φ : SmoothCcTensor g₀ 4 2) (C : SmoothCcTensor g₀ 2 4) (S : SmoothCcTensor g₀ 0 2) :
    appCc (I := I) (M := M) g₀ 4 2 Φ (appCcRS (I := I) (M := M) g₀ 0 2 4 C S) =
      appCc (I := I) (M := M) g₀ 2 2 (appCcRS (I := I) (M := M) g₀ 2 4 2 Φ C) S := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [appCc_toSection, appCc_toSection, appCcRS_toSection, appCcRS_toSection,
    ContinuousLinearMap.comp_assoc]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem appCc_smul_left_fw (g₀ : SmoothRiemannianMetric I M) (r s : ℕ) (c : ℝ)
    (Φ : SmoothCcTensor g₀ r s) (W : SmoothCcTensor g₀ 0 r) :
    appCc (I := I) (M := M) g₀ r s (c • Φ) W = c • appCc (I := I) (M := M) g₀ r s Φ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((c • appCc (I := I) (M := M) g₀ r s Φ W).toSection x) =
      c • (appCc (I := I) (M := M) g₀ r s Φ W).toSection x from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [appCc_toSection, appCc_toSection]
  rw [show ((c • Φ).toSection x : Tensor0SBundle.TensorRSSpace r s I x) = c • Φ.toSection x from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [ContinuousLinearMap.smul_comp]

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
theorem exists_deTurckPhiMetTotal_background_curvatureFold_of_symm
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ K₀ : SmoothCcTensor g₀ 2 2,
      ∀ (S : SmoothCcTensor g₀ 0 2),
        (∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ S x v w = ccTensorBilin (I := I) g₀ S x w v) →
        appCc (I := I) (M := M) g₀ 4 2
            (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀
              - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
                  (I := I) (M := M) g₀ g₀)
            (iteratedCovGrad (I := I) g₀ 0 2 2 S) =
          appCc (I := I) (M := M) g₀ 2 2 K₀ (iteratedCovGrad (I := I) g₀ 0 2 0 S) := by
  classical
  obtain ⟨C24, hC24⟩ :=
    exists_iteratedCovGradTwo_gradSlotAntisym_curvatureCoeff (I := I) (M := M) g₀
  refine ⟨(1/2 : ℝ) • appCcRS (I := I) (M := M) g₀ 2 4 2
    (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀
      - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
          (I := I) (M := M) g₀ g₀) C24, ?_⟩
  intro S hSsymm
  set Φd : SmoothCcTensor g₀ 4 2 :=
    deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀
      - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
          (I := I) (M := M) g₀ g₀ with hΦd_def
  set W : SmoothCcTensor g₀ 0 4 := iteratedCovGrad (I := I) g₀ 0 2 2 S with hW_def
  set Wsw : SmoothCcTensor g₀ 0 4 :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrSection (I := I) g₀
      (Equiv.swap (0 : Fin 4) 1) W with hWsw_def
  have hsplit : W = (1/2 : ℝ) • (W + Wsw) + (1/2 : ℝ) • (W - Wsw) := by
    have h : (1/2 : ℝ) • (W + Wsw) + (1/2 : ℝ) • (W - Wsw) =
        ((1/2 : ℝ) + (1/2 : ℝ)) • W + ((1/2 : ℝ) - (1/2 : ℝ)) • Wsw := by
      rw [smul_add, smul_sub, add_smul, sub_smul]
      abel
    rw [h]
    norm_num
  have hsym : ∀ (x : M) (u₀ u₁ u₂ u₃ : TangentSpace I x),
      unitModel (I := I) (M := M) g₀ 4 (W + Wsw) x ![u₀, u₁, u₂, u₃] =
        unitModel (I := I) (M := M) g₀ 4 (W + Wsw) x ![u₁, u₀, u₂, u₃] := by
    intro x u₀ u₁ u₂ u₃
    have hv : ∀ a b : TangentSpace I x,
        (fun i => (![a, b, u₂, u₃] : Fin 4 → TangentSpace I x) ((Equiv.swap (0 : Fin 4) 1) i)) =
          ![b, a, u₂, u₃] := by
      intro a b
      funext i
      fin_cases i <;> rfl
    rw [unitModel_add_local (I := I) (M := M) g₀ 4 W Wsw x,
      ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.add_apply,
      hWsw_def,
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrSection_unitModel
        (I := I) g₀ (Equiv.swap (0 : Fin 4) 1) W x,
      ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply,
      hv u₀ u₁, hv u₁ u₀]
    exact add_comm _ _
  have hkill : appCc (I := I) (M := M) g₀ 4 2 Φd ((1/2 : ℝ) • (W + Wsw)) = 0 := by
    rw [appCc_smul_right, hΦd_def,
      deTurckPhiMetTotal_background_appCc_eq_zero_of_slot01Symm (I := I) (M := M) g₀ g_bg
        (W + Wsw) hsym, smul_zero]
  calc appCc (I := I) (M := M) g₀ 4 2 Φd W
      = appCc (I := I) (M := M) g₀ 4 2 Φd
          ((1/2 : ℝ) • (W + Wsw) + (1/2 : ℝ) • (W - Wsw)) := by rw [← hsplit]
    _ = appCc (I := I) (M := M) g₀ 4 2 Φd ((1/2 : ℝ) • (W + Wsw))
        + appCc (I := I) (M := M) g₀ 4 2 Φd ((1/2 : ℝ) • (W - Wsw)) :=
      appCc_add_right (I := I) (M := M) g₀ 4 2 Φd _ _
    _ = appCc (I := I) (M := M) g₀ 4 2 Φd ((1/2 : ℝ) • (W - Wsw)) := by
      rw [hkill, zero_add]
    _ = (1/2 : ℝ) • appCc (I := I) (M := M) g₀ 4 2 Φd (W - Wsw) :=
      appCc_smul_right (I := I) (M := M) g₀ 4 2 (1/2 : ℝ) Φd _
    _ = (1/2 : ℝ) • appCc (I := I) (M := M) g₀ 4 2 Φd
        (appCcRS (I := I) (M := M) g₀ 0 2 4 C24 S) := by
      rw [hW_def, hWsw_def, hW_def, hC24 S]
    _ = (1/2 : ℝ) • appCc (I := I) (M := M) g₀ 2 2
        (appCcRS (I := I) (M := M) g₀ 2 4 2 Φd C24) S := by
      rw [appCc_appCcRS_assoc_fw (I := I) (M := M) g₀ Φd C24 S]
    _ = appCc (I := I) (M := M) g₀ 2 2
        ((1/2 : ℝ) • appCcRS (I := I) (M := M) g₀ 2 4 2 Φd C24) S := by
      rw [appCc_smul_left_fw (I := I) (M := M) g₀ 2 2 (1/2 : ℝ) _ S]
    _ = appCc (I := I) (M := M) g₀ 2 2
        ((1/2 : ℝ) • appCcRS (I := I) (M := M) g₀ 2 4 2 Φd C24)
        (iteratedCovGrad (I := I) g₀ 0 2 0 S) := by
      rw [iteratedCovGrad_zero]

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (reindexCoeffGen reindexCoeffFibGen reindexCoeffFibGen_apply reindexCoeffGen_toSection deTurckLieTraceCoeff deTurckLieTraceCoeff_toSection deTurckLieTraceFib traceHessianFib domDomCongrFibPerm_apply domDomCongrFib_apply traceHessianSlotPerm deTurckLieArm2DivSlotPermA deTurckLieArm2DivSlotPermAT traceHessianCoeff_toSection)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem thp_perm_comp_fw (σ : Equiv.Perm (Fin 4)) (j : Fin 4) :
    traceHessianSlotPerm ((traceHessianSlotPerm⁻¹ * σ) j) = σ j := by
  rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.apply_symm_apply]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
theorem lieTrace_eq_reindex_fw (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ ρ : Equiv.Perm (Fin 4))
    (hcomp : ∀ j : Fin 4, traceHessianSlotPerm (ρ j) = σ j) :
    deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ =
      reindexCoeffGen (I := I) (M := M) g₀ 4 2
        (traceHessianCoeff (I := I) (M := M) g₀ g₁) ρ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [deTurckLieTraceCoeff_toSection, reindexCoeffGen_toSection, traceHessianCoeff_toSection]
  apply ContinuousLinearMap.ext
  intro D
  rw [reindexCoeffFibGen_apply, deTurckLieTraceFib, traceHessianFib,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    domDomCongrFibPerm_apply, domDomCongrFib_apply,
    Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
  have harg : ContinuousMultilinearMap.domDomCongr σ
      (Tensor0SBundle.Tensor0SSpace.toModel D) =
      ContinuousMultilinearMap.domDomCongr traceHessianSlotPerm
        (ContinuousMultilinearMap.domDomCongr ρ
          (Tensor0SBundle.Tensor0SSpace.toModel D)) := by
    apply ContinuousMultilinearMap.ext
    intro v
    simp only [ContinuousMultilinearMap.domDomCongr_apply]
    refine congrArg _ (funext fun j => ?_)
    rw [hcomp j]
  rw [harg]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem reindexCoeffGen_sub_fw (g₀ : SmoothRiemannianMetric I M)
    (A B : SmoothCcTensor g₀ 4 2) (ρ : Equiv.Perm (Fin 4)) :
    reindexCoeffGen (I := I) (M := M) g₀ 4 2 (A - B) ρ =
      reindexCoeffGen (I := I) (M := M) g₀ 4 2 A ρ -
        reindexCoeffGen (I := I) (M := M) g₀ 4 2 B ρ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    reindexCoeffGen_toSection, reindexCoeffGen_toSection, reindexCoeffGen_toSection,
    SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  apply ContinuousLinearMap.ext
  intro D
  rw [ContinuousLinearMap.sub_apply, reindexCoeffFibGen_apply, reindexCoeffFibGen_apply,
    reindexCoeffFibGen_apply, ContinuousLinearMap.sub_apply]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem normSq_icg_sub_le_fw (g : SmoothRiemannianMetric I M) (r s q : ℕ)
    (A B : SmoothCcTensor g r s) :
    ‖iteratedCovGrad (I := I) g r s q (A - B)‖ ^ 2 ≤
      2 * ‖iteratedCovGrad (I := I) g r s q A‖ ^ 2 +
        2 * ‖iteratedCovGrad (I := I) g r s q B‖ ^ 2 := by
  have htri : ‖iteratedCovGrad (I := I) g r s q (A - B)‖ ≤
      ‖iteratedCovGrad (I := I) g r s q A‖ + ‖iteratedCovGrad (I := I) g r s q B‖ := by
    rw [iteratedCovGrad_sub]
    exact norm_sub_le _ _
  nlinarith [htri, norm_nonneg (iteratedCovGrad (I := I) g r s q (A - B)),
    norm_nonneg (iteratedCovGrad (I := I) g r s q A),
    norm_nonneg (iteratedCovGrad (I := I) g r s q B),
    sq_nonneg (‖iteratedCovGrad (I := I) g r s q A‖ - ‖iteratedCovGrad (I := I) g r s q B‖)]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem rfns_toSection_sub_le_fw (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (A B : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r s x ((A - B).toSection x) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g r s x (A.toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g r s x (B.toSection x) := by
  rw [show (A - B).toSection x = A.toSection x - B.toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  exact riemannianFiberNormSq_sub_le (I := I) (M := M) g r s x _ _

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem normSq_icg_reindex_eq_fw (g₀ : SmoothRiemannianMetric I M)
    (R : SmoothCcTensor g₀ 4 2) (ρ : Equiv.Perm (Fin 4)) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 4 2 i
        (reindexCoeffGen (I := I) (M := M) g₀ 4 2 R ρ)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ 4 2 i R‖ ^ 2 := by
  rw [lc0b_normSq_eq_integral (I := I) (M := M) g₀ 4 (2 + i),
    lc0b_normSq_eq_integral (I := I) (M := M) g₀ 4 (2 + i)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact rfns_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 4 2 R ρ i x

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem gFibreOpBound_mono_fw (g₀ : SmoothRiemannianMetric I M)
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    {δ δ' : ℝ} (hle : δ ≤ δ')
    (hb : gFibreOpBound (I := I) (M := M) g₀ h δ) :
    gFibreOpBound (I := I) (M := M) g₀ h δ' := by
  intro y a b
  refine le_trans (hb y a b) ?_
  have hnn : 0 ≤ Real.sqrt (g₀.inner y a a) * Real.sqrt (g₀.inner y b b) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc δ * Real.sqrt (g₀.inner y a a) * Real.sqrt (g₀.inner y b b)
      = δ * (Real.sqrt (g₀.inner y a a) * Real.sqrt (g₀.inner y b b)) := by ring
    _ ≤ δ' * (Real.sqrt (g₀.inner y a a) * Real.sqrt (g₀.inner y b b)) :=
        mul_le_mul_of_nonneg_right hle hnn
    _ = δ' * Real.sqrt (g₀.inner y a a) * Real.sqrt (g₀.inner y b b) := by ring

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem gFibreOpBound_min_fw (g₀ : SmoothRiemannianMetric I M)
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    {δ₁ δ₂ : ℝ} (h₁ : gFibreOpBound (I := I) (M := M) g₀ h δ₁)
    (h₂ : gFibreOpBound (I := I) (M := M) g₀ h δ₂) :
    gFibreOpBound (I := I) (M := M) g₀ h (min δ₁ δ₂) := by
  intro x v w
  rcases le_total δ₁ δ₂ with hle | hle
  · rw [min_eq_left hle]
    exact h₁ x v w
  · rw [min_eq_right hle]
    exact h₂ x v w

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
theorem deTurckPhiMetTotal_eq_reindex_decomp_fw
    (g₀ g_bg g : SmoothRiemannianMetric I M) :
    deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g =
      reindexCoeffGen (I := I) (M := M) g₀ 4 2
          (traceHessianCoeff (I := I) (M := M) g₀ g)
          (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA)
        + reindexCoeffGen (I := I) (M := M) g₀ 4 2
          (traceHessianCoeff (I := I) (M := M) g₀ g)
          (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT)
        - (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g
            + ricciArmPrincipalCoeff (I := I) (M := M) g₀ g) := by
  have hPhi : deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g =
      (deTurckLieTraceCoeff (I := I) (M := M) g₀ g deTurckLieArm2DivSlotPermA
        + deTurckLieTraceCoeff (I := I) (M := M) g₀ g deTurckLieArm2DivSlotPermAT
        - traceHessianCoeff (I := I) (M := M) g₀ g)
      + traceHessianCoeff (I := I) (M := M) g₀ g
      - (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g
          + ricciArmPrincipalCoeff (I := I) (M := M) g₀ g) := rfl
  rw [hPhi,
    lieTrace_eq_reindex_fw (I := I) (M := M) g₀ g deTurckLieArm2DivSlotPermA
      (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA)
      (thp_perm_comp_fw deTurckLieArm2DivSlotPermA),
    lieTrace_eq_reindex_fw (I := I) (M := M) g₀ g deTurckLieArm2DivSlotPermAT
      (traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT)
      (thp_perm_comp_fw deTurckLieArm2DivSlotPermAT)]
  abel

open DifferentialGeometry.PDE.DeTurck.RicciLinearization (convexPerturbation convexPerturbation_gFibreOpBound realizedFam_inner_of_mem)

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
theorem deTurckPhiTotPathIntegral_deviation_fibreWeighted_jetL2_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (hδ₀_nn : 0 ≤ δ₀) :
    ∃ c Γd : ℝ, 0 ≤ c ∧ 0 ≤ Γd ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
        {βT βT' : ℝ} (hβT_nn : 0 ≤ βT) (hβT'_nn : 0 ≤ βT')
        (hβT : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) βT)
        (hβT' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') βT'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
            ((deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T T'
                (lt_of_le_of_lt hδ_le hδ₀) hδ (lt_of_le_of_lt hδ'_le hδ₀) hδ'
              - deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀).toSection x) ≤
          (c * max βT βT') ^ 2) ∧
        (∑ i ∈ Finset.range (a + 1),
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T T'
                (lt_of_le_of_lt hδ_le hδ₀) hδ (lt_of_le_of_lt hδ'_le hδ₀) hδ'
              - deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)‖ ^ 2) ≤ Γd ^ 2 := by
  classical
  obtain ⟨CTH, hCTH_nn, hCTH⟩ :=
    traceHessianCoeff_sub_background_perOrder_rfns_le_gInvDiffSlotCoeff_rfns (I := I) (M := M) g₀
  obtain ⟨CR, hCR_nn, hCR⟩ :=
    ricciArmPrincipalCoeff_sub_background_perOrder_rfns_le_gInvDiffSlotCoeff_rfns
      (I := I) (M := M) g₀
  obtain ⟨DTH, hDTH_nn, hDTH⟩ :=
    traceHessianCoeff_realizedFam_sub_background_jetL2_perOrder_ballUniform (I := I) (M := M) g₀
      a ha_super hR hδ₀
  obtain ⟨DR, hDR_nn, hDR⟩ :=
    ricciArmPrincipalCoeff_realizedFam_sub_background_jetL2_perOrder_ballUniform
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  set dim : ℝ := (Module.finrank ℝ E : ℝ) with hdim_def
  have hdim_nn : (0 : ℝ) ≤ dim := Nat.cast_nonneg _
  have h1δ₀ : (0 : ℝ) < 1 - δ₀ := by linarith
  set Sco : ℝ := 8 * CTH 0 + 8 * CR 0 with hSco_def
  have hSco_nn : 0 ≤ Sco := by
    have := hCTH_nn 0
    have := hCR_nn 0
    rw [hSco_def]
    linarith
  set Γsq : ℝ := 8 * (∑ i ∈ Finset.range (a + 1), DTH i)
    + 8 * (∑ i ∈ Finset.range (a + 1), DR i) with hΓsq_def
  have hΓsq_nn : 0 ≤ Γsq := by
    have h1 : 0 ≤ ∑ i ∈ Finset.range (a + 1), DTH i :=
      Finset.sum_nonneg fun i _ => hDTH_nn i
    have h2 : 0 ≤ ∑ i ∈ Finset.range (a + 1), DR i :=
      Finset.sum_nonneg fun i _ => hDR_nn i
    rw [hΓsq_def]
    linarith
  refine ⟨Real.sqrt Sco * (dim / (1 - δ₀)), Real.sqrt Γsq,
    mul_nonneg (Real.sqrt_nonneg _) (div_nonneg hdim_nn (le_of_lt h1δ₀)),
    Real.sqrt_nonneg _, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' βT βT' hβT_nn hβT'_nn hβT hβT' hTball hT'ball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ') := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_realizedSmallSet hδ_lt hδ'_lt
  have hSopen : IsOpen (realizedSmallSet (δ := δ) (δ' := δ')) := realizedSmallSet_isOpen
  set ρA : Equiv.Perm (Fin 4) := traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA with hρA_def
  set ρAT : Equiv.Perm (Fin 4) := traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT
    with hρAT_def
  set Ψdev : ℝ → SmoothCcTensor g₀ 4 2 := fun s =>
    deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg (realizedFam (I := I) g₀ T T' hδ hδ' s)
      - deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀ with hΨdev_def
  have hdev_eq : ∀ s : ℝ, Ψdev s =
      reindexCoeffGen (I := I) (M := M) g₀ 4 2
          (traceHessianCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s)
            - traceHessianCoeff (I := I) (M := M) g₀ g₀) ρA
        + reindexCoeffGen (I := I) (M := M) g₀ 4 2
          (traceHessianCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s)
            - traceHessianCoeff (I := I) (M := M) g₀ g₀) ρAT
        - ((ricciArmPrincipalCoeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s)
            - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)
          + (ricciArmPrincipalCoeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s)
            - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)) := by
    intro s
    simp only [hΨdev_def]
    rw [deTurckPhiMetTotal_eq_reindex_decomp_fw (I := I) (M := M) g₀ g_bg
        (realizedFam (I := I) g₀ T T' hδ hδ' s),
      deTurckPhiMetTotal_eq_reindex_decomp_fw (I := I) (M := M) g₀ g_bg g₀,
      reindexCoeffGen_sub_fw (I := I) (M := M) g₀ _ _ ρA,
      reindexCoeffGen_sub_fw (I := I) (M := M) g₀ _ _ ρAT]
    abel
  have hj2 : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4
      (fun s => deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
        (realizedFam (I := I) g₀ T T' hδ hδ' s)) (δ := δ) (δ' := δ') :=
    deTurckPhiMetTotal_realizedFam_jointSmooth (I := I) (M := M) g₀ g_bg T T' hδ hδ'
  have hjdev : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4 Ψdev
      (δ := δ) (δ' := δ') := by
    have hconst : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1
          ((deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀).toSection p.1))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
      (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀).toSection.contMDiff.comp_contMDiffOn
        contMDiffOn_fst
    have hj2' : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1
          ((deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2)).toSection p.1))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
      have h := hj2
      rw [linearizedRicciThreeArmHjoint] at h
      exact h
    have hsub := jointTotalSpaceRS_sub_fw (I := I) (r := 4) (s := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ'))
      (fun p : M × ℝ => (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2)).toSection p.1)
      (fun p : M × ℝ => (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀).toSection p.1)
      hj2' hconst
    refine hsub.congr (fun p _ => ?_)
    refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
      (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1 t) ?_
    simp only [hΨdev_def]
    rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  set Pdev : SmoothCcTensor g₀ 4 2 := pathIntegralCoeffField (I := I) (M := M) g₀ 4 2 Ψdev
    (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hjdev with hPdev_def
  have hc2tot : ∀ x : M, ContinuousOn (fun t : ℝ =>
      Tensor0SBundle.TensorRSSpace.toModel
        ((deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
          (realizedFam (I := I) g₀ T T' hδ hδ' t)).toSection x))
      (realizedSmallSet (δ := δ) (δ' := δ')) := by
    intro x
    have h := hj2
    rw [linearizedRicciThreeArmHjoint] at h
    exact jointContMDiff_toModel_continuous_slice (I := I) g₀ 4 2
      (fun s => deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
        (realizedFam (I := I) g₀ T T' hδ hδ' s))
      (realizedSmallSet (δ := δ) (δ' := δ')) h x
  have hcdev : ∀ x : M, ContinuousOn (fun t : ℝ =>
      Tensor0SBundle.TensorRSSpace.toModel ((Ψdev t).toSection x))
      (realizedSmallSet (δ := δ) (δ' := δ')) := fun x =>
    jointContMDiff_toModel_continuous_slice (I := I) g₀ 4 2 Ψdev
      (realizedSmallSet (δ := δ) (δ' := δ')) hjdev x
  have heq : deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T T'
      (lt_of_le_of_lt hδ_le hδ₀) hδ (lt_of_le_of_lt hδ'_le hδ₀) hδ'
      - deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀ = Pdev := by
    have hPeq : deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T T'
        (lt_of_le_of_lt hδ_le hδ₀) hδ (lt_of_le_of_lt hδ'_le hδ₀) hδ' =
        pathIntegralCoeffField (I := I) (M := M) g₀ 4 2
          (fun s => deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
            (realizedFam (I := I) g₀ T T' hδ hδ' s))
          (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj2 := rfl
    apply SmoothCcTensor.ext
    apply ContMDiffSection.ext
    intro x
    apply Tensor0SBundle.TensorRSSpace.toModel_injective
    show Tensor0SBundle.TensorRSSpace.toModel
        ((deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T T'
          (lt_of_le_of_lt hδ_le hδ₀) hδ (lt_of_le_of_lt hδ'_le hδ₀) hδ'
        - deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀).toSection x) =
      Tensor0SBundle.TensorRSSpace.toModel (Pdev.toSection x)
    rw [show (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T T'
          (lt_of_le_of_lt hδ_le hδ₀) hδ (lt_of_le_of_lt hδ'_le hδ₀) hδ'
        - deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀).toSection x =
        (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T T'
          (lt_of_le_of_lt hδ_le hδ₀) hδ (lt_of_le_of_lt hδ'_le hδ₀) hδ').toSection x
        - (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀).toSection x from by
      rw [SmoothCcTensor.toSection_sub]; rfl]
    rw [Tensor0SBundle.TensorRSSpace.toModel_sub, hPeq, hPdev_def,
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pathIntegralCoeffField_toModel,
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pathIntegralCoeffField_toModel]
    have hint : IntervalIntegrable (fun t : ℝ =>
        Tensor0SBundle.TensorRSSpace.toModel
          ((deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
            (realizedFam (I := I) g₀ T T' hδ hδ' t)).toSection x))
        MeasureTheory.volume 0 1 :=
      ((hc2tot x).mono hSI).intervalIntegrable
    rw [show (∫ t in (0:ℝ)..1, Tensor0SBundle.TensorRSSpace.toModel ((Ψdev t).toSection x)) =
        ∫ t in (0:ℝ)..1,
          (Tensor0SBundle.TensorRSSpace.toModel
            ((deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
              (realizedFam (I := I) g₀ T T' hδ hδ' t)).toSection x)
          - Tensor0SBundle.TensorRSSpace.toModel
            ((deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀).toSection x)) from
      intervalIntegral.integral_congr (fun t _ => by
        simp only [hΨdev_def]
        rw [show ((deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
              (realizedFam (I := I) g₀ T T' hδ hδ' t))
            - deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀).toSection x =
            (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
              (realizedFam (I := I) g₀ T T' hδ hδ' t)).toSection x
            - (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀).toSection x from by
          rw [SmoothCcTensor.toSection_sub]; rfl]
        rw [Tensor0SBundle.TensorRSSpace.toModel_sub])]
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const,
      intervalIntegral.integral_const]
    norm_num
  refine ⟨?_, ?_⟩
  · intro x
    rw [heq, hPdev_def]
    set K : ℝ := riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
      ((gInvDiffSlotCoeff (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' (0 : ℝ))).toSection x)
      with hK_def
    have hmaxβ_nn : (0 : ℝ) ≤ max βT βT' := le_trans hβT_nn (le_max_left _ _)
    have hcb_nn : (0 : ℝ) ≤ Real.sqrt Sco * (dim / (1 - δ₀)) * max βT βT' :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (div_nonneg hdim_nn (le_of_lt h1δ₀))) hmaxβ_nn
    have hsup : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x ((Ψdev t).toSection x)) ≤
          Real.sqrt Sco * (dim / (1 - δ₀)) * max βT βT' := by
      intro t ht
      have hbound : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x ((Ψdev t).toSection x) ≤
          (Real.sqrt Sco * (dim / (1 - δ₀)) * max βT βT') ^ 2 := by
        set g₁ := realizedFam (I := I) g₀ T T' hδ hδ' t with hg₁_def
        set DTHs : SmoothCcTensor g₀ 4 2 :=
          traceHessianCoeff (I := I) (M := M) g₀ g₁
            - traceHessianCoeff (I := I) (M := M) g₀ g₀ with hDTHs_def
        set DRs : SmoothCcTensor g₀ 4 2 :=
          ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
            - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀ with hDRs_def
        have h0 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x ((Ψdev t).toSection x) ≤
            4 * riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
              ((reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρA).toSection x)
            + 4 * riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
              ((reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρAT).toSection x)
            + 8 * riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (DRs.toSection x) := by
          rw [hdev_eq t]
          have h1 := rfns_toSection_sub_le_fw (I := I) (M := M) g₀ 4 2
            (reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρA
              + reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρAT) (DRs + DRs) x
          have h2 := lc0b_rfns_toSection_add_le (I := I) (M := M) g₀ 4 2
            (reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρA)
            (reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρAT) x
          have h3 := lc0b_rfns_toSection_add_le (I := I) (M := M) g₀ 4 2 DRs DRs x
          linarith
        have hAr : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
            ((reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρA).toSection x) =
            riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (DTHs.toSection x) := by
          rw [reindexCoeffGen_toSection]
          exact DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannianFiberNormSq_reindexCoeffFibGen
            (I := I) (M := M) g₀ 4 2 x ρA
            (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
              DTHs.toSection x)
        have hATr : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
            ((reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρAT).toSection x) =
            riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (DTHs.toSection x) := by
          rw [reindexCoeffGen_toSection]
          exact DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannianFiberNormSq_reindexCoeffFibGen
            (I := I) (M := M) g₀ 4 2 x ρAT
            (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
              DTHs.toSection x)
        rw [hAr, hATr] at h0
        set Ks : ℝ := riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          ((gInvDiffSlotCoeff (I := I) g₀ g₁).toSection x) with hKs_def
        have hTH0 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (DTHs.toSection x) ≤
            CTH 0 * Ks := by
          have h := hCTH g₁ 0 x
          simpa [hDTHs_def, hKs_def] using h
        have hR0 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (DRs.toSection x) ≤
            CR 0 * Ks := by
          have h := hCR g₁ 0 x
          simpa [hDRs_def, hKs_def] using h
        have hKs_nn : 0 ≤ Ks := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 2 x _
        set δc : ℝ := min ((1 - t) * βT' + t * βT) δ₀ with hδc_def
        have hβconv : gFibreOpBound (I := I) (M := M) g₀
            (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' t))
            ((1 - t) * βT' + t * βT) :=
          convexPerturbation_gFibreOpBound (I := I) g₀ T T' hβT hβT' ht.1 ht.2
        have hδconv : gFibreOpBound (I := I) (M := M) g₀
            (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' t))
            ((1 - t) * δ' + t * δ) :=
          convexPerturbation_gFibreOpBound (I := I) g₀ T T' hδ hδ' ht.1 ht.2
        have hδ₀b : gFibreOpBound (I := I) (M := M) g₀
            (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' t)) δ₀ :=
          gFibreOpBound_mono_fw (I := I) (M := M) g₀ _
            (by nlinarith [ht.1, ht.2]) hδconv
        have hmin : gFibreOpBound (I := I) (M := M) g₀
            (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' t)) δc :=
          gFibreOpBound_min_fw (I := I) (M := M) g₀ _ hβconv hδ₀b
        have hδc_nn : 0 ≤ δc :=
          le_min (by nlinarith [ht.1, ht.2]) hδ₀_nn
        have hδc_lt : δc < 1 := lt_of_le_of_lt (min_le_right _ _) hδ₀
        have htmem : t ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
          Icc_subset_realizedSmallSet hδ_lt hδ'_lt ht
        have htie : ∀ (y : M) (v w : TangentSpace I y),
            g₁.inner y v w = g₀.inner y v w +
              ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' t) y v w := by
          intro y v w
          rw [hg₁_def]
          exact realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ' htmem y v w
        have hendo :=
          DifferentialGeometry.Analysis.Sobolev.TensorHilbert.riemannianFiberNormSq_gInvDiffSlotEndo_le
            (I := I) (M := M) g₀ g₁ _ htie hδc_lt hδc_nn hmin x
        have hKs_endo : Ks ≤ ((Module.finrank ℝ E : ℝ) * (δc / (1 - δc))) ^ 2 := by
          rw [hKs_def]
          rw [show (gInvDiffSlotCoeff (I := I) g₀ g₁).toSection x =
              (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM
                (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvDiffSlotEndo
                  (I := I) g₀ g₁ x)) from rfl]
          exact hendo
        have hratio : δc / (1 - δc) ≤ max βT βT' / (1 - δ₀) := by
          have h1 : δc ≤ max βT βT' := by
            refine le_trans (min_le_left _ _) ?_
            nlinarith [le_max_left βT βT', le_max_right βT βT', ht.1, ht.2]
          have h2 : 1 - δ₀ ≤ 1 - δc := by
            have := min_le_right ((1 - t) * βT' + t * βT) δ₀
            linarith
          rw [div_le_div_iff₀ (by linarith) h1δ₀]
          nlinarith [mul_le_mul_of_nonneg_right h1 (show (0:ℝ) ≤ 1 - δc by linarith),
            mul_le_mul_of_nonneg_left h2 hδc_nn]
        have hslot : Ks ≤ (dim * (max βT βT' / (1 - δ₀))) ^ 2 := by
          refine le_trans hKs_endo ?_
          refine pow_le_pow_left₀
            (mul_nonneg hdim_nn (div_nonneg hδc_nn (by linarith))) ?_ 2
          exact mul_le_mul_of_nonneg_left hratio hdim_nn
        have hc2 : (Real.sqrt Sco * (dim / (1 - δ₀)) * max βT βT') ^ 2 =
            Sco * (dim * (max βT βT' / (1 - δ₀))) ^ 2 := by
          rw [show (Real.sqrt Sco * (dim / (1 - δ₀)) * max βT βT') ^ 2 =
              Real.sqrt Sco ^ 2 * (dim * (max βT βT' / (1 - δ₀))) ^ 2 from by ring,
            Real.sq_sqrt hSco_nn]
        rw [hc2, hSco_def]
        have hmul := mul_le_mul_of_nonneg_left hslot hSco_nn
        rw [hSco_def] at hmul
        nlinarith [h0, hTH0, hR0, hmul, hKs_nn, hCTH_nn 0, hCR_nn 0]
      calc Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x ((Ψdev t).toSection x))
          ≤ Real.sqrt ((Real.sqrt Sco * (dim / (1 - δ₀)) * max βT βT') ^ 2) :=
            Real.sqrt_le_sqrt hbound
        _ = Real.sqrt Sco * (dim / (1 - δ₀)) * max βT βT' := Real.sqrt_sq hcb_nn
    exact riemannianFiberNormSq_pathIntegralCoeffField_le_sq (I := I) (M := M) g₀ 4 2 Ψdev
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hjdev x
      (Real.sqrt Sco * (dim / (1 - δ₀)) * max βT βT') hcb_nn
      ((hcdev x).mono (Icc_subset_realizedSmallSet hδ_lt hδ'_lt)) hsup
  · rw [heq, hPdev_def]
    have hjet : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i (Ψdev s)‖ ^ 2) ≤
          Real.sqrt Γsq ^ 2 := by
      intro s hs
      rw [Real.sq_sqrt hΓsq_nn]
      set g₁ := realizedFam (I := I) g₀ T T' hδ hδ' s with hg₁_def
      set DTHs : SmoothCcTensor g₀ 4 2 :=
        traceHessianCoeff (I := I) (M := M) g₀ g₁
          - traceHessianCoeff (I := I) (M := M) g₀ g₀ with hDTHs_def
      set DRs : SmoothCcTensor g₀ 4 2 :=
        ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
          - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀ with hDRs_def
      have hs1 : (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i (Ψdev s)‖ ^ 2) ≤
          2 * (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρA
              + reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρAT)‖ ^ 2)
          + 2 * (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (DRs + DRs)‖ ^ 2) := by
        have h := Finset.sum_le_sum (f := fun i => ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (Ψdev s)‖ ^ 2)
          (g := fun i => 2 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
              (reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρA
                + reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρAT)‖ ^ 2
            + 2 * ‖iteratedCovGrad (I := I) g₀ 4 2 i (DRs + DRs)‖ ^ 2)
          (s := Finset.range (a + 1)) (fun i _ => by
            rw [hdev_eq s]
            exact normSq_icg_sub_le_fw (I := I) (M := M) g₀ 4 2 i _ _)
        calc (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i (Ψdev s)‖ ^ 2)
            ≤ ∑ i ∈ Finset.range (a + 1),
              (2 * ‖iteratedCovGrad (I := I) g₀ 4 2 i
                  (reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρA
                    + reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρAT)‖ ^ 2
                + 2 * ‖iteratedCovGrad (I := I) g₀ 4 2 i (DRs + DRs)‖ ^ 2) := h
          _ = 2 * (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i
                (reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρA
                  + reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρAT)‖ ^ 2)
              + 2 * (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i
                (DRs + DRs)‖ ^ 2) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      have hAB := jetTowerSum_add_le (I := I) g₀ 4 2 (a + 1)
        (reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρA)
        (reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρAT)
      have hCC := jetTowerSum_add_le (I := I) g₀ 4 2 (a + 1) DRs DRs
      have hAeq : (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i
          (reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρA)‖ ^ 2) =
          ∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i DTHs‖ ^ 2 :=
        Finset.sum_congr rfl (fun i _ => normSq_icg_reindex_eq_fw (I := I) (M := M) g₀ DTHs ρA i)
      have hATeq : (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i
          (reindexCoeffGen (I := I) (M := M) g₀ 4 2 DTHs ρAT)‖ ^ 2) =
          ∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i DTHs‖ ^ 2 :=
        Finset.sum_congr rfl (fun i _ => normSq_icg_reindex_eq_fw (I := I) (M := M) g₀ DTHs ρAT i)
      have hDTHsum : (∑ i ∈ Finset.range (a + 1),
          ‖iteratedCovGrad (I := I) g₀ 4 2 i DTHs‖ ^ 2) ≤
          ∑ i ∈ Finset.range (a + 1), DTH i :=
        Finset.sum_le_sum (fun i hi => by
          rw [hDTHs_def, hg₁_def]
          exact hDTH T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i
            (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) s hs)
      have hDRsum : (∑ i ∈ Finset.range (a + 1),
          ‖iteratedCovGrad (I := I) g₀ 4 2 i DRs‖ ^ 2) ≤
          ∑ i ∈ Finset.range (a + 1), DR i :=
        Finset.sum_le_sum (fun i hi => by
          rw [hDRs_def, hg₁_def]
          exact hDR T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i
            (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) s hs)
      rw [hAeq, hATeq] at hAB
      rw [hΓsq_def]
      linarith
    exact armField_pathIntegral_jetL2_tower_le (I := I) g₀ 4 a Ψdev hSI hSopen hjdev
      (Real.sqrt_nonneg _) hjet

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
theorem deTurckSmoothRemainderDiff_threeArm_coeffC0_jetL2_fibreWeighted_ballUniform_of_symm
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
          ccTensorBilin (I := I) g₀ T' x v w = ccTensorBilin (I := I) g₀ T' x w v)
        {βT βT' : ℝ} (hβT_nn : 0 ≤ βT) (hβT'_nn : 0 ≤ βT')
        (hβT : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) βT)
        (hβT' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') βT'),
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
            (ΛC * max βT βT') ^ 2) ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i C₀‖ ^ 2) ≤ Γ ^ 2 ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 3 2 i C₁‖ ^ 2) ≤ Γ ^ 2 ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i C₂‖ ^ 2) ≤ Γ ^ 2 := by
  classical
  obtain ⟨K₀, hK₀fold⟩ :=
    exists_deTurckPhiMetTotal_background_curvatureFold_of_symm (I := I) (M := M) g₀ g_bg
  obtain ⟨ΛA, ΓA, hΛA_nn, hΓA_nn, harm⟩ :=
    deTurckRHSArmDiff_threeArm_canonicalTop_coeffC0_jetL2_ballUniform_of_symm
      (I := I) g₀ g_bg a ha_super hR hδ₀
  obtain ⟨cD, ΓD, hcD_nn, hΓD_nn, hdev⟩ :=
    deTurckPhiTotPathIntegral_deviation_fibreWeighted_jetL2_ballUniform
      (I := I) g₀ g_bg a ha_super hR hδ₀ hδ₀_nn
  obtain ⟨ΛK, hΛK_nn, hΛK⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 2 K₀
  set ΓK : ℝ := Real.sqrt (∑ i ∈ Finset.range (a + 1),
    ‖iteratedCovGrad (I := I) g₀ 2 2 i K₀‖ ^ 2) with hΓK_def
  have hΓK_nn : 0 ≤ ΓK := Real.sqrt_nonneg _
  have hΓKjet : (∑ i ∈ Finset.range (a + 1),
      ‖iteratedCovGrad (I := I) g₀ 2 2 i K₀‖ ^ 2) ≤ ΓK ^ 2 := by
    rw [hΓK_def, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  have hsq_mono : ∀ s t : ℝ, 0 ≤ s → s ≤ t → s ^ 2 ≤ t ^ 2 := by
    intro s t hs hst
    nlinarith
  refine ⟨max (Real.sqrt (2 * ΛA ^ 2 + 2 * Real.sqrt ΛK ^ 2)) (max ΛA cD),
    max (Real.sqrt (2 * ΓA ^ 2 + 2 * ΓK ^ 2)) (max ΓA ΓD),
    le_trans (Real.sqrt_nonneg _) (le_max_left _ _),
    le_trans (Real.sqrt_nonneg _) (le_max_left _ _), ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTsymm hT'symm βT βT' hβT_nn hβT'_nn hβT hβT'
    hTball hT'ball
  obtain ⟨C₀, C₁, hidArm, hC₀sup, hC₁sup, hC₀jet, hC₁jet⟩ :=
    harm T T' hδ_le hδ hδ'_le hδ' hTsymm hT'symm hTball hT'ball
  obtain ⟨hdevsup, hdevjet⟩ :=
    hdev T T' hδ_le hδ hδ'_le hδ' hβT_nn hβT'_nn hβT hβT' hTball hT'ball
  have hSsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ (T - T') x v w = ccTensorBilin (I := I) g₀ (T - T') x w v := by
    intro x v w
    rw [ccTensorBilin_sub_fw, ccTensorBilin_sub_fw, hTsymm x v w, hT'symm x v w]
  have hKfold := hK₀fold (T - T') hSsymm
  have hKfold' : appCc (I := I) (M := M) g₀ 4 2
        (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀)
        (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) -
      appCc (I := I) (M := M) g₀ 4 2
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
          (I := I) (M := M) g₀ g₀)
        (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) =
      appCc (I := I) (M := M) g₀ 2 2 K₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) := by
    rw [← appCc_sub_left]
    exact hKfold
  have hlift : rawTensorConnLapSmooth (I := I) g₀ 0 2 (T - T') =
      appCc (I := I) (M := M) g₀ 4 2
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmPrincipalCoeffPure
          (I := I) (M := M) g₀ g₀)
        (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) := by
    apply smoothCcTensor_ext_of_unitModel
    intro x
    apply ContinuousMultilinearMap.ext
    intro v
    exact
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.rawTensorConnLapSmooth_eq_appCc_cometricDoubleTrace
        (I := I) (M := M) g₀ (T - T') x v
  refine ⟨C₀ + K₀, C₁,
    deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T T'
        (lt_of_le_of_lt hδ_le hδ₀) hδ (lt_of_le_of_lt hδ'_le hδ₀) hδ'
      - deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [deTurckSmoothRemainderDiff_eq_armDiff_sub_connLapDiff (I := I) g₀ g_bg T T'
      (lt_of_le_of_lt hδ_le hδ₀) hδ (lt_of_le_of_lt hδ'_le hδ₀) hδ', hidArm, hlift,
      appCc_add_left, appCc_sub_left, ← hKfold']
    abel
  · intro x
    have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (K₀.toSection x) ≤
        Real.sqrt ΛK ^ 2 := by
      rw [Real.sq_sqrt hΛK_nn]
      exact hΛK x
    exact (threeArmCoeffSum_rfns_le (I := I) g₀ C₀ K₀ ΛA (Real.sqrt ΛK) x (hC₀sup x) h1).trans
      (hsq_mono _ _ (Real.sqrt_nonneg _) (le_max_left _ _))
  · intro x
    exact (hC₁sup x).trans
      (hsq_mono _ _ hΛA_nn (le_trans (le_max_left ΛA cD) (le_max_right _ _)))
  · intro x
    have hm_nn : 0 ≤ max βT βT' := le_trans hβT_nn (le_max_left _ _)
    refine (hdevsup x).trans (hsq_mono _ _ (mul_nonneg hcD_nn hm_nn) ?_)
    exact mul_le_mul_of_nonneg_right
      (le_trans (le_max_right ΛA cD) (le_max_right _ _)) hm_nn
  · calc (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i (C₀ + K₀)‖ ^ 2)
        ≤ 2 * (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i C₀‖ ^ 2) +
            2 * (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i K₀‖ ^ 2) :=
          jetTowerSum_add_le (I := I) g₀ 2 2 (a + 1) C₀ K₀
      _ ≤ 2 * ΓA ^ 2 + 2 * ΓK ^ 2 := by linarith [hC₀jet, hΓKjet]
      _ ≤ (max (Real.sqrt (2 * ΓA ^ 2 + 2 * ΓK ^ 2)) (max ΓA ΓD)) ^ 2 := by
          have hs : Real.sqrt (2 * ΓA ^ 2 + 2 * ΓK ^ 2) ^ 2 = 2 * ΓA ^ 2 + 2 * ΓK ^ 2 :=
            Real.sq_sqrt (by positivity)
          have hle : Real.sqrt (2 * ΓA ^ 2 + 2 * ΓK ^ 2) ≤
              max (Real.sqrt (2 * ΓA ^ 2 + 2 * ΓK ^ 2)) (max ΓA ΓD) := le_max_left _ _
          nlinarith [hs, hle, Real.sqrt_nonneg (2 * ΓA ^ 2 + 2 * ΓK ^ 2)]
  · exact hC₁jet.trans
      (hsq_mono _ _ hΓA_nn (le_trans (le_max_left ΓA ΓD) (le_max_right _ _)))
  · exact hdevjet.trans
      (hsq_mono _ _ hΓD_nn (le_trans (le_max_right ΓA ΓD) (le_max_right _ _)))

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
