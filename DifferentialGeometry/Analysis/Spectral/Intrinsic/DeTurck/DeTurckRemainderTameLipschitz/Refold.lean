import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitz.TameJet

/-!
# Path-integral triple refold and the arm-1 tame envelopes

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

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck (cometricLmodel)

open DifferentialGeometry.PDE.DeTurck.RicciLinearization (lieDeTurckChartSlope deriv_realizedFam_chartLieDeTurckComp_eq_chartSlope)

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (deTurckLieArm2PrincipalCoeff deTurckLieArm1Coeff deTurckLieCoeffField deTurckLieArm2PrincipalCoeff_realizedFam_jointSmooth deTurckLieArm1Coeff_realizedFam_jointSmooth deTurckLieCoeffField_realizedFam_jointSmooth)

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (reindexCoeffGen reindexCoeffFibGen reindexCoeffFibGen_apply reindexCoeffGen_toSection deTurckLieTraceCoeff deTurckLieTraceCoeff_toSection deTurckLieTraceFib traceHessianFib domDomCongrFibPerm_apply domDomCongrFib_apply traceHessianSlotPerm deTurckLieArm2DivSlotPermA deTurckLieArm2DivSlotPermAT traceHessianCoeff_toSection)

open DifferentialGeometry.PDE.DeTurck.RicciLinearization (convexPerturbation convexPerturbation_gFibreOpBound realizedFam_inner_of_mem)

namespace DeTurckRemainderTameLipschitz
end DeTurckRemainderTameLipschitz

open DeTurckRemainderTameLipschitz

namespace DeTurckRemainderTameLipschitz

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
lemma smoothCcToTensorHs_zero_norm_le_fw (g₀ : SmoothRiemannianMetric I M) (σ : ℝ)
    {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ (0 : SmoothCcTensor g₀ 0 2)‖ ≤ R₀ := by
  have hzero : smoothCcToTensorHs (I := I) (M := M) g₀ σ (0 : SmoothCcTensor g₀ 0 2) = 0 := by
    refine DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHs.ext ?_
    funext i
    rw [smoothCcToTensorHs_coeff]
    rw [show SmoothCcTensor.toL2 (0 : SmoothCcTensor g₀ 0 2) = 0 from map_zero _]
    rw [DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorL2Coeff_eq_inner,
      inner_zero_right]
    rfl
  rw [hzero, norm_zero]
  exact hR₀

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
lemma ccTensorBilin_zero_symm_fw (g₀ : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    ccTensorBilin (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2) x v w =
      ccTensorBilin (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2) x w v := by
  have h0 : ∀ (u₁ u₂ : TangentSpace I x),
      ccTensorBilin (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2) x u₁ u₂ = 0 := by
    intro u₁ u₂
    have hs := ccTensorBilin_sub_fw (I := I) (M := M) g₀
      (0 : SmoothCcTensor g₀ 0 2) (0 : SmoothCcTensor g₀ 0 2) x u₁ u₂
    rw [sub_zero] at hs
    linarith
  rw [h0, h0]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
theorem deTurckPhiZero_jointSmooth_fw (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2
      (fun s => (-2 : ℝ) • linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s
        + (deTurckLieCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
          + lieCorr0Field (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)) (δ := δ) (δ' := δ') :=
  threeArmHjoint_neg_two_smul_add_fw (I := I) (M := M) g₀ 2 _ _
    (linearizedRicci_arm0Field_jointSmooth (I := I) g₀ T T' hδ hδ')
    (lieCorr0Phi0b_jointSmooth (I := I) g₀ T T' hδ hδ' g_bg)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
theorem deTurckPhiOne_jointSmooth_fw (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3
      (fun s => (-2 : ℝ) • linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s
        + deTurckLieArm1Coeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) (δ := δ) (δ' := δ') :=
  threeArmHjoint_neg_two_smul_add_fw (I := I) (M := M) g₀ 3 _ _
    (linearizedRicci_arm1Field_jointSmooth (I := I) g₀ T T' hδ hδ')
    (deTurckLieArm1Coeff_realizedFam_jointSmooth (I := I) g₀ T T' hδ hδ' g_bg)

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 3200000 in
set_option backward.isDefEq.respectTransparency false in
noncomputable def deTurckPhiZeroPathIntegral (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    SmoothCcTensor g₀ 2 2 :=
  pathIntegralCoeffField (I := I) (M := M) g₀ 2 2
    (fun s => (-2 : ℝ) • linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s
      + (deTurckLieCoeffField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
        + lieCorr0Field (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg))
    (realizedSmallSet (δ := δ) (δ' := δ')) realizedSmallSet_isOpen
    (by rw [Set.uIcc_of_le zero_le_one]; exact Icc_subset_realizedSmallSet hδ_lt hδ'_lt)
    (deTurckPhiZero_jointSmooth_fw (I := I) (M := M) g₀ g_bg T T' hδ hδ')

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 3200000 in
set_option backward.isDefEq.respectTransparency false in
noncomputable def deTurckPhiOnePathIntegral (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    SmoothCcTensor g₀ 3 2 :=
  pathIntegralCoeffField (I := I) (M := M) g₀ 3 2
    (fun s => (-2 : ℝ) • linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s
      + deTurckLieArm1Coeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
    (realizedSmallSet (δ := δ) (δ' := δ')) realizedSmallSet_isOpen
    (by rw [Set.uIcc_of_le zero_le_one]; exact Icc_subset_realizedSmallSet hδ_lt hδ'_lt)
    (deTurckPhiOne_jointSmooth_fw (I := I) (M := M) g₀ g_bg T T' hδ hδ')

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 3200000 in
set_option backward.isDefEq.respectTransparency false in
theorem deTurckRHSArmDiff_eq_pathIntegralCoeff_triple_of_symm
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ T x v w = ccTensorBilin (I := I) g₀ T x w v)
    (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ T' x v w = ccTensorBilin (I := I) g₀ T' x w v) :
    deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ -
        deTurckRHSArmG0 (I := I) g₀ g_bg T' hδ'_lt hδ' =
      appCc (I := I) (M := M) g₀ 2 2
          (deTurckPhiZeroPathIntegral (I := I) (M := M) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ')
          (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
        appCc (I := I) (M := M) g₀ 3 2
          (deTurckPhiOnePathIntegral (I := I) (M := M) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ')
          (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
        appCc (I := I) (M := M) g₀ 4 2
          (deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ')
          (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) := by
  classical
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
  have hPi0 : deTurckPhiZeroPathIntegral (I := I) (M := M) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' =
      pathIntegralCoeffField (I := I) (M := M) g₀ 2 2 Ψ₀
        (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj0 := rfl
  have hPi1 : deTurckPhiOnePathIntegral (I := I) (M := M) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' =
      pathIntegralCoeffField (I := I) (M := M) g₀ 3 2 Ψ₁
        (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj1 := rfl
  have hPitop : deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' =
      pathIntegralCoeffField (I := I) (M := M) g₀ 4 2 Ψ₂
        (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj2 := rfl
  rw [hPi0, hPi1, hPitop]
  apply smoothCcTensor_ext_of_unitModel
  intro x
  apply ContinuousMultilinearMap.ext
  intro v
  set g₁ := tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ with hg₁
  set g₁' := tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ' with hg₁'
  rw [unitModel_sub_local (I := I) g₀ 2 _ _ x, ContinuousMultilinearMap.sub_apply]
  rw [show (unitModel (I := I) (M := M) g₀ 2
        (deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ) x) v =
      deTurckRicciRHS (I := I) g_bg g₁ x (v 0) (v 1) from
    unitModel_of_deTurckRHSSection_realize (I := I) g₀ g_bg T hδ_lt hδ
      (deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ) rfl x v]
  rw [show (unitModel (I := I) (M := M) g₀ 2
        (deTurckRHSArmG0 (I := I) g₀ g_bg T' hδ'_lt hδ') x) v =
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
  rw [unitModel_add2_apply_tame, unitModel_add2_apply_tame, he0, he1, he2]

end DeTurckRemainderTameLipschitz

private theorem lieArm1_norm_block6_le_fw {V : Type*} [SeminormedAddCommGroup V]
    (b1 b2 b3 b4 b5 b6 : V) :
    ‖b1 - b2 - b3 - b4 - b5 - b6‖ ≤ ‖b1‖ + ‖b2‖ + ‖b3‖ + ‖b4‖ + ‖b5‖ + ‖b6‖ := by
  calc ‖b1 - b2 - b3 - b4 - b5 - b6‖
      ≤ ‖b1 - b2 - b3 - b4 - b5‖ + ‖b6‖ := norm_sub_le _ _
    _ ≤ (‖b1 - b2 - b3 - b4‖ + ‖b5‖) + ‖b6‖ := by
        have := norm_sub_le (b1 - b2 - b3 - b4) b5
        linarith
    _ ≤ ((‖b1 - b2 - b3‖ + ‖b4‖) + ‖b5‖) + ‖b6‖ := by
        have := norm_sub_le (b1 - b2 - b3) b4
        linarith
    _ ≤ (((‖b1 - b2‖ + ‖b3‖) + ‖b4‖) + ‖b5‖) + ‖b6‖ := by
        have := norm_sub_le (b1 - b2) b3
        linarith
    _ ≤ ((((‖b1‖ + ‖b2‖) + ‖b3‖) + ‖b4‖) + ‖b5‖) + ‖b6‖ := by
        have := norm_sub_le b1 b2
        linarith
    _ = ‖b1‖ + ‖b2‖ + ‖b3‖ + ‖b4‖ + ‖b5‖ + ‖b6‖ := by ring

private theorem lieArm1_norm_block6_le'_fw {V : Type*} [SeminormedAddCommGroup V]
    (b1 b2 b3 b4 b5 b6 : V) :
    ‖b1 + b2 - b3 - b4 - b5 - b6‖ ≤ ‖b1‖ + ‖b2‖ + ‖b3‖ + ‖b4‖ + ‖b5‖ + ‖b6‖ := by
  calc ‖b1 + b2 - b3 - b4 - b5 - b6‖
      ≤ ‖b1 + b2 - b3 - b4 - b5‖ + ‖b6‖ := norm_sub_le _ _
    _ ≤ (‖b1 + b2 - b3 - b4‖ + ‖b5‖) + ‖b6‖ := by
        have := norm_sub_le (b1 + b2 - b3 - b4) b5
        linarith
    _ ≤ ((‖b1 + b2 - b3‖ + ‖b4‖) + ‖b5‖) + ‖b6‖ := by
        have := norm_sub_le (b1 + b2 - b3) b4
        linarith
    _ ≤ (((‖b1 + b2‖ + ‖b3‖) + ‖b4‖) + ‖b5‖) + ‖b6‖ := by
        have := norm_sub_le (b1 + b2) b3
        linarith
    _ ≤ ((((‖b1‖ + ‖b2‖) + ‖b3‖) + ‖b4‖) + ‖b5‖) + ‖b6‖ := by
        have := norm_add_le b1 b2
        linarith
    _ = ‖b1‖ + ‖b2‖ + ‖b3‖ + ‖b4‖ + ‖b5‖ + ‖b6‖ := by ring

private theorem lieArm1_norm_le_sqrt_fw {V : Type*} [SeminormedAddCommGroup V]
    {v : V} {P : ℝ} (h : ‖v‖ ^ 2 ≤ P) : ‖v‖ ≤ Real.sqrt P := by
  have h1 : ‖v‖ = Real.sqrt (‖v‖ ^ 2) := (Real.sqrt_sq (norm_nonneg v)).symm
  rw [h1]
  exact Real.sqrt_le_sqrt h

namespace DeTurckRemainderTameLipschitz

lemma pAO_range_subset {m n : ℕ} (h : m ≤ n) :
    Finset.range m ⊆ Finset.range n := by
  intro x hx
  exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) h)

end DeTurckRemainderTameLipschitz

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in

private theorem pAO_gInvDiffSlotCoeff_jetL2_tame (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ j, 0 ≤ K j) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδP : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ j : ℕ,
          ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 ≤
            K j * (1 + ∑ q ∈ Finset.range (j + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2) := by
  classical
  obtain ⟨C, hC_nn, hCp⟩ :=
    rfns_iteratedCovGrad_gInvDiffSlotCoeff_diagonalProductGrid_le (I := I) (M := M) g₀ hδ₀
  obtain ⟨Kt, hKt_nn, hKt⟩ :=
    antidiagonalTupleGrid_integral_ballUniform_tameWindow (I := I) (M := M) g₀ a ha_super hR
  refine ⟨fun j => C j * Kt j, fun j => mul_nonneg (hC_nn j) (hKt_nn j), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδP hPball j
  obtain ⟨hint, hbound⟩ := hKt P hPball j
  have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (2 + j)
    (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁))
    (fun x => C j * ∑ n ∈ Finset.range (j + 1),
      ∑ e ∈ Finset.Nat.antidiagonalTuple n j,
        ∏ m : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
    (hint.const_mul (C j))
    (fun x => hCp g₁ P htie hδ_le hδ0 hδP j x)
  refine le_trans key ?_
  rw [MeasureTheory.integral_const_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (le_trans hbound (le_of_eq rfl)) (hC_nn j)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in

private theorem pAO_traceHessian_jetSum_tame (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Q : ℕ → ℝ, (∀ i, 0 ≤ Q i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδP : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ i : ℕ,
          ∑ n ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 4 2 n
              (traceHessianCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
            Q i * (1 + ∑ q ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2) := by
  classical
  obtain ⟨Cth, hCth_nn, hCth⟩ :=
    traceHessianCoeff_sub_background_jetL2_le_gInvDiffSlotCoeff_jetL2 (I := I) (M := M) g₀
  obtain ⟨Kg, hKg_nn, hKg⟩ :=
    pAO_gInvDiffSlotCoeff_jetL2_tame (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨fun i => 2 * (∑ n ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 4 2 n
          (traceHessianCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2)
      + 2 * (∑ n ∈ Finset.range (i + 1), Cth n) * (∑ q ∈ Finset.range (i + 1), Kg q),
    fun i => by
      have h1 : (0 : ℝ) ≤ ∑ n ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 4 2 n
            (traceHessianCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 :=
        Finset.sum_nonneg fun n _ => sq_nonneg _
      have h2 : (0 : ℝ) ≤ ∑ n ∈ Finset.range (i + 1), Cth n :=
        Finset.sum_nonneg fun n _ => hCth_nn n
      have h3 : (0 : ℝ) ≤ ∑ q ∈ Finset.range (i + 1), Kg q :=
        Finset.sum_nonneg fun q _ => hKg_nn q
      positivity, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδP hPball i
  set W : ℝ := 1 + ∑ q ∈ Finset.range (i + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2 with hW_def
  have hW1 : (1 : ℝ) ≤ W := by
    rw [hW_def]
    have : (0 : ℝ) ≤ ∑ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  have hW_nn : (0 : ℝ) ≤ W := le_trans zero_le_one hW1
  have hgterm : ∀ q ∈ Finset.range (i + 1),
      ‖iteratedCovGrad (I := I) g₀ 2 2 q (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 ≤
        Kg q * W := by
    intro q hq
    have hq_le : q + 1 ≤ i + 1 := by
      have := Finset.mem_range.mp hq; omega
    refine le_trans (hKg g₁ P htie hδ_le hδ0 hδP hPball q) ?_
    refine mul_le_mul_of_nonneg_left ?_ (hKg_nn q)
    rw [hW_def]
    have hmono : ∑ q' ∈ Finset.range (q + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 q' P‖ ^ 2 ≤
        ∑ q' ∈ Finset.range (i + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 q' P‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (pAO_range_subset hq_le) (fun _ _ _ => sq_nonneg _)
    linarith
  have hgsum : ∑ q ∈ Finset.range (i + 1),
      ‖iteratedCovGrad (I := I) g₀ 2 2 q (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 ≤
      (∑ q ∈ Finset.range (i + 1), Kg q) * W := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum hgterm
  have hterm : ∀ n ∈ Finset.range (i + 1),
      ‖iteratedCovGrad (I := I) g₀ 4 2 n (traceHessianCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
        2 * ‖iteratedCovGrad (I := I) g₀ 4 2 n
            (traceHessianCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2
          + 2 * Cth n * ∑ j ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 := by
    intro n hn
    have hn_le : n + 1 ≤ i + 1 := by
      have := Finset.mem_range.mp hn; omega
    have hsplit : traceHessianCoeff (I := I) (M := M) g₀ g₁ =
        (traceHessianCoeff (I := I) (M := M) g₀ g₁
          - traceHessianCoeff (I := I) (M := M) g₀ g₀)
        + traceHessianCoeff (I := I) (M := M) g₀ g₀ := by
      rw [sub_add_cancel]
    have hadd := lieArm1_normSq_icg_add_le (I := I) (M := M) g₀ 4 2 n
      (traceHessianCoeff (I := I) (M := M) g₀ g₁
        - traceHessianCoeff (I := I) (M := M) g₀ g₀)
      (traceHessianCoeff (I := I) (M := M) g₀ g₀)
    have hdiff := hCth g₁ n
    have hdiff_wide : ‖iteratedCovGrad (I := I) g₀ 4 2 n
        (traceHessianCoeff (I := I) (M := M) g₀ g₁
          - traceHessianCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤
        Cth n * ∑ j ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 := by
      refine le_trans hdiff ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCth_nn n)
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (pAO_range_subset hn_le) (fun _ _ _ => sq_nonneg _)
    calc ‖iteratedCovGrad (I := I) g₀ 4 2 n
            (traceHessianCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2
        = ‖iteratedCovGrad (I := I) g₀ 4 2 n
            ((traceHessianCoeff (I := I) (M := M) g₀ g₁
              - traceHessianCoeff (I := I) (M := M) g₀ g₀)
            + traceHessianCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 := by rw [← hsplit]
      _ ≤ 2 * ‖iteratedCovGrad (I := I) g₀ 4 2 n
            (traceHessianCoeff (I := I) (M := M) g₀ g₁
              - traceHessianCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2
          + 2 * ‖iteratedCovGrad (I := I) g₀ 4 2 n
            (traceHessianCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 := hadd
      _ ≤ 2 * ‖iteratedCovGrad (I := I) g₀ 4 2 n
            (traceHessianCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2
          + 2 * Cth n * ∑ j ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 := by
          linarith [hdiff_wide]
  have hgsum_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 1),
      ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc ∑ n ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 4 2 n
          (traceHessianCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2
      ≤ ∑ n ∈ Finset.range (i + 1),
          (2 * ‖iteratedCovGrad (I := I) g₀ 4 2 n
              (traceHessianCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2
            + 2 * Cth n * ∑ j ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2) :=
        Finset.sum_le_sum hterm
    _ = 2 * (∑ n ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 4 2 n
            (traceHessianCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2)
        + 2 * (∑ n ∈ Finset.range (i + 1), Cth n)
          * ∑ j ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ 2 * (∑ n ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 4 2 n
            (traceHessianCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2)
        + 2 * (∑ n ∈ Finset.range (i + 1), Cth n)
          * ((∑ q ∈ Finset.range (i + 1), Kg q) * W) := by
        have h2c : (0 : ℝ) ≤ 2 * (∑ n ∈ Finset.range (i + 1), Cth n) := by
          have : (0 : ℝ) ≤ ∑ n ∈ Finset.range (i + 1), Cth n :=
            Finset.sum_nonneg fun n _ => hCth_nn n
          linarith
        have := mul_le_mul_of_nonneg_left hgsum h2c
        linarith
    _ ≤ (2 * (∑ n ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 4 2 n
            (traceHessianCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2)
        + 2 * (∑ n ∈ Finset.range (i + 1), Cth n)
          * (∑ q ∈ Finset.range (i + 1), Kg q)) * W := by
        have h1 : (0 : ℝ) ≤ ∑ n ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 4 2 n
              (traceHessianCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 :=
          Finset.sum_nonneg fun n _ => sq_nonneg _
        have h2 : (0 : ℝ) ≤ ∑ n ∈ Finset.range (i + 1), Cth n :=
          Finset.sum_nonneg fun n _ => hCth_nn n
        have h3 : (0 : ℝ) ≤ ∑ q ∈ Finset.range (i + 1), Kg q :=
          Finset.sum_nonneg fun q _ => hKg_nn q
        have e1 : (∑ n ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 4 2 n
              (traceHessianCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2) ≤
            (∑ n ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 4 2 n
                (traceHessianCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2) * W :=
          le_mul_of_one_le_right h1 hW1
        nlinarith [e1]

namespace DeTurckRemainderTameLipschitz

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in

theorem pAO_connDiffSection_jetL2_tame (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ F : ℕ → ℝ, (∀ l, 0 ≤ F l) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδP : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ l : ℕ,
          ‖iteratedCovGrad (I := I) g₀ 1 2 l (connDiffSection (I := I) g₁ g₀)‖ ^ 2 ≤
            F l * (1 + ∑ q ∈ Finset.range (l + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2) := by
  classical
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    exists_rfns_iteratedCovGrad_connDiffSection_tgrid (I := I) (M := M) g₀ hδ₀
  obtain ⟨Kt, hKt_nn, hKt⟩ :=
    antidiagonalTupleGrid_integral_ballUniform_tameWindow (I := I) (M := M) g₀ a ha_super hR
  refine ⟨fun l => CA l * ∑ k ∈ Finset.range (l + 2), Kt k,
    fun l => mul_nonneg (hCA_nn l)
      (Finset.sum_nonneg fun k _ => hKt_nn k), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδP hPball l
  set W : ℝ := 1 + ∑ q ∈ Finset.range (l + 2),
    ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2 with hW_def
  have hW1 : (1 : ℝ) ≤ W := by
    rw [hW_def]
    have : (0 : ℝ) ≤ ∑ q ∈ Finset.range (l + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  have hint_all : ∀ k ∈ Finset.range (l + 2), MeasureTheory.Integrable
      (fun x => ∑ n ∈ Finset.range (k + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
          ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    fun k _ => (hKt P hPball k).1
  have hptw : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 1 2 l
          (connDiffSection (I := I) g₁ g₀)).toSection x) ≤
      CA l * ∑ k ∈ Finset.range (l + 2),
        Combinatorics.antidiagonalTupleGrid
          (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
            ((iteratedCovGrad (I := I) g₀ 0 2 j' P).toSection x)) k :=
    fun x => hCA g₁ P htie hδ_le hδ0 hδP l x
  have hgrid_eq : ∀ (x : M) (k : ℕ),
      Combinatorics.antidiagonalTupleGrid
        (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
          ((iteratedCovGrad (I := I) g₀ 0 2 j' P).toSection x)) k =
      ∑ n ∈ Finset.range (k + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
          ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) :=
    fun x k => rfl
  have hint : MeasureTheory.Integrable
      (fun x => CA l * ∑ k ∈ Finset.range (l + 2),
        Combinatorics.antidiagonalTupleGrid
          (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
            ((iteratedCovGrad (I := I) g₀ 0 2 j' P).toSection x)) k)
      (riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    refine MeasureTheory.Integrable.const_mul ?_ (CA l)
    have : (fun x => ∑ k ∈ Finset.range (l + 2),
        Combinatorics.antidiagonalTupleGrid
          (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
            ((iteratedCovGrad (I := I) g₀ 0 2 j' P).toSection x)) k) =
        (fun x => ∑ k ∈ Finset.range (l + 2),
          ∑ n ∈ Finset.range (k + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
              ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) := by
      funext x
      exact Finset.sum_congr rfl (fun k _ => hgrid_eq x k)
    rw [this]
    exact MeasureTheory.integrable_finset_sum (Finset.range (l + 2)) hint_all
  have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 1 (2 + l)
    (iteratedCovGrad (I := I) g₀ 1 2 l (connDiffSection (I := I) g₁ g₀))
    (fun x => CA l * ∑ k ∈ Finset.range (l + 2),
      Combinatorics.antidiagonalTupleGrid
        (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
          ((iteratedCovGrad (I := I) g₀ 0 2 j' P).toSection x)) k)
    hint hptw
  refine le_trans key ?_
  rw [MeasureTheory.integral_const_mul]
  have hsum_int_eq : (∫ x, ∑ k ∈ Finset.range (l + 2),
      Combinatorics.antidiagonalTupleGrid
        (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
          ((iteratedCovGrad (I := I) g₀ 0 2 j' P).toSection x)) k
      ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
      ∑ k ∈ Finset.range (l + 2), ∫ x,
        ∑ n ∈ Finset.range (k + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
            ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    rw [show (fun x => ∑ k ∈ Finset.range (l + 2),
        Combinatorics.antidiagonalTupleGrid
          (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
            ((iteratedCovGrad (I := I) g₀ 0 2 j' P).toSection x)) k) =
        (fun x => ∑ k ∈ Finset.range (l + 2),
          ∑ n ∈ Finset.range (k + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
              ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) from by
      funext x
      exact Finset.sum_congr rfl (fun k _ => hgrid_eq x k)]
    exact MeasureTheory.integral_finset_sum (Finset.range (l + 2)) hint_all
  rw [hsum_int_eq, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (hCA_nn l)
  rw [Finset.sum_mul]
  refine le_trans (Finset.sum_le_sum (fun k hk => (hKt P hPball k).2)) ?_
  refine Finset.sum_le_sum (fun k hk => ?_)
  refine mul_le_mul_of_nonneg_left ?_ (hKt_nn k)
  have hk2 : k + 1 ≤ l + 2 := by
    have := Finset.mem_range.mp hk; omega
  rw [hW_def]
  have hmono : ∑ q ∈ Finset.range (k + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2 ≤
      ∑ q ∈ Finset.range (l + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (pAO_range_subset hk2) (fun _ _ _ => sq_nonneg _)
  linarith

end DeTurckRemainderTameLipschitz

set_option linter.unusedSectionVars false in
private lemma pAO_connDiff_self_zero (gA : SmoothRiemannianMetric I M) (x : M)
    (u v : TangentSpace I x) :
    PDE.DeTurck.connDiff (I := I) gA gA x u v = 0 := by
  have h := PDE.DeTurck.connDiff_cocycle (I := I) gA gA gA x u v
  have h2 : PDE.DeTurck.connDiff (I := I) gA gA x u v +
      PDE.DeTurck.connDiff (I := I) gA gA x u v =
      PDE.DeTurck.connDiff (I := I) gA gA x u v + 0 := by
    rw [add_zero]
    exact h.symm
  exact add_left_cancel h2

set_option linter.unusedSectionVars false in
private lemma pAO_connDiff_antisymm (gA gB : SmoothRiemannianMetric I M) (x : M)
    (u v : TangentSpace I x) :
    PDE.DeTurck.connDiff (I := I) gA gB x u v =
      -PDE.DeTurck.connDiff (I := I) gB gA x u v := by
  have h := PDE.DeTurck.connDiff_cocycle (I := I) gB gA gA x u v
  rw [pAO_connDiff_self_zero (I := I) (M := M) gA x u v] at h
  exact eq_neg_of_add_eq_zero_left h.symm

set_option linter.unusedSectionVars false in
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (connDiffLoweredField) in
private lemma pAO_lieArm1Kappa_unitModel_apply (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (x : M) (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg) x m =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g_bg g₁ x (m 0) (m 1)) (m 2) := by
  rw [unitModel]
  show Tensor0SSpace.toModel
      (((lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg).toSection x)
        (unitTensor (I := I) (M := M) x)) m =
    g₁.inner x (PDE.DeTurck.connDiff (I := I) g_bg g₁ x (m 0) (m 1)) (m 2)
  rw [show ((lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg).toSection x)
      (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (connDiffLoweredField (I := I) g₁ g_bg x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rfl

set_option linter.unusedSectionVars false in
private lemma pAO_lieArm1Kappa_eq_neg_lc0Kappa (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg =
      -(lc0Kappa (I := I) (M := M) g₀ g₁ g_bg) := by
  rw [show -(lc0Kappa (I := I) (M := M) g₀ g₁ g_bg) =
      lc0Kappa (I := I) (M := M) g₀ g₁ g_bg -
        (lc0Kappa (I := I) (M := M) g₀ g₁ g_bg + lc0Kappa (I := I) (M := M) g₀ g₁ g_bg)
      from by abel]
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  apply ContinuousMultilinearMap.ext
  intro m
  rw [unitModel_sub_local (I := I) (M := M) g₀ 3 (lc0Kappa (I := I) (M := M) g₀ g₁ g_bg)
      (lc0Kappa (I := I) (M := M) g₀ g₁ g_bg + lc0Kappa (I := I) (M := M) g₀ g₁ g_bg) x,
    unitModel_add_local (I := I) (M := M) g₀ 3 (lc0Kappa (I := I) (M := M) g₀ g₁ g_bg)
      (lc0Kappa (I := I) (M := M) g₀ g₁ g_bg) x]
  rw [ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.add_apply]
  rw [pAO_lieArm1Kappa_unitModel_apply (I := I) (M := M) g₀ g₁ g_bg x m,
    lc0Kappa_unitModel_apply (I := I) (M := M) g₀ g₁ g_bg x m]
  rw [pAO_connDiff_antisymm (I := I) (M := M) g_bg g₁ x (m 0) (m 1)]
  rw [map_neg (g₁.inner x), ContinuousLinearMap.neg_apply]
  ring

set_option linter.unusedSectionVars false in
private lemma pAO_normSq_icg_lieArm1Kappa_eq (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (q : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 0 3 q
        (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ 0 3 q (lc0Kappa (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 := by
  rw [pAO_lieArm1Kappa_eq_neg_lc0Kappa (I := I) (M := M) g₀ g₁ g_bg,
    iteratedCovGrad_neg, norm_neg]

set_option linter.unusedSectionVars false in
private lemma pAO_rfns_lieArm1Kappa_eq (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
        ((lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
        ((lc0Kappa (I := I) (M := M) g₀ g₁ g_bg).toSection x) := by
  have hsec : (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg).toSection x =
      -((lc0Kappa (I := I) (M := M) g₀ g₁ g_bg).toSection x) := by
    rw [pAO_lieArm1Kappa_eq_neg_lc0Kappa (I := I) (M := M) g₀ g₁ g_bg,
      SmoothCcTensor.toSection_neg]
    rfl
  rw [hsec]
  exact riemannianFiberNormSq_neg_value (I := I) (M := M) g₀ 0 3 x _

set_option linter.unusedSectionVars false in
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (cometricRaiseSlot0Field rfns_iteratedCovGrad_cometricRaiseSlot0Field_eq) in
private lemma pAO_rfns_icg_raiseDomDom_eq (g₀ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 3)) (κ' : SmoothCcTensor g₀ 0 3) (n : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 2 n
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
            (domDomCongrSection (I := I) g₀ σ κ'))).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n κ').toSection x) := by
  rw [rfns_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 1
    (domDomCongrSection (I := I) g₀ σ κ') n x]
  exact riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
    σ κ' n x

set_option linter.unusedSectionVars false in
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (cometricRaiseSlot0Field) in
private lemma pAO_normSq_icg_raiseDomDom_eq (g₀ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 3)) (κ' : SmoothCcTensor g₀ 0 3) (n : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 1 2 n
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
          (domDomCongrSection (I := I) g₀ σ κ'))‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ 0 3 n κ'‖ ^ 2 := by
  rw [lc0b_normSq_eq_integral, lc0b_normSq_eq_integral]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact pAO_rfns_icg_raiseDomDom_eq (I := I) (M := M) g₀ σ κ' n x

namespace DeTurckRemainderTameLipschitz

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (sharpFlatEndoCc) in

theorem pAO_sharpFlat_jetSum_tame (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ F : ℕ → ℝ, (∀ l, 0 ≤ F l) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδP : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ l : ℕ,
          ∑ q ∈ Finset.range (l + 1),
            ‖iteratedCovGrad (I := I) g₀ 1 1 q (sharpFlatEndoCc (I := I) g₀ g₁)‖ ^ 2 ≤
            F l * (1 + ∑ q ∈ Finset.range (l + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2) := by
  classical
  obtain ⟨Cb, hCb_nn, hCb⟩ :=
    rfns_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨Kt, hKt_nn, hKt⟩ :=
    antidiagonalTupleGrid_integral_ballUniform_tameWindow (I := I) (M := M) g₀ a ha_super hR
  set IdIns : SmoothCcTensor g₀ 1 1 :=
    slotInsertEndoCc (I := I) (M := M) g₀ 0
      (fullRaisedEndoField (I := I) (M := M) g₀ g₀) with hIdIns_def
  refine ⟨fun l => ∑ q ∈ Finset.range (l + 1),
      (2 * (Cb q * Kt q) + 2 * ‖iteratedCovGrad (I := I) g₀ 1 1 q IdIns‖ ^ 2),
    fun l => Finset.sum_nonneg fun q _ => add_nonneg
      (mul_nonneg (by norm_num) (mul_nonneg (hCb_nn q) (hKt_nn q)))
      (mul_nonneg (by norm_num) (sq_nonneg _)), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδP hPball l
  set W : ℝ := 1 + ∑ q ∈ Finset.range (l + 2),
    ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2 with hW_def
  have hW1 : (1 : ℝ) ≤ W := by
    rw [hW_def]
    have : (0 : ℝ) ≤ ∑ q ∈ Finset.range (l + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  set DiffIns : SmoothCcTensor g₀ 1 1 :=
    slotInsertEndoCc (I := I) (M := M) g₀ 0 (gInvDiffRaisedEndoField (I := I) g₀ g₁)
    with hDiffIns_def
  have hdecomp : sharpFlatEndoCc (I := I) g₀ g₁ = DiffIns + IdIns := by
    rw [lc0b_sharpFlat_eq_slotInsert_fullRaised (I := I) (M := M) g₀ g₁,
      lc0b_fullRaised_diff_split (I := I) (M := M) g₀ g₁,
      lc0b_slotInsert_add (I := I) (M := M) g₀ 0]
  have hterm : ∀ q ∈ Finset.range (l + 1),
      ‖iteratedCovGrad (I := I) g₀ 1 1 q (sharpFlatEndoCc (I := I) g₀ g₁)‖ ^ 2 ≤
        (2 * (Cb q * Kt q) + 2 * ‖iteratedCovGrad (I := I) g₀ 1 1 q IdIns‖ ^ 2) * W := by
    intro q hq
    have hq_le : q + 1 ≤ l + 2 := by have := Finset.mem_range.mp hq; omega
    obtain ⟨hgi, hgb⟩ := hKt P hPball q
    have hDq : ‖iteratedCovGrad (I := I) g₀ 1 1 q DiffIns‖ ^ 2 ≤ Cb q * Kt q * W := by
      have hint : MeasureTheory.Integrable
          (fun x => Cb q *
            (∑ n ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n q,
              ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)))
          (riemannianVolumeMeasure (I := I) (M := M) g₀) := hgi.const_mul _
      have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀
        1 (1 + q) (iteratedCovGrad (I := I) g₀ 1 1 q DiffIns) _ hint
        (fun x => hCb g₁ P htie hδ_le hδ0 hδP q x)
      refine le_trans hkey ?_
      rw [MeasureTheory.integral_const_mul]
      have hwin : Kt q * (1 + ∑ j ∈ Finset.range (q + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ Kt q * W := by
        refine mul_le_mul_of_nonneg_left ?_ (hKt_nn q)
        rw [hW_def]
        have hmono : ∑ j ∈ Finset.range (q + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 ≤
            ∑ j ∈ Finset.range (l + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (pAO_range_subset hq_le)
            (fun _ _ _ => sq_nonneg _)
        linarith
      refine le_trans (mul_le_mul_of_nonneg_left hgb (hCb_nn q)) ?_
      refine le_trans (mul_le_mul_of_nonneg_left hwin (hCb_nn q)) (le_of_eq (by ring))
    have hsplit : ‖iteratedCovGrad (I := I) g₀ 1 1 q (sharpFlatEndoCc (I := I) g₀ g₁)‖ ^ 2 ≤
        2 * ‖iteratedCovGrad (I := I) g₀ 1 1 q DiffIns‖ ^ 2 +
          2 * ‖iteratedCovGrad (I := I) g₀ 1 1 q IdIns‖ ^ 2 := by
      rw [hdecomp]
      exact lc0b_normSq_icg_add_le (I := I) (M := M) g₀ 1 1 q DiffIns IdIns
    have hexp : (2 * (Cb q * Kt q) + 2 * ‖iteratedCovGrad (I := I) g₀ 1 1 q IdIns‖ ^ 2) * W =
        2 * (Cb q * Kt q * W) + 2 * ‖iteratedCovGrad (I := I) g₀ 1 1 q IdIns‖ ^ 2 * W := by
      ring
    have hIdW : ‖iteratedCovGrad (I := I) g₀ 1 1 q IdIns‖ ^ 2 ≤
        ‖iteratedCovGrad (I := I) g₀ 1 1 q IdIns‖ ^ 2 * W :=
      le_mul_of_one_le_right (sq_nonneg _) hW1
    linarith [hsplit, hDq, hIdW, hexp]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_mul]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (connDiffLoweredCc cometricRaiseSlot0Field) in

theorem pAO_kappa_jetSum_tame (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ F : ℕ → ℝ, (∀ l, 0 ≤ F l) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδP : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ l : ℕ,
          ∑ q ∈ Finset.range (l + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 3 q
              (lc0Kappa (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
            F l * (1 + ∑ q ∈ Finset.range (l + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2) := by
  classical
  obtain ⟨Fcd, hFcd_nn, hFcd⟩ :=
    pAO_connDiffSection_jetL2_tame (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨Λcd, Fcdtr, hΛcd_nn, hFcdtr_nn, hcd⟩ :=
    lc0b_cds_feed (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨Λlow, hΛlow_nn, hΛlow⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 0 3
      (lc0LowFix (I := I) (M := M) g₀ g_bg)
  obtain ⟨Λfx, hΛfx_nn, hΛfx⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 1 2
      (lc0FixCd (I := I) (M := M) g₀ g_bg)
  obtain ⟨C2b, hC2b_nn, hC2b⟩ := lc0b_twoArm_fn (I := I) (M := M) g₀ 1 1 2 1
  set nQ : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * max δ₀ 0 ^ 2 with hnQ_def
  have hnQ_nn : 0 ≤ nQ := by rw [hnQ_def]; positivity
  set FB : ℕ → ℝ := fun l => ∑ q ∈ Finset.range (l + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 3 q (lc0LowFix (I := I) (M := M) g₀ g_bg)‖ ^ 2
    with hFB_def
  have hFB_nn : ∀ l, 0 ≤ FB l := fun l => Finset.sum_nonneg fun q _ => sq_nonneg _
  set Ffx : ℕ → ℝ := fun q => ∑ j ∈ Finset.range (q + 1),
    ‖iteratedCovGrad (I := I) g₀ 1 2 j (lc0FixCd (I := I) (M := M) g₀ g_bg)‖ ^ 2
    with hFfx_def
  have hFfx_nn : ∀ q, 0 ≤ Ffx q := fun q => Finset.sum_nonneg fun j _ => sq_nonneg _
  set FcdS : ℕ → ℝ := fun q => ∑ n ∈ Finset.range (q + 1), Fcd n with hFcdS_def
  have hFcdS_nn : ∀ q, 0 ≤ FcdS q := fun q => Finset.sum_nonneg fun n _ => hFcd_nn n
  set FC : ℕ → ℝ := fun l => ∑ q ∈ Finset.range (l + 1),
    appCcGdiag (E := E) q * (C2b q * (nQ * FcdS q + Λcd)) with hFC_def
  have hFC_nn : ∀ l, 0 ≤ FC l := fun l =>
    Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
      (mul_nonneg (hC2b_nn q) (add_nonneg (mul_nonneg hnQ_nn (hFcdS_nn q)) hΛcd_nn))
  set FD : ℕ → ℝ := fun l => ∑ q ∈ Finset.range (l + 1),
    appCcGdiag (E := E) q * (C2b q * (nQ * Ffx q + Λfx)) with hFD_def
  have hFD_nn : ∀ l, 0 ≤ FD l := fun l =>
    Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
      (mul_nonneg (hC2b_nn q) (add_nonneg (mul_nonneg hnQ_nn (hFfx_nn q)) hΛfx_nn))
  refine ⟨fun l => 8 * FcdS l + 8 * FB l + 4 * FC l + 2 * FD l,
    fun l => by
      have := hFcdS_nn l
      have := hFB_nn l
      have := hFC_nn l
      have := hFD_nn l
      linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδP hPball l
  set W : ℝ := 1 + ∑ q ∈ Finset.range (l + 2),
    ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2 with hW_def
  have hW1 : (1 : ℝ) ≤ W := by
    rw [hW_def]
    have : (0 : ℝ) ≤ ∑ q ∈ Finset.range (l + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  have hW_nn : (0 : ℝ) ≤ W := le_trans zero_le_one hW1
  obtain ⟨hWB0, _⟩ := lc0b_WB_feed (I := I) (M := M) g₀ a P hδ_le hδ0 hδP hPball
  obtain ⟨hcd0, _⟩ := hcd g₁ P htie hδ_le hδ0 hδP hPball
  have hκeq := lc0b_kappa_decomp (I := I) (M := M) g₀ g₁ g_bg P htie
  have hΨcC : ∀ x : M, (connDiffSection (I := I) g₁ g₀).toSection x =
      connDiffFib (I := I) g₁ g₀ x := fun x => rfl
  have hΨcD : ∀ x : M, (lc0FixCd (I := I) (M := M) g₀ g_bg).toSection x =
      connDiffFib (I := I) g₀ g_bg x := fun x => rfl
  have hWBsum : ∀ q : ℕ, q ≤ l →
      ∑ j ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 1 1 j
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (symmS (I := I) (M := M) g₀ P))‖ ^ 2 ≤ W := by
    intro q hq
    have hstep : ∀ j ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 1 1 j
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (symmS (I := I) (M := M) g₀ P))‖ ^ 2 ≤
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by
      intro j _
      rw [lc0b_normSq_icg_raise_eq (I := I) (M := M) g₀ 0 (symmS (I := I) (M := M) g₀ P) j]
      exact lc0b_normSq_icg_symmS_le (I := I) (M := M) g₀ P j
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [hW_def]
    have hmono : ∑ j ∈ Finset.range (q + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 ≤
        ∑ j ∈ Finset.range (l + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (pAO_range_subset (by omega : q + 1 ≤ l + 2))
        (fun _ _ _ => sq_nonneg _)
    linarith
  have hcdsum : ∀ q : ℕ, q ≤ l →
      ∑ n ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 1 2 n (connDiffSection (I := I) g₁ g₀)‖ ^ 2 ≤
        FcdS q * W := by
    intro q hq
    have hstep : ∀ n ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 1 2 n (connDiffSection (I := I) g₁ g₀)‖ ^ 2 ≤
          Fcd n * W := by
      intro n hn
      refine le_trans (hFcd g₁ P htie hδ_le hδ0 hδP hPball n) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hFcd_nn n)
      rw [hW_def]
      have hnle : n + 2 ≤ l + 2 := by
        have h1 := Finset.mem_range.mp hn
        omega
      have hmono : ∑ q' ∈ Finset.range (n + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 q' P‖ ^ 2 ≤
          ∑ q' ∈ Finset.range (l + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 q' P‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (pAO_range_subset hnle)
          (fun _ _ _ => sq_nonneg _)
      linarith
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [hFcdS_def, Finset.sum_mul]
  have hstep : ∀ q ∈ Finset.range (l + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 3 q (lc0Kappa (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
      8 * ‖iteratedCovGrad (I := I) g₀ 0 3 q (connDiffLoweredCc (I := I) g₀ g₁)‖ ^ 2 +
        8 * ‖iteratedCovGrad (I := I) g₀ 0 3 q (lc0LowFix (I := I) (M := M) g₀ g_bg)‖ ^ 2 +
        4 * ‖iteratedCovGrad (I := I) g₀ 0 3 q
          (lc0PbLow (I := I) (M := M) g₀ P g₁ g₀)‖ ^ 2 +
        2 * ‖iteratedCovGrad (I := I) g₀ 0 3 q
          (lc0PbLow (I := I) (M := M) g₀ P g₀ g_bg)‖ ^ 2 := by
    intro q _
    have hnorm : ‖iteratedCovGrad (I := I) g₀ 0 3 q
        (lc0Kappa (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 =
        ‖iteratedCovGrad (I := I) g₀ 0 3 q
          (connDiffLoweredCc (I := I) g₀ g₁ + lc0LowFix (I := I) (M := M) g₀ g_bg
            + lc0PbLow (I := I) (M := M) g₀ P g₁ g₀
            + lc0PbLow (I := I) (M := M) g₀ P g₀ g_bg)‖ ^ 2 := by
      rw [hκeq]
    rw [hnorm]
    have k1 := lc0b_normSq_icg_add_le (I := I) (M := M) g₀ 0 3 q
      (connDiffLoweredCc (I := I) g₀ g₁ + lc0LowFix (I := I) (M := M) g₀ g_bg
        + lc0PbLow (I := I) (M := M) g₀ P g₁ g₀)
      (lc0PbLow (I := I) (M := M) g₀ P g₀ g_bg)
    have k2 := lc0b_normSq_icg_add_le (I := I) (M := M) g₀ 0 3 q
      (connDiffLoweredCc (I := I) g₀ g₁ + lc0LowFix (I := I) (M := M) g₀ g_bg)
      (lc0PbLow (I := I) (M := M) g₀ P g₁ g₀)
    have k3 := lc0b_normSq_icg_add_le (I := I) (M := M) g₀ 0 3 q
      (connDiffLoweredCc (I := I) g₀ g₁) (lc0LowFix (I := I) (M := M) g₀ g_bg)
    linarith [k1, k2, k3]
  refine le_trans (Finset.sum_le_sum hstep) ?_
  have hsplit : ∑ q ∈ Finset.range (l + 1),
      (8 * ‖iteratedCovGrad (I := I) g₀ 0 3 q (connDiffLoweredCc (I := I) g₀ g₁)‖ ^ 2 +
        8 * ‖iteratedCovGrad (I := I) g₀ 0 3 q (lc0LowFix (I := I) (M := M) g₀ g_bg)‖ ^ 2 +
        4 * ‖iteratedCovGrad (I := I) g₀ 0 3 q
          (lc0PbLow (I := I) (M := M) g₀ P g₁ g₀)‖ ^ 2 +
        2 * ‖iteratedCovGrad (I := I) g₀ 0 3 q
          (lc0PbLow (I := I) (M := M) g₀ P g₀ g_bg)‖ ^ 2) =
      8 * ∑ q ∈ Finset.range (l + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 3 q (connDiffLoweredCc (I := I) g₀ g₁)‖ ^ 2 +
        8 * ∑ q ∈ Finset.range (l + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 3 q (lc0LowFix (I := I) (M := M) g₀ g_bg)‖ ^ 2 +
        4 * ∑ q ∈ Finset.range (l + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 3 q (lc0PbLow (I := I) (M := M) g₀ P g₁ g₀)‖ ^ 2 +
        2 * ∑ q ∈ Finset.range (l + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 3 q (lc0PbLow (I := I) (M := M) g₀ P g₀ g_bg)‖ ^ 2 := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hsplit]
  have hAsum : ∑ q ∈ Finset.range (l + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 3 q (connDiffLoweredCc (I := I) g₀ g₁)‖ ^ 2 ≤
      FcdS l * W := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun q _ =>
      lc0b_normSq_icg_lowered_eq (I := I) (M := M) g₀ g₁ q)) ?_
    exact hcdsum l le_rfl
  have hBsum : ∑ q ∈ Finset.range (l + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 3 q (lc0LowFix (I := I) (M := M) g₀ g_bg)‖ ^ 2 ≤
      FB l * W := by
    have : FB l ≤ FB l * W := le_mul_of_one_le_right (hFB_nn l) hW1
    rw [hFB_def] at this ⊢
    exact this
  have hCsum : ∑ q ∈ Finset.range (l + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 3 q (lc0PbLow (I := I) (M := M) g₀ P g₁ g₀)‖ ^ 2 ≤
      FC l * W := by
    rw [hFC_def, Finset.sum_mul]
    refine Finset.sum_le_sum fun q hq => ?_
    have hq_le : q ≤ l := by have := Finset.mem_range.mp hq; omega
    rw [lc0b_normSq_icg_pbLow_eq (I := I) (M := M) g₀ P g₁ g₀
      (connDiffSection (I := I) g₁ g₀) hΨcC q]
    refine le_trans (lc0b_appCcRS_normSq_le (I := I) (M := M) g₀ 1 1 2
      (connDiffSection (I := I) g₁ g₀)
      (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0 (symmS (I := I) (M := M) g₀ P)) q
      (C2b q) Λcd nQ (FcdS q * W) W
      (hC2b_nn q) hΛcd_nn hnQ_nn hcd0 hWB0 (hcdsum q hq_le) (hWBsum q hq_le)
      (hC2b q)) ?_
    exact le_of_eq (by ring)
  have hDsum : ∑ q ∈ Finset.range (l + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 3 q (lc0PbLow (I := I) (M := M) g₀ P g₀ g_bg)‖ ^ 2 ≤
      FD l * W := by
    rw [hFD_def, Finset.sum_mul]
    refine Finset.sum_le_sum fun q hq => ?_
    have hq_le : q ≤ l := by have := Finset.mem_range.mp hq; omega
    rw [lc0b_normSq_icg_pbLow_eq (I := I) (M := M) g₀ P g₀ g_bg
      (lc0FixCd (I := I) (M := M) g₀ g_bg) hΨcD q]
    refine le_trans (lc0b_appCcRS_normSq_le (I := I) (M := M) g₀ 1 1 2
      (lc0FixCd (I := I) (M := M) g₀ g_bg)
      (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0 (symmS (I := I) (M := M) g₀ P)) q
      (C2b q) Λfx nQ (Ffx q) W
      (hC2b_nn q) hΛfx_nn hnQ_nn hΛfx hWB0 le_rfl (hWBsum q hq_le)
      (hC2b q)) ?_
    have hgd := appCcGdiag_nonneg (E := E) q
    have hbase : nQ * Ffx q ≤ nQ * Ffx q * W :=
      le_mul_of_one_le_right (mul_nonneg hnQ_nn (hFfx_nn q)) hW1
    have hfac : (0 : ℝ) ≤ appCcGdiag (E := E) q * C2b q :=
      mul_nonneg hgd (hC2b_nn q)
    have hin : nQ * Ffx q + Λfx * W ≤ (nQ * Ffx q + Λfx) * W := by
      have : (nQ * Ffx q + Λfx) * W = nQ * Ffx q * W + Λfx * W := by ring
      linarith [hbase, this]
    calc appCcGdiag (E := E) q * (C2b q * (nQ * Ffx q + Λfx * W))
        = appCcGdiag (E := E) q * C2b q * (nQ * Ffx q + Λfx * W) := by ring
      _ ≤ appCcGdiag (E := E) q * C2b q * ((nQ * Ffx q + Λfx) * W) :=
          mul_le_mul_of_nonneg_left hin hfac
      _ = appCcGdiag (E := E) q * (C2b q * (nQ * Ffx q + Λfx)) * W := by ring
  have hexp : (8 * FcdS l + 8 * FB l + 4 * FC l + 2 * FD l) * W =
      8 * (FcdS l * W) + 8 * (FB l * W) + 4 * (FC l * W) + 2 * (FD l * W) := by ring
  linarith [hAsum, hBsum, hCsum, hDsum, hexp]

end DeTurckRemainderTameLipschitz

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in

private theorem pAO_lieArm1PsiB_jetL2_tame (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ F : ℕ → ℝ, (∀ l, 0 ≤ F l) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδP : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ l : ℕ,
          ‖iteratedCovGrad (I := I) g₀ 1 2 l
              (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
            F l * (1 + ∑ q ∈ Finset.range (l + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2) := by
  classical
  obtain ⟨Λκ, Fκtr, hΛκ_nn, hFκtr_nn, hκ⟩ :=
    lc0b_kappa_feed (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  obtain ⟨Λsf, Fsftr, hΛsf_nn, hFsftr_nn, hsf⟩ :=
    lc0b_sharpFlat_feed (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨Fκt, hFκt_nn, hκt⟩ :=
    pAO_kappa_jetSum_tame (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  obtain ⟨Fsft, hFsft_nn, hsft⟩ :=
    pAO_sharpFlat_jetSum_tame (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨C2b, hC2b_nn, hC2b⟩ := lc0b_twoArm_fn (I := I) (M := M) g₀ 1 1 2 1
  refine ⟨fun l => appCcGdiag (E := E) l * (C2b l * (Λsf * Fκt l + Λκ * Fsft l)),
    fun l => mul_nonneg (appCcGdiag_nonneg (E := E) l)
      (mul_nonneg (hC2b_nn l) (add_nonneg (mul_nonneg hΛsf_nn (hFκt_nn l))
        (mul_nonneg hΛκ_nn (hFsft_nn l)))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδP hPball l
  obtain ⟨hκ0, _⟩ := hκ g₁ P htie hδ_le hδ0 hδP hPball
  obtain ⟨hsf0, _⟩ := hsf g₁ P htie hδ_le hδ0 hδP hPball
  have hκtW := hκt g₁ P htie hδ_le hδ0 hδP hPball l
  have hsftW := hsft g₁ P htie hδ_le hδ0 hδP hPball l
  have hdef : lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg =
      appCcRS (I := I) (M := M) g₀ 1 1 2
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
          (domDomCongrSection (I := I) g₀ lieArm1RhoSlot0
            (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg)))
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sharpFlatEndoCc (I := I) g₀ g₁) := rfl
  have hA0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
      ((DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
        (domDomCongrSection (I := I) g₀ lieArm1RhoSlot0
          (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg))).toSection x) ≤ Λκ := by
    intro x
    have h := pAO_rfns_icg_raiseDomDom_eq (I := I) (M := M) g₀ lieArm1RhoSlot0
      (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg) 0 x
    simp only [iteratedCovGrad_zero] at h
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
          ((DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
            (domDomCongrSection (I := I) g₀ lieArm1RhoSlot0
              (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg))).toSection x)
        = riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
            ((lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg).toSection x) := h
      _ = riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
            ((lc0Kappa (I := I) (M := M) g₀ g₁ g_bg).toSection x) :=
          pAO_rfns_lieArm1Kappa_eq (I := I) (M := M) g₀ g₁ g_bg x
      _ ≤ Λκ := hκ0 x
  have hAL2 : ∑ n ∈ Finset.range (l + 1),
      ‖iteratedCovGrad (I := I) g₀ 1 2 n
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
          (domDomCongrSection (I := I) g₀ lieArm1RhoSlot0
            (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg)))‖ ^ 2 ≤
      Fκt l * (1 + ∑ q ∈ Finset.range (l + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2) := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun n _ => ?_)) hκtW
    rw [pAO_normSq_icg_raiseDomDom_eq (I := I) (M := M) g₀ lieArm1RhoSlot0
        (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg) n,
      pAO_normSq_icg_lieArm1Kappa_eq (I := I) (M := M) g₀ g₁ g_bg n]
  rw [hdef]
  refine le_trans (lc0b_appCcRS_normSq_le (I := I) (M := M) g₀ 1 1 2
    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
      (domDomCongrSection (I := I) g₀ lieArm1RhoSlot0
        (lieArm1LoweredBgKappa (I := I) (M := M) g₀ g₁ g_bg)))
    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sharpFlatEndoCc (I := I) g₀ g₁) l
    (C2b l) Λκ Λsf
    (Fκt l * (1 + ∑ q ∈ Finset.range (l + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2))
    (Fsft l * (1 + ∑ q ∈ Finset.range (l + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 q P‖ ^ 2))
    (hC2b_nn l) hΛκ_nn hΛsf_nn hA0 hsf0 hAL2 hsftW
    (hC2b l)) (le_of_eq (by ring))

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem lieArm1Piece_connDiff_realizedFam_allOrder_tameEnvelope
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
        ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
        ∀ (i : ℕ), ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (DifferentialGeometry.Integral.Connection.lieArm1Piece (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
                (DifferentialGeometry.Integral.Connection.connDiffSection (I := I)
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀))‖ ^ 2 ≤
            P i * (1 + ∑ j ∈ Finset.range (i + 2),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  classical
  obtain ⟨Λcom, hΛcom_nn, hLich⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_lichnerowicz_cometric_realizedFam_rfns_ballUniform (I := I) (M := M) g₀ a
      ha_super hR hδ₀
  obtain ⟨Qth, hQth_nn, hQth⟩ :=
    pAO_traceHessian_jetSum_tame (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨Fcd, hFcd_nn, hFcd⟩ :=
    pAO_connDiffSection_jetL2_tame (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨Λcd, Fcd0, hΛcd_nn, hFcd0_nn, hcd⟩ :=
    lieArm1_connDiff_feed (I := I) (M := M) g₀ a ha_super hR hδ₀
  have h2A : ∀ k : ℕ, ∃ c : ℝ, 0 ≤ c ∧
      ∀ (S : SmoothCcTensor g₀ 4 2) (T : SmoothCcTensor g₀ 3 4)
        (ΛS ΛT : ℝ), 0 ≤ ΛS → 0 ≤ ΛT →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (S.toSection x) ≤ ΛS ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x (T.toSection x) ≤ ΛT ^ 2) →
        MeasureTheory.Integrable
            (fun x => ∑ n ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + n) x
                  ((iteratedCovGrad (I := I) g₀ 4 2 n S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) x
                      ((iteratedCovGrad (I := I) g₀ 3 4 l T).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
          (∫ x, (∑ n ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + n) x
                  ((iteratedCovGrad (I := I) g₀ 4 2 n S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) x
                      ((iteratedCovGrad (I := I) g₀ 3 4 l T).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            c * (ΛT ^ 2 * ∑ n ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g₀ 4 2 n S‖ ^ 2
                + ΛS ^ 2 * ∑ l ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g₀ 3 4 l T‖ ^ 2) := by
    intro k
    obtain ⟨C, hC_nn, hC⟩ :=
      exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
        (I := I) (M := M) g₀ 4 3 2 4 k
    exact ⟨C, hC_nn, fun S T ΛS ΛT h1 h2 h3 h4 => hC S T ΛS ΛT h1 h2 h3 h4⟩
  choose C2 hC2_nn hC2 using h2A
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨fun i => appCcGdiag (E := E) i *
      (C2 i * ((fr ^ 2 * Λcd) * (2 * Qth i)
        + Λcom * (fr ^ 2 * (2 * ∑ l ∈ Finset.range (i + 1), Fcd l)))), ?_, ?_⟩
  · intro i
    have h1 : (0 : ℝ) ≤ ∑ l ∈ Finset.range (i + 1), Fcd l :=
      Finset.sum_nonneg fun l _ => hFcd_nn l
    have h2 := hQth_nn i
    have h3 := hC2_nn i
    have h4 := appCcGdiag_nonneg (E := E) i
    positivity
  · intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball σ' ρ i s hs
    set W : ℝ := 1 + ∑ j ∈ Finset.range (i + 2),
      (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) with hW_def
    have hW1 : (1 : ℝ) ≤ W := by
      rw [hW_def]
      have : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
          (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) :=
        Finset.sum_nonneg fun _ _ => add_nonneg (sq_nonneg _) (sq_nonneg _)
      linarith
    have hW_nn : (0 : ℝ) ≤ W := le_trans zero_le_one hW1
    by_cases hM : Nonempty M
    · haveI := hM
      obtain ⟨htie, hδP, hδP_le⟩ :=
        lieArm1_realizedFam_pack (I := I) (M := M) g₀ hδ₀ T T' hδ_le hδ hδ'_le hδ' hs
      have hδP0 : (0 : ℝ) ≤ (1 - s) * δ' + s * δ :=
        lieArm1_gFibreOpBound_nonneg (I := I) (M := M) g₀ _ hδP
      have hPball := lieArm1_convexPerturbation_ball (I := I) (M := M) g₀ T T' a
        hTball hT'ball hs
      have hs0 : (0 : ℝ) ≤ s := hs.1
      have h1ms : (0 : ℝ) ≤ 1 - s := by linarith [hs.2]
      have hPq : ∀ q : ℕ,
          ‖iteratedCovGrad (I := I) g₀ 0 2 q (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2 ≤
            2 * (‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ ^ 2) := by
        intro q
        have heq := tsmConvex_jet_eq (I := I) (M := M) g₀ T T' s q
        have hle : ‖iteratedCovGrad (I := I) g₀ 0 2 q
            (convexPerturbation (I := I) g₀ T T' s)‖ ≤
            ‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ +
              ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ := by
          rw [heq]
          calc ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 q T'
                  + s • iteratedCovGrad (I := I) g₀ 0 2 q T‖
              ≤ ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 q T'‖
                  + ‖s • iteratedCovGrad (I := I) g₀ 0 2 q T‖ := norm_add_le _ _
            _ = (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖
                  + s * ‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ := by
                rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
                  abs_of_nonneg h1ms, abs_of_nonneg hs0]
            _ ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ +
                  ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ := by
                have hnT := norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 q T)
                have hnT' := norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 q T')
                nlinarith
        have hnn : (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 q
            (convexPerturbation (I := I) g₀ T T' s)‖ := norm_nonneg _
        nlinarith [sq_nonneg (‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ -
          ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖)]
      have hPwin : ∀ w : ℕ, w ≤ i + 2 →
          (1 + ∑ q ∈ Finset.range w,
            ‖iteratedCovGrad (I := I) g₀ 0 2 q
              (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2) ≤ 2 * W := by
        intro w hw
        have hsum : ∑ q ∈ Finset.range w,
            ‖iteratedCovGrad (I := I) g₀ 0 2 q
              (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2 ≤
            ∑ q ∈ Finset.range w,
              2 * (‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ ^ 2) :=
          Finset.sum_le_sum fun q _ => hPq q
        have hmono : ∑ q ∈ Finset.range w,
            2 * (‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ ^ 2) ≤
            ∑ q ∈ Finset.range (i + 2),
              2 * (‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ ^ 2) :=
          Finset.sum_le_sum_of_subset_of_nonneg (pAO_range_subset hw)
            (fun _ _ _ => by positivity)
        have hexp : ∑ q ∈ Finset.range (i + 2),
            2 * (‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ ^ 2) =
            2 * ∑ q ∈ Finset.range (i + 2),
              (‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ ^ 2) := by
          rw [Finset.mul_sum]
        rw [hW_def]
        rw [hexp] at hmono
        linarith [hsum, hmono]
      obtain ⟨hcd0, _⟩ := hcd (realizedFam (I := I) g₀ T T' hδ hδ' s)
        (convexPerturbation (I := I) g₀ T T' s) htie hδP_le hδP0 hδP hPball
      have hS0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          ((deTurckLieTraceCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) σ').toSection x) ≤
          (Real.sqrt Λcom) ^ 2 := by
        intro x
        rw [Real.sq_sqrt hΛcom_nn, lieArm1_rfns_dLTC_toSection_eq]
        exact (hLich T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x).2
      have hT0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x
          ((slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2
            (connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
              g₀))).toSection x) ≤
          (Real.sqrt (fr ^ 2 * Λcd)) ^ 2 := by
        intro x
        rw [Real.sq_sqrt (mul_nonneg (by positivity) hΛcd_nn)]
        refine le_trans (lieArm1_rfns_sE2_zero_le (I := I) (M := M) g₀ _ x) ?_
        rw [hfr_def]
        exact mul_le_mul_of_nonneg_left (hcd0 x) (by positivity)
      have hFS : ∑ n ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 4 2 n
            (deTurckLieTraceCoeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) σ')‖ ^ 2 ≤
          (2 * Qth i) * W := by
        have heq : ∑ n ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 4 2 n
              (deTurckLieTraceCoeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) σ')‖ ^ 2 =
            ∑ n ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 4 2 n
                (traceHessianCoeff (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 :=
          Finset.sum_congr rfl fun n _ => lieArm1_normSq_icg_dLTC_eq (I := I) (M := M)
            g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' n
        rw [heq]
        refine le_trans (hQth (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (convexPerturbation (I := I) g₀ T T' s) htie hδP_le hδP0 hδP hPball i) ?_
        have hwin := hPwin (i + 1) (by omega)
        have := hQth_nn i
        nlinarith
      have hFT : ∑ l ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 3 4 l
            (slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2
              (connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀)))‖ ^ 2 ≤
          fr ^ 2 * ((2 * ∑ l ∈ Finset.range (i + 1), Fcd l) * W) := by
        have hstep : ∀ l ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 3 4 l
              (slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2
                (connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
                  g₀)))‖ ^ 2 ≤
            fr ^ 2 * (Fcd l * (2 * W)) := by
          intro l hl
          refine le_trans (lieArm1_normSq_icg_sE2_le (I := I) (M := M) g₀ _ l) ?_
          rw [hfr_def]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine le_trans (hFcd (realizedFam (I := I) g₀ T T' hδ hδ' s)
            (convexPerturbation (I := I) g₀ T T' s) htie hδP_le hδP0 hδP hPball l) ?_
          have hl2 : l + 2 ≤ i + 2 := by
            have := Finset.mem_range.mp hl; omega
          have hwin := hPwin (l + 2) hl2
          have := hFcd_nn l
          nlinarith
        refine le_trans (Finset.sum_le_sum hstep) ?_
        rw [← Finset.mul_sum, ← Finset.sum_mul]
        have : (∑ l ∈ Finset.range (i + 1), Fcd l) * (2 * W) =
            (2 * ∑ l ∈ Finset.range (i + 1), Fcd l) * W := by ring
        rw [this]
      have hmaster := lieArm1_piece_normSq_le (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
        (connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀) i
        (C2 i) (Real.sqrt Λcom) (Real.sqrt (fr ^ 2 * Λcd))
        ((2 * Qth i) * W) (fr ^ 2 * ((2 * ∑ l ∈ Finset.range (i + 1), Fcd l) * W))
        (hC2_nn i) hFS hFT
        (hC2 i _ _ (Real.sqrt Λcom) (Real.sqrt (fr ^ 2 * Λcd))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hS0 hT0)
      refine le_trans hmaster (le_of_eq ?_)
      rw [Real.sq_sqrt hΛcom_nn, Real.sq_sqrt (mul_nonneg (by positivity) hΛcd_nn)]
      dsimp only
      ring
    · haveI hIsE := not_nonempty_iff.mp hM
      have h0 := lieArm1_norm_isEmpty (I := I) (M := M) hIsE g₀ 3 (2 + i)
        (iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
            (connDiffSection (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀)))
      rw [h0]
      have hP_nn : (0 : ℝ) ≤ appCcGdiag (E := E) i *
          (C2 i * ((fr ^ 2 * Λcd) * (2 * Qth i)
            + Λcom * (fr ^ 2 * (2 * ∑ l ∈ Finset.range (i + 1), Fcd l)))) := by
        have h1 : (0 : ℝ) ≤ ∑ l ∈ Finset.range (i + 1), Fcd l :=
          Finset.sum_nonneg fun l _ => hFcd_nn l
        have h2 := hQth_nn i
        have h3 := hC2_nn i
        have h4 := appCcGdiag_nonneg (E := E) i
        positivity
      dsimp only
      nlinarith

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem lieArm1Piece_connDiffBg_realizedFam_allOrder_tameEnvelope
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
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
        ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
        ∀ (i : ℕ), ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (DifferentialGeometry.Integral.Connection.lieArm1Piece (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
                (DifferentialGeometry.Integral.Connection.lieArm1ConnDiffBgCc (I := I) (M := M)
                  g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg))‖ ^ 2 ≤
            P i * (1 + ∑ j ∈ Finset.range (i + 2),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  classical
  obtain ⟨Λcom, hΛcom_nn, hLich⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_lichnerowicz_cometric_realizedFam_rfns_ballUniform (I := I) (M := M) g₀ a
      ha_super hR hδ₀
  obtain ⟨Qth, hQth_nn, hQth⟩ :=
    pAO_traceHessian_jetSum_tame (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨Fcd, hFcd_nn, hFcd⟩ :=
    pAO_connDiffSection_jetL2_tame (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨Λcd, Fcd0, hΛcd_nn, hFcd0_nn, hcd⟩ :=
    lieArm1_connDiff_feed (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨Λfx, hΛfx_nn, hΛfx⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 1 2
      (lieArm1FixCd (I := I) (M := M) g₀ g_bg)
  have h2A : ∀ k : ℕ, ∃ c : ℝ, 0 ≤ c ∧
      ∀ (S : SmoothCcTensor g₀ 4 2) (T : SmoothCcTensor g₀ 3 4)
        (ΛS ΛT : ℝ), 0 ≤ ΛS → 0 ≤ ΛT →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (S.toSection x) ≤ ΛS ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x (T.toSection x) ≤ ΛT ^ 2) →
        MeasureTheory.Integrable
            (fun x => ∑ n ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + n) x
                  ((iteratedCovGrad (I := I) g₀ 4 2 n S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) x
                      ((iteratedCovGrad (I := I) g₀ 3 4 l T).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
          (∫ x, (∑ n ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + n) x
                  ((iteratedCovGrad (I := I) g₀ 4 2 n S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) x
                      ((iteratedCovGrad (I := I) g₀ 3 4 l T).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            c * (ΛT ^ 2 * ∑ n ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g₀ 4 2 n S‖ ^ 2
                + ΛS ^ 2 * ∑ l ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g₀ 3 4 l T‖ ^ 2) := by
    intro k
    obtain ⟨C, hC_nn, hC⟩ :=
      exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
        (I := I) (M := M) g₀ 4 3 2 4 k
    exact ⟨C, hC_nn, fun S T ΛS ΛT h1 h2 h3 h4 => hC S T ΛS ΛT h1 h2 h3 h4⟩
  choose C2 hC2_nn hC2 using h2A
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨fun i => appCcGdiag (E := E) i *
      (C2 i * ((fr ^ 2 * (2 * Λcd + 2 * Λfx)) * (2 * Qth i)
        + Λcom * (fr ^ 2 * (∑ l ∈ Finset.range (i + 1), (4 * Fcd l
            + 2 * ‖iteratedCovGrad (I := I) g₀ 1 2 l
                (lieArm1FixCd (I := I) (M := M) g₀ g_bg)‖ ^ 2))))), ?_, ?_⟩
  · intro i
    have h1 : (0 : ℝ) ≤ ∑ l ∈ Finset.range (i + 1), (4 * Fcd l
        + 2 * ‖iteratedCovGrad (I := I) g₀ 1 2 l
            (lieArm1FixCd (I := I) (M := M) g₀ g_bg)‖ ^ 2) :=
      Finset.sum_nonneg fun l _ => by
        have := hFcd_nn l
        positivity
    have h2 := hQth_nn i
    have h3 := hC2_nn i
    have h4 := appCcGdiag_nonneg (E := E) i
    have h5 : (0 : ℝ) ≤ 2 * Λcd + 2 * Λfx := by linarith
    positivity
  · intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball σ' ρ i s hs
    set W : ℝ := 1 + ∑ j ∈ Finset.range (i + 2),
      (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) with hW_def
    have hW1 : (1 : ℝ) ≤ W := by
      rw [hW_def]
      have : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
          (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) :=
        Finset.sum_nonneg fun _ _ => add_nonneg (sq_nonneg _) (sq_nonneg _)
      linarith
    have hW_nn : (0 : ℝ) ≤ W := le_trans zero_le_one hW1
    by_cases hM : Nonempty M
    · haveI := hM
      obtain ⟨htie, hδP, hδP_le⟩ :=
        lieArm1_realizedFam_pack (I := I) (M := M) g₀ hδ₀ T T' hδ_le hδ hδ'_le hδ' hs
      have hδP0 : (0 : ℝ) ≤ (1 - s) * δ' + s * δ :=
        lieArm1_gFibreOpBound_nonneg (I := I) (M := M) g₀ _ hδP
      have hPball := lieArm1_convexPerturbation_ball (I := I) (M := M) g₀ T T' a
        hTball hT'ball hs
      have hs0 : (0 : ℝ) ≤ s := hs.1
      have h1ms : (0 : ℝ) ≤ 1 - s := by linarith [hs.2]
      have hPq : ∀ q : ℕ,
          ‖iteratedCovGrad (I := I) g₀ 0 2 q (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2 ≤
            2 * (‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ ^ 2) := by
        intro q
        have heq := tsmConvex_jet_eq (I := I) (M := M) g₀ T T' s q
        have hle : ‖iteratedCovGrad (I := I) g₀ 0 2 q
            (convexPerturbation (I := I) g₀ T T' s)‖ ≤
            ‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ +
              ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ := by
          rw [heq]
          calc ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 q T'
                  + s • iteratedCovGrad (I := I) g₀ 0 2 q T‖
              ≤ ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 q T'‖
                  + ‖s • iteratedCovGrad (I := I) g₀ 0 2 q T‖ := norm_add_le _ _
            _ = (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖
                  + s * ‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ := by
                rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
                  abs_of_nonneg h1ms, abs_of_nonneg hs0]
            _ ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ +
                  ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ := by
                have hnT := norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 q T)
                have hnT' := norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 q T')
                nlinarith
        have hnn : (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 q
            (convexPerturbation (I := I) g₀ T T' s)‖ := norm_nonneg _
        nlinarith [sq_nonneg (‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ -
          ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖)]
      have hPwin : ∀ w : ℕ, w ≤ i + 2 →
          (1 + ∑ q ∈ Finset.range w,
            ‖iteratedCovGrad (I := I) g₀ 0 2 q
              (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2) ≤ 2 * W := by
        intro w hw
        have hsum : ∑ q ∈ Finset.range w,
            ‖iteratedCovGrad (I := I) g₀ 0 2 q
              (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2 ≤
            ∑ q ∈ Finset.range w,
              2 * (‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ ^ 2) :=
          Finset.sum_le_sum fun q _ => hPq q
        have hmono : ∑ q ∈ Finset.range w,
            2 * (‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ ^ 2) ≤
            ∑ q ∈ Finset.range (i + 2),
              2 * (‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ ^ 2) :=
          Finset.sum_le_sum_of_subset_of_nonneg (pAO_range_subset hw)
            (fun _ _ _ => by positivity)
        have hexp : ∑ q ∈ Finset.range (i + 2),
            2 * (‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ ^ 2) =
            2 * ∑ q ∈ Finset.range (i + 2),
              (‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ ^ 2) := by
          rw [Finset.mul_sum]
        rw [hW_def]
        rw [hexp] at hmono
        linarith [hsum, hmono]
      obtain ⟨hcd0, _⟩ := hcd (realizedFam (I := I) g₀ T T' hδ hδ' s)
        (convexPerturbation (I := I) g₀ T T' s) htie hδP_le hδP0 hδP hPball
      have hΨ0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
          ((lieArm1ConnDiffBgCc (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg).toSection x) ≤
          2 * Λcd + 2 * Λfx := by
        intro x
        rw [lieArm1_connDiffBg_decomp (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg]
        refine le_trans (lieArm1_rfns_toSection_add_le (I := I) (M := M) g₀ 1 2 _ _ x) ?_
        have h1 := hcd0 x
        have h2 := hΛfx x
        linarith
      have hΨ0_nn : (0 : ℝ) ≤ 2 * Λcd + 2 * Λfx := by linarith
      have hS0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          ((deTurckLieTraceCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) σ').toSection x) ≤
          (Real.sqrt Λcom) ^ 2 := by
        intro x
        rw [Real.sq_sqrt hΛcom_nn, lieArm1_rfns_dLTC_toSection_eq]
        exact (hLich T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x).2
      have hT0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x
          ((slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2
            (lieArm1ConnDiffBgCc (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg))).toSection x) ≤
          (Real.sqrt (fr ^ 2 * (2 * Λcd + 2 * Λfx))) ^ 2 := by
        intro x
        rw [Real.sq_sqrt (mul_nonneg (by positivity) hΨ0_nn)]
        refine le_trans (lieArm1_rfns_sE2_zero_le (I := I) (M := M) g₀ _ x) ?_
        rw [hfr_def]
        exact mul_le_mul_of_nonneg_left (hΨ0 x) (by positivity)
      have hFS : ∑ n ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 4 2 n
            (deTurckLieTraceCoeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) σ')‖ ^ 2 ≤
          (2 * Qth i) * W := by
        have heq : ∑ n ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 4 2 n
              (deTurckLieTraceCoeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) σ')‖ ^ 2 =
            ∑ n ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 4 2 n
                (traceHessianCoeff (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 :=
          Finset.sum_congr rfl fun n _ => lieArm1_normSq_icg_dLTC_eq (I := I) (M := M)
            g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' n
        rw [heq]
        refine le_trans (hQth (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (convexPerturbation (I := I) g₀ T T' s) htie hδP_le hδP0 hδP hPball i) ?_
        have hwin := hPwin (i + 1) (by omega)
        have := hQth_nn i
        nlinarith
      have hFT : ∑ l ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 3 4 l
            (slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2
              (lieArm1ConnDiffBgCc (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)))‖ ^ 2 ≤
          fr ^ 2 * ((∑ l ∈ Finset.range (i + 1), (4 * Fcd l
            + 2 * ‖iteratedCovGrad (I := I) g₀ 1 2 l
                (lieArm1FixCd (I := I) (M := M) g₀ g_bg)‖ ^ 2)) * W) := by
        have hstep : ∀ l ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 3 4 l
              (slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2
                (lieArm1ConnDiffBgCc (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)))‖ ^ 2 ≤
            fr ^ 2 * ((4 * Fcd l
              + 2 * ‖iteratedCovGrad (I := I) g₀ 1 2 l
                  (lieArm1FixCd (I := I) (M := M) g₀ g_bg)‖ ^ 2) * W) := by
          intro l hl
          refine le_trans (lieArm1_normSq_icg_sE2_le (I := I) (M := M) g₀ _ l) ?_
          rw [hfr_def]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hdecomp : ‖iteratedCovGrad (I := I) g₀ 1 2 l
              (lieArm1ConnDiffBgCc (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2 ≤
              2 * ‖iteratedCovGrad (I := I) g₀ 1 2 l
                  (connDiffSection (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀)‖ ^ 2
                + 2 * ‖iteratedCovGrad (I := I) g₀ 1 2 l
                  (lieArm1FixCd (I := I) (M := M) g₀ g_bg)‖ ^ 2 := by
            rw [lieArm1_connDiffBg_decomp (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg]
            exact lieArm1_normSq_icg_add_le (I := I) (M := M) g₀ 1 2 l _ _
          have hcdl : ‖iteratedCovGrad (I := I) g₀ 1 2 l
              (connDiffSection (I := I)
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀)‖ ^ 2 ≤
              Fcd l * (2 * W) := by
            refine le_trans (hFcd (realizedFam (I := I) g₀ T T' hδ hδ' s)
              (convexPerturbation (I := I) g₀ T T' s) htie hδP_le hδP0 hδP hPball l) ?_
            have hl2 : l + 2 ≤ i + 2 := by
              have := Finset.mem_range.mp hl; omega
            have hwin := hPwin (l + 2) hl2
            have := hFcd_nn l
            nlinarith
          have hBfx_nn : (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ 1 2 l
              (lieArm1FixCd (I := I) (M := M) g₀ g_bg)‖ ^ 2 := sq_nonneg _
          nlinarith [hdecomp, hcdl, hBfx_nn, hW1]
        refine le_trans (Finset.sum_le_sum hstep) ?_
        rw [← Finset.mul_sum, ← Finset.sum_mul]
      have hmaster := lieArm1_piece_normSq_le (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
        (lieArm1ConnDiffBgCc (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) i
        (C2 i) (Real.sqrt Λcom) (Real.sqrt (fr ^ 2 * (2 * Λcd + 2 * Λfx)))
        ((2 * Qth i) * W)
        (fr ^ 2 * ((∑ l ∈ Finset.range (i + 1), (4 * Fcd l
          + 2 * ‖iteratedCovGrad (I := I) g₀ 1 2 l
              (lieArm1FixCd (I := I) (M := M) g₀ g_bg)‖ ^ 2)) * W))
        (hC2_nn i) hFS hFT
        (hC2 i _ _ (Real.sqrt Λcom) (Real.sqrt (fr ^ 2 * (2 * Λcd + 2 * Λfx)))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hS0 hT0)
      refine le_trans hmaster (le_of_eq ?_)
      rw [Real.sq_sqrt hΛcom_nn, Real.sq_sqrt (mul_nonneg (by positivity) hΨ0_nn)]
      dsimp only
      ring
    · haveI hIsE := not_nonempty_iff.mp hM
      have h0 := lieArm1_norm_isEmpty (I := I) (M := M) hIsE g₀ 3 (2 + i)
        (iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
            (lieArm1ConnDiffBgCc (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)))
      rw [h0]
      have hP_nn : (0 : ℝ) ≤ appCcGdiag (E := E) i *
          (C2 i * ((fr ^ 2 * (2 * Λcd + 2 * Λfx)) * (2 * Qth i)
            + Λcom * (fr ^ 2 * (∑ l ∈ Finset.range (i + 1), (4 * Fcd l
                + 2 * ‖iteratedCovGrad (I := I) g₀ 1 2 l
                    (lieArm1FixCd (I := I) (M := M) g₀ g_bg)‖ ^ 2))))) := by
        have h1 : (0 : ℝ) ≤ ∑ l ∈ Finset.range (i + 1), (4 * Fcd l
            + 2 * ‖iteratedCovGrad (I := I) g₀ 1 2 l
                (lieArm1FixCd (I := I) (M := M) g₀ g_bg)‖ ^ 2) :=
          Finset.sum_nonneg fun l _ => by
            have := hFcd_nn l
            positivity
        have h2 := hQth_nn i
        have h3 := hC2_nn i
        have h4 := appCcGdiag_nonneg (E := E) i
        have h5 : (0 : ℝ) ≤ 2 * Λcd + 2 * Λfx := by linarith
        positivity
      dsimp only
      nlinarith

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem lieArm1Piece_psiB_realizedFam_allOrder_tameEnvelope
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
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
        ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
        ∀ (i : ℕ), ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (DifferentialGeometry.Integral.Connection.lieArm1Piece (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
                (DifferentialGeometry.Integral.Connection.lieArm1PsiB (I := I) (M := M)
                  g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg))‖ ^ 2 ≤
            P i * (1 + ∑ j ∈ Finset.range (i + 2),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  classical
  obtain ⟨Λcom, hΛcom_nn, hLich⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_lichnerowicz_cometric_realizedFam_rfns_ballUniform (I := I) (M := M) g₀ a
      ha_super hR hδ₀
  obtain ⟨Qth, hQth_nn, hQth⟩ :=
    pAO_traceHessian_jetSum_tame (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨Fpb, hFpb_nn, hFpbJ⟩ :=
    pAO_lieArm1PsiB_jetL2_tame (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  obtain ⟨Λpb, Fpb0, hΛpb_nn, hFpb0_nn, hpb⟩ :=
    lieArm1_psiB_feed (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  have h2A : ∀ k : ℕ, ∃ c : ℝ, 0 ≤ c ∧
      ∀ (S : SmoothCcTensor g₀ 4 2) (T : SmoothCcTensor g₀ 3 4)
        (ΛS ΛT : ℝ), 0 ≤ ΛS → 0 ≤ ΛT →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (S.toSection x) ≤ ΛS ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x (T.toSection x) ≤ ΛT ^ 2) →
        MeasureTheory.Integrable
            (fun x => ∑ n ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + n) x
                  ((iteratedCovGrad (I := I) g₀ 4 2 n S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) x
                      ((iteratedCovGrad (I := I) g₀ 3 4 l T).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
          (∫ x, (∑ n ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + n) x
                  ((iteratedCovGrad (I := I) g₀ 4 2 n S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) x
                      ((iteratedCovGrad (I := I) g₀ 3 4 l T).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            c * (ΛT ^ 2 * ∑ n ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g₀ 4 2 n S‖ ^ 2
                + ΛS ^ 2 * ∑ l ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g₀ 3 4 l T‖ ^ 2) := by
    intro k
    obtain ⟨C, hC_nn, hC⟩ :=
      exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
        (I := I) (M := M) g₀ 4 3 2 4 k
    exact ⟨C, hC_nn, fun S T ΛS ΛT h1 h2 h3 h4 => hC S T ΛS ΛT h1 h2 h3 h4⟩
  choose C2 hC2_nn hC2 using h2A
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨fun i => appCcGdiag (E := E) i *
      (C2 i * ((fr ^ 2 * Λpb) * (2 * Qth i)
        + Λcom * (fr ^ 2 * (2 * ∑ l ∈ Finset.range (i + 1), Fpb l)))), ?_, ?_⟩
  · intro i
    have h1 : (0 : ℝ) ≤ ∑ l ∈ Finset.range (i + 1), Fpb l :=
      Finset.sum_nonneg fun l _ => hFpb_nn l
    have h2 := hQth_nn i
    have h3 := hC2_nn i
    have h4 := appCcGdiag_nonneg (E := E) i
    positivity
  · intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball σ' ρ i s hs
    set W : ℝ := 1 + ∑ j ∈ Finset.range (i + 2),
      (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) with hW_def
    have hW1 : (1 : ℝ) ≤ W := by
      rw [hW_def]
      have : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
          (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) :=
        Finset.sum_nonneg fun _ _ => add_nonneg (sq_nonneg _) (sq_nonneg _)
      linarith
    have hW_nn : (0 : ℝ) ≤ W := le_trans zero_le_one hW1
    by_cases hM : Nonempty M
    · haveI := hM
      obtain ⟨htie, hδP, hδP_le⟩ :=
        lieArm1_realizedFam_pack (I := I) (M := M) g₀ hδ₀ T T' hδ_le hδ hδ'_le hδ' hs
      have hδP0 : (0 : ℝ) ≤ (1 - s) * δ' + s * δ :=
        lieArm1_gFibreOpBound_nonneg (I := I) (M := M) g₀ _ hδP
      have hPball := lieArm1_convexPerturbation_ball (I := I) (M := M) g₀ T T' a
        hTball hT'ball hs
      have hs0 : (0 : ℝ) ≤ s := hs.1
      have h1ms : (0 : ℝ) ≤ 1 - s := by linarith [hs.2]
      have hPq : ∀ q : ℕ,
          ‖iteratedCovGrad (I := I) g₀ 0 2 q (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2 ≤
            2 * (‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ ^ 2) := by
        intro q
        have heq := tsmConvex_jet_eq (I := I) (M := M) g₀ T T' s q
        have hle : ‖iteratedCovGrad (I := I) g₀ 0 2 q
            (convexPerturbation (I := I) g₀ T T' s)‖ ≤
            ‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ +
              ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ := by
          rw [heq]
          calc ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 q T'
                  + s • iteratedCovGrad (I := I) g₀ 0 2 q T‖
              ≤ ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 q T'‖
                  + ‖s • iteratedCovGrad (I := I) g₀ 0 2 q T‖ := norm_add_le _ _
            _ = (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖
                  + s * ‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ := by
                rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
                  abs_of_nonneg h1ms, abs_of_nonneg hs0]
            _ ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ +
                  ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ := by
                have hnT := norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 q T)
                have hnT' := norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 q T')
                nlinarith
        have hnn : (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 q
            (convexPerturbation (I := I) g₀ T T' s)‖ := norm_nonneg _
        nlinarith [sq_nonneg (‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ -
          ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖)]
      have hPwin : ∀ w : ℕ, w ≤ i + 2 →
          (1 + ∑ q ∈ Finset.range w,
            ‖iteratedCovGrad (I := I) g₀ 0 2 q
              (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2) ≤ 2 * W := by
        intro w hw
        have hsum : ∑ q ∈ Finset.range w,
            ‖iteratedCovGrad (I := I) g₀ 0 2 q
              (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2 ≤
            ∑ q ∈ Finset.range w,
              2 * (‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ ^ 2) :=
          Finset.sum_le_sum fun q _ => hPq q
        have hmono : ∑ q ∈ Finset.range w,
            2 * (‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ ^ 2) ≤
            ∑ q ∈ Finset.range (i + 2),
              2 * (‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ ^ 2) :=
          Finset.sum_le_sum_of_subset_of_nonneg (pAO_range_subset hw)
            (fun _ _ _ => by positivity)
        have hexp : ∑ q ∈ Finset.range (i + 2),
            2 * (‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ ^ 2) =
            2 * ∑ q ∈ Finset.range (i + 2),
              (‖iteratedCovGrad (I := I) g₀ 0 2 q T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 q T'‖ ^ 2) := by
          rw [Finset.mul_sum]
        rw [hW_def]
        rw [hexp] at hmono
        linarith [hsum, hmono]
      obtain ⟨hpb0, _⟩ := hpb (realizedFam (I := I) g₀ T T' hδ hδ' s)
        (convexPerturbation (I := I) g₀ T T' s) htie hδP_le hδP0 hδP hPball
      have hS0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          ((deTurckLieTraceCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) σ').toSection x) ≤
          (Real.sqrt Λcom) ^ 2 := by
        intro x
        rw [Real.sq_sqrt hΛcom_nn, lieArm1_rfns_dLTC_toSection_eq]
        exact (hLich T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x).2
      have hT0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x
          ((slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2
            (lieArm1PsiB (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg))).toSection x) ≤
          (Real.sqrt (fr ^ 2 * Λpb)) ^ 2 := by
        intro x
        rw [Real.sq_sqrt (mul_nonneg (by positivity) hΛpb_nn)]
        refine le_trans (lieArm1_rfns_sE2_zero_le (I := I) (M := M) g₀ _ x) ?_
        rw [hfr_def]
        exact mul_le_mul_of_nonneg_left (hpb0 x) (by positivity)
      have hFS : ∑ n ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 4 2 n
            (deTurckLieTraceCoeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) σ')‖ ^ 2 ≤
          (2 * Qth i) * W := by
        have heq : ∑ n ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 4 2 n
              (deTurckLieTraceCoeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) σ')‖ ^ 2 =
            ∑ n ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 4 2 n
                (traceHessianCoeff (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 :=
          Finset.sum_congr rfl fun n _ => lieArm1_normSq_icg_dLTC_eq (I := I) (M := M)
            g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' n
        rw [heq]
        refine le_trans (hQth (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (convexPerturbation (I := I) g₀ T T' s) htie hδP_le hδP0 hδP hPball i) ?_
        have hwin := hPwin (i + 1) (by omega)
        have := hQth_nn i
        nlinarith
      have hFT : ∑ l ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 3 4 l
            (slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2
              (lieArm1PsiB (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)))‖ ^ 2 ≤
          fr ^ 2 * ((2 * ∑ l ∈ Finset.range (i + 1), Fpb l) * W) := by
        have hstep : ∀ l ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 3 4 l
              (slotExtend (I := I) (M := M) g₀ 2 3 (slotExtend (I := I) (M := M) g₀ 1 2
                (lieArm1PsiB (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)))‖ ^ 2 ≤
            fr ^ 2 * (Fpb l * (2 * W)) := by
          intro l hl
          refine le_trans (lieArm1_normSq_icg_sE2_le (I := I) (M := M) g₀ _ l) ?_
          rw [hfr_def]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine le_trans (hFpbJ (realizedFam (I := I) g₀ T T' hδ hδ' s)
            (convexPerturbation (I := I) g₀ T T' s) htie hδP_le hδP0 hδP hPball l) ?_
          have hl2 : l + 2 ≤ i + 2 := by
            have := Finset.mem_range.mp hl; omega
          have hwin := hPwin (l + 2) hl2
          have := hFpb_nn l
          nlinarith
        refine le_trans (Finset.sum_le_sum hstep) ?_
        rw [← Finset.mul_sum, ← Finset.sum_mul]
        have : (∑ l ∈ Finset.range (i + 1), Fpb l) * (2 * W) =
            (2 * ∑ l ∈ Finset.range (i + 1), Fpb l) * W := by ring
        rw [this]
      have hmaster := lieArm1_piece_normSq_le (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
        (lieArm1PsiB (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) i
        (C2 i) (Real.sqrt Λcom) (Real.sqrt (fr ^ 2 * Λpb))
        ((2 * Qth i) * W) (fr ^ 2 * ((2 * ∑ l ∈ Finset.range (i + 1), Fpb l) * W))
        (hC2_nn i) hFS hFT
        (hC2 i _ _ (Real.sqrt Λcom) (Real.sqrt (fr ^ 2 * Λpb))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hS0 hT0)
      refine le_trans hmaster (le_of_eq ?_)
      rw [Real.sq_sqrt hΛcom_nn, Real.sq_sqrt (mul_nonneg (by positivity) hΛpb_nn)]
      dsimp only
      ring
    · haveI hIsE := not_nonempty_iff.mp hM
      have h0 := lieArm1_norm_isEmpty (I := I) (M := M) hIsE g₀ 3 (2 + i)
        (iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) σ' ρ
            (lieArm1PsiB (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)))
      rw [h0]
      have hP_nn : (0 : ℝ) ≤ appCcGdiag (E := E) i *
          (C2 i * ((fr ^ 2 * Λpb) * (2 * Qth i)
            + Λcom * (fr ^ 2 * (2 * ∑ l ∈ Finset.range (i + 1), Fpb l)))) := by
        have h1 : (0 : ℝ) ≤ ∑ l ∈ Finset.range (i + 1), Fpb l :=
          Finset.sum_nonneg fun l _ => hFpb_nn l
        have h2 := hQth_nn i
        have h3 := hC2_nn i
        have h4 := appCcGdiag_nonneg (E := E) i
        positivity
      dsimp only
      nlinarith

private theorem p1_sq_le_target_fw {V : Type*} [SeminormedAddCommGroup V]
    {v : V} {B Sw W : ℝ} (hSw_sq : Sw ^ 2 = W) (hB_nn : 0 ≤ B * Sw)
    (h : ‖v‖ ≤ B * Sw) : ‖v‖ ^ 2 ≤ B ^ 2 * W := by
  have h2 := pow_le_pow_left₀ (norm_nonneg v) h 2
  rwa [mul_pow, hSw_sq] at h2

namespace DeTurckRemainderTameLipschitz

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
theorem deTurckLieArm1Coeff_realizedFam_allOrder_tameEnvelope
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (deTurckLieArm1Coeff (I := I) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 2),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  classical
  obtain ⟨Pc, hPc_nn, hPc⟩ :=
    lieArm1Piece_connDiff_realizedFam_allOrder_tameEnvelope (I := I) (M := M) g₀ a
      ha_super hR hδ₀
  obtain ⟨Pbg, hPbg_nn, hPbg⟩ :=
    lieArm1Piece_connDiffBg_realizedFam_allOrder_tameEnvelope (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  obtain ⟨Pb, hPb_nn, hPb⟩ :=
    lieArm1Piece_psiB_realizedFam_allOrder_tameEnvelope (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  refine ⟨fun i => (11 * Real.sqrt (Pc i) + 2 * Real.sqrt (Pb i) + Real.sqrt (Pbg i)) ^ 2,
    fun i => sq_nonneg _, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i s hs
  set g₁ : SmoothRiemannianMetric I M := realizedFam (I := I) g₀ T T' hδ hδ' s with hg₁
  set W : ℝ := 1 + ∑ j ∈ Finset.range (i + 2),
    (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
      ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) with hW_def
  have hW_nn : (0 : ℝ) ≤ W := by
    rw [hW_def]
    positivity
  set Sw : ℝ := Real.sqrt W with hSw_def
  have hSw_nn : 0 ≤ Sw := Real.sqrt_nonneg _
  have hSw_sq : Sw ^ 2 = W := Real.sq_sqrt hW_nn
  have hcd : ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
      ‖iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ σ' ρ (connDiffSection (I := I) g₁ g₀))‖ ≤
        Real.sqrt (Pc i) * Sw := by
    intro σ' ρ
    have h := lieArm1_norm_le_sqrt_fw
      (hPc T T' hδ_le hδ hδ'_le hδ' hTball hT'ball σ' ρ i s hs)
    rw [Real.sqrt_mul (hPc_nn i)] at h
    exact h
  have hbg : ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
      ‖iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ σ' ρ
          (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg))‖ ≤
        Real.sqrt (Pbg i) * Sw := by
    intro σ' ρ
    have h := lieArm1_norm_le_sqrt_fw
      (hPbg T T' hδ_le hδ hδ'_le hδ' hTball hT'ball σ' ρ i s hs)
    rw [Real.sqrt_mul (hPbg_nn i)] at h
    exact h
  have hpb : ∀ (σ' : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)),
      ‖iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ σ' ρ
          (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg))‖ ≤
        Real.sqrt (Pb i) * Sw := by
    intro σ' ρ
    have h := lieArm1_norm_le_sqrt_fw
      (hPb T T' hδ_le hδ hδ'_le hδ' hTball hT'ball σ' ρ i s hs)
    rw [Real.sqrt_mul (hPb_nn i)] at h
    exact h
  rw [deTurckLieArm1Coeff_eq_lieArm1Piece_sum (I := I) (M := M) g₀ g₁ g_bg]
  simp only [iteratedCovGrad_add, iteratedCovGrad_sub]
  refine p1_sq_le_target_fw hSw_sq (by positivity) ?_
  have hsqrtPc_nn : 0 ≤ Real.sqrt (Pc i) := Real.sqrt_nonneg _
  have hsqrtPb_nn : 0 ≤ Real.sqrt (Pb i) := Real.sqrt_nonneg _
  have hblock1 := lieArm1_norm_block6_le'_fw
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
        (connDiffSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
        (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC (Equiv.refl (Fin 3))
        (connDiffSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaD lieArm1RhoSlot0
        (connDiffSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (lieArm1Piece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot1
        (connDiffSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaF (Equiv.refl (Fin 3))
        (connDiffSection (I := I) g₁ g₀)))
  have hblock2 := lieArm1_norm_block6_le'_fw
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
        (connDiffSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
        (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaCSwap (Equiv.refl (Fin 3))
        (connDiffSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaDSwap lieArm1RhoSlot0
        (connDiffSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaESwap lieArm1RhoSlot1
        (connDiffSection (I := I) g₁ g₀)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaFSwap (Equiv.refl (Fin 3))
        (connDiffSection (I := I) g₁ g₀)))
  have htri1 := norm_add_le
    (iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC lieArm1RhoSlot0
          (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg))
      + (iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))
        + iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
            (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaD lieArm1RhoSlot0
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot1
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaF (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀)))
      + (iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))
        + iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
            (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaCSwap (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaDSwap lieArm1RhoSlot0
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaESwap lieArm1RhoSlot1
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaFSwap (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))))
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (lieArm1Piece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot0
        (connDiffSection (I := I) g₁ g₀)))
  have htri2 := norm_add_le
    (iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC lieArm1RhoSlot0
          (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg))
      + (iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))
        + iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
            (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaD lieArm1RhoSlot0
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot1
            (connDiffSection (I := I) g₁ g₀))
        - iteratedCovGrad (I := I) g₀ 3 2 i
          (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaF (Equiv.refl (Fin 3))
            (connDiffSection (I := I) g₁ g₀))))
    (iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
          (connDiffSection (I := I) g₁ g₀))
      + iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaASwap (Equiv.refl (Fin 3))
          (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaCSwap (Equiv.refl (Fin 3))
          (connDiffSection (I := I) g₁ g₀))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaDSwap lieArm1RhoSlot0
          (connDiffSection (I := I) g₁ g₀))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaESwap lieArm1RhoSlot1
          (connDiffSection (I := I) g₁ g₀))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaFSwap (Equiv.refl (Fin 3))
          (connDiffSection (I := I) g₁ g₀)))
  have htri3 := norm_add_le
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC lieArm1RhoSlot0
        (lieArm1ConnDiffBgCc (I := I) (M := M) g₀ g₁ g_bg)))
    (iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
          (connDiffSection (I := I) g₁ g₀))
      + iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaA (Equiv.refl (Fin 3))
          (lieArm1PsiB (I := I) (M := M) g₀ g₁ g_bg))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaC (Equiv.refl (Fin 3))
          (connDiffSection (I := I) g₁ g₀))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaD lieArm1RhoSlot0
          (connDiffSection (I := I) g₁ g₀))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ (Equiv.refl (Fin 4)) lieArm1RhoSlot1
          (connDiffSection (I := I) g₁ g₀))
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (lieArm1Piece (I := I) (M := M) g₀ g₁ lieArm1SigmaF (Equiv.refl (Fin 3))
          (connDiffSection (I := I) g₁ g₀)))
  have h1 := hcd lieArm1SigmaA (Equiv.refl (Fin 3))
  have h2 := hpb lieArm1SigmaA (Equiv.refl (Fin 3))
  have h3 := hcd lieArm1SigmaC (Equiv.refl (Fin 3))
  have h4 := hcd lieArm1SigmaD lieArm1RhoSlot0
  have h5 := hcd (Equiv.refl (Fin 4)) lieArm1RhoSlot1
  have h6 := hcd lieArm1SigmaF (Equiv.refl (Fin 3))
  have h7 := hcd lieArm1SigmaASwap (Equiv.refl (Fin 3))
  have h8 := hpb lieArm1SigmaASwap (Equiv.refl (Fin 3))
  have h9 := hcd lieArm1SigmaCSwap (Equiv.refl (Fin 3))
  have h10 := hcd lieArm1SigmaDSwap lieArm1RhoSlot0
  have h11 := hcd lieArm1SigmaESwap lieArm1RhoSlot1
  have h12 := hcd lieArm1SigmaFSwap (Equiv.refl (Fin 3))
  have h13 := hbg lieArm1SigmaC lieArm1RhoSlot0
  have h14 := hcd (Equiv.refl (Fin 4)) lieArm1RhoSlot0
  linarith [htri1, htri2, htri3, hblock1, hblock2]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in

theorem linearizedRicciArm1CorrField_allOrder_tameEnvelope_interface
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (linearizedRicciArm1CorrField (I := I) g₀ T T' hδ hδ' s)‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 2),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  classical
  obtain ⟨K, hK_nn, hK⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_corrArm1Field_realizedFam_jetL2_tameEnvelope
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨K, hK_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i s hs
  have hid :=
    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_arm0_arm1_corrField_data
      (I := I) g₀ T T' hδ hδ').choose_spec.choose_spec.2.2.2.2.2
  rw [show linearizedRicciArm1CorrField (I := I) g₀ T T' hδ hδ' s =
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder1Coeff
          (I := I) g₀ T T' hδ hδ' s
        - linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s from hid s]
  exact hK T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i s hs

end DeTurckRemainderTameLipschitz

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
