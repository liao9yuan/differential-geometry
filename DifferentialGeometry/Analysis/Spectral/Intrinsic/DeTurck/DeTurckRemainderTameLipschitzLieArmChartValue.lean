import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Sobolev.MoserTameProduct
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenbergProductTwoArm
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradParametricJointSmooth
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
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmAppCc
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.PathIntegralFibreNormTransfer
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RemainderCoeffL2JetMoser
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SymmAbsorbedCoeffInputReindexBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciArmPrincipalCoeffBackgroundJetBound
import DifferentialGeometry.Analysis.Sobolev.Embedding.ContinuousSobolevRealization
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckLieHigherOrderCoeffField
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RealizedFamChartLieDeriv
import DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.LieDeTurckRemainderOrderSplit
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieKernelL2JetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckLieCoeffAppCcValue
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.RealizedGramDerivChartEvaluation
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieCoeffL2JetBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieArm1CoeffL2JetBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieArm2CoeffL2JetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.IteratedCovGradHsJetBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefold
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzArmConnLapJetBounds
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzRicciArmCoeffBallUniform
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzLiePathValueDerivative
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzLieArmChartValueMatrixNormalFormCombinatorics

set_option linter.unusedSectionVars false

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
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (covGrad unitModel smoothCcTensor_ext_of_unitModel unitTensor pathIntegralCoeffField pathIntegralCoeffField_appCc_eq pathIntegralCoeffField_toSection linearizedRicciThreeArmHjoint linearizedRicciThreeArmHcont linearizedRicciThreeArmHjoint_zero exists_linearizedRicci_threeArm_coeffFields ricciTensor_realize_sub_eq_threeArm_appCc linearizedRicciArm0Field linearizedRicciArm1Field linearizedRicciArm2FieldLichnerowicz linearizedRicciArm0BaseCoeff linearizedRicciArm0CorrField linearizedRicciArm1BaseCoeff linearizedRicciArm1CorrField ricciArmPrincipalCoeff traceHessianCoeff linearizedRicci_arm0Field_jointSmooth linearizedRicci_arm1Field_jointSmooth linearizedRicci_arm2FieldLichnerowicz_jointSmooth ricciArmOrder1KoszulCoeff exists_arm1Koszul_realizedFam_rfns_ballUniform continuousBilinearMap_basis_expand unitModel_basis_expand_two unitModel_eq_ccTensorBilin_local appCc_zero_left_local ccTensor02Symm symmS_sub ccTensorBilin_symmS iteratedCovGrad_symmS_eq domDomCongrSection riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection)
open DifferentialGeometry.PDE.DeTurck (deTurckVF)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (realizedSmallSet realizedSmallSet_isOpen Icc_subset_realizedSmallSet linearizedRicciAt ricciTensor_realized_sub_eq_integral_linearizedRicci linearizedRicciAt_eq_deriv_chartSum_on_Ioo realizedRicciChartSum jointContMDiff_toModel_continuous_slice hasDerivAt_realizedRicciChartSum_general realizedFam)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (symmAbsorbedCoeff symmAbsorbedCoeff_appCc_eq exists_iteratedCovGrad_unitModel_domDomCongrSection symmAbsorbedCoeff_riemannianFiberNormSq_le symmAbsorbedCoeff_jet_le)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance instCompleteSpaceE_tame : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

section

open DifferentialGeometry.Integral.DivergenceTheorem (chartInvGramMatrix)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (lieDeTurckChartSlope deriv_realizedFam_chartLieDeTurckComp_eq_chartSlope lieDeTurckChartSlope_eq_orderSplit contMDiffOn_clm_section_of_pointwise_joint_manifold_time)
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck (cometricLmodel)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (reindexCoeffGen reindexCoeffFibGen reindexCoeffFibGen_apply reindexCoeffGen_toSection deTurckLieArm2PrincipalCoeff deTurckLieArm1Coeff deTurckLieCoeffField deTurckLieArm2PrincipalCoeff_realizedFam_jointSmooth deTurckLieArm1Coeff_realizedFam_jointSmooth deTurckLieCoeffField_realizedFam_jointSmooth deTurckLieArm2PrincipalCoeff_apply_eq cometricFinBasisTrace_eq_chartInvGram_bilin quadrilinearMapSlotBilinearAt unitModel4SlotBilin_apply)

set_option backward.isDefEq.respectTransparency false

private theorem lieArm_shell_reduction
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (Φ₀b : ℝ → SmoothCcTensor g₀ 2 2)
    (hj0 : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 Φ₀b (δ := δ) (δ' := δ'))
    (hjAbsorb : ∀ (r : ℕ) (Φ : ℝ → SmoothCcTensor g₀ (2 + r) 2)
      (σ' : Equiv.Perm (Fin (2 + r))),
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ (2 + r) Φ (δ := δ) (δ' := δ') →
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ (2 + r)
        (fun s => symmAbsorbedCoeff (I := I) (M := M) g₀ r (Φ s) σ') (δ := δ) (δ' := δ'))
    (hcore : ∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ (x : M) (i j : Fin (Module.finrank ℝ E)),
        lieDeTurckChartSlope (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' g_bg x i j s
            (extChartAt I x x) =
          unitModel (I := I) (M := M) g₀ 2
            (operatorFieldApply (I := I) (M := M) g₀ 2 2 (Φ₀b s)
                (iteratedCovGrad (I := I) g₀ 0 2 0 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))
              + operatorFieldApply (I := I) (M := M) g₀ 3 2
                (deTurckLieArm1Coeff (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
                (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))
              + operatorFieldApply (I := I) (M := M) g₀ 4 2
                (deTurckLieArm2PrincipalCoeff (I := I) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
                (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x
            ![(chartModelBasis E) i, (chartModelBasis E) j]) :
    ∃ (Φ₀L : ℝ → SmoothCcTensor g₀ 2 2) (Φ₁L : ℝ → SmoothCcTensor g₀ 3 2)
      (Φ₂L : ℝ → SmoothCcTensor g₀ 4 2),
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 Φ₀L (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3 Φ₁L (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4 Φ₂L (δ := δ) (δ' := δ') ∧
      ∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 →
        ∀ (x : M) (v : Fin 2 → TangentSpace I x),
          (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) j *
              deriv (fun s : ℝ =>
                DeTurckCoefficients.chartLieDeTurckComp (I := I)
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i j (extChartAt I x x)) s) =
            unitModel (I := I) (M := M) g₀ 2
              (operatorFieldApply (I := I) (M := M) g₀ 2 2 (Φ₀L s)
                  (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
                + operatorFieldApply (I := I) (M := M) g₀ 3 2 (Φ₁L s)
                  (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
                + operatorFieldApply (I := I) (M := M) g₀ 4 2 (Φ₂L s)
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  classical
  obtain ⟨σ'₀, hσ'₀⟩ :=
    exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) (T - T') 0
  obtain ⟨σ'₁, hσ'₁⟩ :=
    exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) (T - T') 1
  obtain ⟨σ'₂, hσ'₂⟩ :=
    exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) (T - T') 2
  refine ⟨fun s => symmAbsorbedCoeff (I := I) (M := M) g₀ 0 (Φ₀b s) σ'₀,
    fun s => symmAbsorbedCoeff (I := I) (M := M) g₀ 1
      (deTurckLieArm1Coeff (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) σ'₁,
    fun s => symmAbsorbedCoeff (I := I) (M := M) g₀ 2
      (deTurckLieArm2PrincipalCoeff (I := I) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) σ'₂,
    hjAbsorb 0 Φ₀b σ'₀ hj0,
    hjAbsorb 1 _ σ'₁ (deTurckLieArm1Coeff_realizedFam_jointSmooth (I := I) g₀ T T' hδ hδ' g_bg),
    hjAbsorb 2 _ σ'₂
      (deTurckLieArm2PrincipalCoeff_realizedFam_jointSmooth (I := I) g₀ T T' hδ hδ' g_bg),
    ?_⟩
  intro s hs x v
  have hcomp : ∀ i j : Fin (Module.finrank ℝ E),
      deriv (fun s : ℝ =>
        DeTurckCoefficients.chartLieDeTurckComp (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i j (extChartAt I x x)) s =
      unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2 (Φ₀b s)
            (iteratedCovGrad (I := I) g₀ 0 2 0 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))
          + operatorFieldApply (I := I) (M := M) g₀ 3 2
            (deTurckLieArm1Coeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
            (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))
          + operatorFieldApply (I := I) (M := M) g₀ 4 2
            (deTurckLieArm2PrincipalCoeff (I := I) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x
        ![(chartModelBasis E) i, (chartModelBasis E) j] := by
    intro i j
    rw [deriv_realizedFam_chartLieDeTurckComp_eq_chartSlope (I := I) g₀ T T'
      hδ_lt hδ hδ'_lt hδ' g_bg x i j hs]
    exact hcore s hs x i j
  set Wbase : SmoothCcTensor g₀ 0 2 :=
    operatorFieldApply (I := I) (M := M) g₀ 2 2 (Φ₀b s)
        (iteratedCovGrad (I := I) g₀ 0 2 0 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))
      + operatorFieldApply (I := I) (M := M) g₀ 3 2
        (deTurckLieArm1Coeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
        (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))
      + operatorFieldApply (I := I) (M := M) g₀ 4 2
        (deTurckLieArm2PrincipalCoeff (I := I) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
        (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) with hWbase
  have hexpand : (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) j *
        deriv (fun s : ℝ =>
          DeTurckCoefficients.chartLieDeTurckComp (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i j (extChartAt I x x)) s) =
      unitModel (I := I) (M := M) g₀ 2 Wbase x v := by
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
  rw [hexpand]
  have habs0 := symmAbsorbedCoeff_appCc_eq (I := I) (M := M) g₀ 0 (T - T') (Φ₀b s) σ'₀ hσ'₀ x v
  have habs1 := symmAbsorbedCoeff_appCc_eq (I := I) (M := M) g₀ 1 (T - T')
    (deTurckLieArm1Coeff (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) σ'₁ hσ'₁ x v
  have habs2 := symmAbsorbedCoeff_appCc_eq (I := I) (M := M) g₀ 2 (T - T')
    (deTurckLieArm2PrincipalCoeff (I := I) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) σ'₂ hσ'₂ x v
  rw [hWbase]
  rw [unitModel_add_local (I := I) g₀ 2 _ _ x, unitModel_add_local (I := I) g₀ 2 _ _ x,
    unitModel_add_local (I := I) g₀ 2 _ _ x, unitModel_add_local (I := I) g₀ 2 _ _ x,
    ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.add_apply,
    ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.add_apply]
  rw [habs0, habs1, habs2]

private lemma lieArm2_appCc_value_invGram
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (D : SmoothCcTensor g₀ 0 4)
    (x : M) (i j : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 4 2
          (deTurckLieArm2PrincipalCoeff (I := I) g₀ g₁ g_bg) D) x
        ![(chartModelBasis E) i, (chartModelBasis E) j] =
      ∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix g₁ x x k₁ l *
          (unitModel (I := I) (M := M) g₀ 4 D x
              ![(chartModelBasis E) i, (chartModelBasis E) l,
                (chartModelBasis E) j, (chartModelBasis E) k₁]
            + unitModel (I := I) (M := M) g₀ 4 D x
              ![(chartModelBasis E) j, (chartModelBasis E) l,
                (chartModelBasis E) i, (chartModelBasis E) k₁]
            - unitModel (I := I) (M := M) g₀ 4 D x
              ![(chartModelBasis E) i, (chartModelBasis E) j,
                (chartModelBasis E) l, (chartModelBasis E) k₁]) := by
  classical
  refine (deTurckLieArm2PrincipalCoeff_apply_eq (I := I) g₀ g₁ g_bg D x
    ![(chartModelBasis E) i, (chartModelBasis E) j]).trans ?_
  have hv0 : (![(chartModelBasis E) i, (chartModelBasis E) j] :
      Fin 2 → TangentSpace I x) 0 = (chartModelBasis E) i := rfl
  have hv1 : (![(chartModelBasis E) i, (chartModelBasis E) j] :
      Fin 2 → TangentSpace I x) 1 = (chartModelBasis E) j := rfl
  simp only [hv0, hv1]
  have hpack13 : ∀ (u w : TangentSpace I x) (c v : E),
      quadrilinearMapSlotBilinearAt (E := E) (unitModel (I := I) (M := M) g₀ 4 D x)
        1 3 (by decide) ![(show E from u), 0, (show E from w), 0] c v =
      unitModel (I := I) (M := M) g₀ 4 D x ![u, c, w, v] := by
    intro u w c v
    rw [unitModel4SlotBilin_apply]
    refine congrArg (fun t : Fin 4 → E => unitModel (I := I) (M := M) g₀ 4 D x t) ?_
    funext m
    fin_cases m <;> simp [Function.update]
  have hpack23 : ∀ (u w : TangentSpace I x) (c v : E),
      quadrilinearMapSlotBilinearAt (E := E) (unitModel (I := I) (M := M) g₀ 4 D x)
        2 3 (by decide) ![(show E from u), (show E from w), 0, 0] c v =
      unitModel (I := I) (M := M) g₀ 4 D x ![u, w, c, v] := by
    intro u w c v
    rw [unitModel4SlotBilin_apply]
    refine congrArg (fun t : Fin 4 → E => unitModel (I := I) (M := M) g₀ 4 D x t) ?_
    funext m
    fin_cases m <;> simp [Function.update]
  have hpat : ∀ (u w : TangentSpace I x),
      (∑ k : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 4 D x
          ![u, cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            w, (Module.finBasis ℝ E) k]) =
      ∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix g₁ x x k₁ l *
          unitModel (I := I) (M := M) g₀ 4 D x
            ![u, (chartModelBasis E) l, w, (chartModelBasis E) k₁] := by
    intro u w
    rw [show (∑ k : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 4 D x
          ![u, cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            w, (Module.finBasis ℝ E) k]) =
      ∑ k : Fin (Module.finrank ℝ E),
        quadrilinearMapSlotBilinearAt (E := E) (unitModel (I := I) (M := M) g₀ 4 D x)
          1 3 (by decide) ![(show E from u), 0, (show E from w), 0]
          (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          ((Module.finBasis ℝ E) k) from
      Finset.sum_congr rfl (fun k _ => (hpack13 u w _ _).symm)]
    rw [cometricFinBasisTrace_eq_chartInvGram_bilin (I := I) g₁ x _]
    refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ => ?_))
    rw [smul_eq_mul, hpack13 u w]
  have hpatH : (∑ k : Fin (Module.finrank ℝ E),
      unitModel (I := I) (M := M) g₀ 4 D x
        ![(chartModelBasis E) i, (chartModelBasis E) j,
          cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)),
          (Module.finBasis ℝ E) k]) =
      ∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix g₁ x x k₁ l *
          unitModel (I := I) (M := M) g₀ 4 D x
            ![(chartModelBasis E) i, (chartModelBasis E) j,
              (chartModelBasis E) l, (chartModelBasis E) k₁] := by
    rw [show (∑ k : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 4 D x
          ![(chartModelBasis E) i, (chartModelBasis E) j,
            cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
            (Module.finBasis ℝ E) k]) =
      ∑ k : Fin (Module.finrank ℝ E),
        quadrilinearMapSlotBilinearAt (E := E) (unitModel (I := I) (M := M) g₀ 4 D x)
          2 3 (by decide)
          ![(chartModelBasis E) i, (chartModelBasis E) j, 0, 0]
          (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          ((Module.finBasis ℝ E) k) from
      Finset.sum_congr rfl (fun k _ =>
        (hpack23 ((chartModelBasis E) i) ((chartModelBasis E) j) _ _).symm)]
    rw [cometricFinBasisTrace_eq_chartInvGram_bilin (I := I) g₁ x _]
    refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ => ?_))
    rw [smul_eq_mul, hpack23 ((chartModelBasis E) i) ((chartModelBasis E) j)]
  rw [hpat ((chartModelBasis E) i) ((chartModelBasis E) j),
    hpat ((chartModelBasis E) j) ((chartModelBasis E) i), hpatH]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k₁ _ => ?_)
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

open DifferentialGeometry.PDE.DeTurck.RicciLinearization (realizedGramDeriv)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (domDomCongrSection_unitModel unitModel_basisChart_eq_tensorChartComponentRaw tensorChartComponentRaw tensorChartComponentRaw_add tensorChartComponentRaw_smul arm2ReadoutCovDerivPair arm1ReadoutCovDeriv iteratedCovGrad2_chartComponent_readout iteratedCovGrad1_chartComponent_readout partialDeriv2_realizedGramDeriv_eq_half_sum_euclidPartial2 partialDeriv_realizedGramDeriv_eq_half_sum_euclidPartial realizedGramDeriv_eventuallyEq_symm_scalarOnE_raw euclidPartial_swap_chartPushedRaw_tensorChartComponentRaw covDerivLowerOrderTerm02_center_eq covDerivLowerOrderTerm03_center_eq euclidPartial2_chartPushedRaw_eq_partialDeriv2_scalarOnE partialDeriv_scalarOnE_eq_euclidPartial_local toEuclidean_extChartAt_mem_chartTargetEuclid symm_toEuclidean_symm_toEuclidean_extChartAt)
open DifferentialGeometry.Analysis.Sobolev.Chart (chartPushedRaw chartPushedRaw_apply_of_mem chartTargetEuclid chartTargetEuclid_isOpen)
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity (tensorChartComponentRaw_eq_chartFrame chartFrameBasisModel covDerivLowerOrderTerm euclidPartial euclidPartial_def covDerivComponent_lowerOrder_contDiffOn euclidPartial_chartPushedRaw_contDiffOn chartPushedRaw_tensorChartComponentRaw_contDiffOn)
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization (chartDeTurckCorrPrincipalSymbolExprRaw chartDeTurckCorrHessBlockRaw)
open DifferentialGeometry.Integral.DivergenceTheorem (partialDeriv chartGramOnE chartInvGramOnE)
open DifferentialGeometry.Integral.Measure (chartGramMatrix)

private lemma lieArm_frame0_eq_unitTensor (x b : M) :
    chartFrameBasisModel (I := I) (M := M) x b 0 ![] = unitTensor (I := I) (M := M) b := by
  apply ContinuousMultilinearMap.ext
  intro v
  rfl

private lemma lieArm_rawComponent_eq_unitModel_frame
    (g : SmoothRiemannianMetric I M) (s : ℕ) (W : SmoothCcTensor g 0 s) (x : M)
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ (chartAt H x).source) :
    tensorChartComponentRaw (I := I) (M := M) g 0 s W x ![] Jdx b =
      unitModel (I := I) (M := M) g s W b
        (fun j => (show E from chartBasisVecFiber (I := I) x (Jdx j) b)) := by
  rw [tensorChartComponentRaw_eq_chartFrame (I := I) (M := M) g 0 s W x hb ![] Jdx]
  rw [lieArm_frame0_eq_unitTensor (I := I) (M := M) x b]
  rfl

private lemma lieArm_euclidPartial_add_local
    (l : Fin (Module.finrank ℝ E))
    {f h : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ}
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hf : DifferentiableAt ℝ f y) (hh : DifferentiableAt ℝ h y) :
    euclidPartial (E := E) l (fun z => f z + h z) y =
      euclidPartial (E := E) l f y + euclidPartial (E := E) l h y := by
  rw [euclidPartial_def, euclidPartial_def, euclidPartial_def, fderiv_fun_add hf hh,
    ContinuousLinearMap.add_apply]

private lemma lieArm_covDerivLowerOrderTerm_differentiableAt_center
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g₀ r s) (x : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    DifferentiableAt ℝ
      (covDerivLowerOrderTerm (I := I) (M := M) g₀ r s S x m Idx Jdx)
      (toEuclidean (E := E) (extChartAt I x x)) := by
  have hmem : (toEuclidean (E := E)) (extChartAt I x x) ∈
      chartTargetEuclid (I := I) (M := M) x :=
    toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) x (mem_chart_source H x)
  have hcd : ContDiffOn ℝ ∞
      (covDerivLowerOrderTerm (I := I) (M := M) g₀ r s S x m Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) x) :=
    covDerivComponent_lowerOrder_contDiffOn (I := I) (M := M) g₀ r s S x m Idx Jdx
      (fun Idx' Jdx' => chartPushedRaw_tensorChartComponentRaw_contDiffOn
        (I := I) (M := M) g₀ r s S x Idx' Jdx')
  exact (hcd.contDiffAt
    ((DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) x).mem_nhds hmem)).differentiableAt (by simp)

private lemma lieArm_euclidPartial_chartPushedRaw_differentiableAt_center
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g₀ r s) (x : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    DifferentiableAt ℝ
      (euclidPartial (E := E) k
        (chartPushedRaw I x
          (tensorChartComponentRaw (I := I) (M := M) g₀ r s S x Idx Jdx)))
      (toEuclidean (E := E) (extChartAt I x x)) := by
  have hmem : (toEuclidean (E := E)) (extChartAt I x x) ∈
      chartTargetEuclid (I := I) (M := M) x :=
    toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) x (mem_chart_source H x)
  have hcd : ContDiffOn ℝ ∞
      (euclidPartial (E := E) k
        (chartPushedRaw I x
          (tensorChartComponentRaw (I := I) (M := M) g₀ r s S x Idx Jdx)))
      (chartTargetEuclid (I := I) (M := M) x) :=
    euclidPartial_chartPushedRaw_contDiffOn (I := I) (M := M) g₀ r s S x k Idx Jdx
  exact (hcd.contDiffAt
    ((DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) x).mem_nhds hmem)).differentiableAt (by simp)

private lemma lieArm_unitModel4_basisChart_readout_split
    (g₀ : SmoothRiemannianMetric I M) (h : SmoothCcTensor g₀ 0 2) (x : M)
    (a b c d : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 h) x
        ![chartModelBasis E a, chartModelBasis E b, chartModelBasis E c, chartModelBasis E d] =
      euclidPartial (E := E) a
          (fun y' => euclidPartial (E := E) b
            (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
              h x ![] ![c, d])) y')
          (toEuclidean (E := E) (extChartAt I x x))
        + arm2ReadoutCovDerivPair (I := I) (M := M) g₀ h x ![a, b, c, d] := by
  classical
  have hmemsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hroundtrip : (extChartAt I x).symm
      ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x))) = x :=
    symm_toEuclidean_symm_toEuclidean_extChartAt (I := I) (M := M) x hmemsrc
  rw [show (![chartModelBasis E a, chartModelBasis E b, chartModelBasis E c,
        chartModelBasis E d] : Fin 4 → TangentSpace I x) =
      (fun j => chartModelBasis E ((![a, b, c, d] : Fin 4 → Fin (Module.finrank ℝ E)) j)) from by
    funext j; fin_cases j <;> rfl]
  rw [unitModel_basisChart_eq_tensorChartComponentRaw (I := I) (M := M) g₀ (2 + 2)
    (iteratedCovGrad (I := I) g₀ 0 2 2 h) x (![a, b, c, d])]
  rw [show tensorChartComponentRaw (I := I) (M := M) g₀ 0 (2 + 2)
        (iteratedCovGrad (I := I) g₀ 0 2 2 h) x ![] (![a, b, c, d]) x =
      tensorChartComponentRaw (I := I) (M := M) g₀ 0 (2 + 2)
        (iteratedCovGrad (I := I) g₀ 0 2 2 h) x ![] (![a, b, c, d])
        ((extChartAt I x).symm
          ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x)))) from by
    rw [hroundtrip] ]
  rw [iteratedCovGrad2_chartComponent_readout (I := I) g₀ h x (![a, b, c, d])]
  have hJ0 : (![a, b, c, d] : Fin (2 + 2) → Fin (Module.finrank ℝ E)) 0 = a := rfl
  have hJ1 : (Matrix.vecTail (![a, b, c, d] : Fin (2 + 2) → Fin (Module.finrank ℝ E))) 0 = b := rfl
  have hJtail2 : Matrix.vecTail (Matrix.vecTail
      (![a, b, c, d] : Fin (2 + 2) → Fin (Module.finrank ℝ E))) = ![c, d] := by
    funext j; fin_cases j <;> rfl
  simp only [arm2ReadoutCovDerivPair, hJ0, hJ1, hJtail2]
  have hPdiff : DifferentiableAt ℝ
      (euclidPartial (E := E) b
        (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![c, d])))
      (toEuclidean (E := E) (extChartAt I x x)) :=
    lieArm_euclidPartial_chartPushedRaw_differentiableAt_center (I := I) (M := M) g₀ 0 2 h x b ![] ![c, d]
  have hQdiff : DifferentiableAt ℝ
      (covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 2 h x b ![] ![c, d])
      (toEuclidean (E := E) (extChartAt I x x)) :=
    lieArm_covDerivLowerOrderTerm_differentiableAt_center (I := I) (M := M) g₀ 0 2 h x b ![] ![c, d]
  rw [lieArm_euclidPartial_add_local a hPdiff hQdiff]
  ring

private lemma lieArm_unitModel3_basisChart_readout_split
    (g₀ : SmoothRiemannianMetric I M) (h : SmoothCcTensor g₀ 0 2) (x : M)
    (a b c : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 h) x
        ![chartModelBasis E a, chartModelBasis E b, chartModelBasis E c] =
      euclidPartial (E := E) a
          (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
            h x ![] ![b, c]))
          (toEuclidean (E := E) (extChartAt I x x))
        + arm1ReadoutCovDeriv (I := I) (M := M) g₀ h x ![a, b, c] := by
  classical
  have hmemsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hroundtrip : (extChartAt I x).symm
      ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x))) = x :=
    symm_toEuclidean_symm_toEuclidean_extChartAt (I := I) (M := M) x hmemsrc
  rw [show (![chartModelBasis E a, chartModelBasis E b, chartModelBasis E c] :
        Fin 3 → TangentSpace I x) =
      (fun j => chartModelBasis E ((![a, b, c] : Fin 3 → Fin (Module.finrank ℝ E)) j)) from by
    funext j; fin_cases j <;> rfl]
  rw [unitModel_basisChart_eq_tensorChartComponentRaw (I := I) (M := M) g₀ (2 + 1)
    (iteratedCovGrad (I := I) g₀ 0 2 1 h) x (![a, b, c])]
  rw [show tensorChartComponentRaw (I := I) (M := M) g₀ 0 (2 + 1)
        (iteratedCovGrad (I := I) g₀ 0 2 1 h) x ![] (![a, b, c]) x =
      tensorChartComponentRaw (I := I) (M := M) g₀ 0 (2 + 1)
        (iteratedCovGrad (I := I) g₀ 0 2 1 h) x ![] (![a, b, c])
        ((extChartAt I x).symm
          ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x)))) from by
    rw [hroundtrip] ]
  rw [iteratedCovGrad1_chartComponent_readout (I := I) g₀ h x (![a, b, c])]
  have hJ0 : (![a, b, c] : Fin (2 + 1) → Fin (Module.finrank ℝ E)) 0 = a := rfl
  have hJtail : Matrix.vecTail (![a, b, c] : Fin (2 + 1) → Fin (Module.finrank ℝ E)) = ![b, c] := by
    funext j; fin_cases j <;> rfl
  simp only [arm1ReadoutCovDeriv, hJ0, hJtail]

private lemma lieArm_symmS_rawComponent
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2) (x : M)
    (c d : Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ (chartAt H x).source) :
    tensorChartComponentRaw (I := I) (M := M) g 0 2
        (ccTensor02Symm (I := I) (M := M) g S) x ![] ![c, d] b =
      (1 / 2 : ℝ) *
        (tensorChartComponentRaw (I := I) (M := M) g 0 2 S x ![] ![c, d] b +
          tensorChartComponentRaw (I := I) (M := M) g 0 2 S x ![] ![d, c] b) := by
  classical
  have hswap : tensorChartComponentRaw (I := I) (M := M) g 0 2
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) S) x ![] ![c, d] b =
      tensorChartComponentRaw (I := I) (M := M) g 0 2 S x ![] ![d, c] b := by
    rw [lieArm_rawComponent_eq_unitModel_frame (I := I) (M := M) g 2 _ x ![c, d] hb,
      lieArm_rawComponent_eq_unitModel_frame (I := I) (M := M) g 2 S x ![d, c] hb]
    rw [domDomCongrSection_unitModel (I := I) (M := M) g (Equiv.swap (0 : Fin 2) 1) S b]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    refine congrArg (fun t : Fin 2 → E => unitModel (I := I) (M := M) g 2 S b t) ?_
    funext j
    fin_cases j <;> rfl
  rw [show ccTensor02Symm (I := I) (M := M) g S =
      (1 / 2 : ℝ) • (S + domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) S) from rfl]
  rw [tensorChartComponentRaw_smul, tensorChartComponentRaw_add, hswap]
  rw [smul_eq_mul]

private lemma lieArm_scalarOnE_symmS_eventuallyEq_realizedGramDeriv
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (c d : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE (I := I) x
        (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
          (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![] ![c, d]) =ᶠ[𝓝 (extChartAt I x x)]
      realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c d := by
  classical
  have hev := realizedGramDeriv_eventuallyEq_symm_scalarOnE_raw (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' x c d
  have hx_src : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source (I := I)]; exact mem_chart_source H x
  have htarget : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hx_src
  have htarget_open : IsOpen ((extChartAt I x).target : Set E) :=
    isOpen_extChartAt_target (I := I) x
  filter_upwards [htarget_open.mem_nhds htarget, hev] with y hy_tgt hev_y
  rw [hev_y]
  have hb : (extChartAt I x).symm y ∈ (chartAt H x).source := by
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I x).map_target hy_tgt
  rw [DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_def]
  rw [lieArm_symmS_rawComponent (I := I) (M := M) g₀ (T - T') x c d hb]
  rw [DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_def,
    DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_def]

private lemma lieArm_partialDeriv_symmS_scalar_eventuallyEq
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (m c d : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m
        (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE (I := I) x
          (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
            (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![] ![c, d])) =ᶠ[𝓝 (extChartAt I x x)]
      DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m
        (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c d) := by
  have hev := (lieArm_scalarOnE_symmS_eventuallyEq_realizedGramDeriv (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' x c d).eventuallyEq_nhds
  filter_upwards [hev] with y hy
  unfold DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
  rw [hy.fderiv_eq]

private lemma lieArm_U4_readout
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (a b c d : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 4
        (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
        ![chartModelBasis E a, chartModelBasis E b, chartModelBasis E c, chartModelBasis E d] =
      DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) a
          (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) b
            (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c d))
          (extChartAt I x x)
        + arm2ReadoutCovDerivPair (I := I) (M := M) g₀
            (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![a, b, c, d] := by
  classical
  rw [lieArm_unitModel4_basisChart_readout_split (I := I) (M := M) g₀
    (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x a b c d]
  refine congrArg (fun t : ℝ =>
    t + arm2ReadoutCovDerivPair (I := I) (M := M) g₀
      (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![a, b, c, d]) ?_
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.euclidPartial2_chartPushedRaw_eq_partialDeriv2_scalarOnE (I := I) (M := M) g₀
    (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x b a c d]
  have hev1 := lieArm_partialDeriv_symmS_scalar_eventuallyEq (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' x b c d
  change fderiv ℝ
      (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) b
        (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE (I := I) x
          (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
            (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![] ![c, d])))
      (extChartAt I x x) ((chartModelBasis E) a) = fderiv ℝ
      (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) b
        (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c d))
      (extChartAt I x x) ((chartModelBasis E) a)
  rw [hev1.fderiv_eq]

private lemma lieArm_U3_readout
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (a b c : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 3
        (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
        ![chartModelBasis E a, chartModelBasis E b, chartModelBasis E c] =
      DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) a
          (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x b c)
          (extChartAt I x x)
        + arm1ReadoutCovDeriv (I := I) (M := M) g₀
            (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![a, b, c] := by
  classical
  rw [lieArm_unitModel3_basisChart_readout_split (I := I) (M := M) g₀
    (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x a b c]
  refine congrArg (fun t : ℝ =>
    t + arm1ReadoutCovDeriv (I := I) (M := M) g₀
      (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![a, b, c]) ?_
  have hYmem : (toEuclidean (E := E)) (extChartAt I x x) ∈
      chartTargetEuclid (I := I) (M := M) x :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.toEuclidean_extChartAt_mem_chartTargetEuclid
      (I := I) (M := M) x (mem_chart_source H x)
  have hround : extChartAt I x ((extChartAt I x).symm
      ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x)))) =
      extChartAt I x x := by
    rw [(toEuclidean (E := E)).symm_apply_apply]
    have htarget : extChartAt I x x ∈ (extChartAt I x).target :=
      (extChartAt I x).map_source
        (by rw [extChartAt_source (I := I)]; exact mem_chart_source H x)
    rw [(extChartAt I x).right_inv htarget]
  have h := DifferentialGeometry.Analysis.Parabolic.TensorSpectral.partialDeriv_scalarOnE_eq_euclidPartial_local (I := I) (M := M)
    (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
      (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![] ![b, c]) x a hYmem
  rw [hround] at h
  rw [← h]
  have hev1 := lieArm_scalarOnE_symmS_eventuallyEq_realizedGramDeriv (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' x b c
  unfold DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
  rw [hev1.fderiv_eq]

private lemma lieArm_chartInvGramOnE_center (g : SmoothRiemannianMetric I M) (x : M)
    (a b : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramOnE (I := I) g x a b
        (extChartAt I x x) =
      chartInvGramMatrix (I := I) g x x a b := by
  rw [DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramOnE_def]
  have hx_src : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source (I := I)]; exact mem_chart_source H x
  rw [(extChartAt I x).left_inv hx_src]

private lemma lieArm_chartGramOnE_center (g : SmoothRiemannianMetric I M) (x : M)
    (a b : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I) g x a b
        (extChartAt I x x) =
      DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) g x x a b := by
  rw [DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE_def]
  have hx_src : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source (I := I)]; exact mem_chart_source H x
  rw [(extChartAt I x).left_inv hx_src]

private lemma lieArm_chartInvGramMatrix_symm (g : SmoothRiemannianMetric I M) (x : M)
    (a b : Fin (Module.finrank ℝ E)) :
    chartInvGramMatrix (I := I) g x x a b = chartInvGramMatrix (I := I) g x x b a := by
  have hherm : (DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) g x x)⁻¹.IsHermitian :=
    (DifferentialGeometry.Integral.Measure.chartGramMatrix_isHermitian (I := I) g x x).inv
  have h := congrFun (congrFun hherm a) b
  rw [Matrix.conjTranspose_apply, star_trivial] at h
  exact h.symm

private lemma lieArm_gram_invGram_collapse (g : SmoothRiemannianMetric I M) (x : M)
    (l j : Fin (Module.finrank ℝ E)) :
    (∑ k : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) g x x k j *
          chartInvGramMatrix (I := I) g x x k l) =
      if l = j then (1 : ℝ) else 0 := by
  classical
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact mem_chart_source H x
  have hmul := DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramMatrix_mul_chartGramMatrix (I := I) g x hx_base
  have h := congrFun (congrFun hmul l) j
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  rw [show (∑ k : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) g x x k j *
        chartInvGramMatrix (I := I) g x x k l) =
    ∑ k : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g x x l k *
        DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) g x x k j from
    Finset.sum_congr rfl (fun k _ => by
      rw [lieArm_chartInvGramMatrix_symm (I := I) g x k l]; ring)]
  rw [h]

private lemma lieArm_partialDeriv2_realizedGramDeriv_swap
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (m₁ m₂ a b : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m₂
        (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m₁
          (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b))
        (extChartAt I x x) =
      DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m₁
        (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m₂
          (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b))
        (extChartAt I x x) := by
  rw [partialDeriv2_realizedGramDeriv_eq_half_sum_euclidPartial2 (I := I) g₀ T T'
      hδ_lt hδ hδ'_lt hδ' x m₁ m₂ a b,
    partialDeriv2_realizedGramDeriv_eq_half_sum_euclidPartial2 (I := I) g₀ T T'
      hδ_lt hδ hδ'_lt hδ' x m₂ m₁ a b]
  rw [euclidPartial_swap_chartPushedRaw_tensorChartComponentRaw (I := I) g₀ (T - T') x m₂ m₁ a b, euclidPartial_swap_chartPushedRaw_tensorChartComponentRaw (I := I) g₀ (T - T') x m₂ m₁ b a]

open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization (chartDeTurckCorrPrincipalSymbolExprRaw chartDeTurckCorrHessBlockRaw)
open DifferentialGeometry.Integral.DivergenceTheorem (partialDeriv chartGramOnE chartInvGramOnE)
open DifferentialGeometry.Integral.Measure (chartGramMatrix)

private lemma lieArm_P2_halfCollapse
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) (d e : Fin (Module.finrank ℝ E)) :
    (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g₁ x k e (extChartAt I x x) *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₁ x a b (extChartAt I x x) *
              chartDeTurckCorrHessBlockRaw (I := I) g₁ g_bg x
                (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) d a b k
                (extChartAt I x x)) =
      ∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ l *
          (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) d
              (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) l
                (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x e k₁))
              (extChartAt I x x)
            - (1 / 2 : ℝ) *
              DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) d
                (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) e
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l k₁))
                (extChartAt I x x)) := by
  classical
  set pd2 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun d' a' l' b' =>
    DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) d'
      (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) a'
        (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l' b'))
      (extChartAt I x x) with hpd2
  set CIM : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun a b =>
    chartInvGramMatrix (I := I) g₁ x x a b with hCIM
  set CGM : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun a b =>
    DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) g₁ x x a b with hCGM
  have hHB : ∀ k a b : Fin (Module.finrank ℝ E),
      chartDeTurckCorrHessBlockRaw (I := I) g₁ g_bg x
          (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) d a b k
          (extChartAt I x x) =
        (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          CIM k l * (pd2 d a l b + pd2 d b l a - pd2 d l a b) := by
    intro k a b
    rw [chartDeTurckCorrHessBlockRaw]
    refine congrArg (fun t : ℝ => (1 / 2 : ℝ) * t) ?_
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [lieArm_chartInvGramOnE_center (I := I) g₁ x k l]
  have hstep1 : (∑ k : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g₁ x k e (extChartAt I x x) *
        ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g₁ x a b (extChartAt I x x) *
            chartDeTurckCorrHessBlockRaw (I := I) g₁ g_bg x
              (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) d a b k
              (extChartAt I x x)) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        CIM a b * ((1 / 2 : ℝ) *
          ((∑ k : Fin (Module.finrank ℝ E), CGM k e * CIM k l) *
            (pd2 d a l b + pd2 d b l a - pd2 d l a b))) := by
    rw [show (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g₁ x k e (extChartAt I x x) *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₁ x a b (extChartAt I x x) *
              chartDeTurckCorrHessBlockRaw (I := I) g₁ g_bg x
                (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) d a b k
                (extChartAt I x x)) =
      ∑ k : Fin (Module.finrank ℝ E),
        CGM k e * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          CIM a b * ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
            CIM k l * (pd2 d a l b + pd2 d b l a - pd2 d l a b)) from by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [lieArm_chartGramOnE_center (I := I) g₁ x k e]
      refine congrArg (fun t : ℝ => CGM k e * t) ?_
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      rw [lieArm_chartInvGramOnE_center (I := I) g₁ x a b, hHB k a b]]
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k _ => ?_))
    ring
  rw [hstep1]
  have hstep2 : ∀ a b : Fin (Module.finrank ℝ E),
      (∑ l : Fin (Module.finrank ℝ E),
        CIM a b * ((1 / 2 : ℝ) *
          ((∑ k : Fin (Module.finrank ℝ E), CGM k e * CIM k l) *
            (pd2 d a l b + pd2 d b l a - pd2 d l a b)))) =
      CIM a b * ((1 / 2 : ℝ) * (pd2 d a e b + pd2 d b e a - pd2 d e a b)) := by
    intro a b
    rw [Finset.sum_congr rfl (fun l _ => by
        rw [lieArm_gram_invGram_collapse (I := I) g₁ x l e] :
      ∀ l ∈ Finset.univ,
        CIM a b * ((1 / 2 : ℝ) *
          ((∑ k : Fin (Module.finrank ℝ E), CGM k e * CIM k l) *
            (pd2 d a l b + pd2 d b l a - pd2 d l a b))) =
        CIM a b * ((1 / 2 : ℝ) *
          ((if l = e then (1 : ℝ) else 0) *
            (pd2 d a l b + pd2 d b l a - pd2 d l a b))))]
    rw [Finset.sum_eq_single e]
    · rw [if_pos rfl, one_mul]
    · intro l _ hl
      rw [if_neg hl, zero_mul, mul_zero, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ e) h
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hstep2 a b))]
  have hterm1 : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      CIM a b * ((1 / 2 : ℝ) * pd2 d a e b)) =
      ∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        CIM k₁ l * ((1 / 2 : ℝ) * pd2 d l e k₁) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ => ?_))
    rw [show CIM l k₁ = CIM k₁ l from lieArm_chartInvGramMatrix_symm (I := I) g₁ x l k₁]
  have hterm3 : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      CIM a b * ((1 / 2 : ℝ) * pd2 d e a b)) =
      ∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        CIM k₁ l * ((1 / 2 : ℝ) * pd2 d e l k₁) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ => ?_))
    rw [show CIM l k₁ = CIM k₁ l from lieArm_chartInvGramMatrix_symm (I := I) g₁ x l k₁]
  have hsplit : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      CIM a b * ((1 / 2 : ℝ) * (pd2 d a e b + pd2 d b e a - pd2 d e a b))) =
      (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        CIM a b * ((1 / 2 : ℝ) * pd2 d a e b))
      + (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        CIM a b * ((1 / 2 : ℝ) * pd2 d b e a))
      - (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        CIM a b * ((1 / 2 : ℝ) * pd2 d e a b)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  rw [hsplit, hterm1, hterm3]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k₁ _ => ?_)
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (deTurckLieArm2PrincipalCoeff deTurckLieArm2PrincipalCoeff_apply_eq cometricFinBasisTrace_eq_chartInvGram_bilin quadrilinearMapSlotBilinearAt unitModel4SlotBilin_apply)

private lemma lieArm_arm2_value_eq_principal_add_tail
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) (i j : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 4 2
          (deTurckLieArm2PrincipalCoeff (I := I) g₀ g₁ g_bg)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x
        ![(chartModelBasis E) i, (chartModelBasis E) j] =
      chartDeTurckCorrPrincipalSymbolExprRaw (I := I) g₁ g_bg x
          (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) i j (extChartAt I x x)
        + ∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g₁ x x k₁ l *
              (arm2ReadoutCovDerivPair (I := I) (M := M) g₀
                  (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![i, l, j, k₁]
                + arm2ReadoutCovDerivPair (I := I) (M := M) g₀
                  (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![j, l, i, k₁]
                - arm2ReadoutCovDerivPair (I := I) (M := M) g₀
                  (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![i, j, l, k₁]) := by
  classical
  set pd2 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun d' a' l' b' =>
    DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) d'
      (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) a'
        (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l' b'))
      (extChartAt I x x) with hpd2
  set R4 : (Fin 4 → Fin (Module.finrank ℝ E)) → ℝ := fun Jdx =>
    arm2ReadoutCovDerivPair (I := I) (M := M) g₀
      (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x Jdx with hR4
  set CIM : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun a b =>
    chartInvGramMatrix (I := I) g₁ x x a b with hCIM
  rw [lieArm2_appCc_value_invGram (I := I) g₀ g₁ g_bg
    (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x i j]
  have hU4 : ∀ a b c d : Fin (Module.finrank ℝ E),
      unitModel (I := I) (M := M) g₀ 4
          (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
          ![chartModelBasis E a, chartModelBasis E b, chartModelBasis E c, chartModelBasis E d] =
        pd2 a b c d + R4 ![a, b, c, d] := fun a b c d =>
    lieArm_U4_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b c d
  rw [Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ => by
      rw [hU4 i l j k₁, hU4 j l i k₁, hU4 i j l k₁] :
    ∀ l ∈ Finset.univ,
      chartInvGramMatrix (I := I) g₁ x x k₁ l *
        (unitModel (I := I) (M := M) g₀ 4
            (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
            ![chartModelBasis E i, chartModelBasis E l, chartModelBasis E j, chartModelBasis E k₁]
          + unitModel (I := I) (M := M) g₀ 4
            (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
            ![chartModelBasis E j, chartModelBasis E l, chartModelBasis E i, chartModelBasis E k₁]
          - unitModel (I := I) (M := M) g₀ 4
            (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
            ![chartModelBasis E i, chartModelBasis E j, chartModelBasis E l, chartModelBasis E k₁]) =
      CIM k₁ l *
        ((pd2 i l j k₁ + R4 ![i, l, j, k₁])
          + (pd2 j l i k₁ + R4 ![j, l, i, k₁])
          - (pd2 i j l k₁ + R4 ![i, j, l, k₁]))))]
  have hsplit : (∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
      CIM k₁ l *
        ((pd2 i l j k₁ + R4 ![i, l, j, k₁])
          + (pd2 j l i k₁ + R4 ![j, l, i, k₁])
          - (pd2 i j l k₁ + R4 ![i, j, l, k₁]))) =
      (∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        CIM k₁ l * (pd2 i l j k₁ + pd2 j l i k₁ - pd2 i j l k₁))
      + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        CIM k₁ l * (R4 ![i, l, j, k₁] + R4 ![j, l, i, k₁] - R4 ![i, j, l, k₁])) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k₁ _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  rw [hsplit]
  refine congrArg (fun t : ℝ => t + _) ?_
  rw [show chartDeTurckCorrPrincipalSymbolExprRaw (I := I) g₁ g_bg x
      (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) i j (extChartAt I x x) =
    (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g₁ x k j (extChartAt I x x) *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₁ x a b (extChartAt I x x) *
              chartDeTurckCorrHessBlockRaw (I := I) g₁ g_bg x
                (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) i a b k
                (extChartAt I x x)) +
    (∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g₁ x i k (extChartAt I x x) *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₁ x a b (extChartAt I x x) *
              chartDeTurckCorrHessBlockRaw (I := I) g₁ g_bg x
                (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) j a b k
                (extChartAt I x x)) from rfl]
  rw [Finset.sum_congr rfl (fun k _ => by
      rw [DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE_symm (I := I) g₁ x i k
        (extChartAt I x x)] :
    ∀ k ∈ Finset.univ,
      chartGramOnE (I := I) g₁ x i k (extChartAt I x x) *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₁ x a b (extChartAt I x x) *
              chartDeTurckCorrHessBlockRaw (I := I) g₁ g_bg x
                (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) j a b k
                (extChartAt I x x) =
      chartGramOnE (I := I) g₁ x k i (extChartAt I x x) *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₁ x a b (extChartAt I x x) *
              chartDeTurckCorrHessBlockRaw (I := I) g₁ g_bg x
                (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) j a b k
                (extChartAt I x x))]
  rw [lieArm_P2_halfCollapse (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' g₁ g_bg x i j,
    lieArm_P2_halfCollapse (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' g₁ g_bg x j i]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k₁ _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  simp only [hpd2]
  rw [lieArm_partialDeriv2_realizedGramDeriv_swap (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' x i j l k₁]
  ring

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private def lieArm_slot34Eval (F : E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (u w : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun c => LinearMap.toContinuousLinearMap
        { toFun := fun v => F c v u w
          map_add' := fun v₁ v₂ => by simp
          map_smul' := fun r v => by simp }
      map_add' := fun c₁ c₂ => by
        ext v
        simp
      map_smul' := fun r c => by
        ext v
        simp }

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private lemma lieArm_slot34Eval_apply (F : E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (u w c v : E) :
    lieArm_slot34Eval (E := E) F u w c v = F c v u w := rfl

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private lemma lieArm_cometric_doubleTrace_eq_invGram
    (g₁ : SmoothRiemannianMetric I M) (x : M)
    (F : E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :
    (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        F (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis l)))
          ((Module.finBasis ℝ E) l)
          (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          ((Module.finBasis ℝ E) k)) =
      ∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g₁ x x k₁ p *
            (chartInvGramMatrix (I := I) g₁ x x l₁ m *
              F (chartModelBasis E m) (chartModelBasis E l₁)
                (chartModelBasis E p) (chartModelBasis E k₁)) := by
  classical
  have hinner : ∀ c v : E,
      (∑ l : Fin (Module.finrank ℝ E),
        F (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis l)))
          ((Module.finBasis ℝ E) l) c v) =
      (∑ l : Fin (Module.finrank ℝ E),
        (F (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis l)))
          ((Module.finBasis ℝ E) l) : E →L[ℝ] E →L[ℝ] ℝ)) c v := by
    intro c v
    rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
  rw [show (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
      F (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis l)))
        ((Module.finBasis ℝ E) l)
        (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        ((Module.finBasis ℝ E) k)) =
    ∑ k : Fin (Module.finrank ℝ E),
      (∑ l : Fin (Module.finrank ℝ E),
        (F (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis l)))
          ((Module.finBasis ℝ E) l) : E →L[ℝ] E →L[ℝ] ℝ))
        (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        ((Module.finBasis ℝ E) k) from
    Finset.sum_congr rfl (fun k _ => (hinner _ _))]
  rw [cometricFinBasisTrace_eq_chartInvGram_bilin (I := I) g₁ x _]
  refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ => ?_))
  rw [smul_eq_mul]
  rw [show (∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g₁ x x k₁ p *
        (chartInvGramMatrix (I := I) g₁ x x l₁ m *
          F (chartModelBasis E m) (chartModelBasis E l₁)
            (chartModelBasis E p) (chartModelBasis E k₁))) =
    chartInvGramMatrix (I := I) g₁ x x k₁ p *
      ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x l₁ m *
          F (chartModelBasis E m) (chartModelBasis E l₁)
            (chartModelBasis E p) (chartModelBasis E k₁) from by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l₁ _ => ?_)
    rw [Finset.mul_sum]]
  refine congrArg (fun t : ℝ => chartInvGramMatrix (I := I) g₁ x x k₁ p * t) ?_
  rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
  rw [show (∑ l : Fin (Module.finrank ℝ E),
      F (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis l)))
        ((Module.finBasis ℝ E) l) (chartModelBasis E p) (chartModelBasis E k₁)) =
    ∑ l : Fin (Module.finrank ℝ E),
      lieArm_slot34Eval (E := E) F (chartModelBasis E p) (chartModelBasis E k₁)
        (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis l)))
        ((Module.finBasis ℝ E) l) from
    Finset.sum_congr rfl (fun l _ => rfl)]
  rw [cometricFinBasisTrace_eq_chartInvGram_bilin (I := I) g₁ x _]
  refine Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => ?_))
  rw [smul_eq_mul]
  rfl

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (unitModel3SlotBilin metricConnDiffLoweredTrilin metricConnDiffLoweredTrilin_apply deTurckLieArm1Coeff deTurckLieArm1Coeff_apply_eq)

private lemma lieArm_unitModel3SlotBilin_apply
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (i j : Fin 3) (hij : i ≠ j) (base : Fin 3 → E) (c v : E) :
    unitModel3SlotBilin (E := E) f i j hij base c v =
      f (Function.update (Function.update base i c) j v) := rfl

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private def lieArm_F4mul (A B : E →L[ℝ] E →L[ℝ] ℝ) :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun c => LinearMap.toContinuousLinearMap
        { toFun := fun v => LinearMap.toContinuousLinearMap
            { toFun := fun c' => LinearMap.toContinuousLinearMap
                { toFun := fun v' => A c c' * B v v'
                  map_add' := fun v₁ v₂ => by
                    simp [map_add,
                      mul_add]
                  map_smul' := fun r v' => by
                    simp [map_smul,
                      smul_eq_mul]
                    ring }
              map_add' := fun c₁ c₂ => by
                ext v'
                simp [LinearMap.toContinuousLinearMap, map_add,
                  ContinuousLinearMap.add_apply, add_mul]
              map_smul' := fun r c' => by
                ext v'
                simp [LinearMap.toContinuousLinearMap, map_smul,
                  ContinuousLinearMap.smul_apply, smul_eq_mul]
                ring }
          map_add' := fun v₁ v₂ => by
            ext c' v'
            simp [LinearMap.toContinuousLinearMap, map_add,
              ContinuousLinearMap.add_apply, mul_add]
          map_smul' := fun r v => by
            ext c' v'
            simp [LinearMap.toContinuousLinearMap, map_smul,
              ContinuousLinearMap.smul_apply, smul_eq_mul]
            ring }
      map_add' := fun c₁ c₂ => by
        ext v c' v'
        simp [LinearMap.toContinuousLinearMap, map_add,
          ContinuousLinearMap.add_apply, add_mul]
      map_smul' := fun r c => by
        ext v c' v'
        simp [LinearMap.toContinuousLinearMap, map_smul,
          ContinuousLinearMap.smul_apply, smul_eq_mul]
        ring }

private lemma lieArm_F4mul_apply (A B : E →L[ℝ] E →L[ℝ] ℝ) (c v c' v' : E) :
    lieArm_F4mul (E := E) A B c v c' v' = A c c' * B v v' := rfl

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private def lieArm_fix3 (f : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (e : E) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun c => LinearMap.toContinuousLinearMap
        { toFun := fun v => f c v e
          map_add' := fun v₁ v₂ => by
            simp [map_add, ContinuousLinearMap.add_apply]
          map_smul' := fun r v => by
            simp [map_smul, ContinuousLinearMap.smul_apply] }
      map_add' := fun c₁ c₂ => by
        ext v
        simp [LinearMap.toContinuousLinearMap, map_add, ContinuousLinearMap.add_apply]
      map_smul' := fun r c => by
        ext v
        simp [LinearMap.toContinuousLinearMap, map_smul, ContinuousLinearMap.smul_apply] }

private lemma lieArm_fix3_apply (f : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (e c v : E) :
    lieArm_fix3 (E := E) f e c v = f c v e := rfl

private lemma lieArm_doubleTrace_slotBilin
    (g₁ : SmoothRiemannianMetric I M) (x : M)
    (W3 : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (i₁ i₂ : Fin 3) (h12 : i₁ ≠ i₂) (base : Fin 3 → E)
    (B : E →L[ℝ] E →L[ℝ] ℝ) :
    (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        unitModel3SlotBilin (E := E) W3 i₁ i₂ h12 base
            (cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis l)))
            (cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))) *
          B ((Module.finBasis ℝ E) l) ((Module.finBasis ℝ E) k)) =
      ∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g₁ x x k₁ p *
            (chartInvGramMatrix (I := I) g₁ x x l₁ m *
              (unitModel3SlotBilin (E := E) W3 i₁ i₂ h12 base
                  (chartModelBasis E m) (chartModelBasis E p) *
                B (chartModelBasis E l₁) (chartModelBasis E k₁))) := by
  classical
  have hbrick := lieArm_cometric_doubleTrace_eq_invGram (I := I) g₁ x
    (lieArm_F4mul (E := E) (unitModel3SlotBilin (E := E) W3 i₁ i₂ h12 base) B)
  rw [show (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
      unitModel3SlotBilin (E := E) W3 i₁ i₂ h12 base
          (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis l)))
          (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k))) *
        B ((Module.finBasis ℝ E) l) ((Module.finBasis ℝ E) k)) =
    ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
      lieArm_F4mul (E := E) (unitModel3SlotBilin (E := E) W3 i₁ i₂ h12 base) B
        (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis l)))
        ((Module.finBasis ℝ E) l)
        (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        ((Module.finBasis ℝ E) k) from
    Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))]
  · rw [hbrick]
    refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => ?_))))
    rw [lieArm_F4mul_apply]
  · rw [lieArm_F4mul_apply]

private lemma lieArm_slot12_pack
    (W3 : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ) (w c v : E) :
    unitModel3SlotBilin (E := E) W3 1 2 (by decide) ![w, 0, 0] c v = W3 ![w, c, v] := by
  rw [lieArm_unitModel3SlotBilin_apply]
  refine congrArg (fun t : Fin 3 → E => W3 t) ?_
  funext j
  fin_cases j <;> simp [Function.update]

private lemma lieArm_slot02_pack
    (W3 : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ) (w c v : E) :
    unitModel3SlotBilin (E := E) W3 0 2 (by decide) ![0, w, 0] c v = W3 ![c, w, v] := by
  rw [lieArm_unitModel3SlotBilin_apply]
  refine congrArg (fun t : Fin 3 → E => W3 t) ?_
  funext j
  fin_cases j <;> simp [Function.update]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private lemma lieArm_arm1_group_traced
    (g₀X g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (W3 : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (v0 v1 : E) :
    ((∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        W3 ![v0,
              cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis l)),
              cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀X x v1 ((Module.finBasis ℝ E) l))
            ((Module.finBasis ℝ E) k))
      - (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        W3 ![v0,
              cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis l)),
              cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g_bg x ((Module.finBasis ℝ E) l)
              ((Module.finBasis ℝ E) k)) v1)
      - W3 ![v0, v1,
          (show E from
            (PDE.DeTurck.deTurckVF (I := I) g₁ g₀X : Π y : M, TangentSpace I y) x)]
      - (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        W3 ![cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis l)),
              v1,
              cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 ((Module.finBasis ℝ E) k))
            ((Module.finBasis ℝ E) l))
      - (∑ k : Fin (Module.finrank ℝ E),
        W3 ![cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
              (show E from PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 v1),
              ((Module.finBasis ℝ E) k)])
      - (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        W3 ![cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis l)),
              v1,
              cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 ((Module.finBasis ℝ E) l))
            ((Module.finBasis ℝ E) k))) =
    ((∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (W3 ![v0, chartModelBasis E m, chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g₀X x v1 (chartModelBasis E l₁))
                (chartModelBasis E k₁))))
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (W3 ![v0, chartModelBasis E m, chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g_bg x (chartModelBasis E l₁)
                  (chartModelBasis E k₁)) v1)))
      - W3 ![v0, v1,
          (show E from
            (PDE.DeTurck.deTurckVF (I := I) g₁ g₀X : Π y : M, TangentSpace I y) x)]
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (W3 ![chartModelBasis E m, v1, chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 (chartModelBasis E k₁))
                (chartModelBasis E l₁))))
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          W3 ![chartModelBasis E p,
                (show E from PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 v1),
                chartModelBasis E k₁])
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (W3 ![chartModelBasis E m, v1, chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 (chartModelBasis E l₁))
                (chartModelBasis E k₁))))) := by
  classical
  have hT2 : (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        W3 ![v0,
              cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis l)),
              cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀X x v1 ((Module.finBasis ℝ E) l))
            ((Module.finBasis ℝ E) k)) =
      (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (W3 ![v0, chartModelBasis E m, chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g₀X x v1 (chartModelBasis E l₁))
                (chartModelBasis E k₁)))) := by
    have h := lieArm_doubleTrace_slotBilin (I := I) g₁ x W3 1 2 (by decide)
      ![v0, 0, 0] ((metricConnDiffLoweredTrilin (I := I) g₁ g₁ g₀X x) v1)
    refine Eq.trans ?_ (Eq.trans h ?_)
    · refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
      rw [lieArm_slot12_pack]
      rfl
    · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => ?_))))
      rw [lieArm_slot12_pack]
      rfl
  have hT3 : (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        W3 ![v0,
              cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis l)),
              cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g_bg x ((Module.finBasis ℝ E) l)
              ((Module.finBasis ℝ E) k)) v1) =
      (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (W3 ![v0, chartModelBasis E m, chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g_bg x (chartModelBasis E l₁)
                  (chartModelBasis E k₁)) v1))) := by
    have h := lieArm_doubleTrace_slotBilin (I := I) g₁ x W3 1 2 (by decide)
      ![v0, 0, 0] (lieArm_fix3 (E := E) (metricConnDiffLoweredTrilin (I := I) g₁ g₁ g_bg x) v1)
    refine Eq.trans ?_ (Eq.trans h ?_)
    · refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
      rw [lieArm_slot12_pack]
      rfl
    · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => ?_))))
      rw [lieArm_slot12_pack]
      rfl
  have hT5 : (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        W3 ![cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis l)),
              v1,
              cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 ((Module.finBasis ℝ E) k))
            ((Module.finBasis ℝ E) l)) =
      (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (W3 ![chartModelBasis E m, v1, chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 (chartModelBasis E k₁))
                (chartModelBasis E l₁)))) := by
    have h := lieArm_doubleTrace_slotBilin (I := I) g₁ x W3 0 2 (by decide)
      ![0, v1, 0] (((metricConnDiffLoweredTrilin (I := I) g₁ g₁ g₀X x) v0).flip)
    refine Eq.trans ?_ (Eq.trans h ?_)
    · refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
      rw [lieArm_slot02_pack]
      rfl
    · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => ?_))))
      rw [lieArm_slot02_pack]
      rfl
  have hT7 : (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        W3 ![cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis l)),
              v1,
              cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))] *
          g₁.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 ((Module.finBasis ℝ E) l))
            ((Module.finBasis ℝ E) k)) =
      (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (W3 ![chartModelBasis E m, v1, chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 (chartModelBasis E l₁))
                (chartModelBasis E k₁)))) := by
    have h := lieArm_doubleTrace_slotBilin (I := I) g₁ x W3 0 2 (by decide)
      ![0, v1, 0] ((metricConnDiffLoweredTrilin (I := I) g₁ g₁ g₀X x) v0)
    refine Eq.trans ?_ (Eq.trans h ?_)
    · refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
      rw [lieArm_slot02_pack]
      rfl
    · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => ?_))))
      rw [lieArm_slot02_pack]
      rfl
  have hT6 : (∑ k : Fin (Module.finrank ℝ E),
        W3 ![cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
              (show E from PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 v1),
              ((Module.finBasis ℝ E) k)]) =
      (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          W3 ![chartModelBasis E p,
                (show E from PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 v1),
                chartModelBasis E k₁]) := by
    have h := cometricFinBasisTrace_eq_chartInvGram_bilin (I := I) g₁ x
      (unitModel3SlotBilin (E := E) W3 0 2 (by decide)
        ![0, (show E from PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 v1), 0])
    refine Eq.trans ?_ (Eq.trans h ?_)
    · refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [lieArm_slot02_pack]
    · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ => ?_))
      rw [smul_eq_mul, lieArm_slot02_pack]
  rw [hT2, hT3, hT5, hT7, hT6]

private lemma lieArm_arm1_T14_traced
    (g₀X g₁ : SmoothRiemannianMetric I M) (x : M)
    (W3 : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (v0 v1 : E) :
    (∑ k : Fin (Module.finrank ℝ E),
        W3 ![(show E from PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 v1),
              cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)),
              ((Module.finBasis ℝ E) k)]) =
      (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          W3 ![(show E from PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 v1),
                chartModelBasis E p,
                chartModelBasis E k₁]) := by
  classical
  have h := cometricFinBasisTrace_eq_chartInvGram_bilin (I := I) g₁ x
    (unitModel3SlotBilin (E := E) W3 1 2 (by decide)
      ![(show E from PDE.DeTurck.connDiff (I := I) g₁ g₀X x v0 v1), 0, 0])
  refine Eq.trans ?_ (Eq.trans h ?_)
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [lieArm_slot12_pack]
  · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ => ?_))
    rw [smul_eq_mul, lieArm_slot12_pack]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private lemma lieArm_arm1_value_traced
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (D : SmoothCcTensor g₀ 0 3)
    (x : M) (i j : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 3 2
          (deTurckLieArm1Coeff (I := I) (M := M) g₀ g₁ g_bg) D) x
        ![chartModelBasis E i, chartModelBasis E j] =
      unitModel (I := I) (M := M) g₀ 3 D x
        ![(show E from
            (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg : Π y : M, TangentSpace I y) x),
          chartModelBasis E i, chartModelBasis E j]
      + ((∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3 D x ![(chartModelBasis E i), chartModelBasis E m, chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (chartModelBasis E j) (chartModelBasis E l₁))
                (chartModelBasis E k₁))))
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3 D x ![(chartModelBasis E i), chartModelBasis E m, chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g_bg x (chartModelBasis E l₁)
                  (chartModelBasis E k₁)) (chartModelBasis E j))))
      - unitModel (I := I) (M := M) g₀ 3 D x ![(chartModelBasis E i), (chartModelBasis E j),
          (show E from
            (PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π y : M, TangentSpace I y) x)]
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3 D x ![chartModelBasis E m, (chartModelBasis E j), chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (chartModelBasis E i) (chartModelBasis E k₁))
                (chartModelBasis E l₁))))
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          unitModel (I := I) (M := M) g₀ 3 D x ![chartModelBasis E p,
                (show E from PDE.DeTurck.connDiff (I := I) g₁ g₀ x (chartModelBasis E i) (chartModelBasis E j)),
                chartModelBasis E k₁])
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3 D x ![chartModelBasis E m, (chartModelBasis E j), chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (chartModelBasis E i) (chartModelBasis E l₁))
                (chartModelBasis E k₁)))))
      + ((∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3 D x ![(chartModelBasis E j), chartModelBasis E m, chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (chartModelBasis E i) (chartModelBasis E l₁))
                (chartModelBasis E k₁))))
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3 D x ![(chartModelBasis E j), chartModelBasis E m, chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g_bg x (chartModelBasis E l₁)
                  (chartModelBasis E k₁)) (chartModelBasis E i))))
      - unitModel (I := I) (M := M) g₀ 3 D x ![(chartModelBasis E j), (chartModelBasis E i),
          (show E from
            (PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π y : M, TangentSpace I y) x)]
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3 D x ![chartModelBasis E m, (chartModelBasis E i), chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (chartModelBasis E j) (chartModelBasis E k₁))
                (chartModelBasis E l₁))))
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          unitModel (I := I) (M := M) g₀ 3 D x ![chartModelBasis E p,
                (show E from PDE.DeTurck.connDiff (I := I) g₁ g₀ x (chartModelBasis E j) (chartModelBasis E i)),
                chartModelBasis E k₁])
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          (chartInvGramMatrix (I := I) g₁ x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3 D x ![chartModelBasis E m, (chartModelBasis E i), chartModelBasis E p] *
              g₁.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (chartModelBasis E j) (chartModelBasis E l₁))
                (chartModelBasis E k₁)))))
      + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ p *
          unitModel (I := I) (M := M) g₀ 3 D x ![(show E from PDE.DeTurck.connDiff (I := I) g₁ g₀ x (chartModelBasis E i) (chartModelBasis E j)),
                chartModelBasis E p,
                chartModelBasis E k₁]) := by
  classical
  refine (deTurckLieArm1Coeff_apply_eq (I := I) g₀ g₁ g_bg D x
    ![chartModelBasis E i, chartModelBasis E j]).trans ?_
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) rfl ?_) ?_) ?_
  · exact lieArm_arm1_group_traced (I := I) g₀ g₁ g_bg x
      (unitModel (I := I) (M := M) g₀ 3 D x) (chartModelBasis E i) (chartModelBasis E j)
  · exact lieArm_arm1_group_traced (I := I) g₀ g₁ g_bg x
      (unitModel (I := I) (M := M) g₀ 3 D x) (chartModelBasis E j) (chartModelBasis E i)
  · exact lieArm_arm1_T14_traced (I := I) g₀ g₁ x
      (unitModel (I := I) (M := M) g₀ 3 D x) (chartModelBasis E i) (chartModelBasis E j)

private lemma lieArm_inner_chartBasis_center (g : SmoothRiemannianMetric I M) (x : M)
    (p q : Fin (Module.finrank ℝ E)) :
    g.inner x ((chartModelBasis E) p : TangentSpace I x)
        ((chartModelBasis E) q : TangentSpace I x) =
      DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) g x x p q := by
  rw [DifferentialGeometry.Integral.Measure.chartGramMatrix_apply,
    DifferentialGeometry.Integral.Connection.chartBasisVecFiber_self (I := I) x p,
    DifferentialGeometry.Integral.Connection.chartBasisVecFiber_self (I := I) x q]

private lemma lieArm_connDiff_chartBasis_center
    (gA gB : SmoothRiemannianMetric I M) (x : M) (j k : Fin (Module.finrank ℝ E)) :
    PDE.DeTurck.connDiff (I := I) gA gB x
        ((chartModelBasis E) j : TangentSpace I x)
        ((chartModelBasis E) k : TangentSpace I x) =
      ∑ p : Fin (Module.finrank ℝ E),
        (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gA x k j p
            (extChartAt I x x) -
          DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gB x k j p
            (extChartAt I x x)) •
          ((chartModelBasis E) p : TangentSpace I x) := by
  rw [show ((chartModelBasis E) j : TangentSpace I x) =
      DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) x j x from
    (DifferentialGeometry.Integral.Connection.chartBasisVecFiber_self (I := I) x j).symm]
  rw [show ((chartModelBasis E) k : TangentSpace I x) =
      DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) x k x from
    (DifferentialGeometry.Integral.Connection.chartBasisVecFiber_self (I := I) x k).symm]
  rw [PDE.DeTurck.connDiff_chartBasis_pair_eq_sum (I := I) gA gB x
    (DifferentialGeometry.Integral.Connection.self_mem_chartLeviCivitaGoodSet (I := I) (α := x))
    j k]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [DifferentialGeometry.Integral.Connection.chartBasisVecFiber_self (I := I) x p]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private lemma lieArm_bilin_expand_fst (F : E →L[ℝ] E →L[ℝ] ℝ)
    (c : Fin (Module.finrank ℝ E) → ℝ) (w : Fin (Module.finrank ℝ E) → E) (v : E) :
    F (∑ q : Fin (Module.finrank ℝ E), c q • w q) v =
      ∑ q : Fin (Module.finrank ℝ E), c q * F (w q) v := by
  rw [map_sum, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private lemma lieArm_bilin_expand_snd (F : E →L[ℝ] E →L[ℝ] ℝ) (u : E)
    (c : Fin (Module.finrank ℝ E) → ℝ) (w : Fin (Module.finrank ℝ E) → E) :
    F u (∑ q : Fin (Module.finrank ℝ E), c q • w q) =
      ∑ q : Fin (Module.finrank ℝ E), c q * F u (w q) := by
  rw [map_sum]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [map_smul, smul_eq_mul]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private lemma lieArm_U3_sum_slot0
    (W3 : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (c : Fin (Module.finrank ℝ E) → ℝ) (u v : E) :
    W3 ![∑ q : Fin (Module.finrank ℝ E), c q • chartModelBasis E q, u, v] =
      ∑ q : Fin (Module.finrank ℝ E), c q * W3 ![chartModelBasis E q, u, v] := by
  refine ((lieArm_slot02_pack (E := E) W3 u
    (∑ q : Fin (Module.finrank ℝ E), c q • chartModelBasis E q) v).symm).trans ?_
  refine (lieArm_bilin_expand_fst (E := E)
    (unitModel3SlotBilin (E := E) W3 0 2 (by decide) ![0, u, 0]) c
    (fun q => chartModelBasis E q) v).trans ?_
  refine Finset.sum_congr rfl (fun q _ => ?_)
  exact congrArg (HMul.hMul (c q)) (lieArm_slot02_pack (E := E) W3 u (chartModelBasis E q) v)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private lemma lieArm_U3_sum_slot1
    (W3 : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (u : E) (c : Fin (Module.finrank ℝ E) → ℝ) (v : E) :
    W3 ![u, ∑ q : Fin (Module.finrank ℝ E), c q • chartModelBasis E q, v] =
      ∑ q : Fin (Module.finrank ℝ E), c q * W3 ![u, chartModelBasis E q, v] := by
  refine ((lieArm_slot12_pack (E := E) W3 u
    (∑ q : Fin (Module.finrank ℝ E), c q • chartModelBasis E q) v).symm).trans ?_
  refine (lieArm_bilin_expand_fst (E := E)
    (unitModel3SlotBilin (E := E) W3 1 2 (by decide) ![u, 0, 0]) c
    (fun q => chartModelBasis E q) v).trans ?_
  refine Finset.sum_congr rfl (fun q _ => ?_)
  exact congrArg (HMul.hMul (c q)) (lieArm_slot12_pack (E := E) W3 u (chartModelBasis E q) v)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private lemma lieArm_U3_sum_slot2
    (W3 : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (u v : E) (c : Fin (Module.finrank ℝ E) → ℝ) :
    W3 ![u, v, ∑ q : Fin (Module.finrank ℝ E), c q • chartModelBasis E q] =
      ∑ q : Fin (Module.finrank ℝ E), c q * W3 ![u, v, chartModelBasis E q] := by
  refine ((lieArm_slot12_pack (E := E) W3 u v
    (∑ q : Fin (Module.finrank ℝ E), c q • chartModelBasis E q)).symm).trans ?_
  refine (lieArm_bilin_expand_snd (E := E)
    (unitModel3SlotBilin (E := E) W3 1 2 (by decide) ![u, 0, 0]) v c
    (fun q => chartModelBasis E q)).trans ?_
  refine Finset.sum_congr rfl (fun q _ => ?_)
  exact congrArg (HMul.hMul (c q)) (lieArm_slot12_pack (E := E) W3 u v (chartModelBasis E q))

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private lemma lieArm_inner_connDiff_chartBasis_value
    (gm gA gB : SmoothRiemannianMetric I M) (x : M)
    (a c d : Fin (Module.finrank ℝ E)) :
    gm.inner x
        (PDE.DeTurck.connDiff (I := I) gA gB x (chartModelBasis E a) (chartModelBasis E c))
        (chartModelBasis E d) =
      ∑ q : Fin (Module.finrank ℝ E),
        (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gA x c a q
            (extChartAt I x x) -
          DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gB x c a q
            (extChartAt I x x)) *
          DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) gm x x q d := by
  refine (congrArg (fun t : TangentSpace I x => gm.inner x t (chartModelBasis E d))
    (lieArm_connDiff_chartBasis_center (I := I) gA gB x a c)).trans ?_
  refine (lieArm_bilin_expand_fst (E := E) (gm.inner x)
    (fun q => DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gA x c a q
        (extChartAt I x x) -
      DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gB x c a q
        (extChartAt I x x))
    (fun q => chartModelBasis E q) (chartModelBasis E d)).trans ?_
  refine Finset.sum_congr rfl (fun q _ => ?_)
  exact congrArg (HMul.hMul _) (lieArm_inner_chartBasis_center (I := I) gm x q d)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private lemma lieArm_U3_deTurckVF_slot0_value
    (W3 : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (gA gB : SmoothRiemannianMetric I M) (x : M) (u v : E) :
    W3 ![(show E from
        (PDE.DeTurck.deTurckVF (I := I) gA gB : Π y : M, TangentSpace I y) x), u, v] =
      ∑ w : Fin (Module.finrank ℝ E),
        PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) gA gB x w
            (extChartAt I x x) *
          W3 ![chartModelBasis E w, u, v] := by
  have hW : (show E from
      (PDE.DeTurck.deTurckVF (I := I) gA gB : Π y : M, TangentSpace I y) x) =
      ∑ w : Fin (Module.finrank ℝ E),
        PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) gA gB x w
            (extChartAt I x x) •
          chartModelBasis E w :=
    PDE.DeTurck.deTurckVF_apply_eq_chartDeTurckVFComp_sum_self (I := I) gA gB x
  refine (congrArg (fun t : E => W3 ![t, u, v]) hW).trans ?_
  exact lieArm_U3_sum_slot0 (E := E) W3
    (fun w => PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) gA gB x w
      (extChartAt I x x)) u v

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private lemma lieArm_U3_deTurckVF_slot2_value
    (W3 : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (gA gB : SmoothRiemannianMetric I M) (x : M) (u v : E) :
    W3 ![u, v, (show E from
        (PDE.DeTurck.deTurckVF (I := I) gA gB : Π y : M, TangentSpace I y) x)] =
      ∑ w : Fin (Module.finrank ℝ E),
        PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) gA gB x w
            (extChartAt I x x) *
          W3 ![u, v, chartModelBasis E w] := by
  have hW : (show E from
      (PDE.DeTurck.deTurckVF (I := I) gA gB : Π y : M, TangentSpace I y) x) =
      ∑ w : Fin (Module.finrank ℝ E),
        PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) gA gB x w
            (extChartAt I x x) •
          chartModelBasis E w :=
    PDE.DeTurck.deTurckVF_apply_eq_chartDeTurckVFComp_sum_self (I := I) gA gB x
  refine (congrArg (fun t : E => W3 ![u, v, t]) hW).trans ?_
  exact lieArm_U3_sum_slot2 (E := E) W3 u v
    (fun w => PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) gA gB x w
      (extChartAt I x x))

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private lemma lieArm_U3_connDiff_slot0_value
    (W3 : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (gA gB : SmoothRiemannianMetric I M) (x : M)
    (a c : Fin (Module.finrank ℝ E)) (u v : E) :
    W3 ![(show E from PDE.DeTurck.connDiff (I := I) gA gB x
        (chartModelBasis E a) (chartModelBasis E c)), u, v] =
      ∑ q : Fin (Module.finrank ℝ E),
        (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gA x c a q
            (extChartAt I x x) -
          DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gB x c a q
            (extChartAt I x x)) *
          W3 ![chartModelBasis E q, u, v] := by
  have hconn : (show E from PDE.DeTurck.connDiff (I := I) gA gB x
      (chartModelBasis E a) (chartModelBasis E c)) =
      ∑ q : Fin (Module.finrank ℝ E),
        (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gA x c a q
            (extChartAt I x x) -
          DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gB x c a q
            (extChartAt I x x)) •
          chartModelBasis E q :=
    lieArm_connDiff_chartBasis_center (I := I) gA gB x a c
  refine (congrArg (fun t : E => W3 ![t, u, v]) hconn).trans ?_
  exact lieArm_U3_sum_slot0 (E := E) W3
    (fun q => DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gA x c a q
        (extChartAt I x x) -
      DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gB x c a q
        (extChartAt I x x)) u v

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private lemma lieArm_U3_connDiff_slot1_value
    (W3 : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (gA gB : SmoothRiemannianMetric I M) (x : M)
    (a c : Fin (Module.finrank ℝ E)) (u v : E) :
    W3 ![u, (show E from PDE.DeTurck.connDiff (I := I) gA gB x
        (chartModelBasis E a) (chartModelBasis E c)), v] =
      ∑ q : Fin (Module.finrank ℝ E),
        (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gA x c a q
            (extChartAt I x x) -
          DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gB x c a q
            (extChartAt I x x)) *
          W3 ![u, chartModelBasis E q, v] := by
  have hconn : (show E from PDE.DeTurck.connDiff (I := I) gA gB x
      (chartModelBasis E a) (chartModelBasis E c)) =
      ∑ q : Fin (Module.finrank ℝ E),
        (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gA x c a q
            (extChartAt I x x) -
          DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gB x c a q
            (extChartAt I x x)) •
          chartModelBasis E q :=
    lieArm_connDiff_chartBasis_center (I := I) gA gB x a c
  refine (congrArg (fun t : E => W3 ![u, t, v]) hconn).trans ?_
  exact lieArm_U3_sum_slot1 (E := E) W3 u
    (fun q => DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gA x c a q
        (extChartAt I x x) -
      DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gB x c a q
        (extChartAt I x x)) v

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private lemma lieArm_arm1_value_realized
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (_hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (_hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (x : M) (i j : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 3 2
          (deTurckLieArm1Coeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
          (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x
        ![chartModelBasis E i, chartModelBasis E j] =
      (∑ w : Fin (Module.finrank ℝ E),
        PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x w (extChartAt I x x) *
          unitModel (I := I) (M := M) g₀ 3
            (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
            ![chartModelBasis E w, chartModelBasis E i, chartModelBasis E j])
      + ((∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3
                (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
                ![(chartModelBasis E i), chartModelBasis E m, chartModelBasis E p] *
              (∑ q : Fin (Module.finrank ℝ E),
                (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) -
                  DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    g₀ x l₁ j q (extChartAt I x x)) *
                  DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁))))
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3
                (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
                ![(chartModelBasis E i), chartModelBasis E m, chartModelBasis E p] *
              (∑ q : Fin (Module.finrank ℝ E),
                (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) -
                  DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    g_bg x k₁ l₁ q (extChartAt I x x)) *
                  DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q j))))
      - (∑ w : Fin (Module.finrank ℝ E),
        PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x w (extChartAt I x x) *
          unitModel (I := I) (M := M) g₀ 3
            (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
            ![chartModelBasis E i, chartModelBasis E j, chartModelBasis E w])
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3
                (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
                ![chartModelBasis E m, (chartModelBasis E j), chartModelBasis E p] *
              (∑ q : Fin (Module.finrank ℝ E),
                (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ i q (extChartAt I x x) -
                  DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    g₀ x k₁ i q (extChartAt I x x)) *
                  DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁))))
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (∑ q : Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) -
              DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                g₀ x j i q (extChartAt I x x)) *
              unitModel (I := I) (M := M) g₀ 3
                (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
                ![chartModelBasis E p, chartModelBasis E q, chartModelBasis E k₁]))
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3
                (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
                ![chartModelBasis E m, (chartModelBasis E j), chartModelBasis E p] *
              (∑ q : Fin (Module.finrank ℝ E),
                (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) -
                  DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    g₀ x l₁ i q (extChartAt I x x)) *
                  DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))))
      + ((∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3
                (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
                ![(chartModelBasis E j), chartModelBasis E m, chartModelBasis E p] *
              (∑ q : Fin (Module.finrank ℝ E),
                (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) -
                  DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    g₀ x l₁ i q (extChartAt I x x)) *
                  DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁))))
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3
                (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
                ![(chartModelBasis E j), chartModelBasis E m, chartModelBasis E p] *
              (∑ q : Fin (Module.finrank ℝ E),
                (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) -
                  DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    g_bg x k₁ l₁ q (extChartAt I x x)) *
                  DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q i))))
      - (∑ w : Fin (Module.finrank ℝ E),
        PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x w (extChartAt I x x) *
          unitModel (I := I) (M := M) g₀ 3
            (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
            ![chartModelBasis E j, chartModelBasis E i, chartModelBasis E w])
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3
                (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
                ![chartModelBasis E m, (chartModelBasis E i), chartModelBasis E p] *
              (∑ q : Fin (Module.finrank ℝ E),
                (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ j q (extChartAt I x x) -
                  DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    g₀ x k₁ j q (extChartAt I x x)) *
                  DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁))))
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (∑ q : Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j q (extChartAt I x x) -
              DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                g₀ x i j q (extChartAt I x x)) *
              unitModel (I := I) (M := M) g₀ 3
                (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
                ![chartModelBasis E p, chartModelBasis E q, chartModelBasis E k₁]))
      - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m *
            (unitModel (I := I) (M := M) g₀ 3
                (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
                ![chartModelBasis E m, (chartModelBasis E i), chartModelBasis E p] *
              (∑ q : Fin (Module.finrank ℝ E),
                (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) -
                  DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                    g₀ x l₁ j q (extChartAt I x x)) *
                  DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))))
      + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p *
          (∑ q : Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) -
              DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I)
                g₀ x j i q (extChartAt I x x)) *
              unitModel (I := I) (M := M) g₀ 3
                (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
                ![chartModelBasis E q, chartModelBasis E p, chartModelBasis E k₁])) := by
  classical
  refine (lieArm_arm1_value_traced (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
    (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x i j).trans ?_
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_) ?_
  · exact lieArm_U3_deTurckVF_slot0_value (I := I)
      (unitModel (I := I) (M := M) g₀ 3
        (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x)
      (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x
      (chartModelBasis E i) (chartModelBasis E j)
  · refine congrArg₂ (· - ·) (congrArg₂ (· - ·) (congrArg₂ (· - ·) (congrArg₂ (· - ·)
      (congrArg₂ (· - ·) ?_ ?_) ?_) ?_) ?_) ?_
    · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => ?_))))
      exact congrArg (HMul.hMul _) (congrArg (HMul.hMul _) (congrArg (HMul.hMul _)
        (lieArm_inner_connDiff_chartBasis_value (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x j l₁ k₁)))
    · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => ?_))))
      exact congrArg (HMul.hMul _) (congrArg (HMul.hMul _) (congrArg (HMul.hMul _)
        (lieArm_inner_connDiff_chartBasis_value (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x l₁ k₁ j)))
    · exact lieArm_U3_deTurckVF_slot2_value (I := I)
        (unitModel (I := I) (M := M) g₀ 3
          (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x
        (chartModelBasis E i) (chartModelBasis E j)
    · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => ?_))))
      exact congrArg (HMul.hMul _) (congrArg (HMul.hMul _) (congrArg (HMul.hMul _)
        (lieArm_inner_connDiff_chartBasis_value (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x i k₁ l₁)))
    · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ => ?_))
      exact congrArg (HMul.hMul _)
        (lieArm_U3_connDiff_slot1_value (I := I)
          (unitModel (I := I) (M := M) g₀ 3
            (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x i j
          (chartModelBasis E p) (chartModelBasis E k₁))
    · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => ?_))))
      exact congrArg (HMul.hMul _) (congrArg (HMul.hMul _) (congrArg (HMul.hMul _)
        (lieArm_inner_connDiff_chartBasis_value (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x i l₁ k₁)))
  · refine congrArg₂ (· - ·) (congrArg₂ (· - ·) (congrArg₂ (· - ·) (congrArg₂ (· - ·)
      (congrArg₂ (· - ·) ?_ ?_) ?_) ?_) ?_) ?_
    · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => ?_))))
      exact congrArg (HMul.hMul _) (congrArg (HMul.hMul _) (congrArg (HMul.hMul _)
        (lieArm_inner_connDiff_chartBasis_value (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x i l₁ k₁)))
    · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => ?_))))
      exact congrArg (HMul.hMul _) (congrArg (HMul.hMul _) (congrArg (HMul.hMul _)
        (lieArm_inner_connDiff_chartBasis_value (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x l₁ k₁ i)))
    · exact lieArm_U3_deTurckVF_slot2_value (I := I)
        (unitModel (I := I) (M := M) g₀ 3
          (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x
        (chartModelBasis E j) (chartModelBasis E i)
    · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => ?_))))
      exact congrArg (HMul.hMul _) (congrArg (HMul.hMul _) (congrArg (HMul.hMul _)
        (lieArm_inner_connDiff_chartBasis_value (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x j k₁ l₁)))
    · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ => ?_))
      exact congrArg (HMul.hMul _)
        (lieArm_U3_connDiff_slot1_value (I := I)
          (unitModel (I := I) (M := M) g₀ 3
            (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x j i
          (chartModelBasis E p) (chartModelBasis E k₁))
    · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => ?_))))
      exact congrArg (HMul.hMul _) (congrArg (HMul.hMul _) (congrArg (HMul.hMul _)
        (lieArm_inner_connDiff_chartBasis_value (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' s)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x j l₁ k₁)))
  · refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ => ?_))
    exact congrArg (HMul.hMul _)
      (lieArm_U3_connDiff_slot0_value (I := I)
        (unitModel (I := I) (M := M) g₀ 3
          (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x i j
        (chartModelBasis E p) (chartModelBasis E k₁))

namespace O1Abstract

variable {n : ℕ}

private lemma o1_sum_ite (g : Fin n → ℝ) (p : Fin n) :
    (∑ q : Fin n, g q * (if p = q then (1 : ℝ) else 0)) = g p := by
  rw [Finset.sum_eq_single p]
  · rw [if_pos rfl, mul_one]
  · intro q _ hq
    rw [if_neg (fun h => hq h.symm), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ p) h

private lemma o1_sink4 (F : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ k₁ : Fin n, ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n, ∑ q : Fin n, F k₁ p l₁ m q)
    = ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n, ∑ q : Fin n, ∑ k₁ : Fin n, F k₁ p l₁ m q := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l₁ _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.sum_comm]

private lemma o1_sink4mid (F : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ k₁ : Fin n, ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n, ∑ q : Fin n, F k₁ p l₁ m q)
    = ∑ k₁ : Fin n, ∑ p : Fin n, ∑ m : Fin n, ∑ q : Fin n, ∑ l₁ : Fin n, F k₁ p l₁ m q := by
  refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ => ?_))
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.sum_comm]

section Collapses

variable (ig cg : Fin n → Fin n → ℝ)

private lemma o1_col2
    (hcol : ∀ l j : Fin n, (∑ k : Fin n, cg k j * ig k l) = if l = j then (1 : ℝ) else 0)
    (hcgs : ∀ a b : Fin n, cg a b = cg b a) (p q : Fin n) :
    (∑ k : Fin n, ig k p * cg q k) = if p = q then (1 : ℝ) else 0 := by
  rw [show (∑ k : Fin n, ig k p * cg q k) = ∑ k : Fin n, cg k q * ig k p from
    Finset.sum_congr rfl (fun k _ => by rw [hcgs q k]; ring)]
  exact hcol p q

private lemma o1_col3
    (hcol : ∀ l j : Fin n, (∑ k : Fin n, cg k j * ig k l) = if l = j then (1 : ℝ) else 0)
    (higs : ∀ a b : Fin n, ig a b = ig b a) (q c : Fin n) :
    (∑ l : Fin n, ig q l * cg l c) = if q = c then (1 : ℝ) else 0 := by
  rw [show (∑ l : Fin n, ig q l * cg l c) = ∑ l : Fin n, cg l c * ig l q from
    Finset.sum_congr rfl (fun l _ => by rw [higs q l]; ring)]
  exact hcol q c

private lemma o1_col4
    (hcol : ∀ l j : Fin n, (∑ k : Fin n, cg k j * ig k l) = if l = j then (1 : ℝ) else 0)
    (hcgs : ∀ a b : Fin n, cg a b = cg b a) (l m : Fin n) :
    (∑ c : Fin n, cg l c * ig c m) = if m = l then (1 : ℝ) else 0 := by
  rw [show (∑ c : Fin n, cg l c * ig c m) = ∑ c : Fin n, cg c l * ig c m from
    Finset.sum_congr rfl (fun c _ => by rw [hcgs l c])]
  exact hcol m l

end Collapses

section QuadCollapse

variable (ig cg : Fin n → Fin n → ℝ) (g1 g0 : Fin n → Fin n → Fin n → ℝ)
    (X : Fin n → Fin n → ℝ)

private lemma o1_quadAC
    (hcol : ∀ l j : Fin n, (∑ k : Fin n, cg k j * ig k l) = if l = j then (1 : ℝ) else 0)
    (hcgs : ∀ a b : Fin n, cg a b = cg b a) (v : Fin n) :
    (∑ k₁ : Fin n, ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n,
      ig k₁ p * (ig l₁ m * (X m p * (∑ q : Fin n, (g1 l₁ v q - g0 l₁ v q) * cg q k₁))))
    = (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g1 a v c * X b c))
      - (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a v c * X b c)) := by
  have hpt : ∀ k₁ p l₁ m : Fin n,
      ig k₁ p * (ig l₁ m * (X m p * (∑ q : Fin n, (g1 l₁ v q - g0 l₁ v q) * cg q k₁)))
      = ∑ q : Fin n,
          (ig l₁ m * ((g1 l₁ v q - g0 l₁ v q) * X m p)) * (ig k₁ p * cg q k₁) := by
    intro k₁ p l₁ m
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun q _ => by ring)
  rw [Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
    Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => hpt k₁ p l₁ m))))]
  rw [o1_sink4 (fun k₁ p l₁ m q =>
    (ig l₁ m * ((g1 l₁ v q - g0 l₁ v q) * X m p)) * (ig k₁ p * cg q k₁))]
  have hcolpt : ∀ p l₁ m q : Fin n,
      (∑ k₁ : Fin n,
        (ig l₁ m * ((g1 l₁ v q - g0 l₁ v q) * X m p)) * (ig k₁ p * cg q k₁))
      = (ig l₁ m * ((g1 l₁ v q - g0 l₁ v q) * X m p)) * (if p = q then (1 : ℝ) else 0) := by
    intro p l₁ m q
    rw [← Finset.mul_sum, o1_col2 ig cg hcol hcgs p q]
  rw [Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun l₁ _ =>
    Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun q _ => hcolpt p l₁ m q))))]
  rw [Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun l₁ _ =>
    Finset.sum_congr rfl (fun m _ =>
      o1_sum_ite (fun q => ig l₁ m * ((g1 l₁ v q - g0 l₁ v q) * X m p)) p)))]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun l₁ _ => Finset.sum_comm)]
  rw [show (∑ l₁ : Fin n, ∑ m : Fin n, ∑ p : Fin n,
      ig l₁ m * ((g1 l₁ v p - g0 l₁ v p) * X m p))
    = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
        (ig a b * (g1 a v c * X b c) - ig a b * (g0 a v c * X b c)) from
    Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      Finset.sum_congr rfl (fun c _ => by ring)))]
  simp only [Finset.sum_sub_distrib]

private lemma o1_quadB
    (hcol : ∀ l j : Fin n, (∑ k : Fin n, cg k j * ig k l) = if l = j then (1 : ℝ) else 0)
    (hcgs : ∀ a b : Fin n, cg a b = cg b a) (v : Fin n) :
    (∑ k₁ : Fin n, ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n,
      ig k₁ p * (ig l₁ m * (X m p * (∑ q : Fin n, (g1 k₁ v q - g0 k₁ v q) * cg q l₁))))
    = (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g1 a v c * X c b))
      - (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a v c * X c b)) := by
  have hpt : ∀ k₁ p l₁ m : Fin n,
      ig k₁ p * (ig l₁ m * (X m p * (∑ q : Fin n, (g1 k₁ v q - g0 k₁ v q) * cg q l₁)))
      = ∑ q : Fin n,
          (ig k₁ p * ((g1 k₁ v q - g0 k₁ v q) * X m p)) * (ig l₁ m * cg q l₁) := by
    intro k₁ p l₁ m
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun q _ => by ring)
  rw [Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
    Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => hpt k₁ p l₁ m))))]
  rw [o1_sink4mid (fun k₁ p l₁ m q =>
    (ig k₁ p * ((g1 k₁ v q - g0 k₁ v q) * X m p)) * (ig l₁ m * cg q l₁))]
  have hcolpt : ∀ k₁ p m q : Fin n,
      (∑ l₁ : Fin n,
        (ig k₁ p * ((g1 k₁ v q - g0 k₁ v q) * X m p)) * (ig l₁ m * cg q l₁))
      = (ig k₁ p * ((g1 k₁ v q - g0 k₁ v q) * X m p)) * (if m = q then (1 : ℝ) else 0) := by
    intro k₁ p m q
    rw [← Finset.mul_sum, o1_col2 ig cg hcol hcgs m q]
  rw [Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
    Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun q _ => hcolpt k₁ p m q))))]
  rw [Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
    Finset.sum_congr rfl (fun m _ =>
      o1_sum_ite (fun q => ig k₁ p * ((g1 k₁ v q - g0 k₁ v q) * X m p)) m)))]
  rw [show (∑ k₁ : Fin n, ∑ p : Fin n, ∑ m : Fin n,
      ig k₁ p * ((g1 k₁ v m - g0 k₁ v m) * X m p))
    = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
        (ig a b * (g1 a v c * X c b) - ig a b * (g0 a v c * X c b)) from
    Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      Finset.sum_congr rfl (fun c _ => by ring)))]
  simp only [Finset.sum_sub_distrib]

end QuadCollapse

end O1Abstract

namespace O1Abstract

variable {n : ℕ}

private lemma o1_sum_ite2 (g : Fin n → ℝ) (p : Fin n) :
    (∑ q : Fin n, (if q = p then (1 : ℝ) else 0) * g q) = g p := by
  rw [Finset.sum_eq_single p]
  · rw [if_pos rfl, one_mul]
  · intro q _ hq
    rw [if_neg hq, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ p) h

section EFshapes

variable (ig : Fin n → Fin n → ℝ) (g1 g0 : Fin n → Fin n → Fin n → ℝ)
    (f3 : Fin n → Fin n → Fin n → ℝ)

private lemma o1_pullE (u v : Fin n) :
    (∑ k : Fin n, ∑ p : Fin n, ig k p * (∑ q : Fin n, (g1 u v q - g0 u v q) * f3 p q k))
    = (∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (g1 u v q * f3 p q k))
      - (∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (g0 u v q * f3 p q k)) := by
  rw [show (∑ k : Fin n, ∑ p : Fin n, ig k p * (∑ q : Fin n, (g1 u v q - g0 u v q) * f3 p q k))
      = ∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n,
          (ig k p * (g1 u v q * f3 p q k) - ig k p * (g0 u v q * f3 p q k)) from
    Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun p _ => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun q _ => by ring)))]
  simp only [Finset.sum_sub_distrib]

private lemma o1_pullF (u v : Fin n) :
    (∑ k : Fin n, ∑ p : Fin n, ig k p * (∑ q : Fin n, (g1 u v q - g0 u v q) * f3 q p k))
    = (∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (g1 u v q * f3 q p k))
      - (∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (g0 u v q * f3 q p k)) := by
  rw [show (∑ k : Fin n, ∑ p : Fin n, ig k p * (∑ q : Fin n, (g1 u v q - g0 u v q) * f3 q p k))
      = ∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n,
          (ig k p * (g1 u v q * f3 q p k) - ig k p * (g0 u v q * f3 q p k)) from
    Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun p _ => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun q _ => by ring)))]
  simp only [Finset.sum_sub_distrib]

private lemma o1_swapE (ga : Fin n → Fin n → Fin n → ℝ)
    (hgas : ∀ a b k : Fin n, ga a b k = ga b a k) (u v : Fin n) :
    (∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (ga u v q * f3 p q k))
    = ∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (ga v u q * f3 p q k) :=
  Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun p _ =>
    Finset.sum_congr rfl (fun q _ => by rw [hgas u v q])))

private lemma o1_swapF (ga : Fin n → Fin n → Fin n → ℝ)
    (hgas : ∀ a b k : Fin n, ga a b k = ga b a k) (u v : Fin n) :
    (∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (ga u v q * f3 q p k))
    = ∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (ga v u q * f3 q p k) :=
  Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun p _ =>
    Finset.sum_congr rfl (fun q _ => by rw [hgas u v q])))

private lemma o1_vf0exp (u v : Fin n) :
    (∑ w : Fin n, (∑ a : Fin n, ∑ b : Fin n, ig a b * (g1 a b w - g0 a b w)) * f3 u v w)
    = (∑ a : Fin n, ∑ b : Fin n, ∑ w : Fin n, ig a b * (g1 a b w * f3 u v w))
      - (∑ a : Fin n, ∑ b : Fin n, ∑ w : Fin n, ig a b * (g0 a b w * f3 u v w)) := by
  rw [show (∑ w : Fin n, (∑ a : Fin n, ∑ b : Fin n, ig a b * (g1 a b w - g0 a b w)) * f3 u v w)
      = ∑ w : Fin n, ∑ a : Fin n, ∑ b : Fin n,
          (ig a b * (g1 a b w * f3 u v w) - ig a b * (g0 a b w * f3 u v w)) from
    Finset.sum_congr rfl (fun w _ => by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun a _ => by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun b _ => by ring)))]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
  simp only [Finset.sum_sub_distrib]

end EFshapes

section DerivedHyps

private lemma o1_hgb2 (ig cg : Fin n → Fin n → ℝ) (gb g1 : Fin n → Fin n → Fin n → ℝ)
    (hcol : ∀ l j : Fin n, (∑ k : Fin n, cg k j * ig k l) = if l = j then (1 : ℝ) else 0)
    (hcgs : ∀ a b : Fin n, cg a b = cg b a)
    (hga1 : ∀ a b k : Fin n, g1 a b k = (1 / 2 : ℝ) * ∑ l : Fin n, ig k l * gb a b l)
    (a b l : Fin n) :
    gb a b l = 2 * ∑ c : Fin n, cg l c * g1 a b c := by
  have h1 : (∑ c : Fin n, cg l c * g1 a b c)
      = ∑ c : Fin n, ∑ m : Fin n, (cg l c * ig c m) * ((1 / 2 : ℝ) * gb a b m) := by
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [hga1 a b c, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun m _ => by ring)
  have h2 : (∑ c : Fin n, ∑ m : Fin n, (cg l c * ig c m) * ((1 / 2 : ℝ) * gb a b m))
      = ∑ m : Fin n, (if m = l then (1 : ℝ) else 0) * ((1 / 2 : ℝ) * gb a b m) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [← Finset.sum_mul, o1_col4 ig cg hcol hcgs l m]
  rw [h1, h2, o1_sum_ite2 (fun m => (1 / 2 : ℝ) * gb a b m) l]
  ring

private lemma o1_hdg2 (ig cg : Fin n → Fin n → ℝ) (dg gb g1 : Fin n → Fin n → Fin n → ℝ)
    (hcol : ∀ l j : Fin n, (∑ k : Fin n, cg k j * ig k l) = if l = j then (1 : ℝ) else 0)
    (hcgs : ∀ a b : Fin n, cg a b = cg b a)
    (hgbdef : ∀ a b l : Fin n, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgs : ∀ m a b : Fin n, dg m a b = dg m b a)
    (hga1 : ∀ a b k : Fin n, g1 a b k = (1 / 2 : ℝ) * ∑ l : Fin n, ig k l * gb a b l)
    (m u v : Fin n) :
    dg m u v = (∑ c : Fin n, cg v c * g1 m u c) + (∑ c : Fin n, cg u c * g1 m v c) := by
  have h1 : dg m u v = (1 / 2 : ℝ) * (gb m u v + gb m v u) := by
    rw [hgbdef m u v, hgbdef m v u, hdgs m v u, hdgs u v m, hdgs v u m]
    ring
  rw [h1, o1_hgb2 ig cg gb g1 hcol hcgs hga1 m u v,
    o1_hgb2 ig cg gb g1 hcol hcgs hga1 m v u]
  ring

private lemma o1_hdig2 (ig cg : Fin n → Fin n → ℝ) (dg gb dig g1 : Fin n → Fin n → Fin n → ℝ)
    (hcol : ∀ l j : Fin n, (∑ k : Fin n, cg k j * ig k l) = if l = j then (1 : ℝ) else 0)
    (higs : ∀ a b : Fin n, ig a b = ig b a)
    (hcgs : ∀ a b : Fin n, cg a b = cg b a)
    (hgbdef : ∀ a b l : Fin n, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgs : ∀ m a b : Fin n, dg m a b = dg m b a)
    (hga1 : ∀ a b k : Fin n, g1 a b k = (1 / 2 : ℝ) * ∑ l : Fin n, ig k l * gb a b l)
    (hdig : ∀ m a b : Fin n, dig m a b
      = -(∑ x : Fin n, ∑ y : Fin n, ig a x * ig y b * dg m x y))
    (m a b : Fin n) :
    dig m a b = -(∑ p : Fin n, (ig a p * g1 m p b + ig p b * g1 m p a)) := by
  have hsub : ∀ x y : Fin n, ig a x * ig y b * dg m x y
      = (∑ c : Fin n, (ig a x * g1 m x c) * (cg y c * ig y b))
        + ∑ c : Fin n, (ig y b * g1 m y c) * (ig a x * cg x c) := by
    intro x y
    rw [o1_hdg2 ig cg dg gb g1 hcol hcgs hgbdef hdgs hga1 m x y]
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl (fun c _ => by ring)
    · exact Finset.sum_congr rfl (fun c _ => by ring)
  have h0 : (∑ x : Fin n, ∑ y : Fin n, ig a x * ig y b * dg m x y)
      = (∑ x : Fin n, ∑ y : Fin n, ∑ c : Fin n, (ig a x * g1 m x c) * (cg y c * ig y b))
        + ∑ x : Fin n, ∑ y : Fin n, ∑ c : Fin n, (ig y b * g1 m y c) * (ig a x * cg x c) := by
    rw [Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => hsub x y))]
    simp only [Finset.sum_add_distrib]
  have hP1 : (∑ x : Fin n, ∑ y : Fin n, ∑ c : Fin n, (ig a x * g1 m x c) * (cg y c * ig y b))
      = ∑ p : Fin n, ig a p * g1 m p b := by
    have e1 : ∀ x : Fin n,
        (∑ y : Fin n, ∑ c : Fin n, (ig a x * g1 m x c) * (cg y c * ig y b))
        = ∑ c : Fin n, (ig a x * g1 m x c) * (if b = c then (1 : ℝ) else 0) := by
      intro x
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [← Finset.mul_sum, hcol b c]
    rw [Finset.sum_congr rfl (fun x _ => e1 x)]
    exact Finset.sum_congr rfl (fun x _ => o1_sum_ite (fun c => ig a x * g1 m x c) b)
  have hP2 : (∑ x : Fin n, ∑ y : Fin n, ∑ c : Fin n, (ig y b * g1 m y c) * (ig a x * cg x c))
      = ∑ p : Fin n, ig p b * g1 m p a := by
    have e2 : ∀ y c : Fin n, (∑ x : Fin n, (ig y b * g1 m y c) * (ig a x * cg x c))
        = (ig y b * g1 m y c) * (if a = c then (1 : ℝ) else 0) := by
      intro y c
      rw [← Finset.mul_sum, o1_col3 ig cg hcol higs a c]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun y _ => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun c _ => e2 y c))]
    exact Finset.sum_congr rfl (fun y _ => o1_sum_ite (fun c => ig y b * g1 m y c) a)
  rw [hdig m a b, h0, hP1, hP2, ← Finset.sum_add_distrib]

end DerivedHyps

end O1Abstract

namespace O1Abstract

variable {n : ℕ}

private lemma o1_neg_push (c d : ℝ) (P : Fin n → Fin n → ℝ) :
    c * ((-(∑ q : Fin n, ∑ p : Fin n, P q p)) * d)
    = ∑ q : Fin n, ∑ p : Fin n, -(P q p * (d * c)) := by
  rw [show c * ((-(∑ q : Fin n, ∑ p : Fin n, P q p)) * d)
      = -((∑ q : Fin n, ∑ p : Fin n, P q p) * (d * c)) from by ring]
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib]

private lemma o1_neg_push1 (t : ℝ) (P : Fin n → Fin n → ℝ) :
    (-(∑ q : Fin n, ∑ p : Fin n, P q p)) * t
    = ∑ q : Fin n, ∑ p : Fin n, -(P q p * t) := by
  rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib]

private lemma o1_sum_ite' (g : Fin n → ℝ) (p : Fin n) :
    (∑ q : Fin n, g q * (if q = p then (1 : ℝ) else 0)) = g p := by
  rw [Finset.sum_eq_single p]
  · rw [if_pos rfl, mul_one]
  · intro q _ hq
    rw [if_neg hq, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ p) h

private lemma o1_neg_push3 (c d : ℝ) (X : Fin n → ℝ) :
    c * (d * (-(∑ q : Fin n, X q))) = ∑ q : Fin n, -(X q * (d * c)) := by
  rw [show c * (d * (-(∑ q : Fin n, X q))) = -((∑ q : Fin n, X q) * (d * c)) from by ring]
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib]

section RQ3

variable (ig cg : Fin n → Fin n → ℝ) (g1 g0 f3 : Fin n → Fin n → Fin n → ℝ)

private lemma o1_rq3
    (higs : ∀ a b : Fin n, ig a b = ig b a)
    (hf3s : ∀ d a b : Fin n, f3 d a b = f3 d b a) (u v : Fin n) :
    (∑ k : Fin n, cg k v * (∑ a : Fin n, ∑ b : Fin n,
      (-(∑ q : Fin n, ∑ p : Fin n, ig a p * f3 u p q * ig q b)) * (g1 a b k - g0 a b k)))
    = -(∑ k₁ : Fin n, ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n,
        ig k₁ p * (ig l₁ m * (f3 u m p * (∑ q : Fin n, (g1 k₁ l₁ q - g0 k₁ l₁ q) * cg q v)))) := by
  have hflat : (∑ k : Fin n, cg k v * (∑ a : Fin n, ∑ b : Fin n,
      (-(∑ q : Fin n, ∑ p : Fin n, ig a p * f3 u p q * ig q b)) * (g1 a b k - g0 a b k)))
      = ∑ k : Fin n, ∑ a : Fin n, ∑ b : Fin n, ∑ q : Fin n, ∑ p : Fin n,
          -((ig a p * f3 u p q * ig q b) * ((g1 a b k - g0 a b k) * cg k v)) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    exact o1_neg_push (cg k v) (g1 a b k - g0 a b k) (fun q p => ig a p * f3 u p q * ig q b)
  rw [hflat]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    Finset.sum_congr rfl (fun q _ => Finset.sum_comm)))]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
  have hrhs : (∑ k₁ : Fin n, ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n,
      ig k₁ p * (ig l₁ m * (f3 u m p * (∑ q : Fin n, (g1 k₁ l₁ q - g0 k₁ l₁ q) * cg q v))))
      = ∑ k₁ : Fin n, ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n, ∑ q : Fin n,
          ig k₁ p * (ig l₁ m * (f3 u m p * ((g1 k₁ l₁ q - g0 k₁ l₁ q) * cg q v))) := by
    refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => ?_))))
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  rw [hrhs]
  simp only [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ =>
    Finset.sum_congr rfl (fun x3 _ => Finset.sum_congr rfl (fun x4 _ =>
      Finset.sum_congr rfl (fun x5 _ => ?_)))))
  rw [higs x4 x3, hf3s u x2 x4]
  ring

end RQ3

section RG7

variable (ig cg : Fin n → Fin n → ℝ) (gb g1 f3 : Fin n → Fin n → Fin n → ℝ)

private lemma o1_rg7
    (hcol : ∀ l j : Fin n, (∑ k : Fin n, cg k j * ig k l) = if l = j then (1 : ℝ) else 0)
    (higs : ∀ a b : Fin n, ig a b = ig b a)
    (hgb2 : ∀ a b l : Fin n, gb a b l = 2 * ∑ c : Fin n, cg l c * g1 a b c)
    (u v : Fin n) :
    (∑ k : Fin n, cg k v * (∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
      ∑ l : Fin n, (-(∑ q : Fin n, ∑ p : Fin n, ig k p * f3 u p q * ig q l)) * gb a b l)))
    = -(∑ a : Fin n, ∑ b : Fin n, ∑ w : Fin n, ig a b * (g1 a b w * f3 u v w)) := by
  have hinner : ∀ k a b : Fin n,
      ((1 / 2 : ℝ) * ∑ l : Fin n,
        (-(∑ q : Fin n, ∑ p : Fin n, ig k p * f3 u p q * ig q l)) * gb a b l)
      = -(∑ q : Fin n, (∑ p : Fin n, ig k p * f3 u p q) * g1 a b q) := by
    intro k a b
    have hpt1 : ∀ l : Fin n,
        (-(∑ q : Fin n, ∑ p : Fin n, ig k p * f3 u p q * ig q l)) * gb a b l
        = ∑ c : Fin n, ∑ q : Fin n, ∑ p : Fin n,
            ((-2 : ℝ) * ((ig k p * f3 u p q) * g1 a b c)) * (ig q l * cg l c) := by
      intro l
      rw [hgb2 a b l]
      rw [show (2 : ℝ) * ∑ c : Fin n, cg l c * g1 a b c
          = ∑ c : Fin n, 2 * (cg l c * g1 a b c) from Finset.mul_sum _ _ _]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [o1_neg_push1 (2 * (cg l c * g1 a b c)) (fun q p => ig k p * f3 u p q * ig q l)]
      refine Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun p _ => ?_))
      ring
    rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun l _ => congrArg (HMul.hMul (1 / 2 : ℝ)) (hpt1 l))]
    have hro : (∑ l : Fin n, (1 / 2 : ℝ) * ∑ c : Fin n, ∑ q : Fin n, ∑ p : Fin n,
        ((-2 : ℝ) * ((ig k p * f3 u p q) * g1 a b c)) * (ig q l * cg l c))
        = ∑ c : Fin n, ∑ q : Fin n, ∑ p : Fin n, ∑ l : Fin n,
            (1 / 2 : ℝ) * (((-2 : ℝ) * ((ig k p * f3 u p q) * g1 a b c)) * (ig q l * cg l c)) := by
      rw [show (∑ l : Fin n, (1 / 2 : ℝ) * ∑ c : Fin n, ∑ q : Fin n, ∑ p : Fin n,
          ((-2 : ℝ) * ((ig k p * f3 u p q) * g1 a b c)) * (ig q l * cg l c))
          = ∑ l : Fin n, ∑ c : Fin n, ∑ q : Fin n, ∑ p : Fin n,
              (1 / 2 : ℝ) * (((-2 : ℝ) * ((ig k p * f3 u p q) * g1 a b c)) * (ig q l * cg l c)) from
        Finset.sum_congr rfl (fun l _ => by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun c _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun q _ => ?_)
          rw [Finset.mul_sum])]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      rw [Finset.sum_comm]
    rw [hro]
    have hcolstep : ∀ c q p : Fin n,
        (∑ l : Fin n, (1 / 2 : ℝ) *
          (((-2 : ℝ) * ((ig k p * f3 u p q) * g1 a b c)) * (ig q l * cg l c)))
        = (-((ig k p * f3 u p q) * g1 a b c)) * (if q = c then (1 : ℝ) else 0) := by
      intro c q p
      rw [show (∑ l : Fin n, (1 / 2 : ℝ) *
          (((-2 : ℝ) * ((ig k p * f3 u p q) * g1 a b c)) * (ig q l * cg l c)))
          = ∑ l : Fin n, (-((ig k p * f3 u p q) * g1 a b c)) * (ig q l * cg l c) from
        Finset.sum_congr rfl (fun l _ => by ring)]
      rw [← Finset.mul_sum, o1_col3 ig cg hcol higs q c]
    rw [Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun q _ =>
      Finset.sum_congr rfl (fun p _ => hcolstep c q p)))]
    have hite : (∑ c : Fin n, ∑ q : Fin n, ∑ p : Fin n,
        (-((ig k p * f3 u p q) * g1 a b c)) * (if q = c then (1 : ℝ) else 0))
        = ∑ q : Fin n, ∑ p : Fin n, -((ig k p * f3 u p q) * g1 a b q) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      exact o1_sum_ite (fun c => -((ig k p * f3 u p q) * g1 a b c)) q
    rw [hite]
    rw [show (∑ q : Fin n, ∑ p : Fin n, -((ig k p * f3 u p q) * g1 a b q))
        = ∑ q : Fin n, -((∑ p : Fin n, ig k p * f3 u p q) * g1 a b q) from
      Finset.sum_congr rfl (fun q _ => by
        rw [Finset.sum_neg_distrib, ← Finset.sum_mul])]
    rw [← Finset.sum_neg_distrib]
  rw [Finset.sum_congr rfl (fun k _ => congrArg (HMul.hMul (cg k v))
    (Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      congrArg (HMul.hMul (ig a b)) (hinner k a b)))))]
  have hflat2 : (∑ k : Fin n, cg k v * (∑ a : Fin n, ∑ b : Fin n,
      ig a b * (-(∑ q : Fin n, (∑ p : Fin n, ig k p * f3 u p q) * g1 a b q))))
      = ∑ k : Fin n, ∑ a : Fin n, ∑ b : Fin n, ∑ q : Fin n, ∑ p : Fin n,
          (-((f3 u p q * (ig a b * g1 a b q))) * (cg k v * ig k p)) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [o1_neg_push3 (cg k v) (ig a b)
      (fun q => (∑ p : Fin n, ig k p * f3 u p q) * g1 a b q)]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [show -((∑ p : Fin n, ig k p * f3 u p q) * g1 a b q * (ig a b * cg k v))
        = ∑ p : Fin n, -((f3 u p q * (ig a b * g1 a b q)) * (cg k v * ig k p)) from by
      rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun p _ => by ring)]
    exact Finset.sum_congr rfl (fun p _ => by ring)
  rw [hflat2]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_comm))]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    Finset.sum_congr rfl (fun q _ => Finset.sum_comm)))]
  have hcolk : ∀ a b q p : Fin n,
      (∑ k : Fin n, (-((f3 u p q * (ig a b * g1 a b q))) * (cg k v * ig k p)))
      = (-((f3 u p q * (ig a b * g1 a b q)))) * (if p = v then (1 : ℝ) else 0) := by
    intro a b q p
    rw [← Finset.mul_sum, hcol p v]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun p _ => hcolk a b q p))))]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    Finset.sum_congr rfl (fun q _ =>
      o1_sum_ite' (fun p => -((f3 u p q * (ig a b * g1 a b q)))) v)))]
  rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ q : Fin n, -((f3 u v q * (ig a b * g1 a b q))))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ q : Fin n, -(ig a b * (g1 a b q * f3 u v q)) from
    Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      Finset.sum_congr rfl (fun q _ => by ring)))]
  simp only [Finset.sum_neg_distrib]

end RG7

end O1Abstract

namespace O1Abstract

variable {n : ℕ}

private lemma o1_neg_push1d (t : ℝ) (P : Fin n → ℝ) :
    (-(∑ p : Fin n, P p)) * t = ∑ p : Fin n, -(P p * t) := by
  rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]

private lemma o1_sum3_add (F G : Fin n → Fin n → Fin n → ℝ) :
    (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, F a b c)
      + (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, G a b c)
    = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, (F a b c + G a b c) := by
  simp only [Finset.sum_add_distrib]

private lemma o1_abswap3 (H : Fin n → Fin n → Fin n → ℝ) :
    (∑ a : Fin n, ∑ b : Fin n, ∑ p : Fin n, H a b p)
    = ∑ a : Fin n, ∑ b : Fin n, ∑ p : Fin n, H b a p :=
  Finset.sum_comm

private lemma o1_abswap5 (H : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ k : Fin n, ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, H k a b l p)
    = ∑ k : Fin n, ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, H k b a l p :=
  Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)

section RF1

variable (ig cg : Fin n → Fin n → ℝ) (dig g1 f3 : Fin n → Fin n → Fin n → ℝ)

private lemma o1_rf1a
    (hcol : ∀ l j : Fin n, (∑ k : Fin n, cg k j * ig k l) = if l = j then (1 : ℝ) else 0)
    (higs : ∀ a b : Fin n, ig a b = ig b a)
    (hf3s : ∀ d a b : Fin n, f3 d a b = f3 d b a)
    (hg1s : ∀ a b k : Fin n, g1 a b k = g1 b a k)
    (hdig2 : ∀ m a b : Fin n, dig m a b
      = -(∑ p : Fin n, (ig a p * g1 m p b + ig p b * g1 m p a)))
    (u v : Fin n) :
    (∑ k : Fin n, cg k v * (∑ a : Fin n, ∑ b : Fin n, dig u a b * ((1 / 2 : ℝ) *
      ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b))))
    = -(∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g1 a u c * f3 b v c))
      - (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g1 a u c * f3 c v b))
      + (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g1 a u c * f3 v b c)) := by
  have hflat : (∑ k : Fin n, cg k v * (∑ a : Fin n, ∑ b : Fin n, dig u a b * ((1 / 2 : ℝ) *
      ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b))))
      = ∑ k : Fin n, ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n,
          (dig u a b * ((1 / 2 : ℝ) * (f3 a l b + f3 b l a - f3 l a b))) * (cg k v * ig k l) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  rw [hflat]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_comm))]
  have hcolk : ∀ a b l : Fin n,
      (∑ k : Fin n,
        (dig u a b * ((1 / 2 : ℝ) * (f3 a l b + f3 b l a - f3 l a b))) * (cg k v * ig k l))
      = (dig u a b * ((1 / 2 : ℝ) * (f3 a l b + f3 b l a - f3 l a b)))
          * (if l = v then (1 : ℝ) else 0) := by
    intro a b l
    rw [← Finset.mul_sum, hcol l v]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    Finset.sum_congr rfl (fun l _ => hcolk a b l)))]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    o1_sum_ite' (fun l => dig u a b * ((1 / 2 : ℝ) * (f3 a l b + f3 b l a - f3 l a b))) v))]
  have h2 : ∀ a b : Fin n,
      dig u a b * ((1 / 2 : ℝ) * (f3 a v b + f3 b v a - f3 v a b))
      = ∑ p : Fin n,
          (-((ig a p * g1 u p b) * ((1 / 2 : ℝ) * (f3 a v b + f3 b v a - f3 v a b)))
           + -((ig p b * g1 u p a) * ((1 / 2 : ℝ) * (f3 a v b + f3 b v a - f3 v a b)))) := by
    intro a b
    rw [hdig2 u a b, o1_neg_push1d ((1 / 2 : ℝ) * (f3 a v b + f3 b v a - f3 v a b))
      (fun p => ig a p * g1 u p b + ig p b * g1 u p a)]
    exact Finset.sum_congr rfl (fun p _ => by ring)
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => h2 a b))]
  simp only [Finset.sum_add_distrib]
  have hmerge : (∑ a : Fin n, ∑ b : Fin n, ∑ p : Fin n,
      -((ig p b * g1 u p a) * ((1 / 2 : ℝ) * (f3 a v b + f3 b v a - f3 v a b))))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ p : Fin n,
          -((ig a p * g1 u p b) * ((1 / 2 : ℝ) * (f3 a v b + f3 b v a - f3 v a b))) := by
    rw [o1_abswap3 (fun a b p =>
      -((ig p b * g1 u p a) * ((1 / 2 : ℝ) * (f3 a v b + f3 b v a - f3 v a b))))]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      Finset.sum_congr rfl (fun p _ => ?_)))
    rw [higs p a, hf3s v b a]
    ring
  rw [hmerge]
  rw [o1_sum3_add
    (fun a b p => -((ig a p * g1 u p b) * ((1 / 2 : ℝ) * (f3 a v b + f3 b v a - f3 v a b))))
    (fun a b p => -((ig a p * g1 u p b) * ((1 / 2 : ℝ) * (f3 a v b + f3 b v a - f3 v a b))))]
  rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ p : Fin n,
      (-((ig a p * g1 u p b) * ((1 / 2 : ℝ) * (f3 a v b + f3 b v a - f3 v a b)))
       + -((ig a p * g1 u p b) * ((1 / 2 : ℝ) * (f3 a v b + f3 b v a - f3 v a b)))))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ p : Fin n,
          ((-((ig a p * g1 u p b) * f3 a v b) + -((ig a p * g1 u p b) * f3 b v a))
           + (ig a p * g1 u p b) * f3 v a b) from
    Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      Finset.sum_congr rfl (fun p _ => by ring)))]
  simp only [Finset.sum_add_distrib]
  have hT1 : (∑ a : Fin n, ∑ b : Fin n, ∑ p : Fin n, -((ig a p * g1 u p b) * f3 a v b))
      = -(∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g1 a u c * f3 b v c)) := by
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [show (∑ p : Fin n, ∑ a : Fin n, ∑ b : Fin n, -((ig a p * g1 u p b) * f3 a v b))
        = ∑ p : Fin n, ∑ a : Fin n, ∑ b : Fin n, -(ig p a * (g1 p u b * f3 a v b)) from
      Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun a _ =>
        Finset.sum_congr rfl (fun b _ => by rw [higs a p, hg1s u p b]; ring)))]
    simp only [Finset.sum_neg_distrib]
  have hT2 : (∑ a : Fin n, ∑ b : Fin n, ∑ p : Fin n, -((ig a p * g1 u p b) * f3 b v a))
      = -(∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g1 a u c * f3 c v b)) := by
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [show (∑ p : Fin n, ∑ a : Fin n, ∑ b : Fin n, -((ig a p * g1 u p b) * f3 b v a))
        = ∑ p : Fin n, ∑ a : Fin n, ∑ b : Fin n, -(ig p a * (g1 p u b * f3 b v a)) from
      Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun a _ =>
        Finset.sum_congr rfl (fun b _ => by rw [higs a p, hg1s u p b]; ring)))]
    simp only [Finset.sum_neg_distrib]
  have hT3 : (∑ a : Fin n, ∑ b : Fin n, ∑ p : Fin n, (ig a p * g1 u p b) * f3 v a b)
      = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g1 a u c * f3 v b c) := by
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun a _ =>
      Finset.sum_congr rfl (fun b _ => by rw [higs a p, hg1s u p b]; ring)))
  rw [hT1, hT2, hT3]
  ring

end RF1

end O1Abstract

namespace O1Abstract

variable {n : ℕ}

private lemma o1_const_pull3 (c : ℝ) (X : Fin n → Fin n → Fin n → ℝ) :
    (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, c * X a b l)
    = c * ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, X a b l := by
  simp only [← Finset.mul_sum]

private lemma o1_const_pull5 (c : ℝ) (X : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n, c * X a b l p k)
    = c * ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n, X a b l p k := by
  simp only [← Finset.mul_sum]

private lemma o1_ftriple3 (f3 : Fin n → Fin n → Fin n → ℝ) (W : Fin n → Fin n → Fin n → ℝ)
    (hW : ∀ a b l : Fin n, W a b l = W b a l) :
    (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, W a b l * (f3 a l b + f3 b l a - f3 l a b))
    = 2 * (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, W a b l * f3 a l b)
      - (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, W a b l * f3 l a b) := by
  rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, W a b l * (f3 a l b + f3 b l a - f3 l a b))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n,
          ((W a b l * f3 a l b + W a b l * f3 b l a) - W a b l * f3 l a b) from
    Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      Finset.sum_congr rfl (fun l _ => by ring)))]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hAB : (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, W a b l * f3 b l a)
      = ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, W a b l * f3 a l b := by
    rw [o1_abswap3 (fun a b l => W a b l * f3 b l a)]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      Finset.sum_congr rfl (fun l _ => ?_)))
    rw [hW b a l]
  rw [hAB]
  ring

private lemma o1_ftriple5 (f3 : Fin n → Fin n → Fin n → ℝ)
    (W : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ)
    (hW : ∀ a b l p k : Fin n, W a b l p k = W b a l p k) :
    (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
      W a b l p k * (f3 a l b + f3 b l a - f3 l a b))
    = 2 * (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
        W a b l p k * f3 a l b)
      - (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
        W a b l p k * f3 l a b) := by
  rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
      W a b l p k * (f3 a l b + f3 b l a - f3 l a b))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
          ((W a b l p k * f3 a l b + W a b l p k * f3 b l a) - W a b l p k * f3 l a b) from
    Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun k _ => by ring)))))]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hAB : (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
      W a b l p k * f3 b l a)
      = ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
          W a b l p k * f3 a l b := by
    rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
        W a b l p k * f3 b l a)
        = ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
            W b a l p k * f3 a l b from Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun k _ => ?_)))))
    rw [hW b a l p k]
  rw [hAB]
  ring

end O1Abstract

namespace O1Abstract

variable {n : ℕ}

section RF1B

variable (ig cg : Fin n → Fin n → ℝ) (dig g1 f3 : Fin n → Fin n → Fin n → ℝ)

private lemma o1_rf1b
    (hcol : ∀ l j : Fin n, (∑ k : Fin n, cg k j * ig k l) = if l = j then (1 : ℝ) else 0)
    (higs : ∀ a b : Fin n, ig a b = ig b a)
    (hdig2 : ∀ m a b : Fin n, dig m a b
      = -(∑ p : Fin n, (ig a p * g1 m p b + ig p b * g1 m p a)))
    (u v : Fin n) :
    (∑ k : Fin n, cg k v * (∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
      ∑ l : Fin n, dig u k l * (f3 a l b + f3 b l a - f3 l a b))))
    = -(∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (g1 u v q * f3 p q k))
      + (1 / 2 : ℝ) * (∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (g1 u v q * f3 q p k))
      - (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
          ig a b * (ig p l * (f3 a l b * (g1 u p k * cg k v))))
      + (1 / 2 : ℝ) * (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
          ig a b * (ig p l * (f3 l a b * (g1 u p k * cg k v)))) := by
  have hflat : (∑ k : Fin n, cg k v * (∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
      ∑ l : Fin n, dig u k l * (f3 a l b + f3 b l a - f3 l a b))))
      = ∑ k : Fin n, ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n,
          ((-((ig a b * ((1 / 2 : ℝ) * (f3 a l b + f3 b l a - f3 l a b))) * g1 u p l))
              * (cg k v * ig k p)
           + -(ig a b * (ig p l * ((1 / 2 : ℝ) *
              ((f3 a l b + f3 b l a - f3 l a b) * (g1 u p k * cg k v)))))) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hdig2 u k l, o1_neg_push1d (f3 a l b + f3 b l a - f3 l a b)
      (fun p => ig k p * g1 u p l + ig p l * g1 u p k)]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p _ => by ring)
  rw [hflat]
  simp only [Finset.sum_add_distrib]
  have hS1 : (∑ k : Fin n, ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n,
      (-((ig a b * ((1 / 2 : ℝ) * (f3 a l b + f3 b l a - f3 l a b))) * g1 u p l))
        * (cg k v * ig k p))
      = -(∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (g1 u v q * f3 p q k))
        + (1 / 2 : ℝ) * (∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n,
            ig k p * (g1 u v q * f3 q p k)) := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      Finset.sum_congr rfl (fun l _ => Finset.sum_comm)))]
    have hck : ∀ a b l p : Fin n,
        (∑ k : Fin n,
          (-((ig a b * ((1 / 2 : ℝ) * (f3 a l b + f3 b l a - f3 l a b))) * g1 u p l))
            * (cg k v * ig k p))
        = (-((ig a b * ((1 / 2 : ℝ) * (f3 a l b + f3 b l a - f3 l a b))) * g1 u p l))
            * (if p = v then (1 : ℝ) else 0) := by
      intro a b l p
      rw [← Finset.mul_sum, hcol p v]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun p _ => hck a b l p))))]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      Finset.sum_congr rfl (fun l _ => o1_sum_ite' (fun p =>
        -((ig a b * ((1 / 2 : ℝ) * (f3 a l b + f3 b l a - f3 l a b))) * g1 u p l)) v)))]
    rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n,
        -((ig a b * ((1 / 2 : ℝ) * (f3 a l b + f3 b l a - f3 l a b))) * g1 u v l))
        = ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n,
            (-((1 / 2 : ℝ) * (ig a b * g1 u v l))) * (f3 a l b + f3 b l a - f3 l a b) from
      Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
        Finset.sum_congr rfl (fun l _ => by ring)))]
    rw [o1_ftriple3 f3 (fun a b l => -((1 / 2 : ℝ) * (ig a b * g1 u v l)))
      (fun a b l => by
        change -((1 / 2 : ℝ) * (ig a b * g1 u v l)) = -((1 / 2 : ℝ) * (ig b a * g1 u v l))
        rw [higs a b])]
    have hE : (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n,
        (-((1 / 2 : ℝ) * (ig a b * g1 u v l))) * f3 a l b)
        = (-(1 / 2 : ℝ)) * (∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n,
            ig k p * (g1 u v q * f3 p q k)) := by
      rw [Finset.sum_comm]
      rw [show (∑ b : Fin n, ∑ a : Fin n, ∑ l : Fin n,
          (-((1 / 2 : ℝ) * (ig a b * g1 u v l))) * f3 a l b)
          = ∑ b : Fin n, ∑ a : Fin n, ∑ l : Fin n,
              (-(1 / 2 : ℝ)) * (ig b a * (g1 u v l * f3 a l b)) from
        Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun a _ =>
          Finset.sum_congr rfl (fun l _ => by rw [higs a b]; ring)))]
      rw [o1_const_pull3]
    have hF : (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n,
        (-((1 / 2 : ℝ) * (ig a b * g1 u v l))) * f3 l a b)
        = (-(1 / 2 : ℝ)) * (∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n,
            ig k p * (g1 u v q * f3 q p k)) := by
      rw [Finset.sum_comm]
      rw [show (∑ b : Fin n, ∑ a : Fin n, ∑ l : Fin n,
          (-((1 / 2 : ℝ) * (ig a b * g1 u v l))) * f3 l a b)
          = ∑ b : Fin n, ∑ a : Fin n, ∑ l : Fin n,
              (-(1 / 2 : ℝ)) * (ig b a * (g1 u v l * f3 l a b)) from
        Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun a _ =>
          Finset.sum_congr rfl (fun l _ => by rw [higs a b]; ring)))]
      rw [o1_const_pull3]
    rw [hE, hF]
    ring
  have hS2 : (∑ k : Fin n, ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n,
      -(ig a b * (ig p l * ((1 / 2 : ℝ) *
        ((f3 a l b + f3 b l a - f3 l a b) * (g1 u p k * cg k v))))))
      = -(∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
          ig a b * (ig p l * (f3 a l b * (g1 u p k * cg k v))))
        + (1 / 2 : ℝ) * (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
          ig a b * (ig p l * (f3 l a b * (g1 u p k * cg k v)))) := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      Finset.sum_congr rfl (fun l _ => Finset.sum_comm)))]
    rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
        -(ig a b * (ig p l * ((1 / 2 : ℝ) *
          ((f3 a l b + f3 b l a - f3 l a b) * (g1 u p k * cg k v))))))
        = ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
            (-((1 / 2 : ℝ) * (ig a b * (ig p l * (g1 u p k * cg k v)))))
              * (f3 a l b + f3 b l a - f3 l a b) from
      Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
        Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun p _ =>
          Finset.sum_congr rfl (fun k _ => by ring)))))]
    rw [o1_ftriple5 f3
      (fun a b l p k => -((1 / 2 : ℝ) * (ig a b * (ig p l * (g1 u p k * cg k v)))))
      (fun a b l p k => by
        change -((1 / 2 : ℝ) * (ig a b * (ig p l * (g1 u p k * cg k v))))
          = -((1 / 2 : ℝ) * (ig b a * (ig p l * (g1 u p k * cg k v))))
        rw [higs a b])]
    have hR1 : (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
        (-((1 / 2 : ℝ) * (ig a b * (ig p l * (g1 u p k * cg k v))))) * f3 a l b)
        = (-(1 / 2 : ℝ)) * (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
            ig a b * (ig p l * (f3 a l b * (g1 u p k * cg k v)))) := by
      rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
          (-((1 / 2 : ℝ) * (ig a b * (ig p l * (g1 u p k * cg k v))))) * f3 a l b)
          = ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
              (-(1 / 2 : ℝ)) * (ig a b * (ig p l * (f3 a l b * (g1 u p k * cg k v)))) from
        Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
          Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun p _ =>
            Finset.sum_congr rfl (fun k _ => by ring)))))]
      rw [o1_const_pull5]
    have hR2 : (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
        (-((1 / 2 : ℝ) * (ig a b * (ig p l * (g1 u p k * cg k v))))) * f3 l a b)
        = (-(1 / 2 : ℝ)) * (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
            ig a b * (ig p l * (f3 l a b * (g1 u p k * cg k v)))) := by
      rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
          (-((1 / 2 : ℝ) * (ig a b * (ig p l * (g1 u p k * cg k v))))) * f3 l a b)
          = ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
              (-(1 / 2 : ℝ)) * (ig a b * (ig p l * (f3 l a b * (g1 u p k * cg k v)))) from
        Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
          Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun p _ =>
            Finset.sum_congr rfl (fun k _ => by ring)))))]
      rw [o1_const_pull5]
    rw [hR1, hR2]
    ring
  rw [hS1, hS2]
  ring

end RF1B

private lemma o1_mul_sum_sum (x y : ℝ) (A B : Fin n → ℝ) :
    (x * (y * ∑ l : Fin n, A l)) * (∑ c : Fin n, B c)
    = ∑ l : Fin n, ∑ c : Fin n, (y * (x * B c)) * A l := by
  rw [show (x * (y * ∑ l : Fin n, A l)) * (∑ c : Fin n, B c)
      = (∑ l : Fin n, A l) * (∑ c : Fin n, B c) * (x * y) from by ring]
  rw [Finset.sum_mul_sum]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun c _ => by ring)

section RLVF

variable (ig cg : Fin n → Fin n → ℝ) (dg g1 f3 : Fin n → Fin n → Fin n → ℝ)

private lemma o1_rlvf
    (higs : ∀ a b : Fin n, ig a b = ig b a)
    (hcgs : ∀ a b : Fin n, cg a b = cg b a)
    (hg1s : ∀ a b k : Fin n, g1 a b k = g1 b a k)
    (hdg2 : ∀ m a b : Fin n, dg m a b
      = (∑ c : Fin n, cg b c * g1 m a c) + (∑ c : Fin n, cg a c * g1 m b c))
    (u v : Fin n) :
    (∑ k : Fin n, (∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
      ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b))) * dg k u v)
    = (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
        ig a b * (ig p l * (f3 a l b * (g1 u p k * cg k v))))
      + (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
        ig a b * (ig p l * (f3 a l b * (g1 v p k * cg k u))))
      - (1 / 2 : ℝ) * (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
        ig a b * (ig p l * (f3 l a b * (g1 u p k * cg k v))))
      - (1 / 2 : ℝ) * (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
        ig a b * (ig p l * (f3 l a b * (g1 v p k * cg k u)))) := by
  have hsplit : (∑ k : Fin n, (∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
      ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b))) * dg k u v)
      = (∑ k : Fin n, (∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
          ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b)))
            * (∑ c : Fin n, cg v c * g1 k u c))
        + ∑ k : Fin n, (∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
            ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b)))
              * (∑ c : Fin n, cg u c * g1 k v c) := by
    rw [show (∑ k : Fin n, (∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
        ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b))) * dg k u v)
        = ∑ k : Fin n, ((∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
            ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b)))
              * (∑ c : Fin n, cg v c * g1 k u c)
           + (∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
            ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b)))
              * (∑ c : Fin n, cg u c * g1 k v c)) from
      Finset.sum_congr rfl (fun k _ => by rw [hdg2 k u v, mul_add])]
    rw [Finset.sum_add_distrib]
  rw [hsplit]
  have hhalf : ∀ u' v' : Fin n,
      (∑ k : Fin n, (∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
        ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b)))
          * (∑ c : Fin n, cg v' c * g1 k u' c))
      = (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
          ig a b * (ig p l * (f3 a l b * (g1 u' p k * cg k v'))))
        - (1 / 2 : ℝ) * (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
          ig a b * (ig p l * (f3 l a b * (g1 u' p k * cg k v')))) := by
    intro u' v'
    have hflat : (∑ k : Fin n, (∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
        ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b)))
          * (∑ c : Fin n, cg v' c * g1 k u' c))
        = ∑ k : Fin n, ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ c : Fin n,
            ((1 / 2 : ℝ) * (ig a b * (ig k l * (cg v' c * g1 k u' c))))
              * (f3 a l b + f3 b l a - f3 l a b) := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [o1_mul_sum_sum (ig a b) (1 / 2 : ℝ)
        (fun l => ig k l * (f3 a l b + f3 b l a - f3 l a b))
        (fun c => cg v' c * g1 k u' c)]
      refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun c _ => ?_))
      ring
    rw [hflat]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_comm))]
    rw [o1_ftriple5 f3
      (fun a b l k c => (1 / 2 : ℝ) * (ig a b * (ig k l * (cg v' c * g1 k u' c))))
      (fun a b l k c => by
        change (1 / 2 : ℝ) * (ig a b * (ig k l * (cg v' c * g1 k u' c)))
          = (1 / 2 : ℝ) * (ig b a * (ig k l * (cg v' c * g1 k u' c)))
        rw [higs a b])]
    have hB1 : (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ k : Fin n, ∑ c : Fin n,
        ((1 / 2 : ℝ) * (ig a b * (ig k l * (cg v' c * g1 k u' c)))) * f3 a l b)
        = (1 / 2 : ℝ) * (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
            ig a b * (ig p l * (f3 a l b * (g1 u' p k * cg k v')))) := by
      rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ k : Fin n, ∑ c : Fin n,
          ((1 / 2 : ℝ) * (ig a b * (ig k l * (cg v' c * g1 k u' c)))) * f3 a l b)
          = ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ k : Fin n, ∑ c : Fin n,
              (1 / 2 : ℝ) * (ig a b * (ig k l * (f3 a l b * (g1 u' k c * cg c v')))) from
        Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
          Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k _ =>
            Finset.sum_congr rfl (fun c _ => by
              rw [hcgs v' c, hg1s k u' c]; ring)))))]
      rw [o1_const_pull5]
    have hB2 : (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ k : Fin n, ∑ c : Fin n,
        ((1 / 2 : ℝ) * (ig a b * (ig k l * (cg v' c * g1 k u' c)))) * f3 l a b)
        = (1 / 2 : ℝ) * (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ p : Fin n, ∑ k : Fin n,
            ig a b * (ig p l * (f3 l a b * (g1 u' p k * cg k v')))) := by
      rw [show (∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ k : Fin n, ∑ c : Fin n,
          ((1 / 2 : ℝ) * (ig a b * (ig k l * (cg v' c * g1 k u' c)))) * f3 l a b)
          = ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ∑ k : Fin n, ∑ c : Fin n,
              (1 / 2 : ℝ) * (ig a b * (ig k l * (f3 l a b * (g1 u' k c * cg c v')))) from
        Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
          Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k _ =>
            Finset.sum_congr rfl (fun c _ => by
              rw [hcgs v' c, hg1s k u' c]; ring)))))]
      rw [o1_const_pull5]
    rw [hB1, hB2]
    ring
  rw [hhalf u v, hhalf v u]
  ring

end RLVF

end O1Abstract

namespace O1Abstract

variable {n : ℕ}

section Tail

variable (ig : Fin n → Fin n → ℝ) (g0 f3 : Fin n → Fin n → Fin n → ℝ)

private lemma o1_tail
    (higs : ∀ a b : Fin n, ig a b = ig b a)
    (hg0s : ∀ a b k : Fin n, g0 a b k = g0 b a k)
    (hf3s : ∀ d a b : Fin n, f3 d a b = f3 d b a)
    (i j : Fin n) :
    (∑ k₁ : Fin n, ∑ l : Fin n, ig k₁ l *
      ((-(∑ r : Fin n, (g0 l j r * f3 i r k₁ + g0 l k₁ r * f3 i j r + g0 i l r * f3 r j k₁
          + g0 i j r * f3 l r k₁ + g0 i k₁ r * f3 l j r)))
       + (-(∑ r : Fin n, (g0 l i r * f3 j r k₁ + g0 l k₁ r * f3 j i r + g0 j l r * f3 r i k₁
          + g0 j i r * f3 l r k₁ + g0 j k₁ r * f3 l i r)))
       - (-(∑ r : Fin n, (g0 j l r * f3 i r k₁ + g0 j k₁ r * f3 i l r + g0 i j r * f3 r l k₁
          + g0 i l r * f3 j r k₁ + g0 i k₁ r * f3 j l r)))))
    = (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a j c * f3 i b c))
      + (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a i c * f3 j b c))
      - (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a i c * f3 c j b))
      - (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a j c * f3 c i b))
      - (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a i c * f3 b j c))
      - (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a j c * f3 b i c))
      - 2 * (∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (g0 i j q * f3 p q k))
      + (∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (g0 i j q * f3 q p k))
      - (∑ a : Fin n, ∑ b : Fin n, ∑ w : Fin n, ig a b * (g0 a b w * f3 i j w))
      - (∑ a : Fin n, ∑ b : Fin n, ∑ w : Fin n, ig a b * (g0 a b w * f3 j i w)) := by
  have hcomb : ∀ k₁ l : Fin n, ig k₁ l *
      ((-(∑ r : Fin n, (g0 l j r * f3 i r k₁ + g0 l k₁ r * f3 i j r + g0 i l r * f3 r j k₁
          + g0 i j r * f3 l r k₁ + g0 i k₁ r * f3 l j r)))
       + (-(∑ r : Fin n, (g0 l i r * f3 j r k₁ + g0 l k₁ r * f3 j i r + g0 j l r * f3 r i k₁
          + g0 j i r * f3 l r k₁ + g0 j k₁ r * f3 l i r)))
       - (-(∑ r : Fin n, (g0 j l r * f3 i r k₁ + g0 j k₁ r * f3 i l r + g0 i j r * f3 r l k₁
          + g0 i l r * f3 j r k₁ + g0 i k₁ r * f3 j l r))))
      = ∑ r : Fin n,
          (((ig k₁ l * (g0 j l r * f3 i r k₁) + ig k₁ l * (g0 j k₁ r * f3 i l r)
              + ig k₁ l * (g0 i j r * f3 r l k₁) + ig k₁ l * (g0 i l r * f3 j r k₁)
              + ig k₁ l * (g0 i k₁ r * f3 j l r))
            - (ig k₁ l * (g0 l j r * f3 i r k₁) + ig k₁ l * (g0 l k₁ r * f3 i j r)
              + ig k₁ l * (g0 i l r * f3 r j k₁) + ig k₁ l * (g0 i j r * f3 l r k₁)
              + ig k₁ l * (g0 i k₁ r * f3 l j r)))
           - (ig k₁ l * (g0 l i r * f3 j r k₁) + ig k₁ l * (g0 l k₁ r * f3 j i r)
              + ig k₁ l * (g0 j l r * f3 r i k₁) + ig k₁ l * (g0 j i r * f3 l r k₁)
              + ig k₁ l * (g0 j k₁ r * f3 l i r))) := by
    intro k₁ l
    rw [show ∀ P Q R : Fin n → ℝ, (-(∑ r : Fin n, P r)) + (-(∑ r : Fin n, Q r))
        - (-(∑ r : Fin n, R r)) = (∑ r : Fin n, R r) - (∑ r : Fin n, P r) - (∑ r : Fin n, Q r)
      from fun P Q R => by ring]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    ring
  rw [Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ => hcomb k₁ l))]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hp1 : (∑ k₁ : Fin n, ∑ l : Fin n, ∑ r : Fin n, ig k₁ l * (g0 l j r * f3 i r k₁))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a j c * f3 i b c) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k₁ _ =>
      Finset.sum_congr rfl (fun r _ => by rw [higs k₁ l, hf3s i r k₁])))
  have hp2 : (∑ k₁ : Fin n, ∑ l : Fin n, ∑ r : Fin n, ig k₁ l * (g0 l k₁ r * f3 i j r))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ w : Fin n, ig a b * (g0 a b w * f3 i j w) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k₁ _ =>
      Finset.sum_congr rfl (fun r _ => by rw [higs k₁ l])))
  have hp3 : (∑ k₁ : Fin n, ∑ l : Fin n, ∑ r : Fin n, ig k₁ l * (g0 i l r * f3 r j k₁))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a i c * f3 c j b) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k₁ _ =>
      Finset.sum_congr rfl (fun r _ => by rw [higs k₁ l, hg0s i l r])))
  have hp4 : (∑ k₁ : Fin n, ∑ l : Fin n, ∑ r : Fin n, ig k₁ l * (g0 i j r * f3 l r k₁))
      = ∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (g0 i j q * f3 p q k) :=
    Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ =>
      Finset.sum_congr rfl (fun r _ => by ring)))
  have hp5 : (∑ k₁ : Fin n, ∑ l : Fin n, ∑ r : Fin n, ig k₁ l * (g0 i k₁ r * f3 l j r))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a i c * f3 b j c) :=
    Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ =>
      Finset.sum_congr rfl (fun r _ => by rw [hg0s i k₁ r])))
  have hq1 : (∑ k₁ : Fin n, ∑ l : Fin n, ∑ r : Fin n, ig k₁ l * (g0 l i r * f3 j r k₁))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a i c * f3 j b c) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k₁ _ =>
      Finset.sum_congr rfl (fun r _ => by rw [higs k₁ l, hf3s j r k₁])))
  have hq2 : (∑ k₁ : Fin n, ∑ l : Fin n, ∑ r : Fin n, ig k₁ l * (g0 l k₁ r * f3 j i r))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ w : Fin n, ig a b * (g0 a b w * f3 j i w) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k₁ _ =>
      Finset.sum_congr rfl (fun r _ => by rw [higs k₁ l])))
  have hq3 : (∑ k₁ : Fin n, ∑ l : Fin n, ∑ r : Fin n, ig k₁ l * (g0 j l r * f3 r i k₁))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a j c * f3 c i b) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k₁ _ =>
      Finset.sum_congr rfl (fun r _ => by rw [higs k₁ l, hg0s j l r])))
  have hq4 : (∑ k₁ : Fin n, ∑ l : Fin n, ∑ r : Fin n, ig k₁ l * (g0 j i r * f3 l r k₁))
      = ∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (g0 i j q * f3 p q k) :=
    Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ =>
      Finset.sum_congr rfl (fun r _ => by rw [hg0s j i r])))
  have hq5 : (∑ k₁ : Fin n, ∑ l : Fin n, ∑ r : Fin n, ig k₁ l * (g0 j k₁ r * f3 l i r))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a j c * f3 b i c) :=
    Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ =>
      Finset.sum_congr rfl (fun r _ => by rw [hg0s j k₁ r])))
  have hr1 : (∑ k₁ : Fin n, ∑ l : Fin n, ∑ r : Fin n, ig k₁ l * (g0 j l r * f3 i r k₁))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a j c * f3 i b c) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k₁ _ =>
      Finset.sum_congr rfl (fun r _ => by rw [higs k₁ l, hg0s j l r, hf3s i r k₁])))
  have hr2 : (∑ k₁ : Fin n, ∑ l : Fin n, ∑ r : Fin n, ig k₁ l * (g0 j k₁ r * f3 i l r))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a j c * f3 i b c) :=
    Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ =>
      Finset.sum_congr rfl (fun r _ => by rw [hg0s j k₁ r])))
  have hr3 : (∑ k₁ : Fin n, ∑ l : Fin n, ∑ r : Fin n, ig k₁ l * (g0 i j r * f3 r l k₁))
      = ∑ k : Fin n, ∑ p : Fin n, ∑ q : Fin n, ig k p * (g0 i j q * f3 q p k) :=
    Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ =>
      Finset.sum_congr rfl (fun r _ => by ring)))
  have hr4 : (∑ k₁ : Fin n, ∑ l : Fin n, ∑ r : Fin n, ig k₁ l * (g0 i l r * f3 j r k₁))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a i c * f3 j b c) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k₁ _ =>
      Finset.sum_congr rfl (fun r _ => by rw [higs k₁ l, hg0s i l r, hf3s j r k₁])))
  have hr5 : (∑ k₁ : Fin n, ∑ l : Fin n, ∑ r : Fin n, ig k₁ l * (g0 i k₁ r * f3 j l r))
      = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ig a b * (g0 a i c * f3 j b c) :=
    Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ =>
      Finset.sum_congr rfl (fun r _ => by rw [hg0s i k₁ r])))
  rw [hp1, hp2, hp3, hp4, hp5, hq1, hq2, hq3, hq4, hq5, hr1, hr2, hr3, hr4, hr5]
  ring

end Tail

end O1Abstract

namespace O1Abstract

variable {n : ℕ}

set_option maxHeartbeats 3200000 in
private lemma o1_master (ig cg : Fin n → Fin n → ℝ)
    (dg gb dig g1 g0 gbg f3 : Fin n → Fin n → Fin n → ℝ) (w1 : Fin n → ℝ)
    (hcol : ∀ l j : Fin n, (∑ k : Fin n, cg k j * ig k l) = if l = j then (1 : ℝ) else 0)
    (higs : ∀ a b : Fin n, ig a b = ig b a)
    (hcgs : ∀ a b : Fin n, cg a b = cg b a)
    (hf3s : ∀ d a b : Fin n, f3 d a b = f3 d b a)
    (hg1s : ∀ a b k : Fin n, g1 a b k = g1 b a k)
    (hg0s : ∀ a b k : Fin n, g0 a b k = g0 b a k)
    (hgbdef : ∀ a b l : Fin n, gb a b l = dg a l b + dg b l a - dg l a b)
    (hdgs : ∀ m a b : Fin n, dg m a b = dg m b a)
    (hga1 : ∀ a b k : Fin n, g1 a b k = (1 / 2 : ℝ) * ∑ l : Fin n, ig k l * gb a b l)
    (hdig : ∀ m a b : Fin n, dig m a b
      = -(∑ x : Fin n, ∑ y : Fin n, ig a x * ig y b * dg m x y))
    (i j : Fin n) :
    ((∑ w : Fin n, w1 w * f3 w i j)
      + ((∑ k₁ : Fin n, ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n,
            ig k₁ p * (ig l₁ m * (f3 i m p * (∑ q : Fin n, (g1 l₁ j q - g0 l₁ j q) * cg q k₁))))
        - (∑ k₁ : Fin n, ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n,
            ig k₁ p * (ig l₁ m * (f3 i m p * (∑ q : Fin n, (g1 k₁ l₁ q - gbg k₁ l₁ q) * cg q j))))
        - (∑ w : Fin n, (∑ a : Fin n, ∑ b : Fin n, ig a b * (g1 a b w - g0 a b w)) * f3 i j w)
        - (∑ k₁ : Fin n, ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n,
            ig k₁ p * (ig l₁ m * (f3 m j p * (∑ q : Fin n, (g1 k₁ i q - g0 k₁ i q) * cg q l₁))))
        - (∑ k₁ : Fin n, ∑ p : Fin n,
            ig k₁ p * (∑ q : Fin n, (g1 j i q - g0 j i q) * f3 p q k₁))
        - (∑ k₁ : Fin n, ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n,
            ig k₁ p * (ig l₁ m * (f3 m j p * (∑ q : Fin n, (g1 l₁ i q - g0 l₁ i q) * cg q k₁)))))
      + ((∑ k₁ : Fin n, ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n,
            ig k₁ p * (ig l₁ m * (f3 j m p * (∑ q : Fin n, (g1 l₁ i q - g0 l₁ i q) * cg q k₁))))
        - (∑ k₁ : Fin n, ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n,
            ig k₁ p * (ig l₁ m * (f3 j m p * (∑ q : Fin n, (g1 k₁ l₁ q - gbg k₁ l₁ q) * cg q i))))
        - (∑ w : Fin n, (∑ a : Fin n, ∑ b : Fin n, ig a b * (g1 a b w - g0 a b w)) * f3 j i w)
        - (∑ k₁ : Fin n, ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n,
            ig k₁ p * (ig l₁ m * (f3 m i p * (∑ q : Fin n, (g1 k₁ j q - g0 k₁ j q) * cg q l₁))))
        - (∑ k₁ : Fin n, ∑ p : Fin n,
            ig k₁ p * (∑ q : Fin n, (g1 i j q - g0 i j q) * f3 p q k₁))
        - (∑ k₁ : Fin n, ∑ p : Fin n, ∑ l₁ : Fin n, ∑ m : Fin n,
            ig k₁ p * (ig l₁ m * (f3 m i p * (∑ q : Fin n, (g1 l₁ j q - g0 l₁ j q) * cg q k₁)))))
      + (∑ k₁ : Fin n, ∑ p : Fin n,
          ig k₁ p * (∑ q : Fin n, (g1 j i q - g0 j i q) * f3 q p k₁)))
    + (∑ k₁ : Fin n, ∑ l : Fin n, ig k₁ l *
        ((-(∑ r : Fin n, (g0 l j r * f3 i r k₁ + g0 l k₁ r * f3 i j r + g0 i l r * f3 r j k₁
            + g0 i j r * f3 l r k₁ + g0 i k₁ r * f3 l j r)))
         + (-(∑ r : Fin n, (g0 l i r * f3 j r k₁ + g0 l k₁ r * f3 j i r + g0 j l r * f3 r i k₁
            + g0 j i r * f3 l r k₁ + g0 j k₁ r * f3 l i r)))
         - (-(∑ r : Fin n, (g0 j l r * f3 i r k₁ + g0 j k₁ r * f3 i l r + g0 i j r * f3 r l k₁
            + g0 i l r * f3 j r k₁ + g0 i k₁ r * f3 j l r)))))
    = ((∑ k : Fin n, cg k j *
          ((∑ a : Fin n, ∑ b : Fin n, dig i a b * ((1 / 2 : ℝ) *
              ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b)))
           + ∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
              ∑ l : Fin n, dig i k l * (f3 a l b + f3 b l a - f3 l a b))))
      + ∑ k : Fin n, cg i k *
          ((∑ a : Fin n, ∑ b : Fin n, dig j a b * ((1 / 2 : ℝ) *
              ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b)))
           + ∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
              ∑ l : Fin n, dig j k l * (f3 a l b + f3 b l a - f3 l a b))))
    + ((∑ k : Fin n, (∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
          ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b))) * dg k i j)
      + (∑ k : Fin n, w1 k * f3 k i j)
      + (∑ k : Fin n, cg k j * (∑ a : Fin n, ∑ b : Fin n,
          ((-(∑ q : Fin n, ∑ p : Fin n, ig a p * f3 i p q * ig q b)) * (g1 a b k - gbg a b k)
           + ig a b * ((1 / 2 : ℝ) * ∑ l : Fin n,
              (-(∑ q : Fin n, ∑ p : Fin n, ig k p * f3 i p q * ig q l)) * gb a b l))))
      + (∑ k : Fin n, cg i k * (∑ a : Fin n, ∑ b : Fin n,
          ((-(∑ q : Fin n, ∑ p : Fin n, ig a p * f3 j p q * ig q b)) * (g1 a b k - gbg a b k)
           + ig a b * ((1 / 2 : ℝ) * ∑ l : Fin n,
              (-(∑ q : Fin n, ∑ p : Fin n, ig k p * f3 j p q * ig q l)) * gb a b l))))) := by
  have hgb2 := o1_hgb2 ig cg gb g1 hcol hcgs hga1
  have hdg2 := o1_hdg2 ig cg dg gb g1 hcol hcgs hgbdef hdgs hga1
  have hdig2 := o1_hdig2 ig cg dg gb dig g1 hcol higs hcgs hgbdef hdgs hga1 hdig
  have hT2 := o1_quadAC ig cg g1 g0 (fun m p => f3 i m p) hcol hcgs j
  have hT5 := o1_quadB ig cg g1 g0 (fun m p => f3 m j p) hcol hcgs i
  have hT7 := o1_quadAC ig cg g1 g0 (fun m p => f3 m j p) hcol hcgs i
  have hT8 := o1_quadAC ig cg g1 g0 (fun m p => f3 j m p) hcol hcgs i
  have hT11 := o1_quadB ig cg g1 g0 (fun m p => f3 m i p) hcol hcgs j
  have hT13 := o1_quadAC ig cg g1 g0 (fun m p => f3 m i p) hcol hcgs j
  have hT4 := o1_vf0exp ig g1 g0 f3 i j
  have hT10 := o1_vf0exp ig g1 g0 f3 j i
  have hT6 := (o1_pullE ig g1 g0 f3 j i).trans
    (congrArg₂ (· - ·) (o1_swapE ig f3 g1 hg1s j i) (o1_swapE ig f3 g0 hg0s j i))
  have hT12 := o1_pullE ig g1 g0 f3 i j
  have hT14 := (o1_pullF ig g1 g0 f3 j i).trans
    (congrArg₂ (· - ·) (o1_swapF ig f3 g1 hg1s j i) (o1_swapF ig f3 g0 hg0s j i))
  have hTail := o1_tail ig g0 f3 higs hg0s hf3s i j
  have hFRsplit : ∀ u' v' : Fin n,
      (∑ k : Fin n, cg k v' *
        ((∑ a : Fin n, ∑ b : Fin n, dig u' a b * ((1 / 2 : ℝ) *
            ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b)))
         + ∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
            ∑ l : Fin n, dig u' k l * (f3 a l b + f3 b l a - f3 l a b))))
      = (∑ k : Fin n, cg k v' * (∑ a : Fin n, ∑ b : Fin n, dig u' a b * ((1 / 2 : ℝ) *
            ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b))))
        + ∑ k : Fin n, cg k v' * (∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
            ∑ l : Fin n, dig u' k l * (f3 a l b + f3 b l a - f3 l a b))) := by
    intro u' v'
    rw [show (∑ k : Fin n, cg k v' *
        ((∑ a : Fin n, ∑ b : Fin n, dig u' a b * ((1 / 2 : ℝ) *
            ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b)))
         + ∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
            ∑ l : Fin n, dig u' k l * (f3 a l b + f3 b l a - f3 l a b))))
        = ∑ k : Fin n,
            (cg k v' * (∑ a : Fin n, ∑ b : Fin n, dig u' a b * ((1 / 2 : ℝ) *
              ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b)))
             + cg k v' * (∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
              ∑ l : Fin n, dig u' k l * (f3 a l b + f3 b l a - f3 l a b)))) from
      Finset.sum_congr rfl (fun k _ => mul_add _ _ _)]
    rw [Finset.sum_add_distrib]
  have hCDsplit : ∀ u' v' : Fin n,
      (∑ k : Fin n, cg k v' * (∑ a : Fin n, ∑ b : Fin n,
        ((-(∑ q : Fin n, ∑ p : Fin n, ig a p * f3 u' p q * ig q b)) * (g1 a b k - gbg a b k)
         + ig a b * ((1 / 2 : ℝ) * ∑ l : Fin n,
            (-(∑ q : Fin n, ∑ p : Fin n, ig k p * f3 u' p q * ig q l)) * gb a b l))))
      = (∑ k : Fin n, cg k v' * (∑ a : Fin n, ∑ b : Fin n,
          (-(∑ q : Fin n, ∑ p : Fin n, ig a p * f3 u' p q * ig q b)) * (g1 a b k - gbg a b k)))
        + ∑ k : Fin n, cg k v' * (∑ a : Fin n, ∑ b : Fin n,
            ig a b * ((1 / 2 : ℝ) * ∑ l : Fin n,
              (-(∑ q : Fin n, ∑ p : Fin n, ig k p * f3 u' p q * ig q l)) * gb a b l)) := by
    intro u' v'
    rw [show (∑ k : Fin n, cg k v' * (∑ a : Fin n, ∑ b : Fin n,
        ((-(∑ q : Fin n, ∑ p : Fin n, ig a p * f3 u' p q * ig q b)) * (g1 a b k - gbg a b k)
         + ig a b * ((1 / 2 : ℝ) * ∑ l : Fin n,
            (-(∑ q : Fin n, ∑ p : Fin n, ig k p * f3 u' p q * ig q l)) * gb a b l))))
        = ∑ k : Fin n,
            (cg k v' * (∑ a : Fin n, ∑ b : Fin n,
              (-(∑ q : Fin n, ∑ p : Fin n, ig a p * f3 u' p q * ig q b)) * (g1 a b k - gbg a b k))
             + cg k v' * (∑ a : Fin n, ∑ b : Fin n,
                ig a b * ((1 / 2 : ℝ) * ∑ l : Fin n,
                  (-(∑ q : Fin n, ∑ p : Fin n, ig k p * f3 u' p q * ig q l)) * gb a b l))) from
      Finset.sum_congr rfl (fun k _ => by
        rw [show (∑ a : Fin n, ∑ b : Fin n,
            ((-(∑ q : Fin n, ∑ p : Fin n, ig a p * f3 u' p q * ig q b)) * (g1 a b k - gbg a b k)
             + ig a b * ((1 / 2 : ℝ) * ∑ l : Fin n,
                (-(∑ q : Fin n, ∑ p : Fin n, ig k p * f3 u' p q * ig q l)) * gb a b l)))
            = (∑ a : Fin n, ∑ b : Fin n,
                (-(∑ q : Fin n, ∑ p : Fin n, ig a p * f3 u' p q * ig q b)) * (g1 a b k - gbg a b k))
              + ∑ a : Fin n, ∑ b : Fin n,
                  ig a b * ((1 / 2 : ℝ) * ∑ l : Fin n,
                    (-(∑ q : Fin n, ∑ p : Fin n, ig k p * f3 u' p q * ig q l)) * gb a b l) from by
          simp only [Finset.sum_add_distrib]]
        rw [mul_add])]
    rw [Finset.sum_add_distrib]
  have hflipFR : (∑ k : Fin n, cg i k *
      ((∑ a : Fin n, ∑ b : Fin n, dig j a b * ((1 / 2 : ℝ) *
          ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b)))
       + ∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
          ∑ l : Fin n, dig j k l * (f3 a l b + f3 b l a - f3 l a b))))
      = ∑ k : Fin n, cg k i *
          ((∑ a : Fin n, ∑ b : Fin n, dig j a b * ((1 / 2 : ℝ) *
              ∑ l : Fin n, ig k l * (f3 a l b + f3 b l a - f3 l a b)))
           + ∑ a : Fin n, ∑ b : Fin n, ig a b * ((1 / 2 : ℝ) *
              ∑ l : Fin n, dig j k l * (f3 a l b + f3 b l a - f3 l a b))) :=
    Finset.sum_congr rfl (fun k _ => by rw [hcgs i k])
  have hflipCD : (∑ k : Fin n, cg i k * (∑ a : Fin n, ∑ b : Fin n,
      ((-(∑ q : Fin n, ∑ p : Fin n, ig a p * f3 j p q * ig q b)) * (g1 a b k - gbg a b k)
       + ig a b * ((1 / 2 : ℝ) * ∑ l : Fin n,
          (-(∑ q : Fin n, ∑ p : Fin n, ig k p * f3 j p q * ig q l)) * gb a b l))))
      = ∑ k : Fin n, cg k i * (∑ a : Fin n, ∑ b : Fin n,
          ((-(∑ q : Fin n, ∑ p : Fin n, ig a p * f3 j p q * ig q b)) * (g1 a b k - gbg a b k)
           + ig a b * ((1 / 2 : ℝ) * ∑ l : Fin n,
              (-(∑ q : Fin n, ∑ p : Fin n, ig k p * f3 j p q * ig q l)) * gb a b l))) :=
    Finset.sum_congr rfl (fun k _ => by rw [hcgs i k])
  rw [hflipFR, hflipCD]
  rw [hFRsplit i j, hFRsplit j i, hCDsplit i j, hCDsplit j i]
  rw [o1_rf1a ig cg dig g1 f3 hcol higs hf3s hg1s hdig2 i j]
  rw [o1_rf1a ig cg dig g1 f3 hcol higs hf3s hg1s hdig2 j i]
  rw [o1_rf1b ig cg dig g1 f3 hcol higs hdig2 i j]
  rw [o1_rf1b ig cg dig g1 f3 hcol higs hdig2 j i]
  rw [o1_rlvf ig cg dg g1 f3 higs hcgs hg1s hdg2 i j]
  rw [o1_rq3 ig cg g1 gbg f3 higs hf3s i j]
  rw [o1_rq3 ig cg g1 gbg f3 higs hf3s j i]
  rw [o1_rg7 ig cg gb g1 f3 hcol higs hgb2 i j]
  rw [o1_rg7 ig cg gb g1 f3 hcol higs hgb2 j i]
  rw [o1_swapE ig f3 g1 hg1s j i, o1_swapF ig f3 g1 hg1s j i]
  rw [hT2, hT5, hT7, hT8, hT11, hT13, hT4, hT10, hT6, hT12, hT14, hTail]
  ring

end O1Abstract

private lemma lieArm_chartGramMatrix_symm (g : SmoothRiemannianMetric I M) (x : M)
    (a b : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) g x x a b
    = DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) g x x b a := by
  rw [DifferentialGeometry.Integral.Measure.chartGramMatrix_apply,
    DifferentialGeometry.Integral.Measure.chartGramMatrix_apply]
  exact g.symm _ _ _

private lemma lieArm_realizedGramDeriv_symm (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (a b : Fin (Module.finrank ℝ E)) :
    realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b
    = realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x b a := by
  funext y
  change DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I)
      (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x a b y
    - DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I)
      (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x a b y
    = DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I)
      (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x b a y
    - DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I)
      (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x b a y
  rw [DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE_symm (I := I) _ x a b,
    DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE_symm (I := I) _ x a b]

private lemma lieArm_chartChristoffel_center (g : SmoothRiemannianMetric I M) (x : M)
    (a b k : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g x a b k (extChartAt I x x)
    = (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x k l *
          DeTurckCoefficients.gramBracket (I := I) g x a b l (extChartAt I x x) := by
  rw [DeTurckCoefficients.chartChristoffel_eq_sum_invGramOnE_bracket (I := I) g x a b k (extChartAt I x x)]
  refine congrArg (HMul.hMul (1 / 2 : ℝ)) (Finset.sum_congr rfl (fun l _ => ?_))
  rw [lieArm_chartInvGramOnE_center (I := I) g x k l]

private lemma lieArm_partial_chartInvGramOnE_center (g : SmoothRiemannianMetric I M) (x : M)
    (m a b : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m
      (DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramOnE (I := I) g x a b) (extChartAt I x x)
    = -(∑ x' : Fin (Module.finrank ℝ E), ∑ y' : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x a x' * chartInvGramMatrix (I := I) g x x y' b *
          DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m
            (DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I) g x x' y') (extChartAt I x x)) := by
  rw [DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv_chartInvGramOnE_eq (I := I) g x
    (extChartAt I x x) m a b
    (DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
      (I := I) x (mem_extChartAt_target x))]
  refine congrArg Neg.neg (Finset.sum_congr rfl (fun x' _ => Finset.sum_congr rfl (fun y' _ => ?_)))
  rw [lieArm_chartInvGramOnE_center (I := I) g x a x', lieArm_chartInvGramOnE_center (I := I) g x y' b]

private lemma lieArm_chartDeTurckVFComp_center (gA gB : SmoothRiemannianMetric I M) (x : M)
    (k : Fin (Module.finrank ℝ E)) :
    PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) gA gB x k (extChartAt I x x)
    = ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) gA x x a b *
          (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gA x a b k (extChartAt I x x)
           - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) gB x a b k (extChartAt I x x)) := by
  rw [PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp_def]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [lieArm_chartInvGramOnE_center (I := I) gA x a b]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private lemma lieArm_o1raw_center_eq (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (x : M) (i j : Fin (Module.finrank ℝ E)) :
    PDE.DeTurck.DeTurckLinearization.lieDeTurckOrder1Raw (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x
        (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) i j (extChartAt I x x)
    = ((∑ k : Fin (Module.finrank ℝ E), DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k j *
        ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) i (DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b) (extChartAt I x x) * ((1 / 2 : ℝ) *
          ∑ l : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k l * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) a (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l b) (extChartAt I x x) + DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) b (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l a) (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) l (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b) (extChartAt I x x))))
         + ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b * ((1 / 2 : ℝ) *
          ∑ l : Fin (Module.finrank ℝ E), DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) i (DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k l) (extChartAt I x x) * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) a (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l b) (extChartAt I x x) + DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) b (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l a) (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) l (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b) (extChartAt I x x)))))
      + ∑ k : Fin (Module.finrank ℝ E), DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x i k *
        ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) j (DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b) (extChartAt I x x) * ((1 / 2 : ℝ) *
          ∑ l : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k l * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) a (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l b) (extChartAt I x x) + DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) b (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l a) (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) l (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b) (extChartAt I x x))))
         + ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b * ((1 / 2 : ℝ) *
          ∑ l : Fin (Module.finrank ℝ E), DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) j (DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k l) (extChartAt I x x) * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) a (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l b) (extChartAt I x x) + DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) b (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l a) (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) l (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b) (extChartAt I x x)))))
    + ((∑ k : Fin (Module.finrank ℝ E), (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b * ((1 / 2 : ℝ) *
          ∑ l : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k l * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) a (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l b) (extChartAt I x x) + DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) b (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l a) (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) l (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b) (extChartAt I x x)))) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) k (DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j) (extChartAt I x x))
      + (∑ k : Fin (Module.finrank ℝ E), PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x k (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) k (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i j) (extChartAt I x x))
      + (∑ k : Fin (Module.finrank ℝ E), DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k j * (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        ((-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a p * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) i (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p q) (extChartAt I x x) * chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q b)) * (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b k (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x a b k (extChartAt I x x))
         + chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b * ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
            (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k p * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) i (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p q) (extChartAt I x x) * chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l)) * DeTurckCoefficients.gramBracket (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b l (extChartAt I x x)))))
      + (∑ k : Fin (Module.finrank ℝ E), DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x i k * (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        ((-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a p * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) j (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p q) (extChartAt I x x) * chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q b)) * (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b k (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x a b k (extChartAt I x x))
         + chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b * ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
            (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k p * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) j (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p q) (extChartAt I x x) * chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l)) * DeTurckCoefficients.gramBracket (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b l (extChartAt I x x)))))) := by
  unfold PDE.DeTurck.DeTurckLinearization.lieDeTurckOrder1Raw
    PDE.DeTurck.DeTurckLinearization.chartDeTurckCorrFirstOrderRemainderRaw
    PDE.DeTurck.DeTurckLinearization.order1PartRaw
    PDE.DeTurck.DeTurckLinearization.chartLinearizedDeTurckVFPrincipalRaw
    PDE.DeTurck.DeTurckLinearization.deTurckVFFirstOrderCorrDeriv1Raw
    PDE.DeTurck.DeTurckLinearization.chartDeTurckCorrGramDerivBlockRaw
    PDE.DeTurck.DeTurckLinearization.chartLinearizedChristoffelPrincipalRaw
  simp only [lieArm_chartInvGramOnE_center, lieArm_chartGramOnE_center]

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
private lemma lieArm_arm1_value_eq_order1Raw_add_tail (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (x : M) (i j : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 3 2
          (deTurckLieArm1Coeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
          (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x
        ![chartModelBasis E i, chartModelBasis E j]
    = PDE.DeTurck.DeTurckLinearization.lieDeTurckOrder1Raw (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x
        (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) i j (extChartAt I x x)
      + (((∑ w : Fin (Module.finrank ℝ E), PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x w (extChartAt I x x) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![w, i, j])
      + ((∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![i, m, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁))))
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![i, m, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q j))))
        - (∑ w : Fin (Module.finrank ℝ E), (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b * (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b w (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x a b w (extChartAt I x x))) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![i, j, w])
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![m, j, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁))))
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![p, q, k₁]))
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![m, j, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))))
      + ((∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![j, m, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁))))
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![j, m, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q i))))
        - (∑ w : Fin (Module.finrank ℝ E), (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b * (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b w (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x a b w (extChartAt I x x))) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![j, i, w])
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![m, i, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁))))
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i j q (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![p, q, k₁]))
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![m, i, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))))
      + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![q, p, k₁])))
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ l *
        ((-(∑ r : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l j r (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) i (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r k₁) (extChartAt I x x)
          + DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l k₁ r (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) i (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j r) (extChartAt I x x)
          + DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i l r (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) r (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j k₁) (extChartAt I x x)
          + DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i j r (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) l (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r k₁) (extChartAt I x x)
          + DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i k₁ r (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) l (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j r) (extChartAt I x x))))
         + (-(∑ r : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l i r (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) j (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r k₁) (extChartAt I x x)
          + DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l k₁ r (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) j (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i r) (extChartAt I x x)
          + DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j l r (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) r (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k₁) (extChartAt I x x)
          + DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i r (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) l (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r k₁) (extChartAt I x x)
          + DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j k₁ r (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) l (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i r) (extChartAt I x x))))
         - (-(∑ r : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j l r (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) i (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r k₁) (extChartAt I x x)
          + DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j k₁ r (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) i (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l r) (extChartAt I x x)
          + DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i j r (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) r (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l k₁) (extChartAt I x x)
          + DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i l r (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) j (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r k₁) (extChartAt I x x)
          + DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i k₁ r (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) j (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l r) (extChartAt I x x))))))) := by
  classical
  refine (lieArm_arm1_value_realized (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' s x i j).trans ?_
  have hs1 : (∑ w : Fin (Module.finrank ℝ E), PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x w (extChartAt I x x) * unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E w, chartModelBasis E i, chartModelBasis E j]) = (∑ w : Fin (Module.finrank ℝ E), PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x w (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) w (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i j) (extChartAt I x x)) + (∑ w : Fin (Module.finrank ℝ E), PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x w (extChartAt I x x) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![w, i, j]) := by
    rw [show (∑ w : Fin (Module.finrank ℝ E), PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x w (extChartAt I x x) * unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E w, chartModelBasis E i, chartModelBasis E j]) = ∑ w : Fin (Module.finrank ℝ E), (PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x w (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) w (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i j) (extChartAt I x x) + PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x w (extChartAt I x x) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![w, i, j]) from
      Finset.sum_congr rfl (fun w _ => by
        rw [lieArm_U3_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x w i j]
        ring)]
    simp only [Finset.sum_add_distrib]
  have hs2 : (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E i, chartModelBasis E m, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) = (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) i (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x m p) (extChartAt I x x) *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![i, m, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) := by
    rw [show (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E i, chartModelBasis E m, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁))))
        = ∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) i (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x m p) (extChartAt I x x) * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))
           + chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![i, m, p] * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) from
      Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => by
          rw [lieArm_U3_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i m p]
          ring))))]
    simp only [Finset.sum_add_distrib]
  have hs3 : (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E i, chartModelBasis E m, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q j)))) = (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) i (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x m p) (extChartAt I x x) *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q j)))) + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![i, m, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q j)))) := by
    rw [show (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E i, chartModelBasis E m, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q j))))
        = ∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) i (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x m p) (extChartAt I x x) * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q j)))
           + chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![i, m, p] * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q j)))) from
      Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => by
          rw [lieArm_U3_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i m p]
          ring))))]
    simp only [Finset.sum_add_distrib]
  have hs4 : (∑ w : Fin (Module.finrank ℝ E), PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x w (extChartAt I x x) * unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E i, chartModelBasis E j, chartModelBasis E w]) = (∑ w : Fin (Module.finrank ℝ E), (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b * (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b w (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x a b w (extChartAt I x x))) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) i (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j w) (extChartAt I x x)) + (∑ w : Fin (Module.finrank ℝ E), (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b * (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b w (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x a b w (extChartAt I x x))) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![i, j, w]) := by
    rw [show (∑ w : Fin (Module.finrank ℝ E), PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x w (extChartAt I x x) * unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E i, chartModelBasis E j, chartModelBasis E w]) = ∑ w : Fin (Module.finrank ℝ E), ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b * (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b w (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x a b w (extChartAt I x x))) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) i (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j w) (extChartAt I x x) + (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b * (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b w (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x a b w (extChartAt I x x))) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![i, j, w]) from
      Finset.sum_congr rfl (fun w _ => by
        rw [lieArm_U3_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i j w,
          lieArm_chartDeTurckVFComp_center (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x w]
        ring)]
    simp only [Finset.sum_add_distrib]
  have hs5 : (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E m, chartModelBasis E j, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁)))) = (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j p) (extChartAt I x x) *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁)))) + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![m, j, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁)))) := by
    rw [show (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E m, chartModelBasis E j, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁))))
        = ∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j p) (extChartAt I x x) * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁)))
           + chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![m, j, p] * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁)))) from
      Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => by
          rw [lieArm_U3_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x m j p]
          ring))))]
    simp only [Finset.sum_add_distrib]
  have hs6 : (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E p, chartModelBasis E q, chartModelBasis E k₁])) = (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) p (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x q k₁) (extChartAt I x x))) + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![p, q, k₁])) := by
    rw [show (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E p, chartModelBasis E q, chartModelBasis E k₁]))
        = ∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) p (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x q k₁) (extChartAt I x x))
           + chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![p, q, k₁])) from
      Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ => by
        rw [show (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E p, chartModelBasis E q, chartModelBasis E k₁])
            = ∑ q : Fin (Module.finrank ℝ E), ((DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) p (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x q k₁) (extChartAt I x x) + (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![p, q, k₁]) from
          Finset.sum_congr rfl (fun q _ => by
            rw [lieArm_U3_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p q k₁]
            ring)]
        rw [Finset.sum_add_distrib, mul_add]))]
    simp only [Finset.sum_add_distrib]
  have hs7 : (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E m, chartModelBasis E j, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) = (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j p) (extChartAt I x x) *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![m, j, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) := by
    rw [show (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E m, chartModelBasis E j, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁))))
        = ∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j p) (extChartAt I x x) * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))
           + chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![m, j, p] * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) from
      Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => by
          rw [lieArm_U3_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x m j p]
          ring))))]
    simp only [Finset.sum_add_distrib]
  have hs8 : (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E j, chartModelBasis E m, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) = (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) j (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x m p) (extChartAt I x x) *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![j, m, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) := by
    rw [show (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E j, chartModelBasis E m, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁))))
        = ∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) j (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x m p) (extChartAt I x x) * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))
           + chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![j, m, p] * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) from
      Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => by
          rw [lieArm_U3_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j m p]
          ring))))]
    simp only [Finset.sum_add_distrib]
  have hs9 : (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E j, chartModelBasis E m, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q i)))) = (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) j (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x m p) (extChartAt I x x) *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q i)))) + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![j, m, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q i)))) := by
    rw [show (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E j, chartModelBasis E m, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q i))))
        = ∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) j (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x m p) (extChartAt I x x) * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q i)))
           + chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![j, m, p] * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q i)))) from
      Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => by
          rw [lieArm_U3_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j m p]
          ring))))]
    simp only [Finset.sum_add_distrib]
  have hs10 : (∑ w : Fin (Module.finrank ℝ E), PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x w (extChartAt I x x) * unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E j, chartModelBasis E i, chartModelBasis E w]) = (∑ w : Fin (Module.finrank ℝ E), (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b * (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b w (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x a b w (extChartAt I x x))) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) j (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i w) (extChartAt I x x)) + (∑ w : Fin (Module.finrank ℝ E), (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b * (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b w (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x a b w (extChartAt I x x))) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![j, i, w]) := by
    rw [show (∑ w : Fin (Module.finrank ℝ E), PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x w (extChartAt I x x) * unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E j, chartModelBasis E i, chartModelBasis E w]) = ∑ w : Fin (Module.finrank ℝ E), ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b * (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b w (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x a b w (extChartAt I x x))) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) j (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i w) (extChartAt I x x) + (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b * (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b w (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x a b w (extChartAt I x x))) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![j, i, w]) from
      Finset.sum_congr rfl (fun w _ => by
        rw [lieArm_U3_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j i w,
          lieArm_chartDeTurckVFComp_center (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x w]
        ring)]
    simp only [Finset.sum_add_distrib]
  have hs11 : (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E m, chartModelBasis E i, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁)))) = (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i p) (extChartAt I x x) *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁)))) + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![m, i, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁)))) := by
    rw [show (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E m, chartModelBasis E i, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁))))
        = ∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i p) (extChartAt I x x) * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁)))
           + chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![m, i, p] * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁)))) from
      Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => by
          rw [lieArm_U3_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x m i p]
          ring))))]
    simp only [Finset.sum_add_distrib]
  have hs12 : (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i j q (extChartAt I x x)) * unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E p, chartModelBasis E q, chartModelBasis E k₁])) = (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i j q (extChartAt I x x)) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) p (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x q k₁) (extChartAt I x x))) + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i j q (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![p, q, k₁])) := by
    rw [show (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i j q (extChartAt I x x)) * unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E p, chartModelBasis E q, chartModelBasis E k₁]))
        = ∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i j q (extChartAt I x x)) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) p (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x q k₁) (extChartAt I x x))
           + chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i j q (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![p, q, k₁])) from
      Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ => by
        rw [show (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i j q (extChartAt I x x)) * unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E p, chartModelBasis E q, chartModelBasis E k₁])
            = ∑ q : Fin (Module.finrank ℝ E), ((DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i j q (extChartAt I x x)) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) p (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x q k₁) (extChartAt I x x) + (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i j q (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![p, q, k₁]) from
          Finset.sum_congr rfl (fun q _ => by
            rw [lieArm_U3_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p q k₁]
            ring)]
        rw [Finset.sum_add_distrib, mul_add]))]
    simp only [Finset.sum_add_distrib]
  have hs13 : (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E m, chartModelBasis E i, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) = (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i p) (extChartAt I x x) *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![m, i, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) := by
    rw [show (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E m, chartModelBasis E i, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁))))
        = ∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i p) (extChartAt I x x) * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))
           + chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![m, i, p] * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) from
      Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => by
          rw [lieArm_U3_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x m i p]
          ring))))]
    simp only [Finset.sum_add_distrib]
  have hs14 : (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E q, chartModelBasis E p, chartModelBasis E k₁])) = (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) q (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p k₁) (extChartAt I x x))) + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![q, p, k₁])) := by
    rw [show (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E q, chartModelBasis E p, chartModelBasis E k₁]))
        = ∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) q (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p k₁) (extChartAt I x x))
           + chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![q, p, k₁])) from
      Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ => by
        rw [show (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E q, chartModelBasis E p, chartModelBasis E k₁])
            = ∑ q : Fin (Module.finrank ℝ E), ((DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) q (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p k₁) (extChartAt I x x) + (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![q, p, k₁]) from
          Finset.sum_congr rfl (fun q _ => by
            rw [lieArm_U3_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x q p k₁]
            ring)]
        rw [Finset.sum_add_distrib, mul_add]))]
    simp only [Finset.sum_add_distrib]
  rw [hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14]
  rw [lieArm_o1raw_center_eq (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' s x i j]
  have hcol' : ∀ l j' : Fin (Module.finrank ℝ E), (∑ k : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k j' *
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k l) = if l = j' then (1 : ℝ) else 0 :=
    fun l j' => lieArm_gram_invGram_collapse (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l j'
  have higs' : ∀ a b : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b = chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x b a :=
    fun a b => lieArm_chartInvGramMatrix_symm (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b
  have hcgs' : ∀ a b : Fin (Module.finrank ℝ E), DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b = DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x b a :=
    fun a b => lieArm_chartGramMatrix_symm (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b
  have hf3s' : ∀ d a b : Fin (Module.finrank ℝ E), DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) d (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b) (extChartAt I x x) = DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) d (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x b a) (extChartAt I x x) :=
    fun d a b => congrArg
      (fun F => DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) d F (extChartAt I x x))
      (lieArm_realizedGramDeriv_symm (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b)
  have hg1s' : ∀ a b k : Fin (Module.finrank ℝ E), DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b k (extChartAt I x x) = DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x b a k (extChartAt I x x) :=
    fun a b k => DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel_symm (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b k (extChartAt I x x)
  have hg0s' : ∀ a b k : Fin (Module.finrank ℝ E), DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x a b k (extChartAt I x x) = DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x b a k (extChartAt I x x) :=
    fun a b k => DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel_symm (I := I)
      g₀ x a b k (extChartAt I x x)
  have hgbdef' : ∀ a b l : Fin (Module.finrank ℝ E), DeTurckCoefficients.gramBracket (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b l (extChartAt I x x)
      = DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) a (DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l b) (extChartAt I x x) + DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) b (DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l a) (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) l (DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b) (extChartAt I x x) :=
    fun a b l => rfl
  have hdgs' : ∀ m a b : Fin (Module.finrank ℝ E), DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m (DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b) (extChartAt I x x) = DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m (DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x b a) (extChartAt I x x) :=
    fun m a b => congrArg
      (fun F => DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m F (extChartAt I x x))
      (funext (fun y => DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE_symm (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b y))
  have hga1' : ∀ a b k : Fin (Module.finrank ℝ E), DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b k (extChartAt I x x)
      = (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k l * DeTurckCoefficients.gramBracket (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b l (extChartAt I x x) :=
    fun a b k => lieArm_chartChristoffel_center (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b k
  have hdig' : ∀ m a b : Fin (Module.finrank ℝ E), DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m (DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b) (extChartAt I x x)
      = -(∑ x' : Fin (Module.finrank ℝ E), ∑ y' : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a x' * chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x y' b * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m (DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x' y') (extChartAt I x x)) :=
    fun m a b => lieArm_partial_chartInvGramOnE_center (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x m a b
  have hM := O1Abstract.o1_master
    (fun a b => chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b)
    (fun a b => DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b)
    (fun m a b => DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m (DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b) (extChartAt I x x))
    (fun a b l => DeTurckCoefficients.gramBracket (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b l (extChartAt I x x))
    (fun m a b => DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m (DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b) (extChartAt I x x))
    (fun a b k => DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b k (extChartAt I x x))
    (fun a b k => DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x a b k (extChartAt I x x))
    (fun a b k => DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x a b k (extChartAt I x x))
    (fun d a b => DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) d (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b) (extChartAt I x x))
    (fun k => PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x k (extChartAt I x x))
    hcol' higs' hcgs' hf3s' hg1s' hg0s' hgbdef' hdgs' hga1' hdig' i j
  linear_combination hM

private theorem lieArm_jointRS_add_local {r s : ℕ} {S : Set ℝ}
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

theorem lieArm_jointRS_const_smul_local {r s : ℕ} {S : Set ℝ} (a : ℝ)
    (A : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (a • A p))
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
  refine ((contMDiffWithinAt_const (c := a)).smul hA'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_smul a (A p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_smul
      a (A p₀)

private theorem lieArm_hjoint_reindex (g₀ : SmoothRiemannianMetric I M) (r : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r 2) (σ' : Equiv.Perm (Fin r)) {δ δ' : ℝ}
    (hΦ : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r Φ (δ := δ) (δ' := δ')) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r
      (fun s => reindexCoeffGen (I := I) (M := M) g₀ r 2 (Φ s) σ') (δ := δ) (δ' := δ') := by
  classical
  rw [linearizedRicciThreeArmHjoint] at hΦ ⊢
  have htest : ∀ (Y : Cₛ^∞⟮I; Tensor0SBundle.Tensor0SModel r ℝ E,
      fun x : M => Tensor0SBundle.Tensor0SSpace r I x⟯),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1
          ((reindexCoeffFibGen (I := I) r 2 σ' p.1
            (show Tensor0SBundle.Tensor0SSpace r I p.1 →L[ℝ]
                Tensor0SBundle.Tensor0SSpace 2 I p.1 from
              (Φ p.2).toSection p.1)) (Y p.1)))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    intro Y
    have hYσ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel r ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel r ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace r I z) x
          (Tensor0SBundle.Tensor0SSpace.ofModel
            (ContinuousMultilinearMap.domDomCongr σ'
              (Tensor0SBundle.Tensor0SSpace.toModel (Y x))))) := by
      refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
        (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
        (fun x => (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
            (ContinuousMultilinearMap.domDomCongr σ'
              (Tensor0SBundle.Tensor0SSpace.toModel (Y x))) :
              Tensor0SBundle.Tensor0SSpace r I x))).mpr ?_
      have hYcoord := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
        (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
        (fun x => Y x)).mp Y.contMDiff
      intro τ x₀
      refine (hYcoord (τ ∘ σ') x₀).congr_of_eventuallyEq ?_
      filter_upwards [Filter.univ_mem] with x _
      rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr]
      change (ContinuousMultilinearMap.domDomCongr σ'
          (Tensor0SBundle.Tensor0SSpace.toModel (Y x)))
          (fun j => (Bundle.Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x)
            ((Module.finBasis ℝ E) (τ j))) = _
      rw [ContinuousMultilinearMap.domDomCongr_apply]
      rfl
    have hYσJ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel r ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel r ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace r I z) p.1
          (Tensor0SBundle.Tensor0SSpace.ofModel
            (ContinuousMultilinearMap.domDomCongr σ'
              (Tensor0SBundle.Tensor0SSpace.toModel (Y p.1)))))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
      (hYσ.comp contMDiff_fst).contMDiffOn
    have hRY := ContMDiffOn.clm_bundle_apply (b := Prod.fst) hΦ hYσJ
    refine hRY.congr (fun p _ => ?_)
    refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
      (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 t) ?_
    exact (reindexCoeffFibGen_apply (I := I) r 2 σ' p.1
      (show Tensor0SBundle.Tensor0SSpace r I p.1 →L[ℝ]
          Tensor0SBundle.Tensor0SSpace 2 I p.1 from (Φ p.2).toSection p.1) (Y p.1)).symm
  have hCLM := contMDiffOn_clm_section_of_pointwise_joint_manifold_time (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel r ℝ E)
    (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace r I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ => reindexCoeffFibGen (I := I) r 2 σ' p.1
      (show Tensor0SBundle.Tensor0SSpace r I p.1 →L[ℝ]
          Tensor0SBundle.Tensor0SSpace 2 I p.1 from (Φ p.2).toSection p.1))
    (S := realizedSmallSet (δ := δ) (δ' := δ')) htest
  refine hCLM.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r 2 I z) p.1 t) ?_
  rw [reindexCoeffGen_toSection]

private theorem lieArm_hjAbsorb (g₀ : SmoothRiemannianMetric I M) {δ δ' : ℝ}
    (r : ℕ) (Φ : ℝ → SmoothCcTensor g₀ (2 + r) 2) (σ' : Equiv.Perm (Fin (2 + r)))
    (hΦ : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ (2 + r) Φ (δ := δ) (δ' := δ')) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ (2 + r)
      (fun s => symmAbsorbedCoeff (I := I) (M := M) g₀ r (Φ s) σ') (δ := δ) (δ' := δ') := by
  classical
  have hRein := lieArm_hjoint_reindex (I := I) g₀ (2 + r)
    Φ σ' (δ := δ) (δ' := δ') hΦ
  rw [linearizedRicciThreeArmHjoint] at hΦ hRein ⊢
  have hA := lieArm_jointRS_const_smul_local (I := I) (r := 2 + r) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) (1 / 2 : ℝ)
    (fun p : M × ℝ => (Φ p.2).toSection p.1) hΦ
  have hB := lieArm_jointRS_const_smul_local (I := I) (r := 2 + r) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) (1 / 2 : ℝ)
    (fun p : M × ℝ => (reindexCoeffGen (I := I) (M := M) g₀ (2 + r) 2 (Φ p.2) σ').toSection p.1)
    hRein
  have hAB := lieArm_jointRS_add_local (I := I) (r := 2 + r) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ hA hB
  refine hAB.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel (2 + r) 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace (2 + r) 2 I z) p.1 t) ?_
  rw [symmAbsorbedCoeff, smoothCcTensor_toSection_add_apply,
    smoothCcTensor_toSection_smul_apply, smoothCcTensor_toSection_smul_apply]

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (deTurckLieWEndo deTurckLieWEndo_apply deTurckLieWEndo_homSection_contMDiff deTurckVFCovDeriv connDiffOp_homSection_contMDiff metricConnDiffLoweredFib metricConnDiffLoweredFib_toModel metricConnDiffLoweredFib_contMDiff domDomCongrFibRank domDomCongrFibRank_apply tensor0SProdKappaFib tensor0SProdKappaFib_apply)
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck (cometricDoubleTraceFib cometricDoubleTraceFib_toModel cometricDoubleTraceFib_contMDiff)

noncomputable def deTurckLieRemainderEndo (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  PDE.DeTurck.connDiff (I := I) g₁ g₀ x
      ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x)
    - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
      ((PDE.DeTurck.deTurckVF (I := I) g₁ g_bg : Π b : M, TangentSpace I b) x)
    - deTurckLieWEndo (I := I) g₁ g₀ x

theorem lieCorr0NEndo_homSection_contMDiff (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) x
        (deTurckLieRemainderEndo (I := I) g₀ g₁ g_bg x)) := by
  have hBV : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x))) :=
    ContMDiff.clm_bundle_apply (b := id)
      (connDiffOp_homSection_contMDiff (I := I) g₁ g₀)
      (PDE.DeTurck.deTurckVF (I := I) g₁ g₀).contMDiff
  have hBW : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          ((PDE.DeTurck.deTurckVF (I := I) g₁ g_bg : Π b : M, TangentSpace I b) x))) :=
    ContMDiff.clm_bundle_apply (b := id)
      (connDiffOp_homSection_contMDiff (I := I) g₁ g₀)
      (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg).contMDiff
  have hW := deTurckLieWEndo_homSection_contMDiff (I := I) g₁ g₀
  exact (hBV.sub_section hBW).sub_section hW

noncomputable def deTurckLieRemainderEndoSlotInsertFib (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  slotInsertEndoFib (I := I) (M := M) 2 0 x (deTurckLieRemainderEndo (I := I) g₀ g₁ g_bg x) +
    slotInsertEndoFib (I := I) (M := M) 2 1 x (deTurckLieRemainderEndo (I := I) g₀ g₁ g_bg x)

theorem lieCorr0InsertFib_toModel (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (deTurckLieRemainderEndoSlotInsertFib (I := I) g₀ g₁ g_bg x D) v =
      Tensor0SSpace.toModel D
          (Function.update v 0 (deTurckLieRemainderEndo (I := I) g₀ g₁ g_bg x (v 0))) +
        Tensor0SSpace.toModel D
          (Function.update v 1 (deTurckLieRemainderEndo (I := I) g₀ g₁ g_bg x (v 1))) := by
  rw [deTurckLieRemainderEndoSlotInsertFib, ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add,
    ContinuousMultilinearMap.add_apply,
    slotInsertEndoFib_apply_eval, slotInsertEndoFib_apply_eval]

private theorem lieCorr0InsertFib_contMDiff (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (deTurckLieRemainderEndoSlotInsertFib (I := I) g₀ g₁ g_bg x))) := by
  classical
  have h0 := slotInsertEndoFib_contMDiff (I := I) (M := M) g₀ 2 0
    (fun x => deTurckLieRemainderEndo (I := I) g₀ g₁ g_bg x)
    (lieCorr0NEndo_homSection_contMDiff (I := I) g₀ g₁ g_bg)
  have h1 := slotInsertEndoFib_contMDiff (I := I) (M := M) g₀ 2 1
    (fun x => deTurckLieRemainderEndo (I := I) g₀ g₁ g_bg x)
    (lieCorr0NEndo_homSection_contMDiff (I := I) g₀ g₁ g_bg)
  have hadd := ContMDiff.add_section
    (s := fun x => (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x
        (deTurckLieRemainderEndo (I := I) g₀ g₁ g_bg x))))
    (t := fun x => (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 1 x
        (deTurckLieRemainderEndo (I := I) g₀ g₁ g_bg x))))
    h0 h1
  refine hadd.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) x) ?_
  rw [deTurckLieRemainderEndoSlotInsertFib]
  rfl

noncomputable def doubleTraceReindexFib (g : SmoothRiemannianMetric I M) (p : ℕ)
    (σ : Equiv.Perm (Fin (p + 2))) (x : M) :
    Tensor0SSpace (p + 2) I x →L[ℝ] Tensor0SSpace p I x :=
  (cometricDoubleTraceFib (I := I) g p x).comp
    (domDomCongrFibRank (I := I) (p + 2) σ x)

def lieCorr0VBPerm : Equiv.Perm (Fin 4) :=
  ⟨![1, 2, 3, 0], ![3, 0, 1, 2], by decide, by decide⟩

noncomputable def lieCorr0VBFib (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  (2 : ℝ) • ((doubleTraceReindexFib (I := I) g₁ 2 lieCorr0VBPerm x).comp
    ((tensor0SProdKappaFib (I := I) (p := 1) (q := 3) x
        (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)).comp
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x
        ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x))))

def lieCorr0AMixPermQ : Equiv.Perm (Fin 5) :=
  ⟨![1, 4, 2, 3, 0], ![4, 0, 2, 3, 1], by decide, by decide⟩

def lieCorr0AMixPerm1 : Equiv.Perm (Fin 6) :=
  ⟨![2, 0, 3, 1, 4, 5], ![1, 3, 0, 2, 4, 5], by decide, by decide⟩

def lieCorr0AMixPerm2 : Equiv.Perm (Fin 4) :=
  ⟨![2, 0, 1, 3], ![1, 2, 0, 3], by decide, by decide⟩

noncomputable def lieCorr0AMixHalfFib (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  (doubleTraceReindexFib (I := I) g₁ 2 lieCorr0AMixPerm2 x).comp
    ((doubleTraceReindexFib (I := I) g₁ 4 lieCorr0AMixPerm1 x).comp
      ((tensor0SProdKappaFib (I := I) (p := 3) (q := 3) x
          (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)).comp
        ((doubleTraceReindexFib (I := I) g₁ 3 lieCorr0AMixPermQ x).comp
          (tensor0SProdKappaFib (I := I) (p := 2) (q := 3) x
            (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)))))

noncomputable def lieCorr0AMixFib (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  (2 : ℝ) • (lieCorr0AMixHalfFib (I := I) g₀ g₁ g_bg x +
    (domDomCongrFibRank (I := I) 2 (Equiv.swap 0 1) x).comp
      (lieCorr0AMixHalfFib (I := I) g₀ g₁ g_bg x))

private noncomputable def lieCorr0RiemQuadlin (g₀ : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
      TangentSpace I x →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ (TangentSpace I x)
      (TangentSpace I x →L[ℝ] TangentSpace I x)
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
      (ContinuousLinearMap.compL ℝ (TangentSpace I x) (TangentSpace I x)
        (TangentSpace I x →L[ℝ] ℝ) (g₀.inner x))).comp
    (Integral.Connection.riemannOp (LeviCivita (I := I) g₀) x)

private theorem lieCorr0RiemQuadlin_apply (g₀ : SmoothRiemannianMetric I M) (x : M)
    (v0 v1 u w : TangentSpace I x) :
    lieCorr0RiemQuadlin (I := I) g₀ x v0 v1 u w =
      g₀.inner x (Integral.Connection.riemannOp (LeviCivita (I := I) g₀) x v0 v1 u) w :=
  rfl

private noncomputable def lieCorr0Quadlin4ToModel (F : Type*) [NormedAddCommGroup F]
    [NormedSpace ℝ F]
    (Q : F →L[ℝ] F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 4 => F) ℝ :=
  (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 4 => F) ℝ).symm
    (((continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin 3 => F) ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
      ((ContinuousLinearMap.compL ℝ F (F →L[ℝ] F →L[ℝ] ℝ)
          (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => F) ℝ)
          ((bilinFormToModelₗᵢ F).toContinuousLinearEquiv.toContinuousLinearMap)).comp Q))

private theorem lieCorr0Quadlin4ToModel_apply (F : Type*) [NormedAddCommGroup F]
    [NormedSpace ℝ F]
    (Q : F →L[ℝ] F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) (v : Fin 4 → F) :
    lieCorr0Quadlin4ToModel F Q v = Q (v 0) (v 1) (v 2) (v 3) := by
  have h1 : lieCorr0Quadlin4ToModel F Q v =
      bilinFormToModel F (Q (v 0) (v 1)) (Fin.tail (Fin.tail v)) := rfl
  rw [h1, bilinFormToModel_apply]
  rfl

noncomputable def lieCorr0RiemLoweredFib (g₀ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 4 I x :=
  Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
    (lieCorr0Quadlin4ToModel (TangentSpace I x) (lieCorr0RiemQuadlin (I := I) g₀ x))

private theorem lieCorr0RiemLoweredFib_toModel (g₀ : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 4 → TangentSpace I x) :
    Tensor0SSpace.toModel (lieCorr0RiemLoweredFib (I := I) g₀ x) v =
      g₀.inner x (Integral.Connection.riemannOp (LeviCivita (I := I) g₀) x
        (v 0) (v 1) (v 2)) (v 3) := by
  rw [lieCorr0RiemLoweredFib, Tensor0SSpace.toModel_ofModel]
  exact lieCorr0Quadlin4ToModel_apply (TangentSpace I x) (lieCorr0RiemQuadlin (I := I) g₀ x) v

def lieCorr0RiemPerm1 : Equiv.Perm (Fin 6) :=
  ⟨![1, 5, 2, 3, 4, 0], ![5, 0, 2, 3, 4, 1], by decide, by decide⟩

def lieCorr0RiemPerm2 : Equiv.Perm (Fin 4) :=
  ⟨![2, 3, 0, 1], ![2, 3, 0, 1], by decide, by decide⟩

noncomputable def deTurckLieRemainderCurvatureFib (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  (-1 : ℝ) • ((doubleTraceReindexFib (I := I) g₁ 2 lieCorr0RiemPerm2 x).comp
    ((doubleTraceReindexFib (I := I) g₀ 4 lieCorr0RiemPerm1 x).comp
      (tensor0SProdKappaFib (I := I) (p := 2) (q := 4) x
        (lieCorr0RiemLoweredFib (I := I) g₀ x))))

private theorem lieCorr0_ddc_section_contMDiff {d : ℕ} (ρ : Equiv.Perm (Fin d))
    (Z : ∀ x : M, Tensor0SSpace d I x)
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel d ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SSpace d I z) x (Z x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel d ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SSpace d I z) x
        (Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (ContinuousMultilinearMap.domDomCongr ρ
            (Tensor0SSpace.toModel (Z x))))) := by
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => (Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (ContinuousMultilinearMap.domDomCongr ρ
          (Tensor0SSpace.toModel (Z x))) :
          Tensor0SSpace d I x))).mpr ?_
  have hZcoord := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => Z x)).mp hZ
  intro τ x₀
  refine (hZcoord (τ ∘ ρ) x₀).congr_of_eventuallyEq ?_
  filter_upwards [Filter.univ_mem] with x _
  rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr]
  change (ContinuousMultilinearMap.domDomCongr ρ
      (Tensor0SSpace.toModel (Z x)))
      (fun j => (Bundle.Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x)
        ((Module.finBasis ℝ E) (τ j))) = _
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rfl

theorem lieCorr0_prod_section_contMDiff {p q : ℕ}
    (Y : ∀ x : M, Tensor0SSpace p I x)
    (K : ∀ x : M, Tensor0SSpace q I x)
    (hY : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel p ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel p ℝ E)
        (E := fun z : M => Tensor0SSpace p I z) x (Y x)))
    (hK : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel q ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel q ℝ E)
        (E := fun z : M => Tensor0SSpace q I z) x (K x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (p + q) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel (p + q) ℝ E)
        (E := fun z : M => Tensor0SSpace (p + q) I z) x
        (tensor0SProdKappaFib (I := I) x (K x) (Y x))) := by
  classical
  have hbase : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (p + q) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel (p + q) ℝ E)
        (E := fun z : M => Tensor0SSpace (p + q) I z) x
        (Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
            (Tensor0SSpace.toModel (Y x))
            (Tensor0SSpace.toModel (K x))))) := by
    refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x => (Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
            (Tensor0SSpace.toModel (Y x))
            (Tensor0SSpace.toModel (K x))) :
            Tensor0SSpace (p + q) I x))).mpr ?_
    have hYc := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x => Y x)).mp hY
    have hKc := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x => K x)).mp hK
    intro τ x₀
    refine (((contMDiffAt_const (I := I) (x := x₀) (n := (∞ : WithTop ℕ∞))
      (c := ContinuousLinearMap.mul ℝ ℝ)).clm_apply
        (hYc (τ ∘ Fin.castAdd q) x₀)).clm_apply
          (hKc (τ ∘ Fin.natAdd p) x₀)).congr_of_eventuallyEq ?_
    filter_upwards [Filter.univ_mem] with x _
    rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr,
      continuousMultilinearMap_basis_repr]
    change (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) p q
        (Tensor0SSpace.toModel (Y x)) (Tensor0SSpace.toModel (K x)))
        (fun j => (Bundle.Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x)
          ((Module.finBasis ℝ E) (τ j))) = _
    rw [Bundle.continuousMultilinearMap.modelProduct_apply]
    rfl
  refine hbase.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel (p + q) ℝ E)
    (E := fun z : M => Tensor0SSpace (p + q) I z) x t) ?_
  rw [tensor0SProdKappaFib_apply]

theorem lieCorr0TraceStep_section_contMDiff (g : SmoothRiemannianMetric I M) (p : ℕ)
    (σ : Equiv.Perm (Fin (p + 2)))
    (Z : ∀ x : M, Tensor0SSpace (p + 2) I x)
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (p + 2) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel (p + 2) ℝ E)
        (E := fun z : M => Tensor0SSpace (p + 2) I z) x (Z x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel p ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel p ℝ E)
        (E := fun z : M => Tensor0SSpace p I z) x
        (doubleTraceReindexFib (I := I) g p σ x (Z x))) := by
  have hZρ := lieCorr0_ddc_section_contMDiff (I := I) σ (fun x => Z x) hZ
  have hfield := ContMDiff.clm_bundle_apply (b := id)
    (cometricDoubleTraceFib_contMDiff (I := I) g p) hZρ
  refine hfield.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel p ℝ E)
    (E := fun z : M => Tensor0SSpace p I z) x t) ?_
  rw [doubleTraceReindexFib, ContinuousLinearMap.comp_apply, domDomCongrFibRank_apply]
  rfl

private theorem lieCorr0VBFib_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (lieCorr0VBFib (I := I) g₀ g₁ x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun x : M => Tensor0SSpace 2 I x)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun x => lieCorr0VBFib (I := I) g₀ g₁ x)
  intro Y
  have hip : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SSpace 1 I z) x
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x
          ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x) (Y x))) :=
    (Tensor0SBundle.contract_Tensor0SField (𝕜 := ℝ) (I := I) (n := (∞ : WithTop ℕ∞)) 1 Y
      (PDE.DeTurck.deTurckVF (I := I) g₁ g₀)).contMDiff
  have hprod := lieCorr0_prod_section_contMDiff (I := I) (p := 1) (q := 3)
    (fun x => Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x
      ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x) (Y x))
    (fun x => metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)
    hip (metricConnDiffLoweredFib_contMDiff (I := I) g₁ g₁ g₀)
  have htr := lieCorr0TraceStep_section_contMDiff (I := I) g₁ 2 lieCorr0VBPerm
    (fun x => tensor0SProdKappaFib (I := I) x (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x
        ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x) (Y x)))
    hprod
  have hsmul : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        ((2 : ℝ) • doubleTraceReindexFib (I := I) g₁ 2 lieCorr0VBPerm x
          (tensor0SProdKappaFib (I := I) x (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)
            (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x
              ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x) (Y x))))) :=
    ContMDiff.smul_section contMDiff_const htr
  refine hsmul.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x t) ?_
  rw [lieCorr0VBFib]
  rfl

private theorem lieCorr0AMixHalfFib_section_contMDiff
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (lieCorr0AMixHalfFib (I := I) g₀ g₁ g_bg x (Y x))) := by
  classical
  have hprod1 := lieCorr0_prod_section_contMDiff (I := I) (p := 2) (q := 3)
    (fun x => Y x)
    (fun x => metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)
    Y.contMDiff (metricConnDiffLoweredFib_contMDiff (I := I) g₁ g₁ g₀)
  have htr1 := lieCorr0TraceStep_section_contMDiff (I := I) g₁ 3 lieCorr0AMixPermQ
    (fun x => tensor0SProdKappaFib (I := I) x (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)
      (Y x)) hprod1
  have hprod2 := lieCorr0_prod_section_contMDiff (I := I) (p := 3) (q := 3)
    (fun x => doubleTraceReindexFib (I := I) g₁ 3 lieCorr0AMixPermQ x
      (tensor0SProdKappaFib (I := I) x (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x) (Y x)))
    (fun x => metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
    htr1 (metricConnDiffLoweredFib_contMDiff (I := I) g₁ g₁ g_bg)
  have htr2 := lieCorr0TraceStep_section_contMDiff (I := I) g₁ 4 lieCorr0AMixPerm1
    (fun x => tensor0SProdKappaFib (I := I) x (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
      (doubleTraceReindexFib (I := I) g₁ 3 lieCorr0AMixPermQ x
        (tensor0SProdKappaFib (I := I) x
          (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x) (Y x)))) hprod2
  have htr3 := lieCorr0TraceStep_section_contMDiff (I := I) g₁ 2 lieCorr0AMixPerm2
    (fun x => doubleTraceReindexFib (I := I) g₁ 4 lieCorr0AMixPerm1 x
      (tensor0SProdKappaFib (I := I) x (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
        (doubleTraceReindexFib (I := I) g₁ 3 lieCorr0AMixPermQ x
          (tensor0SProdKappaFib (I := I) x
            (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x) (Y x))))) htr2
  refine htr3.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x t) ?_
  rw [lieCorr0AMixHalfFib]
  rfl

private theorem lieCorr0AMixFib_contMDiff (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (lieCorr0AMixFib (I := I) g₀ g₁ g_bg x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun x : M => Tensor0SSpace 2 I x)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun x => lieCorr0AMixFib (I := I) g₀ g₁ g_bg x)
  intro Y
  have hhalf := lieCorr0AMixHalfFib_section_contMDiff (I := I) g₀ g₁ g_bg Y
  have hswap := lieCorr0_ddc_section_contMDiff (I := I) (Equiv.swap 0 1)
    (fun x => lieCorr0AMixHalfFib (I := I) g₀ g₁ g_bg x (Y x)) hhalf
  have hswap' : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (domDomCongrFibRank (I := I) 2 (Equiv.swap 0 1) x
          (lieCorr0AMixHalfFib (I := I) g₀ g₁ g_bg x (Y x)))) := by
    refine hswap.congr (fun x => ?_)
    refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
      (E := fun z : M => Tensor0SSpace 2 I z) x t) ?_
    rw [domDomCongrFibRank_apply]
  have hadd := ContMDiff.add_section
    (s := fun x => lieCorr0AMixHalfFib (I := I) g₀ g₁ g_bg x (Y x))
    (t := fun x => domDomCongrFibRank (I := I) 2 (Equiv.swap 0 1) x
      (lieCorr0AMixHalfFib (I := I) g₀ g₁ g_bg x (Y x)))
    hhalf hswap'
  have hsmul : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        ((2 : ℝ) • (lieCorr0AMixHalfFib (I := I) g₀ g₁ g_bg x (Y x) +
          domDomCongrFibRank (I := I) 2 (Equiv.swap 0 1) x
            (lieCorr0AMixHalfFib (I := I) g₀ g₁ g_bg x (Y x))))) :=
    ContMDiff.smul_section contMDiff_const hadd
  refine hsmul.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x t) ?_
  rw [lieCorr0AMixFib]
  rfl

theorem lieCorr0RiemLoweredFib_section_contMDiff (g₀ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 4 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SSpace 4 I z) x
        (lieCorr0RiemLoweredFib (I := I) g₀ x)) := by
  classical
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x : M => (lieCorr0RiemLoweredFib (I := I) g₀ x : Tensor0SSpace 4 I x))).mpr ?_
  intro σ x₀
  set b := Module.finBasis ℝ E with hb
  set e₁ := trivializationAt E (TangentSpace I : M → Type _) x₀ with he₁def
  have he₁ : x₀ ∈ e₁.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
  obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
  have hscalar : ContMDiff I 𝓘(ℝ) ∞
      (fun x : M => g₀.inner x
        (Integral.Connection.riemannOp (LeviCivita (I := I) g₀) x
          ((Y (σ 0)) x) ((Y (σ 1)) x) ((Y (σ 2)) x)) ((Y (σ 3)) x)) :=
    Integral.Connection.mixedKernelScalar_global (I := I) g₀ g₀
      (Y (σ 0)).contMDiff (Y (σ 3)).contMDiff (Y (σ 1)).contMDiff (Y (σ 2)).contMDiff
  refine (hscalar.contMDiffAt).congr_of_eventuallyEq ?_
  have h_base₁ : ∀ᶠ x in 𝓝 x₀, x ∈ e₁.baseSet := e₁.open_baseSet.mem_nhds he₁
  filter_upwards [h_base₁, hY] with x hx₁ hYx
  rw [continuousMultilinearMap_basis_repr]
  have hframe' : ∀ j : Fin 4, e₁.symmL ℝ x (b (σ j)) = (Y (σ j)) x := by
    intro j
    rw [hYx (σ j), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
    simp [Trivialization.basisAt]
  change Tensor0SSpace.toModel (lieCorr0RiemLoweredFib (I := I) g₀ x)
      (fun j : Fin 4 => e₁.symmL ℝ x (b (σ j))) = _
  rw [lieCorr0RiemLoweredFib_toModel]
  rw [hframe' 0, hframe' 1, hframe' 2, hframe' 3]

private theorem lieCorr0RiemFib_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (deTurckLieRemainderCurvatureFib (I := I) g₀ g₁ x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun x : M => Tensor0SSpace 2 I x)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun x => deTurckLieRemainderCurvatureFib (I := I) g₀ g₁ x)
  intro Y
  have hprod := lieCorr0_prod_section_contMDiff (I := I) (p := 2) (q := 4)
    (fun x => Y x) (fun x => lieCorr0RiemLoweredFib (I := I) g₀ x)
    Y.contMDiff (lieCorr0RiemLoweredFib_section_contMDiff (I := I) g₀)
  have htr1 := lieCorr0TraceStep_section_contMDiff (I := I) g₀ 4 lieCorr0RiemPerm1
    (fun x => tensor0SProdKappaFib (I := I) x (lieCorr0RiemLoweredFib (I := I) g₀ x) (Y x))
    hprod
  have htr2 := lieCorr0TraceStep_section_contMDiff (I := I) g₁ 2 lieCorr0RiemPerm2
    (fun x => doubleTraceReindexFib (I := I) g₀ 4 lieCorr0RiemPerm1 x
      (tensor0SProdKappaFib (I := I) x (lieCorr0RiemLoweredFib (I := I) g₀ x) (Y x))) htr1
  have hsmul : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        ((-1 : ℝ) • doubleTraceReindexFib (I := I) g₁ 2 lieCorr0RiemPerm2 x
          (doubleTraceReindexFib (I := I) g₀ 4 lieCorr0RiemPerm1 x
            (tensor0SProdKappaFib (I := I) x
              (lieCorr0RiemLoweredFib (I := I) g₀ x) (Y x))))) :=
    ContMDiff.smul_section contMDiff_const htr2
  refine hsmul.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x t) ?_
  rw [deTurckLieRemainderCurvatureFib]
  rfl

noncomputable def deTurckLieRemainderTotalFib (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  deTurckLieRemainderEndoSlotInsertFib (I := I) g₀ g₁ g_bg x + lieCorr0VBFib (I := I) g₀ g₁ x +
    lieCorr0AMixFib (I := I) g₀ g₁ g_bg x + deTurckLieRemainderCurvatureFib (I := I) g₀ g₁ x

private theorem lieCorr0TotalFib_contMDiff (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (deTurckLieRemainderTotalFib (I := I) g₀ g₁ g_bg x))) := by
  classical
  have h12 := ContMDiff.add_section
    (s := fun x => (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (deTurckLieRemainderEndoSlotInsertFib (I := I) g₀ g₁ g_bg x)))
    (t := fun x => (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (lieCorr0VBFib (I := I) g₀ g₁ x)))
    (lieCorr0InsertFib_contMDiff (I := I) g₀ g₁ g_bg)
    (lieCorr0VBFib_contMDiff (I := I) g₀ g₁)
  have h123 := ContMDiff.add_section
    (s := fun x => (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (deTurckLieRemainderEndoSlotInsertFib (I := I) g₀ g₁ g_bg x)) +
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (lieCorr0VBFib (I := I) g₀ g₁ x)))
    (t := fun x => (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (lieCorr0AMixFib (I := I) g₀ g₁ g_bg x)))
    h12 (lieCorr0AMixFib_contMDiff (I := I) g₀ g₁ g_bg)
  have h1234 := ContMDiff.add_section
    (s := fun x => ((show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (deTurckLieRemainderEndoSlotInsertFib (I := I) g₀ g₁ g_bg x)) +
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (lieCorr0VBFib (I := I) g₀ g₁ x))) +
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (lieCorr0AMixFib (I := I) g₀ g₁ g_bg x)))
    (t := fun x => (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (deTurckLieRemainderCurvatureFib (I := I) g₀ g₁ x)))
    h123 (lieCorr0RiemFib_contMDiff (I := I) g₀ g₁)
  refine h1234.congr (fun x => ?_)
  refine congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) x) ?_
  rw [deTurckLieRemainderTotalFib]
  rfl

noncomputable def deTurckLieRemainderField (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (deTurckLieRemainderTotalFib (I := I) g₀ g₁ g_bg x))
      contMDiff_toFun := lieCorr0TotalFib_contMDiff (I := I) g₀ g₁ g_bg }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

private theorem lieCorr0Field_toSection (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    (deTurckLieRemainderField (I := I) (M := M) g₀ g₁ g_bg).toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (deTurckLieRemainderTotalFib (I := I) g₀ g₁ g_bg x)) :=
  rfl

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (deTurckVF_realizedFam_jointContMDiffOn metricConnDiffLowered_selfFam_jointContMDiffOn metricConnDiffLowered_bgFam_jointContMDiffOn jointTensor0SProd_local deTurckLieWEndo_realizedFam_jointContMDiffOn deTurckLieCoeffField deTurckLieCoeffField_realizedFam_jointSmooth linearizedRicciThreeArmHjoint)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (interiorProductField_jointContMDiffOn_vecJoint inverseMetricSharpField_realizedFam_jointContMDiffOn domDomCongrField_jointContMDiffOn cometricDoubleTraceFib_realizedFam_jointContMDiffOn slotInsertEndo0Field_apply_jointContMDiffOn slotInsertEndo1Field_apply_jointContMDiffOn contMDiffOn_clm_section_of_pointwise_joint_manifold_time)
open DifferentialGeometry.Integral.L2 (SmoothCcTensor)

section LieCorr0Joint

variable (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
variable {δ δ' : ℝ}

private theorem lieCorr0_jhom_sub_local {S : Set ℝ}
    (A B : ∀ p : M × ℝ, TangentSpace I p.1 →L[ℝ] TangentSpace I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) p.1 (A p))
      ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) p.1 (B p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) p.1 (A p - B p))
      ((Set.univ : Set M) ×ˢ S) := by
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (E →L[ℝ] E)
    (fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := E →L[ℝ] E)
    (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := E →L[ℝ] E)
    (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z)).mp (hB p₀ hp₀)
  refine (hA'.2.sub hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_sub (A p) (B p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_sub
      (A p₀) (B p₀)

private theorem lieCorr0_jhom_smulConst_local {S : Set ℝ} (c : ℝ)
    (A : ∀ p : M × ℝ, TangentSpace I p.1 →L[ℝ] TangentSpace I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) p.1 (A p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) p.1 (c • A p))
      ((Set.univ : Set M) ×ˢ S) := by
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (E →L[ℝ] E)
    (fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := E →L[ℝ] E)
    (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z)).mp (hA p₀ hp₀)
  refine ((contMDiffWithinAt_const (c := c)).smul hA'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_smul c (A p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_smul
      c (A p₀)

private theorem lieCorr0_j0S_add_local {d : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SSpace d I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SSpace d I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SSpace d I z) p.1 (B p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SSpace d I z) p.1 (A p + B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) d
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SModel d ℝ E)
    (fun z : M => Tensor0SSpace d I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SSpace d I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SSpace d I z)).mp (hB p₀ hp₀)
  refine (hA'.2.add hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_add (A p) (B p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_add
      (A p₀) (B p₀)

private theorem lieCorr0_j0S_smulConst_local {d : ℕ} {S : Set ℝ} (c : ℝ)
    (A : ∀ p : M × ℝ, Tensor0SSpace d I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SSpace d I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SSpace d I z) p.1 (c • A p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) d
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SModel d ℝ E)
    (fun z : M => Tensor0SSpace d I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SSpace d I z)).mp (hA p₀ hp₀)
  refine ((contMDiffWithinAt_const (c := c)).smul hA'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_smul c (A p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_smul
      c (A p₀)

private theorem lieCorr0_toModel_g0Flat (g : SmoothRiemannianMetric I M) (x : M)
    (w t : TangentSpace I x) :
    Tensor0SSpace.toModel
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g x w)
        (Fin.cons t (fun i => Fin.elim0 i)) = g.inner x w t := by
  have h1 : Tensor0SSpace.toModel
      (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g x w)
      (Fin.cons t (fun i => Fin.elim0 i)) =
      (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g x w)
        (fun _ : Fin 1 => t) := by
    change (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g x w)
      (Fin.cons t (fun i => Fin.elim0 i)) = _
    congr 1
    funext j
    refine Fin.cases rfl (fun j => j.elim0) j
  rw [h1, ← Tensor0SBundle.cotangentToDual_apply (I := I) (x := x) _ t]
  exact DifferentialGeometry.Analysis.Sobolev.TensorHilbert.cotangentToDual_g0FlatCLM
    (I := I) g x w t

private theorem lieCorr0_connDiffVF_apply_jointContMDiffOn
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (gP : SmoothRiemannianMetric I M)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
        (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1
          ((PDE.DeTurck.deTurckVF (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) gP :
              Π b : M, TangentSpace I b) p.1) (Z p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hM := metricConnDiffLowered_selfFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
  have hW := deTurckVF_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ' gP
  have hι1 := interiorProductField_jointContMDiffOn_vecJoint (I := I) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (X := fun p : M × ℝ => (PDE.DeTurck.deTurckVF (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) gP : Π b : M, TangentSpace I b) p.1) hW
    (α := fun p : M × ℝ => metricConnDiffLoweredFib (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1) hM
  have hZjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1 (Z p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    Z.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hι2 := interiorProductField_jointContMDiffOn_vecJoint (I := I) (s := 1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (X := fun p : M × ℝ => Z p.1) hZjoint
    (α := fun p : M × ℝ => Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 2 p.1
      ((PDE.DeTurck.deTurckVF (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) gP : Π b : M, TangentSpace I b) p.1)
      (metricConnDiffLoweredFib (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2)
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1)) hι1
  have hsharp := ContMDiffOn.clm_bundle_apply (b := Prod.fst)
    (inverseMetricSharpField_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ') hι2
  refine hsharp.congr (fun p hp => ?_)
  refine congrArg (fun t => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1 t) ?_
  have hform : Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 p.1 (Z p.1)
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 2 p.1
        ((PDE.DeTurck.deTurckVF (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) gP : Π b : M, TangentSpace I b) p.1)
        (metricConnDiffLoweredFib (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1)) =
      DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1
        (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1
          ((PDE.DeTurck.deTurckVF (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) gP :
              Π b : M, TangentSpace I b) p.1) (Z p.1)) := by
    apply Tensor0SSpace.toModel_injective
    apply ContinuousMultilinearMap.ext
    intro m
    have hm : m = Fin.cons (m 0) (fun i => Fin.elim0 i) := by
      funext j
      refine Fin.cases rfl (fun j => j.elim0) j
    have e1 : Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 p.1 (Z p.1)
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 2 p.1
            ((PDE.DeTurck.deTurckVF (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' p.2) gP :
                Π b : M, TangentSpace I b) p.1)
            (metricConnDiffLoweredFib (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' p.2)
              (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1))) m =
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2).inner p.1
          (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1
            ((PDE.DeTurck.deTurckVF (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' p.2) gP :
                Π b : M, TangentSpace I b) p.1) (Z p.1)) (m 0) := by
      change Tensor0SSpace.toModel
        (metricConnDiffLoweredFib (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1)
        (Fin.cons ((PDE.DeTurck.deTurckVF (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) gP :
              Π b : M, TangentSpace I b) p.1)
          (Fin.cons (Z p.1) m)) = _
      rw [metricConnDiffLoweredFib_toModel]
      rfl
    have e2 : Tensor0SSpace.toModel
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1
          (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1
            ((PDE.DeTurck.deTurckVF (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' p.2) gP :
                Π b : M, TangentSpace I b) p.1) (Z p.1))) m =
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2).inner p.1
          (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1
            ((PDE.DeTurck.deTurckVF (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' p.2) gP :
                Π b : M, TangentSpace I b) p.1) (Z p.1)) (m 0) := by
      refine Eq.trans (congrArg (Tensor0SSpace.toModel
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1
          (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1
            ((PDE.DeTurck.deTurckVF (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' p.2) gP :
                Π b : M, TangentSpace I b) p.1) (Z p.1)))) hm) ?_
      exact lieCorr0_toModel_g0Flat (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1 _ (m 0)
    exact e1.trans e2.symm
  rw [hform, DifferentialGeometry.Analysis.Sobolev.TensorHilbert.inverseMetricSharpFib_g0FlatCLM]

private theorem lieCorr0_connDiffVFEndo_jointContMDiffOn
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (gP : SmoothRiemannianMetric I M) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) p.1
        (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1
          ((PDE.DeTurck.deTurckVF (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) gP :
              Π b : M, TangentSpace I b) p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  apply contMDiffOn_clm_section_of_pointwise_joint_manifold_time (I := I) (M := M)
    (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
    (F₂ := E) (V₂ := fun x : M => TangentSpace I x)
    (φ := fun p : M × ℝ =>
      PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1
        ((PDE.DeTurck.deTurckVF (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) gP :
            Π b : M, TangentSpace I b) p.1))
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
  intro Z
  exact lieCorr0_connDiffVF_apply_jointContMDiffOn (I := I) g₀ T T' hδ hδ' gP Z

private theorem lieCorr0NEndo_realizedFam_jointContMDiffOn
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) p.1
        (deTurckLieRemainderEndo (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hBV := lieCorr0_connDiffVFEndo_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g₀
  have hBW := lieCorr0_connDiffVFEndo_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg
  have hW := deTurckLieWEndo_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g₀
  have hsub1 := lieCorr0_jhom_sub_local (I := I)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ hBV hBW
  have hsub2 := lieCorr0_jhom_sub_local (I := I)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ hsub1 hW
  refine hsub2.congr (fun p _ => ?_)
  rfl

private theorem lieCorr0TraceStepFam_jointContMDiffOn (p : ℕ) (σ : Equiv.Perm (Fin (p + 2)))
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (Z : ∀ pp : M × ℝ, Tensor0SSpace (p + 2) I pp.1)
    (hZ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel (p + 2) ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel (p + 2) ℝ E)
        (E := fun z : M => Tensor0SSpace (p + 2) I z) pp.1 (Z pp))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ'))) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel p ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel p ℝ E)
        (E := fun z : M => Tensor0SSpace p I z) pp.1
        (doubleTraceReindexFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) p σ pp.1 (Z pp)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hddc := domDomCongrField_jointContMDiffOn (I := I) σ
    (S := realizedSmallSet (δ := δ) (δ' := δ')) Z hZ
  have htr := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := p)
    g₀ T T' hδ hδ' _ hddc
  refine htr.congr (fun pp _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel p ℝ E)
    (E := fun z : M => Tensor0SSpace p I z) pp.1 t) ?_
  rw [doubleTraceReindexFib, ContinuousLinearMap.comp_apply, domDomCongrFibRank_apply]

private theorem lieCorr0TraceStepFixed_jointContMDiffOn (g : SmoothRiemannianMetric I M)
    (p : ℕ) (σ : Equiv.Perm (Fin (p + 2))) {S : Set ℝ}
    (Z : ∀ pp : M × ℝ, Tensor0SSpace (p + 2) I pp.1)
    (hZ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel (p + 2) ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel (p + 2) ℝ E)
        (E := fun z : M => Tensor0SSpace (p + 2) I z) pp.1 (Z pp))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel p ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel p ℝ E)
        (E := fun z : M => Tensor0SSpace p I z) pp.1
        (doubleTraceReindexFib (I := I) g p σ pp.1 (Z pp)))
      ((Set.univ : Set M) ×ˢ S) := by
  have hddcJ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel (p + 2) ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel (p + 2) ℝ E)
        (E := fun z : M => Tensor0SSpace (p + 2) I z) pp.1
        (Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := pp.1)
          (ContinuousMultilinearMap.domDomCongr σ (Tensor0SSpace.toModel (Z pp)))))
      ((Set.univ : Set M) ×ˢ S) :=
    domDomCongrField_jointContMDiffOn (I := I) σ (S := S) Z hZ
  have hhom : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel (p + 2) p ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (TensorRSModel (p + 2) p ℝ E)
        (E := fun z : M => TensorRSSpace (p + 2) p I z) pp.1
        (cometricDoubleTraceFib (I := I) g p pp.1))
      ((Set.univ : Set M) ×ˢ S) :=
    (cometricDoubleTraceFib_contMDiff (I := I) g p).comp_contMDiffOn contMDiffOn_fst
  have happ := ContMDiffOn.clm_bundle_apply (b := Prod.fst) hhom hddcJ
  refine happ.congr (fun pp _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel p ℝ E)
    (E := fun z : M => Tensor0SSpace p I z) pp.1 t) ?_
  rw [doubleTraceReindexFib, ContinuousLinearMap.comp_apply, domDomCongrFibRank_apply]

private theorem lieCorr0InsertFib_apply_jointContMDiffOn
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) pp.1
        (deTurckLieRemainderEndoSlotInsertFib (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) g_bg pp.1
          (Y pp.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hΛ := lieCorr0NEndo_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg
  have hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) pp.1 (Y pp.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have h0 := slotInsertEndo0Field_apply_jointContMDiffOn (I := I) (M := M) (d := 1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (Λ := fun pp : M × ℝ =>
      deTurckLieRemainderEndo (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) g_bg pp.1) hΛ
    (A := fun pp : M × ℝ => Y pp.1) hY
  have h1 := slotInsertEndo1Field_apply_jointContMDiffOn (I := I) (M := M) (d := 0)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) g₀
    (Λ := fun pp : M × ℝ =>
      deTurckLieRemainderEndo (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) g_bg pp.1) hΛ
    (A := fun pp : M × ℝ => Y pp.1) hY
  have hsum := lieCorr0_j0S_add_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ h0 h1
  refine hsum.congr (fun pp _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) pp.1 t) ?_
  rw [deTurckLieRemainderEndoSlotInsertFib, ContinuousLinearMap.add_apply]

private theorem lieCorr0VBFib_apply_jointContMDiffOn
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) pp.1
        (lieCorr0VBFib (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) pp.1 (Y pp.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) pp.1 (Y pp.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hVF := deTurckVF_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g₀
  have hip := interiorProductField_jointContMDiffOn_vecJoint (I := I) (s := 1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (X := fun pp : M × ℝ => (PDE.DeTurck.deTurckVF (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) g₀ : Π b : M, TangentSpace I b) pp.1) hVF
    (α := fun pp : M × ℝ => Y pp.1) hY
  have hLB := metricConnDiffLowered_selfFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
  have hprod := jointTensor0SProd_local (I := I) (p := 1) (q := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun pp : M × ℝ => Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 pp.1
      ((PDE.DeTurck.deTurckVF (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) g₀ : Π b : M, TangentSpace I b) pp.1)
      (Y pp.1))
    (fun pp : M × ℝ => metricConnDiffLoweredFib (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' pp.2)
      (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) g₀ pp.1)
    hip hLB
  have hprod' : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 4 ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SSpace 4 I z) pp.1
        (tensor0SProdKappaFib (I := I) pp.1
          (metricConnDiffLoweredFib (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' pp.2)
            (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) g₀ pp.1)
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 pp.1
            ((PDE.DeTurck.deTurckVF (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) g₀ :
                Π b : M, TangentSpace I b) pp.1) (Y pp.1))))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine hprod.congr (fun pp _ => ?_)
    refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
      (E := fun z : M => Tensor0SSpace 4 I z) pp.1 t) ?_
    rw [tensor0SProdKappaFib_apply]
  have htr := lieCorr0TraceStepFam_jointContMDiffOn (I := I) g₀ T T' 2 lieCorr0VBPerm hδ hδ' _
    hprod'
  have hs := lieCorr0_j0S_smulConst_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) (2 : ℝ) _ htr
  refine hs.congr (fun pp _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) pp.1 t) ?_
  rw [lieCorr0VBFib]
  rfl

private theorem lieCorr0AMixHalfFib_apply_jointContMDiffOn
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) pp.1
        (lieCorr0AMixHalfFib (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) g_bg pp.1
          (Y pp.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) pp.1 (Y pp.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hLB := metricConnDiffLowered_selfFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
  have hLA := metricConnDiffLowered_bgFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg
  have hprod1 := jointTensor0SProd_local (I := I) (p := 2) (q := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun pp : M × ℝ => Y pp.1)
    (fun pp : M × ℝ => metricConnDiffLoweredFib (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' pp.2)
      (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) g₀ pp.1)
    hY hLB
  have hprod1' : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 5 ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel 5 ℝ E)
        (E := fun z : M => Tensor0SSpace 5 I z) pp.1
        (tensor0SProdKappaFib (I := I) pp.1
          (metricConnDiffLoweredFib (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' pp.2)
            (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) g₀ pp.1) (Y pp.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine hprod1.congr (fun pp _ => ?_)
    refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 5 ℝ E)
      (E := fun z : M => Tensor0SSpace 5 I z) pp.1 t) ?_
    rw [tensor0SProdKappaFib_apply]
  have htr1 := lieCorr0TraceStepFam_jointContMDiffOn (I := I) g₀ T T' 3 lieCorr0AMixPermQ
    hδ hδ' _ hprod1'
  have hprod2 := jointTensor0SProd_local (I := I) (p := 3) (q := 3)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun pp : M × ℝ => doubleTraceReindexFib (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) 3 lieCorr0AMixPermQ pp.1
      (tensor0SProdKappaFib (I := I) pp.1
        (metricConnDiffLoweredFib (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' pp.2)
          (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) g₀ pp.1) (Y pp.1)))
    (fun pp : M × ℝ => metricConnDiffLoweredFib (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' pp.2)
      (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) g_bg pp.1)
    htr1 hLA
  have hprod2' : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 6 ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel 6 ℝ E)
        (E := fun z : M => Tensor0SSpace 6 I z) pp.1
        (tensor0SProdKappaFib (I := I) pp.1
          (metricConnDiffLoweredFib (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' pp.2)
            (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) g_bg pp.1)
          (doubleTraceReindexFib (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) 3 lieCorr0AMixPermQ pp.1
            (tensor0SProdKappaFib (I := I) pp.1
              (metricConnDiffLoweredFib (I := I)
                (realizedFam (I := I) g₀ T T' hδ hδ' pp.2)
                (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) g₀ pp.1) (Y pp.1)))))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine hprod2.congr (fun pp _ => ?_)
    refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 6 ℝ E)
      (E := fun z : M => Tensor0SSpace 6 I z) pp.1 t) ?_
    rw [tensor0SProdKappaFib_apply]
  have htr2 := lieCorr0TraceStepFam_jointContMDiffOn (I := I) g₀ T T' 4 lieCorr0AMixPerm1
    hδ hδ' _ hprod2'
  have htr3 := lieCorr0TraceStepFam_jointContMDiffOn (I := I) g₀ T T' 2 lieCorr0AMixPerm2
    hδ hδ' _ htr2
  refine htr3.congr (fun pp _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) pp.1 t) ?_
  rw [lieCorr0AMixHalfFib]
  rfl

private theorem lieCorr0AMixFib_apply_jointContMDiffOn
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) pp.1
        (lieCorr0AMixFib (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) g_bg pp.1
          (Y pp.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hhalf := lieCorr0AMixHalfFib_apply_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg Y
  have hswapRaw := domDomCongrField_jointContMDiffOn (I := I) (Equiv.swap 0 1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun pp : M × ℝ => lieCorr0AMixHalfFib (I := I) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) g_bg pp.1 (Y pp.1)) hhalf
  have hswap : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) pp.1
        (domDomCongrFibRank (I := I) 2 (Equiv.swap 0 1) pp.1
          (lieCorr0AMixHalfFib (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) g_bg pp.1 (Y pp.1))))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine hswapRaw.congr (fun pp _ => ?_)
    refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
      (E := fun z : M => Tensor0SSpace 2 I z) pp.1 t) ?_
    rw [domDomCongrFibRank_apply]
  have hadd := lieCorr0_j0S_add_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ hhalf hswap
  have hs := lieCorr0_j0S_smulConst_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) (2 : ℝ) _ hadd
  refine hs.congr (fun pp _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) pp.1 t) ?_
  rw [lieCorr0AMixFib]
  rfl

private theorem lieCorr0RiemFib_apply_jointContMDiffOn
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) pp.1
        (deTurckLieRemainderCurvatureFib (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) pp.1 (Y pp.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) pp.1 (Y pp.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hR : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 4 ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SSpace 4 I z) pp.1
        (lieCorr0RiemLoweredFib (I := I) g₀ pp.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    (lieCorr0RiemLoweredFib_section_contMDiff (I := I) g₀).comp_contMDiffOn contMDiffOn_fst
  have hprod := jointTensor0SProd_local (I := I) (p := 2) (q := 4)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun pp : M × ℝ => Y pp.1)
    (fun pp : M × ℝ => lieCorr0RiemLoweredFib (I := I) g₀ pp.1)
    hY hR
  have hprod' : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 6 ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel 6 ℝ E)
        (E := fun z : M => Tensor0SSpace 6 I z) pp.1
        (tensor0SProdKappaFib (I := I) pp.1 (lieCorr0RiemLoweredFib (I := I) g₀ pp.1) (Y pp.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine hprod.congr (fun pp _ => ?_)
    refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 6 ℝ E)
      (E := fun z : M => Tensor0SSpace 6 I z) pp.1 t) ?_
    rw [tensor0SProdKappaFib_apply]
  have htr1 := lieCorr0TraceStepFixed_jointContMDiffOn (I := I) g₀ 4 lieCorr0RiemPerm1
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ hprod'
  have htr2 := lieCorr0TraceStepFam_jointContMDiffOn (I := I) g₀ T T' 2 lieCorr0RiemPerm2
    hδ hδ' _ htr1
  have hs := lieCorr0_j0S_smulConst_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) (-1 : ℝ) _ htr2
  refine hs.congr (fun pp _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) pp.1 t) ?_
  rw [deTurckLieRemainderCurvatureFib]
  rfl

private theorem lieCorr0TotalFib_apply_jointContMDiffOn
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) pp.1
        (deTurckLieRemainderTotalFib (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) g_bg pp.1
          (Y pp.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have h1 := lieCorr0InsertFib_apply_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg Y
  have h2 := lieCorr0VBFib_apply_jointContMDiffOn (I := I) g₀ T T' hδ hδ' Y
  have h3 := lieCorr0AMixFib_apply_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg Y
  have h4 := lieCorr0RiemFib_apply_jointContMDiffOn (I := I) g₀ T T' hδ hδ' Y
  have h12 := lieCorr0_j0S_add_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ h1 h2
  have h123 := lieCorr0_j0S_add_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ h12 h3
  have h1234 := lieCorr0_j0S_add_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ h123 h4
  refine h1234.congr (fun pp _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) pp.1 t) ?_
  rw [deTurckLieRemainderTotalFib]
  rfl

theorem lieCorr0Field_realizedFam_jointSmooth
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2
      (fun s => deTurckLieRemainderField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) (δ := δ) (δ' := δ') := by
  rw [linearizedRicciThreeArmHjoint]
  have hCLM := contMDiffOn_clm_section_of_pointwise_joint_manifold_time (I := I) (M := M)
    (F₁ := Tensor0SModel 2 ℝ E)
    (V₁ := fun x : M => Tensor0SSpace 2 I x)
    (F₂ := Tensor0SModel 2 ℝ E)
    (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun pp : M × ℝ =>
      deTurckLieRemainderTotalFib (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) g_bg pp.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun Y => lieCorr0TotalFib_apply_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg Y)
  refine hCLM.congr (fun pp _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) pp.1 t) ?_
  rw [lieCorr0Field_toSection]
  rfl

theorem deTurckLieCoeffField_add_deTurckLieRemainderField_realizedFam_jointSmooth
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2
      (fun s => deTurckLieCoeffField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg +
        deTurckLieRemainderField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) (δ := δ) (δ' := δ') := by
  have h1 := deTurckLieCoeffField_realizedFam_jointSmooth (I := I) g₀ T T' hδ hδ' g_bg
  have h2 := lieCorr0Field_realizedFam_jointSmooth (I := I) g₀ T T' hδ hδ' g_bg
  rw [linearizedRicciThreeArmHjoint] at h1 h2 ⊢
  have hadd := lieArm_jointRS_add_local (I := I) (r := 2) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => (deTurckLieCoeffField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg).toSection p.1)
    (fun p : M × ℝ => (deTurckLieRemainderField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg).toSection p.1)
    h1 h2
  refine hadd.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) p.1 t) ?_
  rw [smoothCcTensor_toSection_add_apply]

section LieCorr0Eval

open DifferentialGeometry.Integral.DivergenceTheorem (chartInvGramMatrix partialDeriv chartChristoffel)
open DifferentialGeometry.Integral.Measure (chartGramMatrix)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (deTurckLieCovDerivW_chartBasis_eq)

variable (g₀ g₁ g_bg : SmoothRiemannianMetric I M)

private noncomputable def lieCorr0NScalar (x : M) (i p : Fin (Module.finrank ℝ E)) : ℝ :=
  (∑ m : Fin (Module.finrank ℝ E),
      PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) g₁ g₀ x m (extChartAt I x x) *
        (chartChristoffel (I := I) g₁ x i m p (extChartAt I x x) -
          chartChristoffel (I := I) g₀ x i m p (extChartAt I x x)))
    - (∑ m : Fin (Module.finrank ℝ E),
        PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) g₁ g_bg x m
            (extChartAt I x x) *
          (chartChristoffel (I := I) g₁ x i m p (extChartAt I x x) -
            chartChristoffel (I := I) g₀ x i m p (extChartAt I x x)))
    - (partialDeriv (E := E) i
        (fun y => PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) g₁ g₀ x p y)
        (extChartAt I x x) +
      ∑ m : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g₁ x i m p (extChartAt I x x) *
          PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) g₁ g₀ x m
            (extChartAt I x x))

private lemma lieCorr0_connDiffVF_chartBasis (gP : SmoothRiemannianMetric I M) (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    PDE.DeTurck.connDiff (I := I) g₁ g₀ x
        ((PDE.DeTurck.deTurckVF (I := I) g₁ gP : Π b : M, TangentSpace I b) x)
        ((chartModelBasis E) i : TangentSpace I x) =
      ∑ p : Fin (Module.finrank ℝ E),
        (∑ m : Fin (Module.finrank ℝ E),
          PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) g₁ gP x m
              (extChartAt I x x) *
            (chartChristoffel (I := I) g₁ x i m p (extChartAt I x x) -
              chartChristoffel (I := I) g₀ x i m p (extChartAt I x x))) •
          ((chartModelBasis E) p : TangentSpace I x) := by
  classical
  have hflip : PDE.DeTurck.connDiff (I := I) g₁ g₀ x
      ((PDE.DeTurck.deTurckVF (I := I) g₁ gP : Π b : M, TangentSpace I b) x)
      ((chartModelBasis E) i : TangentSpace I x) =
      ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x).flip
        ((chartModelBasis E) i : TangentSpace I x))
        ((PDE.DeTurck.deTurckVF (I := I) g₁ gP : Π b : M, TangentSpace I b) x) := rfl
  rw [hflip]
  rw [show (PDE.DeTurck.deTurckVF (I := I) g₁ gP : Π b : M, TangentSpace I b) x =
      (PDE.DeTurck.deTurckVF (I := I) g₁ gP :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x from rfl]
  rw [PDE.DeTurck.deTurckVF_apply_eq_chartDeTurckVFComp_sum_self (I := I) g₁ gP x]
  rw [map_sum]
  rw [show (∑ m : Fin (Module.finrank ℝ E),
      ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x).flip
        ((chartModelBasis E) i : TangentSpace I x))
        (PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) g₁ gP x m
            (extChartAt I x x) •
          ((chartModelBasis E) m : TangentSpace I x))) =
    ∑ m : Fin (Module.finrank ℝ E),
      PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) g₁ gP x m
          (extChartAt I x x) •
        (∑ p : Fin (Module.finrank ℝ E),
          (chartChristoffel (I := I) g₁ x i m p (extChartAt I x x) -
            chartChristoffel (I := I) g₀ x i m p (extChartAt I x x)) •
          ((chartModelBasis E) p : TangentSpace I x)) from
    Finset.sum_congr rfl (fun m _ => by
      rw [map_smul]
      refine congrArg (fun t => PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I)
        g₁ gP x m (extChartAt I x x) • t) ?_
      exact lieArm_connDiff_chartBasis_center (I := I) g₁ g₀ x m i)]
  rw [show (∑ m : Fin (Module.finrank ℝ E),
      PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) g₁ gP x m
          (extChartAt I x x) •
        (∑ p : Fin (Module.finrank ℝ E),
          (chartChristoffel (I := I) g₁ x i m p (extChartAt I x x) -
            chartChristoffel (I := I) g₀ x i m p (extChartAt I x x)) •
          ((chartModelBasis E) p : TangentSpace I x))) =
    ∑ m : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
      (PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) g₁ gP x m
          (extChartAt I x x) *
        (chartChristoffel (I := I) g₁ x i m p (extChartAt I x x) -
          chartChristoffel (I := I) g₀ x i m p (extChartAt I x x))) •
        ((chartModelBasis E) p : TangentSpace I x) from
    Finset.sum_congr rfl (fun m _ => by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [smul_smul])]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.sum_smul]

private lemma lieCorr0NEndo_chartBasis (x : M) (i : Fin (Module.finrank ℝ E)) :
    deTurckLieRemainderEndo (I := I) g₀ g₁ g_bg x ((chartModelBasis E) i : TangentSpace I x) =
      ∑ p : Fin (Module.finrank ℝ E),
        lieCorr0NScalar (I := I) (M := M) g₀ g₁ g_bg x i p •
          ((chartModelBasis E) p : TangentSpace I x) := by
  classical
  rw [deTurckLieRemainderEndo]
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply]
  rw [lieCorr0_connDiffVF_chartBasis (I := I) g₀ g₁ g₀ x i,
    lieCorr0_connDiffVF_chartBasis (I := I) g₀ g₁ g_bg x i]
  rw [deTurckLieWEndo_apply (I := I) g₁ g₀ x ((chartModelBasis E) i : TangentSpace I x)]
  rw [deTurckLieCovDerivW_chartBasis_eq (I := I) g₁ g₀ x i]
  rw [show (∑ p : Fin (Module.finrank ℝ E),
      (partialDeriv (E := E) i
          (fun y => PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) g₁ g₀ x p y)
          (extChartAt I x x) +
        ∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₁ x i m p (extChartAt I x x) *
            PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) g₁ g₀ x m
              (extChartAt I x x)) •
        DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) x p x) =
    ∑ p : Fin (Module.finrank ℝ E),
      (partialDeriv (E := E) i
          (fun y => PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) g₁ g₀ x p y)
          (extChartAt I x x) +
        ∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₁ x i m p (extChartAt I x x) *
            PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) g₁ g₀ x m
              (extChartAt I x x)) •
        ((chartModelBasis E) p : TangentSpace I x) from
    Finset.sum_congr rfl (fun p _ => by
      rw [DifferentialGeometry.Integral.Connection.chartBasisVecFiber_self (I := I) x p])]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [lieCorr0NScalar, sub_smul, sub_smul]

private lemma lieCorr0_upd0 (a b w : E) :
    Function.update ![a, b] (0 : Fin 2) w = ![w, b] := by
  funext k
  fin_cases k <;> simp [Function.update]

private lemma lieCorr0_upd1 (a b w : E) :
    Function.update ![a, b] (1 : Fin 2) w = ![a, w] := by
  funext k
  fin_cases k <;> simp [Function.update]

private lemma lieCorr0_cmm2_expand_slot0
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ)
    (c : Fin (Module.finrank ℝ E) → ℝ) (w : E) :
    f ![∑ p : Fin (Module.finrank ℝ E), c p • (chartModelBasis E) p, w] =
      ∑ p : Fin (Module.finrank ℝ E), c p * f ![(chartModelBasis E) p, w] := by
  classical
  rw [show (![∑ p : Fin (Module.finrank ℝ E), c p • (chartModelBasis E) p, w] :
      Fin 2 → E) =
    Function.update ![w, w] (0 : Fin 2)
      (∑ p : Fin (Module.finrank ℝ E), c p • (chartModelBasis E) p) from by
    rw [lieCorr0_upd0]]
  change f.toMultilinearMap (Function.update ![w, w] (0 : Fin 2)
    (∑ p : Fin (Module.finrank ℝ E), c p • (chartModelBasis E) p)) = _
  rw [f.toMultilinearMap.map_update_sum (t := Finset.univ) (i := (0 : Fin 2))
    (g := fun p : Fin (Module.finrank ℝ E) => c p • (chartModelBasis E) p) (m := ![w, w])]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [f.toMultilinearMap.map_update_smul (m := ![w, w]) (i := (0 : Fin 2)) (c := c p)
    (x := (chartModelBasis E) p)]
  rw [lieCorr0_upd0]
  rfl

private lemma lieCorr0_cmm2_expand_slot1
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ)
    (c : Fin (Module.finrank ℝ E) → ℝ) (w : E) :
    f ![w, ∑ p : Fin (Module.finrank ℝ E), c p • (chartModelBasis E) p] =
      ∑ p : Fin (Module.finrank ℝ E), c p * f ![w, (chartModelBasis E) p] := by
  classical
  rw [show (![w, ∑ p : Fin (Module.finrank ℝ E), c p • (chartModelBasis E) p] :
      Fin 2 → E) =
    Function.update ![w, w] (1 : Fin 2)
      (∑ p : Fin (Module.finrank ℝ E), c p • (chartModelBasis E) p) from by
    rw [lieCorr0_upd1]]
  change f.toMultilinearMap (Function.update ![w, w] (1 : Fin 2)
    (∑ p : Fin (Module.finrank ℝ E), c p • (chartModelBasis E) p)) = _
  rw [f.toMultilinearMap.map_update_sum (t := Finset.univ) (i := (1 : Fin 2))
    (g := fun p : Fin (Module.finrank ℝ E) => c p • (chartModelBasis E) p) (m := ![w, w])]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [f.toMultilinearMap.map_update_smul (m := ![w, w]) (i := (1 : Fin 2)) (c := c p)
    (x := (chartModelBasis E) p)]
  rw [lieCorr0_upd1]
  rfl

private lemma lieCorr0InsertFib_basis_value (x : M) (D : Tensor0SSpace 2 I x)
    (i j : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel (deTurckLieRemainderEndoSlotInsertFib (I := I) g₀ g₁ g_bg x D)
        ![(chartModelBasis E) i, (chartModelBasis E) j] =
      (∑ p : Fin (Module.finrank ℝ E),
        lieCorr0NScalar (I := I) (M := M) g₀ g₁ g_bg x i p *
          Tensor0SSpace.toModel D ![(chartModelBasis E) p, (chartModelBasis E) j])
      + (∑ p : Fin (Module.finrank ℝ E),
        lieCorr0NScalar (I := I) (M := M) g₀ g₁ g_bg x j p *
          Tensor0SSpace.toModel D ![(chartModelBasis E) i, (chartModelBasis E) p]) := by
  classical
  rw [lieCorr0InsertFib_toModel (I := I) g₀ g₁ g_bg x D]
  have h0 : Function.update
      (![(chartModelBasis E) i, (chartModelBasis E) j] : Fin 2 → E) (0 : Fin 2)
      (deTurckLieRemainderEndo (I := I) g₀ g₁ g_bg x
        ((![(chartModelBasis E) i, (chartModelBasis E) j] : Fin 2 → E) 0)) =
      ![(deTurckLieRemainderEndo (I := I) g₀ g₁ g_bg x
          ((chartModelBasis E) i : TangentSpace I x) : E), (chartModelBasis E) j] := by
    rw [lieCorr0_upd0]
    rfl
  have h1 : Function.update
      (![(chartModelBasis E) i, (chartModelBasis E) j] : Fin 2 → E) (1 : Fin 2)
      (deTurckLieRemainderEndo (I := I) g₀ g₁ g_bg x
        ((![(chartModelBasis E) i, (chartModelBasis E) j] : Fin 2 → E) 1)) =
      ![(chartModelBasis E) i, (deTurckLieRemainderEndo (I := I) g₀ g₁ g_bg x
          ((chartModelBasis E) j : TangentSpace I x) : E)] := by
    rw [lieCorr0_upd1]
    rfl
  rw [h0, h1]
  rw [lieCorr0NEndo_chartBasis (I := I) g₀ g₁ g_bg x i,
    lieCorr0NEndo_chartBasis (I := I) g₀ g₁ g_bg x j]
  rw [show ((∑ p : Fin (Module.finrank ℝ E),
      lieCorr0NScalar (I := I) (M := M) g₀ g₁ g_bg x i p •
        ((chartModelBasis E) p : TangentSpace I x) : TangentSpace I x) : E) =
    (∑ p : Fin (Module.finrank ℝ E),
      lieCorr0NScalar (I := I) (M := M) g₀ g₁ g_bg x i p • (chartModelBasis E) p : E) from rfl]
  rw [show ((∑ p : Fin (Module.finrank ℝ E),
      lieCorr0NScalar (I := I) (M := M) g₀ g₁ g_bg x j p •
        ((chartModelBasis E) p : TangentSpace I x) : TangentSpace I x) : E) =
    (∑ p : Fin (Module.finrank ℝ E),
      lieCorr0NScalar (I := I) (M := M) g₀ g₁ g_bg x j p • (chartModelBasis E) p : E) from rfl]
  rw [lieCorr0_cmm2_expand_slot0 (Tensor0SSpace.toModel D)
    (fun p => lieCorr0NScalar (I := I) (M := M) g₀ g₁ g_bg x i p) ((chartModelBasis E) j),
    lieCorr0_cmm2_expand_slot1 (Tensor0SSpace.toModel D)
    (fun p => lieCorr0NScalar (I := I) (M := M) g₀ g₁ g_bg x j p) ((chartModelBasis E) i)]

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (quadrilinearMapSlotBilinearAt unitModel4SlotBilin_apply cometricFinBasisTrace_eq_chartInvGram_bilin)

private lemma lieCorr0TraceStep_toModel (g : SmoothRiemannianMetric I M) (p : ℕ)
    (σ : Equiv.Perm (Fin (p + 2))) (x : M) (T : Tensor0SSpace (p + 2) I x)
    (u : Fin p → E) :
    Tensor0SSpace.toModel (doubleTraceReindexFib (I := I) g p σ x T) u =
      ∑ k : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel T
          (fun i => (Fin.cons (DeTurck.cometricLmodel (I := I) g x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))
            (Fin.cons ((Module.finBasis ℝ E) k) u) : Fin (p + 2) → E) (σ i)) := by
  classical
  rw [doubleTraceReindexFib, ContinuousLinearMap.comp_apply, domDomCongrFibRank_apply,
    cometricDoubleTraceFib_toModel]
  rw [DeTurck.modelDoubleTrace_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]

private lemma lieCorr0_vbArg (a b v0 v1 : E) :
    (fun i : Fin 4 =>
      (Fin.cons a (Fin.cons b (![v0, v1] : Fin 2 → E)) : Fin 4 → E) (lieCorr0VBPerm i)) =
      ![b, v0, v1, a] := by
  funext i
  fin_cases i <;> rfl

private lemma lieCorr0_upd4_30 (z0 z1 z2 z3 a b : E) :
    Function.update (Function.update (![z0, z1, z2, z3] : Fin 4 → E) (3 : Fin 4) a)
        (0 : Fin 4) b = ![b, z1, z2, a] := by
  funext i
  fin_cases i <;> simp [Function.update]

private lemma lieCorr0_prodKappa_toModel {pq q : ℕ} (x : M)
    (κ : Tensor0SSpace q I x) (D : Tensor0SSpace pq I x) (v : Fin (pq + q) → E) :
    Tensor0SSpace.toModel (tensor0SProdKappaFib (I := I) x κ D) v =
      Tensor0SSpace.toModel D (fun i => v (Fin.castAdd q i)) *
        Tensor0SSpace.toModel κ (fun i => v (Fin.natAdd pq i)) := by
  rw [tensor0SProdKappaFib_apply, Tensor0SSpace.toModel_ofModel,
    Bundle.continuousMultilinearMap.modelProduct_apply]
  rfl

private lemma lieCorr0_ip_toModel (x : M) (V : TangentSpace I x)
    (D : Tensor0SSpace 2 I x) (b : E) :
    Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x V D) ![b] =
      Tensor0SSpace.toModel D ![(V : E), b] := by
  rfl

private lemma lieCorr0_castAdd1 (b v0 v1 a : E) :
    (fun i : Fin 1 => (![b, v0, v1, a] : Fin 4 → E) (Fin.castAdd 3 i)) = ![b] := by
  funext i
  fin_cases i
  rfl

private lemma lieCorr0_natAdd1 (b v0 v1 a : E) :
    (fun i : Fin 3 => (![b, v0, v1, a] : Fin 4 → E) (Fin.natAdd 1 i)) = ![v0, v1, a] := by
  funext i
  fin_cases i <;> rfl

private lemma lieCorr0_D_VF_expand (g₁ gP : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) (b : E) :
    Tensor0SSpace.toModel D
        ![((PDE.DeTurck.deTurckVF (I := I) g₁ gP : Π b' : M, TangentSpace I b') x : E), b] =
      ∑ ρ : Fin (Module.finrank ℝ E),
        PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) g₁ gP x ρ
            (extChartAt I x x) *
          Tensor0SSpace.toModel D ![(chartModelBasis E) ρ, b] := by
  have hV : ((PDE.DeTurck.deTurckVF (I := I) g₁ gP : Π b' : M, TangentSpace I b') x : E) =
      ((∑ ρ : Fin (Module.finrank ℝ E),
        PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) g₁ gP x ρ
            (extChartAt I x x) •
          ((chartModelBasis E) ρ : TangentSpace I x) : TangentSpace I x) : E) := by
    have h1 : (PDE.DeTurck.deTurckVF (I := I) g₁ gP : Π b' : M, TangentSpace I b') x =
        (PDE.DeTurck.deTurckVF (I := I) g₁ gP :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x := rfl
    rw [h1, PDE.DeTurck.deTurckVF_apply_eq_chartDeTurckVFComp_sum_self (I := I) g₁ gP x]
  rw [hV]
  exact lieCorr0_cmm2_expand_slot0 (Tensor0SSpace.toModel D)
    (fun ρ => PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) g₁ gP x ρ
      (extChartAt I x x)) b

private lemma lieCorr0VBFib_basis_value (x : M) (D : Tensor0SSpace 2 I x)
    (i j : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel (lieCorr0VBFib (I := I) g₀ g₁ x D)
        ![(chartModelBasis E) i, (chartModelBasis E) j] =
      2 * ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k l *
          ((∑ c : Fin (Module.finrank ℝ E),
            (chartChristoffel (I := I) g₁ x j i c (extChartAt I x x) -
              chartChristoffel (I := I) g₀ x j i c (extChartAt I x x)) *
              chartGramMatrix (I := I) g₁ x x c l) *
            (∑ ρ : Fin (Module.finrank ℝ E),
              PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) g₁ g₀ x ρ
                  (extChartAt I x x) *
                Tensor0SSpace.toModel D ![(chartModelBasis E) ρ, (chartModelBasis E) k])) := by
  classical
  rw [show lieCorr0VBFib (I := I) g₀ g₁ x D =
      (2 : ℝ) • doubleTraceReindexFib (I := I) g₁ 2 lieCorr0VBPerm x
        (tensor0SProdKappaFib (I := I) x (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x
            ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x) D)) from by
    rw [lieCorr0VBFib]
    rfl]
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  refine congrArg (fun t : ℝ => 2 * t) ?_
  set P4 : Tensor0SSpace 4 I x :=
    tensor0SProdKappaFib (I := I) x (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) 1 x
        ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x) D)
    with hP4
  rw [lieCorr0TraceStep_toModel (I := I) g₁ 2 lieCorr0VBPerm x P4
    ![(chartModelBasis E) i, (chartModelBasis E) j]]
  rw [show (∑ k : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel P4
        (fun i' => (Fin.cons (DeTurck.cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          (Fin.cons ((Module.finBasis ℝ E) k)
            (![(chartModelBasis E) i, (chartModelBasis E) j] : Fin 2 → E)) :
            Fin 4 → E) (lieCorr0VBPerm i'))) =
    ∑ k : Fin (Module.finrank ℝ E),
      quadrilinearMapSlotBilinearAt (E := E) (Tensor0SSpace.toModel P4) 3 0 (by decide)
        ![(chartModelBasis E) i, (chartModelBasis E) i, (chartModelBasis E) j,
          (chartModelBasis E) j]
        (DeTurck.cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        ((Module.finBasis ℝ E) k) from
    Finset.sum_congr rfl (fun k _ => by
      rw [unitModel4SlotBilin_apply, lieCorr0_upd4_30, lieCorr0_vbArg])]
  rw [cometricFinBasisTrace_eq_chartInvGram_bilin (I := I) g₁ x _]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  rw [smul_eq_mul]
  refine congrArg (fun t : ℝ => chartInvGramMatrix (I := I) g₁ x x k l * t) ?_
  rw [unitModel4SlotBilin_apply, lieCorr0_upd4_30]
  rw [hP4]
  rw [lieCorr0_prodKappa_toModel (I := I) (pq := 1) (q := 3) x _ _
    ![(chartModelBasis E) k, (chartModelBasis E) i, (chartModelBasis E) j,
      (chartModelBasis E) l]]
  rw [show (fun i' : Fin 1 =>
      (![(chartModelBasis E) k, (chartModelBasis E) i, (chartModelBasis E) j,
        (chartModelBasis E) l] : Fin 4 → E) (Fin.castAdd 3 i')) =
    ![(chartModelBasis E) k] from by
    funext i'
    fin_cases i'
    rfl]
  rw [show (fun i' : Fin 3 =>
      (![(chartModelBasis E) k, (chartModelBasis E) i, (chartModelBasis E) j,
        (chartModelBasis E) l] : Fin 4 → E) (Fin.natAdd 1 i')) =
    ![(chartModelBasis E) i, (chartModelBasis E) j, (chartModelBasis E) l] from by
    funext i'
    fin_cases i' <;> rfl]
  rw [lieCorr0_ip_toModel (I := I) x _ D ((chartModelBasis E) k)]
  rw [show Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)
      ![(chartModelBasis E) i, (chartModelBasis E) j, (chartModelBasis E) l] =
    g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
      ((chartModelBasis E) i : TangentSpace I x) ((chartModelBasis E) j : TangentSpace I x))
      ((chartModelBasis E) l : TangentSpace I x) from by
    rw [metricConnDiffLoweredFib_toModel]
    rfl]
  rw [lieArm_connDiff_chartBasis_center (I := I) g₁ g₀ x i j]
  rw [show g₁.inner x (∑ c : Fin (Module.finrank ℝ E),
      (chartChristoffel (I := I) g₁ x j i c (extChartAt I x x) -
        chartChristoffel (I := I) g₀ x j i c (extChartAt I x x)) •
      ((chartModelBasis E) c : TangentSpace I x))
      ((chartModelBasis E) l : TangentSpace I x) =
    ∑ c : Fin (Module.finrank ℝ E),
      (chartChristoffel (I := I) g₁ x j i c (extChartAt I x x) -
        chartChristoffel (I := I) g₀ x j i c (extChartAt I x x)) *
        chartGramMatrix (I := I) g₁ x x c l from by
    rw [show g₁.inner x (∑ c : Fin (Module.finrank ℝ E),
        (chartChristoffel (I := I) g₁ x j i c (extChartAt I x x) -
          chartChristoffel (I := I) g₀ x j i c (extChartAt I x x)) •
        ((chartModelBasis E) c : TangentSpace I x))
        ((chartModelBasis E) l : TangentSpace I x) =
      ∑ c : Fin (Module.finrank ℝ E),
        (chartChristoffel (I := I) g₁ x j i c (extChartAt I x x) -
          chartChristoffel (I := I) g₀ x j i c (extChartAt I x x)) *
          g₁.inner x ((chartModelBasis E) c : TangentSpace I x)
            ((chartModelBasis E) l : TangentSpace I x) from by
      rw [map_sum (g₁.inner x)]
      rw [ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [map_smul (g₁.inner x), ContinuousLinearMap.smul_apply, smul_eq_mul]]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [lieArm_inner_chartBasis_center (I := I) g₁ x c l]]
  rw [lieCorr0_D_VF_expand (I := I) g₁ g₀ x D ((chartModelBasis E) k)]
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun ρ _ => ?_)
  ring

private noncomputable def lieCorr0SlotBilin {n : ℕ}
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ)
    (i j : Fin n) (hij : i ≠ j) (base : Fin n → E) : E →L[ℝ] E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun c => LinearMap.toContinuousLinearMap
        { toFun := fun v => f (Function.update (Function.update base i c) j v)
          map_add' := fun v1 v2 => by
            rw [f.map_update_add (Function.update base i c) j v1 v2]
          map_smul' := fun r v => by
            rw [f.map_update_smul (Function.update base i c) j r v]; rfl }
      map_add' := fun c1 c2 => by
        ext v
        change f (Function.update (Function.update base i (c1 + c2)) j v) =
          f (Function.update (Function.update base i c1) j v) +
          f (Function.update (Function.update base i c2) j v)
        rw [Function.update_comm hij c1 v base, Function.update_comm hij c2 v base,
          Function.update_comm hij (c1 + c2) v base]
        rw [f.map_update_add (Function.update base j v) i c1 c2]
      map_smul' := fun r c => by
        ext v
        change f (Function.update (Function.update base i (r • c)) j v) =
          r • f (Function.update (Function.update base i c) j v)
        rw [Function.update_comm hij (r • c) v base, Function.update_comm hij c v base,
          f.map_update_smul (Function.update base j v) i r c] }

private lemma lieCorr0SlotBilin_apply {n : ℕ}
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ)
    (i j : Fin n) (hij : i ≠ j) (base : Fin n → E) (c v : E) :
    lieCorr0SlotBilin (E := E) f i j hij base c v =
      f (Function.update (Function.update base i c) j v) := rfl

section LieCorr0AMixEval

variable (g₀ g₁ g_bg : SmoothRiemannianMetric I M)

private lemma lieCorr0_amixQArg (a b : E) (u : Fin 3 → E) :
    (fun i : Fin 5 =>
      (Fin.cons a (Fin.cons b u) : Fin 5 → E) (lieCorr0AMixPermQ i)) =
      ![b, u 2, u 0, u 1, a] := by
  funext i
  fin_cases i <;> rfl

private lemma lieCorr0_upd5_40 (z0 z1 z2 z3 z4 a b : E) :
    Function.update (Function.update (![z0, z1, z2, z3, z4] : Fin 5 → E) (4 : Fin 5) a)
        (0 : Fin 5) b = ![b, z1, z2, z3, a] := by
  funext i
  fin_cases i <;> simp [Function.update]

private lemma lieCorr0_castAdd2of5 (b u2 u0 u1 a : E) :
    (fun i : Fin 2 => (![b, u2, u0, u1, a] : Fin 5 → E) (Fin.castAdd 3 i)) = ![b, u2] := by
  funext i
  fin_cases i <;> rfl

private lemma lieCorr0_natAdd3of5 (b u2 u0 u1 a : E) :
    (fun i : Fin 3 => (![b, u2, u0, u1, a] : Fin 5 → E) (Fin.natAdd 2 i)) = ![u0, u1, a] := by
  funext i
  fin_cases i <;> rfl

private lemma lieCorr0Q_value (x : M) (D : Tensor0SSpace 2 I x) (u : Fin 3 → E) :
    Tensor0SSpace.toModel
        (doubleTraceReindexFib (I := I) g₁ 3 lieCorr0AMixPermQ x
          (tensor0SProdKappaFib (I := I) x
            (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x) D)) u =
      ∑ k : Fin (Module.finrank ℝ E), ∑ kl : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k kl *
          (Tensor0SSpace.toModel D ![(chartModelBasis E) k, u 2] *
            Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)
              ![u 0, u 1, (chartModelBasis E) kl]) := by
  classical
  set P5 : Tensor0SSpace 5 I x :=
    tensor0SProdKappaFib (I := I) x (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x) D with hP5
  rw [lieCorr0TraceStep_toModel (I := I) g₁ 3 lieCorr0AMixPermQ x P5 u]
  rw [show (∑ k : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel P5
        (fun i' => (Fin.cons (DeTurck.cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          (Fin.cons ((Module.finBasis ℝ E) k) u) : Fin 5 → E) (lieCorr0AMixPermQ i'))) =
    ∑ k : Fin (Module.finrank ℝ E),
      lieCorr0SlotBilin (E := E) (Tensor0SSpace.toModel P5) 4 0 (by decide)
        ![u 0, u 2, u 0, u 1, u 1]
        (DeTurck.cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        ((Module.finBasis ℝ E) k) from
    Finset.sum_congr rfl (fun k _ => by
      rw [lieCorr0SlotBilin_apply, lieCorr0_upd5_40, lieCorr0_amixQArg])]
  rw [cometricFinBasisTrace_eq_chartInvGram_bilin (I := I) g₁ x _]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun kl _ => ?_))
  rw [smul_eq_mul]
  refine congrArg (fun t : ℝ => chartInvGramMatrix (I := I) g₁ x x k kl * t) ?_
  rw [lieCorr0SlotBilin_apply, lieCorr0_upd5_40]
  rw [hP5]
  rw [lieCorr0_prodKappa_toModel (I := I) (pq := 2) (q := 3) x _ _
    ![(chartModelBasis E) k, u 2, u 0, u 1, (chartModelBasis E) kl]]
  rw [show (fun i' : Fin 2 =>
      (![(chartModelBasis E) k, u 2, u 0, u 1, (chartModelBasis E) kl] : Fin 5 → E)
        (Fin.castAdd 3 i')) = ![(chartModelBasis E) k, u 2] from
    lieCorr0_castAdd2of5 (E := E) _ _ _ _ _]
  rw [show (fun i' : Fin 3 =>
      (![(chartModelBasis E) k, u 2, u 0, u 1, (chartModelBasis E) kl] : Fin 5 → E)
        (Fin.natAdd 2 i')) = ![u 0, u 1, (chartModelBasis E) kl] from
    lieCorr0_natAdd3of5 (E := E) _ _ _ _ _]

private lemma lieCorr0_amixT4Arg (a b : E) (w : Fin 4 → E) :
    (fun i : Fin 6 =>
      (Fin.cons a (Fin.cons b w) : Fin 6 → E) (lieCorr0AMixPerm1 i)) =
      ![w 0, a, w 1, b, w 2, w 3] := by
  funext i
  fin_cases i <;> rfl

private lemma lieCorr0_upd6_13 (z0 z1 z2 z3 z4 z5 a b : E) :
    Function.update (Function.update (![z0, z1, z2, z3, z4, z5] : Fin 6 → E) (1 : Fin 6) a)
        (3 : Fin 6) b = ![z0, a, z2, b, z4, z5] := by
  funext i
  fin_cases i <;> simp [Function.update]

private lemma lieCorr0_castAdd3of6 (w0 a w1 b w2 w3 : E) :
    (fun i : Fin 3 => (![w0, a, w1, b, w2, w3] : Fin 6 → E) (Fin.castAdd 3 i)) =
      ![w0, a, w1] := by
  funext i
  fin_cases i <;> rfl

private lemma lieCorr0_natAdd3of6 (w0 a w1 b w2 w3 : E) :
    (fun i : Fin 3 => (![w0, a, w1, b, w2, w3] : Fin 6 → E) (Fin.natAdd 3 i)) =
      ![b, w2, w3] := by
  funext i
  fin_cases i <;> rfl

private lemma lieCorr0T4_value (x : M) (D : Tensor0SSpace 2 I x) (w : Fin 4 → E) :
    Tensor0SSpace.toModel
        (doubleTraceReindexFib (I := I) g₁ 4 lieCorr0AMixPerm1 x
          (tensor0SProdKappaFib (I := I) x
            (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
            (doubleTraceReindexFib (I := I) g₁ 3 lieCorr0AMixPermQ x
              (tensor0SProdKappaFib (I := I) x
                (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x) D)))) w =
      ∑ j : Fin (Module.finrank ℝ E), ∑ jl : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x j jl *
          (Tensor0SSpace.toModel
              (doubleTraceReindexFib (I := I) g₁ 3 lieCorr0AMixPermQ x
                (tensor0SProdKappaFib (I := I) x
                  (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x) D))
              ![w 0, (chartModelBasis E) jl, w 1] *
            Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
              ![(chartModelBasis E) j, w 2, w 3]) := by
  classical
  set QD : Tensor0SSpace 3 I x :=
    doubleTraceReindexFib (I := I) g₁ 3 lieCorr0AMixPermQ x
      (tensor0SProdKappaFib (I := I) x
        (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x) D) with hQD
  set P6 : Tensor0SSpace 6 I x :=
    tensor0SProdKappaFib (I := I) x (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x) QD
    with hP6
  rw [lieCorr0TraceStep_toModel (I := I) g₁ 4 lieCorr0AMixPerm1 x P6 w]
  rw [show (∑ j : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel P6
        (fun i' => (Fin.cons (DeTurck.cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis j)))
          (Fin.cons ((Module.finBasis ℝ E) j) w) : Fin 6 → E) (lieCorr0AMixPerm1 i'))) =
    ∑ j : Fin (Module.finrank ℝ E),
      lieCorr0SlotBilin (E := E) (Tensor0SSpace.toModel P6) 1 3 (by decide)
        ![w 0, w 0, w 1, w 1, w 2, w 3]
        (DeTurck.cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis j)))
        ((Module.finBasis ℝ E) j) from
    Finset.sum_congr rfl (fun j _ => by
      rw [lieCorr0SlotBilin_apply, lieCorr0_upd6_13, lieCorr0_amixT4Arg])]
  rw [cometricFinBasisTrace_eq_chartInvGram_bilin (I := I) g₁ x _]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun jl _ => ?_))
  rw [smul_eq_mul]
  refine congrArg (fun t : ℝ => chartInvGramMatrix (I := I) g₁ x x j jl * t) ?_
  rw [lieCorr0SlotBilin_apply, lieCorr0_upd6_13]
  rw [hP6]
  rw [lieCorr0_prodKappa_toModel (I := I) (pq := 3) (q := 3) x _ _
    ![w 0, (chartModelBasis E) jl, w 1, (chartModelBasis E) j, w 2, w 3]]
  rw [show (fun i' : Fin 3 =>
      (![w 0, (chartModelBasis E) jl, w 1, (chartModelBasis E) j, w 2, w 3] : Fin 6 → E)
        (Fin.castAdd 3 i')) = ![w 0, (chartModelBasis E) jl, w 1] from
    lieCorr0_castAdd3of6 (E := E) _ _ _ _ _ _]
  rw [show (fun i' : Fin 3 =>
      (![w 0, (chartModelBasis E) jl, w 1, (chartModelBasis E) j, w 2, w 3] : Fin 6 → E)
        (Fin.natAdd 3 i')) = ![(chartModelBasis E) j, w 2, w 3] from
    lieCorr0_natAdd3of6 (E := E) _ _ _ _ _ _]

private lemma lieCorr0_amixTopArg (a b v0 v1 : E) :
    (fun i : Fin 4 =>
      (Fin.cons a (Fin.cons b (![v0, v1] : Fin 2 → E)) : Fin 4 → E)
        (lieCorr0AMixPerm2 i)) = ![v0, a, b, v1] := by
  funext i
  fin_cases i <;> rfl

private lemma lieCorr0_upd4_12 (z0 z1 z2 z3 a b : E) :
    Function.update (Function.update (![z0, z1, z2, z3] : Fin 4 → E) (1 : Fin 4) a)
        (2 : Fin 4) b = ![z0, a, b, z3] := by
  funext i
  fin_cases i <;> simp [Function.update]

private lemma lieCorr0_lowered_basis_value (gB : SmoothRiemannianMetric I M) (x : M)
    (a b c : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) g₁ g₁ gB x)
        ![(chartModelBasis E) a, (chartModelBasis E) b, (chartModelBasis E) c] =
      ∑ d : Fin (Module.finrank ℝ E),
        (chartChristoffel (I := I) g₁ x b a d (extChartAt I x x) -
          chartChristoffel (I := I) gB x b a d (extChartAt I x x)) *
          chartGramMatrix (I := I) g₁ x x d c := by
  rw [show Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) g₁ g₁ gB x)
      ![(chartModelBasis E) a, (chartModelBasis E) b, (chartModelBasis E) c] =
    g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ gB x
      ((chartModelBasis E) a : TangentSpace I x) ((chartModelBasis E) b : TangentSpace I x))
      ((chartModelBasis E) c : TangentSpace I x) from by
    rw [metricConnDiffLoweredFib_toModel]
    rfl]
  rw [lieArm_connDiff_chartBasis_center (I := I) g₁ gB x a b]
  rw [map_sum (g₁.inner x), ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [map_smul (g₁.inner x), ContinuousLinearMap.smul_apply, smul_eq_mul,
    lieArm_inner_chartBasis_center (I := I) g₁ x d c]

private lemma lieCorr0AMixHalfFib_basis_value (x : M) (D : Tensor0SSpace 2 I x)
    (i j : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel (lieCorr0AMixHalfFib (I := I) g₀ g₁ g_bg x D)
        ![(chartModelBasis E) i, (chartModelBasis E) j] =
      ∑ m : Fin (Module.finrank ℝ E), ∑ ml : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x m ml *
          ((∑ a : Fin (Module.finrank ℝ E), ∑ al : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g₁ x x a al *
              ((∑ k : Fin (Module.finrank ℝ E), ∑ kl : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g₁ x x k kl *
                  (Tensor0SSpace.toModel D
                      ![(chartModelBasis E) k, (chartModelBasis E) ml] *
                    (∑ c : Fin (Module.finrank ℝ E),
                      (chartChristoffel (I := I) g₁ x al i c (extChartAt I x x) -
                        chartChristoffel (I := I) g₀ x al i c (extChartAt I x x)) *
                        chartGramMatrix (I := I) g₁ x x c kl))) *
                (∑ d : Fin (Module.finrank ℝ E),
                  (chartChristoffel (I := I) g₁ x m a d (extChartAt I x x) -
                    chartChristoffel (I := I) g_bg x m a d (extChartAt I x x)) *
                    chartGramMatrix (I := I) g₁ x x d j)))) := by
  classical
  set QD : Tensor0SSpace 3 I x :=
    doubleTraceReindexFib (I := I) g₁ 3 lieCorr0AMixPermQ x
      (tensor0SProdKappaFib (I := I) x
        (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x) D) with hQD
  set T4 : Tensor0SSpace 4 I x :=
    doubleTraceReindexFib (I := I) g₁ 4 lieCorr0AMixPerm1 x
      (tensor0SProdKappaFib (I := I) x
        (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x) QD) with hT4
  rw [show lieCorr0AMixHalfFib (I := I) g₀ g₁ g_bg x D =
      doubleTraceReindexFib (I := I) g₁ 2 lieCorr0AMixPerm2 x T4 from by
    rw [lieCorr0AMixHalfFib, hT4, hQD]
    rfl]
  rw [lieCorr0TraceStep_toModel (I := I) g₁ 2 lieCorr0AMixPerm2 x T4
    ![(chartModelBasis E) i, (chartModelBasis E) j]]
  rw [show (∑ m : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel T4
        (fun i' => (Fin.cons (DeTurck.cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis m)))
          (Fin.cons ((Module.finBasis ℝ E) m)
            (![(chartModelBasis E) i, (chartModelBasis E) j] : Fin 2 → E)) :
            Fin 4 → E) (lieCorr0AMixPerm2 i'))) =
    ∑ m : Fin (Module.finrank ℝ E),
      lieCorr0SlotBilin (E := E) (Tensor0SSpace.toModel T4) 1 2 (by decide)
        ![(chartModelBasis E) i, (chartModelBasis E) i, (chartModelBasis E) j,
          (chartModelBasis E) j]
        (DeTurck.cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis m)))
        ((Module.finBasis ℝ E) m) from
    Finset.sum_congr rfl (fun m _ => by
      rw [lieCorr0SlotBilin_apply, lieCorr0_upd4_12, lieCorr0_amixTopArg])]
  rw [cometricFinBasisTrace_eq_chartInvGram_bilin (I := I) g₁ x _]
  refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun ml _ => ?_))
  rw [smul_eq_mul]
  refine congrArg (fun t : ℝ => chartInvGramMatrix (I := I) g₁ x x m ml * t) ?_
  rw [lieCorr0SlotBilin_apply, lieCorr0_upd4_12]
  rw [hT4]
  rw [lieCorr0T4_value (I := I) g₀ g₁ g_bg x D
    ![(chartModelBasis E) i, (chartModelBasis E) ml, (chartModelBasis E) m,
      (chartModelBasis E) j]]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun al _ => ?_))
  refine congrArg (fun t : ℝ => chartInvGramMatrix (I := I) g₁ x x a al * t) ?_
  rw [show ((![(chartModelBasis E) i, (chartModelBasis E) ml, (chartModelBasis E) m,
      (chartModelBasis E) j] : Fin 4 → E) 0) = (chartModelBasis E) i from rfl]
  rw [show ((![(chartModelBasis E) i, (chartModelBasis E) ml, (chartModelBasis E) m,
      (chartModelBasis E) j] : Fin 4 → E) 1) = (chartModelBasis E) ml from rfl]
  rw [show ((![(chartModelBasis E) i, (chartModelBasis E) ml, (chartModelBasis E) m,
      (chartModelBasis E) j] : Fin 4 → E) 2) = (chartModelBasis E) m from rfl]
  rw [show ((![(chartModelBasis E) i, (chartModelBasis E) ml, (chartModelBasis E) m,
      (chartModelBasis E) j] : Fin 4 → E) 3) = (chartModelBasis E) j from rfl]
  rw [lieCorr0Q_value (I := I) g₀ g₁ x D
    ![(chartModelBasis E) i, (chartModelBasis E) al, (chartModelBasis E) ml]]
  rw [lieCorr0_lowered_basis_value (I := I) g₁ g_bg x a m j]
  refine congrArg (fun t : ℝ => t *
    (∑ d : Fin (Module.finrank ℝ E),
      (chartChristoffel (I := I) g₁ x m a d (extChartAt I x x) -
        chartChristoffel (I := I) g_bg x m a d (extChartAt I x x)) *
        chartGramMatrix (I := I) g₁ x x d j)) ?_
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun kl _ => ?_))
  refine congrArg (fun t : ℝ => chartInvGramMatrix (I := I) g₁ x x k kl * t) ?_
  rw [show ((![(chartModelBasis E) i, (chartModelBasis E) al, (chartModelBasis E) ml] :
      Fin 3 → E) 2) = (chartModelBasis E) ml from rfl]
  rw [show ((![(chartModelBasis E) i, (chartModelBasis E) al, (chartModelBasis E) ml] :
      Fin 3 → E) 0) = (chartModelBasis E) i from rfl]
  rw [show ((![(chartModelBasis E) i, (chartModelBasis E) al, (chartModelBasis E) ml] :
      Fin 3 → E) 1) = (chartModelBasis E) al from rfl]
  refine congrArg (fun t : ℝ =>
    Tensor0SSpace.toModel D ![(chartModelBasis E) k, (chartModelBasis E) ml] * t) ?_
  rw [lieCorr0_lowered_basis_value (I := I) g₁ g₀ x i al kl]

private lemma lieCorr0_swapArg (v0 v1 : E) :
    (fun i : Fin 2 => (![v0, v1] : Fin 2 → E) ((Equiv.swap (0 : Fin 2) 1) i)) =
      ![v1, v0] := by
  funext i
  fin_cases i <;> simp

private lemma lieCorr0AMixFib_basis_value (x : M) (D : Tensor0SSpace 2 I x)
    (i j : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel (lieCorr0AMixFib (I := I) g₀ g₁ g_bg x D)
        ![(chartModelBasis E) i, (chartModelBasis E) j] =
      2 * (Tensor0SSpace.toModel (lieCorr0AMixHalfFib (I := I) g₀ g₁ g_bg x D)
          ![(chartModelBasis E) i, (chartModelBasis E) j]
        + Tensor0SSpace.toModel (lieCorr0AMixHalfFib (I := I) g₀ g₁ g_bg x D)
          ![(chartModelBasis E) j, (chartModelBasis E) i]) := by
  rw [show lieCorr0AMixFib (I := I) g₀ g₁ g_bg x D =
      (2 : ℝ) • (lieCorr0AMixHalfFib (I := I) g₀ g₁ g_bg x D +
        domDomCongrFibRank (I := I) 2 (Equiv.swap 0 1) x
          (lieCorr0AMixHalfFib (I := I) g₀ g₁ g_bg x D)) from by
    rw [lieCorr0AMixFib]
    rfl]
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  refine congrArg (fun t : ℝ => 2 * t) ?_
  rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
  refine congrArg (fun t : ℝ =>
    Tensor0SSpace.toModel (lieCorr0AMixHalfFib (I := I) g₀ g₁ g_bg x D)
      ![(chartModelBasis E) i, (chartModelBasis E) j] + t) ?_
  rw [domDomCongrFibRank_apply, Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  refine congrArg (fun t => Tensor0SSpace.toModel
    (lieCorr0AMixHalfFib (I := I) g₀ g₁ g_bg x D) t) ?_
  exact lieCorr0_swapArg (E := E) _ _

private lemma lieCorr0_riemT4Arg (a b : E) (w : Fin 4 → E) :
    (fun i : Fin 6 =>
      (Fin.cons a (Fin.cons b w) : Fin 6 → E) (lieCorr0RiemPerm1 i)) =
      ![b, w 3, w 0, w 1, w 2, a] := by
  funext i
  fin_cases i <;> rfl

private lemma lieCorr0_upd6_50 (z0 z1 z2 z3 z4 z5 a b : E) :
    Function.update (Function.update (![z0, z1, z2, z3, z4, z5] : Fin 6 → E) (5 : Fin 6) a)
        (0 : Fin 6) b = ![b, z1, z2, z3, z4, a] := by
  funext i
  fin_cases i <;> simp [Function.update]

private lemma lieCorr0_castAdd2of6 (b w3 w0 w1 w2 a : E) :
    (fun i : Fin 2 => (![b, w3, w0, w1, w2, a] : Fin 6 → E) (Fin.castAdd 4 i)) =
      ![b, w3] := by
  funext i
  fin_cases i <;> rfl

private lemma lieCorr0_natAdd4of6 (b w3 w0 w1 w2 a : E) :
    (fun i : Fin 4 => (![b, w3, w0, w1, w2, a] : Fin 6 → E) (Fin.natAdd 2 i)) =
      ![w0, w1, w2, a] := by
  funext i
  fin_cases i <;> rfl

private lemma lieCorr0RiemT4_value (x : M) (D : Tensor0SSpace 2 I x) (w : Fin 4 → E) :
    Tensor0SSpace.toModel
        (doubleTraceReindexFib (I := I) g₀ 4 lieCorr0RiemPerm1 x
          (tensor0SProdKappaFib (I := I) x (lieCorr0RiemLoweredFib (I := I) g₀ x) D)) w =
      ∑ k : Fin (Module.finrank ℝ E), ∑ kl : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₀ x x k kl *
          (Tensor0SSpace.toModel D ![(chartModelBasis E) k, w 3] *
            Tensor0SSpace.toModel (lieCorr0RiemLoweredFib (I := I) g₀ x)
              ![w 0, w 1, w 2, (chartModelBasis E) kl]) := by
  classical
  set P6 : Tensor0SSpace 6 I x :=
    tensor0SProdKappaFib (I := I) x (lieCorr0RiemLoweredFib (I := I) g₀ x) D with hP6
  rw [lieCorr0TraceStep_toModel (I := I) g₀ 4 lieCorr0RiemPerm1 x P6 w]
  rw [show (∑ k : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel P6
        (fun i' => (Fin.cons (DeTurck.cometricLmodel (I := I) g₀ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          (Fin.cons ((Module.finBasis ℝ E) k) w) : Fin 6 → E) (lieCorr0RiemPerm1 i'))) =
    ∑ k : Fin (Module.finrank ℝ E),
      lieCorr0SlotBilin (E := E) (Tensor0SSpace.toModel P6) 5 0 (by decide)
        ![w 0, w 3, w 0, w 1, w 2, w 2]
        (DeTurck.cometricLmodel (I := I) g₀ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        ((Module.finBasis ℝ E) k) from
    Finset.sum_congr rfl (fun k _ => by
      rw [lieCorr0SlotBilin_apply, lieCorr0_upd6_50, lieCorr0_riemT4Arg])]
  rw [cometricFinBasisTrace_eq_chartInvGram_bilin (I := I) g₀ x _]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun kl _ => ?_))
  rw [smul_eq_mul]
  refine congrArg (fun t : ℝ => chartInvGramMatrix (I := I) g₀ x x k kl * t) ?_
  rw [lieCorr0SlotBilin_apply, lieCorr0_upd6_50]
  rw [hP6]
  rw [lieCorr0_prodKappa_toModel (I := I) (pq := 2) (q := 4) x _ _
    ![(chartModelBasis E) k, w 3, w 0, w 1, w 2, (chartModelBasis E) kl]]
  rw [show (fun i' : Fin 2 =>
      (![(chartModelBasis E) k, w 3, w 0, w 1, w 2, (chartModelBasis E) kl] : Fin 6 → E)
        (Fin.castAdd 4 i')) = ![(chartModelBasis E) k, w 3] from
    lieCorr0_castAdd2of6 (E := E) _ _ _ _ _ _]
  rw [show (fun i' : Fin 4 =>
      (![(chartModelBasis E) k, w 3, w 0, w 1, w 2, (chartModelBasis E) kl] : Fin 6 → E)
        (Fin.natAdd 2 i')) = ![w 0, w 1, w 2, (chartModelBasis E) kl] from
    lieCorr0_natAdd4of6 (E := E) _ _ _ _ _ _]

private lemma lieCorr0_riemTopArg (a b v0 v1 : E) :
    (fun i : Fin 4 =>
      (Fin.cons a (Fin.cons b (![v0, v1] : Fin 2 → E)) : Fin 4 → E)
        (lieCorr0RiemPerm2 i)) = ![v0, v1, a, b] := by
  funext i
  fin_cases i <;> rfl

private lemma lieCorr0_upd4_23 (z0 z1 z2 z3 a b : E) :
    Function.update (Function.update (![z0, z1, z2, z3] : Fin 4 → E) (2 : Fin 4) a)
        (3 : Fin 4) b = ![z0, z1, a, b] := by
  funext i
  fin_cases i <;> simp [Function.update]

private lemma lieCorr0_riemLowered_basis_value (x : M)
    (i j ml kl : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel (lieCorr0RiemLoweredFib (I := I) g₀ x)
        ![(chartModelBasis E) i, (chartModelBasis E) j, (chartModelBasis E) ml,
          (chartModelBasis E) kl] =
      ∑ ρ : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Integral.DivergenceTheorem.chartRiemannTensor (I := I) g₀ x
            ml i j ρ (extChartAt I x x) *
          chartGramMatrix (I := I) g₀ x x ρ kl := by
  rw [show Tensor0SSpace.toModel (lieCorr0RiemLoweredFib (I := I) g₀ x)
      ![(chartModelBasis E) i, (chartModelBasis E) j, (chartModelBasis E) ml,
        (chartModelBasis E) kl] =
    g₀.inner x (Integral.Connection.riemannOp (LeviCivita (I := I) g₀) x
      ((chartModelBasis E) i : TangentSpace I x)
      ((chartModelBasis E) j : TangentSpace I x)
      ((chartModelBasis E) ml : TangentSpace I x))
      ((chartModelBasis E) kl : TangentSpace I x) from by
    rw [lieCorr0RiemLoweredFib_toModel]
    rfl]
  rw [Integral.Connection.riemannOp_eq_chartRiemannCLM_apply (I := I) g₀ x]
  rw [Integral.Connection.chartRiemannCLM_basis_apply (I := I) g₀ x ml i j]
  rw [map_sum (g₀.inner x), ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun ρ _ => ?_)
  rw [map_smul (g₀.inner x), ContinuousLinearMap.smul_apply, smul_eq_mul,
    lieArm_inner_chartBasis_center (I := I) g₀ x ρ kl]

private lemma lieCorr0RiemFib_basis_value (x : M) (D : Tensor0SSpace 2 I x)
    (i j : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel (deTurckLieRemainderCurvatureFib (I := I) g₀ g₁ x D)
        ![(chartModelBasis E) i, (chartModelBasis E) j] =
      -(∑ m : Fin (Module.finrank ℝ E), ∑ ml : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x m ml *
          ∑ ρ : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Integral.DivergenceTheorem.chartRiemannTensor (I := I) g₀ x
                ml i j ρ (extChartAt I x x) *
              Tensor0SSpace.toModel D ![(chartModelBasis E) ρ, (chartModelBasis E) m]) := by
  classical
  set T4 : Tensor0SSpace 4 I x :=
    doubleTraceReindexFib (I := I) g₀ 4 lieCorr0RiemPerm1 x
      (tensor0SProdKappaFib (I := I) x (lieCorr0RiemLoweredFib (I := I) g₀ x) D) with hT4
  rw [show deTurckLieRemainderCurvatureFib (I := I) g₀ g₁ x D =
      (-1 : ℝ) • doubleTraceReindexFib (I := I) g₁ 2 lieCorr0RiemPerm2 x T4 from by
    rw [deTurckLieRemainderCurvatureFib, hT4]
    rfl]
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul,
    neg_one_mul, neg_inj]
  rw [lieCorr0TraceStep_toModel (I := I) g₁ 2 lieCorr0RiemPerm2 x T4
    ![(chartModelBasis E) i, (chartModelBasis E) j]]
  rw [show (∑ m : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel T4
        (fun i' => (Fin.cons (DeTurck.cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis m)))
          (Fin.cons ((Module.finBasis ℝ E) m)
            (![(chartModelBasis E) i, (chartModelBasis E) j] : Fin 2 → E)) :
            Fin 4 → E) (lieCorr0RiemPerm2 i'))) =
    ∑ m : Fin (Module.finrank ℝ E),
      lieCorr0SlotBilin (E := E) (Tensor0SSpace.toModel T4) 2 3 (by decide)
        ![(chartModelBasis E) i, (chartModelBasis E) j, (chartModelBasis E) i,
          (chartModelBasis E) j]
        (DeTurck.cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis m)))
        ((Module.finBasis ℝ E) m) from
    Finset.sum_congr rfl (fun m _ => by
      rw [lieCorr0SlotBilin_apply, lieCorr0_upd4_23, lieCorr0_riemTopArg])]
  rw [cometricFinBasisTrace_eq_chartInvGram_bilin (I := I) g₁ x _]
  refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun ml _ => ?_))
  rw [smul_eq_mul]
  refine congrArg (fun t : ℝ => chartInvGramMatrix (I := I) g₁ x x m ml * t) ?_
  rw [lieCorr0SlotBilin_apply, lieCorr0_upd4_23]
  rw [hT4]
  rw [lieCorr0RiemT4_value (I := I) g₀ x D
    ![(chartModelBasis E) i, (chartModelBasis E) j, (chartModelBasis E) ml,
      (chartModelBasis E) m]]
  rw [show ((![(chartModelBasis E) i, (chartModelBasis E) j, (chartModelBasis E) ml,
      (chartModelBasis E) m] : Fin 4 → E) 3) = (chartModelBasis E) m from rfl]
  rw [show ((![(chartModelBasis E) i, (chartModelBasis E) j, (chartModelBasis E) ml,
      (chartModelBasis E) m] : Fin 4 → E) 0) = (chartModelBasis E) i from rfl]
  rw [show ((![(chartModelBasis E) i, (chartModelBasis E) j, (chartModelBasis E) ml,
      (chartModelBasis E) m] : Fin 4 → E) 1) = (chartModelBasis E) j from rfl]
  rw [show ((![(chartModelBasis E) i, (chartModelBasis E) j, (chartModelBasis E) ml,
      (chartModelBasis E) m] : Fin 4 → E) 2) = (chartModelBasis E) ml from rfl]
  rw [show (∑ k : Fin (Module.finrank ℝ E), ∑ kl : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g₀ x x k kl *
        (Tensor0SSpace.toModel D ![(chartModelBasis E) k, (chartModelBasis E) m] *
          Tensor0SSpace.toModel (lieCorr0RiemLoweredFib (I := I) g₀ x)
            ![(chartModelBasis E) i, (chartModelBasis E) j, (chartModelBasis E) ml,
              (chartModelBasis E) kl])) =
    ∑ k : Fin (Module.finrank ℝ E), ∑ kl : Fin (Module.finrank ℝ E),
      ∑ ρ : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Integral.DivergenceTheorem.chartRiemannTensor (I := I) g₀ x
            ml i j ρ (extChartAt I x x) *
          (Tensor0SSpace.toModel D ![(chartModelBasis E) k, (chartModelBasis E) m] *
            (chartGramMatrix (I := I) g₀ x x ρ kl *
              chartInvGramMatrix (I := I) g₀ x x k kl)) from
    Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun kl _ => by
      rw [lieCorr0_riemLowered_basis_value (I := I) g₀ x i j ml kl]
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun ρ _ => ?_)
      ring))]
  rw [show (∑ k : Fin (Module.finrank ℝ E), ∑ kl : Fin (Module.finrank ℝ E),
      ∑ ρ : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Integral.DivergenceTheorem.chartRiemannTensor (I := I) g₀ x
            ml i j ρ (extChartAt I x x) *
          (Tensor0SSpace.toModel D ![(chartModelBasis E) k, (chartModelBasis E) m] *
            (chartGramMatrix (I := I) g₀ x x ρ kl *
              chartInvGramMatrix (I := I) g₀ x x k kl))) =
    ∑ ρ : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Integral.DivergenceTheorem.chartRiemannTensor (I := I) g₀ x
          ml i j ρ (extChartAt I x x) *
        (Tensor0SSpace.toModel D ![(chartModelBasis E) k, (chartModelBasis E) m] *
          ∑ kl : Fin (Module.finrank ℝ E),
            chartGramMatrix (I := I) g₀ x x ρ kl *
              chartInvGramMatrix (I := I) g₀ x x k kl) from by
    rw [Finset.sum_comm]
    rw [show (∑ kl : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ∑ ρ : Fin (Module.finrank ℝ E),
          DifferentialGeometry.Integral.DivergenceTheorem.chartRiemannTensor (I := I) g₀ x
              ml i j ρ (extChartAt I x x) *
            (Tensor0SSpace.toModel D ![(chartModelBasis E) k, (chartModelBasis E) m] *
              (chartGramMatrix (I := I) g₀ x x ρ kl *
                chartInvGramMatrix (I := I) g₀ x x k kl))) =
      ∑ kl : Fin (Module.finrank ℝ E), ∑ ρ : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E),
          DifferentialGeometry.Integral.DivergenceTheorem.chartRiemannTensor (I := I) g₀ x
              ml i j ρ (extChartAt I x x) *
            (Tensor0SSpace.toModel D ![(chartModelBasis E) k, (chartModelBasis E) m] *
              (chartGramMatrix (I := I) g₀ x x ρ kl *
                chartInvGramMatrix (I := I) g₀ x x k kl)) from
      Finset.sum_congr rfl (fun kl _ => Finset.sum_comm)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun ρ _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum]]
  refine Finset.sum_congr rfl (fun ρ _ => ?_)
  rw [show (∑ k : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Integral.DivergenceTheorem.chartRiemannTensor (I := I) g₀ x
          ml i j ρ (extChartAt I x x) *
        (Tensor0SSpace.toModel D ![(chartModelBasis E) k, (chartModelBasis E) m] *
          ∑ kl : Fin (Module.finrank ℝ E),
            chartGramMatrix (I := I) g₀ x x ρ kl *
              chartInvGramMatrix (I := I) g₀ x x k kl)) =
    ∑ k : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Integral.DivergenceTheorem.chartRiemannTensor (I := I) g₀ x
          ml i j ρ (extChartAt I x x) *
        (Tensor0SSpace.toModel D ![(chartModelBasis E) k, (chartModelBasis E) m] *
          (if k = ρ then (1 : ℝ) else 0)) from
    Finset.sum_congr rfl (fun k _ => by
      refine congrArg (fun t : ℝ =>
        DifferentialGeometry.Integral.DivergenceTheorem.chartRiemannTensor (I := I) g₀ x
          ml i j ρ (extChartAt I x x) *
          (Tensor0SSpace.toModel D ![(chartModelBasis E) k, (chartModelBasis E) m] * t)) ?_
      rw [show (∑ kl : Fin (Module.finrank ℝ E),
          chartGramMatrix (I := I) g₀ x x ρ kl *
            chartInvGramMatrix (I := I) g₀ x x k kl) =
        ∑ kl : Fin (Module.finrank ℝ E),
          chartGramMatrix (I := I) g₀ x x kl ρ *
            chartInvGramMatrix (I := I) g₀ x x kl k from
        Finset.sum_congr rfl (fun kl _ => by
          rw [lieArm_chartGramMatrix_symm (I := I) g₀ x ρ kl,
            lieArm_chartInvGramMatrix_symm (I := I) g₀ x k kl])]
      exact lieArm_gram_invGram_collapse (I := I) g₀ x k ρ)]
  rw [Finset.sum_eq_single ρ]
  · rw [if_pos rfl, mul_one]
  · intro k _ hk
    rw [if_neg hk, mul_zero, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ ρ) h

end LieCorr0AMixEval

end LieCorr0Eval

section LieCorr0Value

open DifferentialGeometry.Integral.DivergenceTheorem (chartInvGramMatrix partialDeriv chartChristoffel)
open DifferentialGeometry.Integral.Measure (chartGramMatrix)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (ccTensor02Symm unitModel unitTensor deTurckLieCoeffField deTurckLieCoeffField_apply_eq deTurckConnDiffCovDeriv deTurckVFCovDeriv deTurckLieCovDerivW_chartBasis_eq deTurckLieCovDerivA_chartBasis_eq connDiffCovDerivOp dLaCovKernel_apply_extend frameConnDiffCovDerivKernel frameDLaKernel_apply double_frame_bilin_trace_eq_fixed unitModel_basisChart_eq_tensorChartComponentRaw tensorChartComponentRaw)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (realizedGramDeriv realizedFam)

variable (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
variable {δ δ' : ℝ}

private lemma lieCorr0_f_readout (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (c d : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x
        ![(chartModelBasis E) c, (chartModelBasis E) d] =
      realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c d (extChartAt I x x) := by
  classical
  have hev := lieArm_scalarOnE_symmS_eventuallyEq_realizedGramDeriv (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' x c d
  have hpt := hev.self_of_nhds
  rw [DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_def] at hpt
  have hx_src : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source (I := I)]; exact mem_chart_source H x
  rw [(extChartAt I x).left_inv hx_src] at hpt
  rw [show (![(chartModelBasis E) c, (chartModelBasis E) d] : Fin 2 → E) =
      (fun k => chartModelBasis E ((![c, d] : Fin 2 → Fin (Module.finrank ℝ E)) k)) from by
    funext k
    fin_cases k <;> rfl]
  rw [unitModel_basisChart_eq_tensorChartComponentRaw (I := I) (M := M) g₀ 2
    (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![c, d]]
  exact hpt

private noncomputable def lieCorr0CovASc (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (a m k p : Fin (Module.finrank ℝ E)) : ℝ :=
  partialDeriv (E := E) a
      (fun y => chartChristoffel (I := I) g₁ x k m p y -
        chartChristoffel (I := I) g_bg x k m p y) (extChartAt I x x) +
    ∑ c : Fin (Module.finrank ℝ E),
      chartChristoffel (I := I) g₁ x a c p (extChartAt I x x) *
        (chartChristoffel (I := I) g₁ x k m c (extChartAt I x x) -
          chartChristoffel (I := I) g_bg x k m c (extChartAt I x x)) -
    ∑ c : Fin (Module.finrank ℝ E),
      chartChristoffel (I := I) g₁ x a m c (extChartAt I x x) *
        (chartChristoffel (I := I) g₁ x k c p (extChartAt I x x) -
          chartChristoffel (I := I) g_bg x k c p (extChartAt I x x)) -
    ∑ c : Fin (Module.finrank ℝ E),
      chartChristoffel (I := I) g₁ x a k c (extChartAt I x x) *
        (chartChristoffel (I := I) g₁ x c m p (extChartAt I x x) -
          chartChristoffel (I := I) g_bg x c m p (extChartAt I x x))

private lemma lieCorr0_dLa_inner_basis (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (a b m k : Fin (Module.finrank ℝ E)) :
    g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x
        ((chartModelBasis E) a : TangentSpace I x)
        ((chartModelBasis E) m : TangentSpace I x)
        ((chartModelBasis E) k : TangentSpace I x))
        ((chartModelBasis E) b : TangentSpace I x) =
      ∑ p : Fin (Module.finrank ℝ E),
        lieCorr0CovASc (I := I) (M := M) g₁ g_bg x a m k p *
          chartGramMatrix (I := I) g₁ x x p b := by
  classical
  rw [dLaCovKernel_apply_extend (I := I) g₁ g_bg x
    ((chartModelBasis E) a : TangentSpace I x)
    ((chartModelBasis E) m : TangentSpace I x)
    ((chartModelBasis E) k : TangentSpace I x)]
  rw [deTurckLieCovDerivA_chartBasis_eq (I := I) g₁ g_bg x a m k]
  rw [show (∑ p : Fin (Module.finrank ℝ E),
      (partialDeriv (E := E) a
          (fun y => chartChristoffel (I := I) g₁ x k m p y -
            chartChristoffel (I := I) g_bg x k m p y) (extChartAt I x x) +
        ∑ c : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₁ x a c p (extChartAt I x x) *
            (chartChristoffel (I := I) g₁ x k m c (extChartAt I x x) -
              chartChristoffel (I := I) g_bg x k m c (extChartAt I x x)) -
        ∑ c : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₁ x a m c (extChartAt I x x) *
            (chartChristoffel (I := I) g₁ x k c p (extChartAt I x x) -
              chartChristoffel (I := I) g_bg x k c p (extChartAt I x x)) -
        ∑ c : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₁ x a k c (extChartAt I x x) *
            (chartChristoffel (I := I) g₁ x c m p (extChartAt I x x) -
              chartChristoffel (I := I) g_bg x c m p (extChartAt I x x))) •
        DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) x p x) =
    ∑ p : Fin (Module.finrank ℝ E),
      lieCorr0CovASc (I := I) (M := M) g₁ g_bg x a m k p •
        ((chartModelBasis E) p : TangentSpace I x) from
    Finset.sum_congr rfl (fun p _ => by
      rw [DifferentialGeometry.Integral.Connection.chartBasisVecFiber_self (I := I) x p]
      rfl)]
  rw [map_sum (g₁.inner x), ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [map_smul (g₁.inner x), ContinuousLinearMap.smul_apply, smul_eq_mul,
    lieArm_inner_chartBasis_center (I := I) g₁ x p b]

private noncomputable def lieCorr0CovWSc (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (a p : Fin (Module.finrank ℝ E)) : ℝ :=
  partialDeriv (E := E) a
      (fun y => PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) g₁ g_bg x p y)
      (extChartAt I x x) +
    ∑ c : Fin (Module.finrank ℝ E),
      chartChristoffel (I := I) g₁ x a c p (extChartAt I x x) *
        PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) g₁ g_bg x c
          (extChartAt I x x)

private lemma lieCorr0_covW_basis (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (a : Fin (Module.finrank ℝ E)) :
    deTurckVFCovDeriv (I := I) g₁ g_bg
        (smoothExtensionTangent (I := I) x ((chartModelBasis E) a : TangentSpace I x)) x =
      ∑ p : Fin (Module.finrank ℝ E),
        lieCorr0CovWSc (I := I) (M := M) g₁ g_bg x a p •
          ((chartModelBasis E) p : TangentSpace I x) := by
  rw [deTurckLieCovDerivW_chartBasis_eq (I := I) g₁ g_bg x a]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [DifferentialGeometry.Integral.Connection.chartBasisVecFiber_self (I := I) x p]
  rfl

private lemma lieCorr0_icg0_readout (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (c d : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 2
        (iteratedCovGrad (I := I) g₀ 0 2 0 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) x
        ![(chartModelBasis E) c, (chartModelBasis E) d] =
      realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c d (extChartAt I x x) := by
  rw [iteratedCovGrad_zero]
  exact lieCorr0_f_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c d

private lemma lieCorr0_ite_pair_eq (x : M) (u w : TangentSpace I x) :
    (fun j : Fin 2 => if j = 0 then u else w) = ![u, w] := by
  funext j
  fin_cases j <;> rfl

private lemma lieCorr0_committed_value (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) (s : ℝ) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
          (deTurckLieCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
          (iteratedCovGrad (I := I) g₀ 0 2 0 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x
        ![((chartModelBasis E) i : TangentSpace I x), ((chartModelBasis E) j : TangentSpace I x)] =
      -(∑ m : Fin (Module.finrank ℝ E), ∑ ml : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x m ml *
          (∑ k : Fin (Module.finrank ℝ E), ∑ kl : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k kl *
              (((∑ p : Fin (Module.finrank ℝ E),
                  lieCorr0CovASc (I := I) (M := M)
                      (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i m k p *
                    chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x p j)
                + (∑ p : Fin (Module.finrank ℝ E),
                  lieCorr0CovASc (I := I) (M := M)
                      (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x j m k p *
                    chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x p i)) *
                realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x ml kl
                  (extChartAt I x x))))
      + ((∑ p : Fin (Module.finrank ℝ E),
          lieCorr0CovWSc (I := I) (M := M)
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i p *
            realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p j (extChartAt I x x))
        + (∑ p : Fin (Module.finrank ℝ E),
          lieCorr0CovWSc (I := I) (M := M)
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x j p *
            realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i p
              (extChartAt I x x))) := by
  classical
  set g₁ : SmoothRiemannianMetric I M := realizedFam (I := I) g₀ T T' hδ hδ' s with hg₁
  set W₀ : SmoothCcTensor g₀ 0 2 :=
    iteratedCovGrad (I := I) g₀ 0 2 0 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) with hW₀
  rw [deTurckLieCoeffField_apply_eq (I := I) (M := M) g₀ g₁ g_bg W₀ x
    ![((chartModelBasis E) i : TangentSpace I x), ((chartModelBasis E) j : TangentSpace I x)]]
  have hv0 : (![((chartModelBasis E) i : TangentSpace I x),
      ((chartModelBasis E) j : TangentSpace I x)] : Fin 2 → TangentSpace I x) 0 =
      ((chartModelBasis E) i : TangentSpace I x) := rfl
  have hv1 : (![((chartModelBasis E) i : TangentSpace I x),
      ((chartModelBasis E) j : TangentSpace I x)] : Fin 2 → TangentSpace I x) 1 =
      ((chartModelBasis E) j : TangentSpace I x) := rfl
  rw [hv0, hv1]
  have hDLa : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      unitModel (I := I) (M := M) g₀ 2 W₀ x
          (fun j' => if j' = 0 then smoothOrthoFrame (I := I) g₁ x a x
            else smoothOrthoFrame (I := I) g₁ x b x) *
        (g₁.inner x
            (deTurckConnDiffCovDeriv (I := I) g₁ g_bg
              (smoothExtensionTangent (I := I) x ((chartModelBasis E) i : TangentSpace I x))
              (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
              (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x)
            ((chartModelBasis E) j : TangentSpace I x)
          + g₁.inner x
            (deTurckConnDiffCovDeriv (I := I) g₁ g_bg
              (smoothExtensionTangent (I := I) x ((chartModelBasis E) j : TangentSpace I x))
              (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
              (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x)
            ((chartModelBasis E) i : TangentSpace I x))) =
      ∑ m : Fin (Module.finrank ℝ E), ∑ ml : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x m ml *
          (∑ k : Fin (Module.finrank ℝ E), ∑ kl : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g₁ x x k kl *
              (((∑ p : Fin (Module.finrank ℝ E),
                  lieCorr0CovASc (I := I) (M := M) g₁ g_bg x i m k p *
                    chartGramMatrix (I := I) g₁ x x p j)
                + (∑ p : Fin (Module.finrank ℝ E),
                  lieCorr0CovASc (I := I) (M := M) g₁ g_bg x j m k p *
                    chartGramMatrix (I := I) g₁ x x p i)) *
                realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x ml kl
                  (extChartAt I x x))) := by
    set K : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
      frameConnDiffCovDerivKernel (I := I) g₁ g_bg x
        ((chartModelBasis E) i : TangentSpace I x)
        ((chartModelBasis E) j : TangentSpace I x) with hK
    set Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
      (bilinFormToModel (TangentSpace I x)).symm
        (unitModel (I := I) (M := M) g₀ 2 W₀ x) with hDd
    have hDdev : ∀ (u w : TangentSpace I x), Dd u w =
        unitModel (I := I) (M := M) g₀ 2 W₀ x (fun j' => if j' = 0 then u else w) := by
      intro u w
      rw [hDd, bilinFormToModel_symm_apply]
      refine congrArg (fun t : Fin 2 → E => unitModel (I := I) (M := M) g₀ 2 W₀ x t) ?_
      funext j'
      fin_cases j' <;> rfl
    have hterm : ∀ a b : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 2 W₀ x
            (fun j' => if j' = 0 then smoothOrthoFrame (I := I) g₁ x a x
              else smoothOrthoFrame (I := I) g₁ x b x) *
          (g₁.inner x
              (deTurckConnDiffCovDeriv (I := I) g₁ g_bg
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i : TangentSpace I x))
                (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x)
              ((chartModelBasis E) j : TangentSpace I x)
            + g₁.inner x
              (deTurckConnDiffCovDeriv (I := I) g₁ g_bg
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) j : TangentSpace I x))
                (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x)
              ((chartModelBasis E) i : TangentSpace I x)) =
        K (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x) *
          Dd (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x) := by
      intro a b
      rw [hK, frameDLaKernel_apply]
      rw [hDdev]
      rw [show (connDiffCovDerivOp (I := I) g₁ g_bg x
          ((chartModelBasis E) i : TangentSpace I x)
          (smoothOrthoFrame (I := I) g₁ x a x)
          (smoothOrthoFrame (I := I) g₁ x b x)) =
        deTurckConnDiffCovDeriv (I := I) g₁ g_bg
          (smoothExtensionTangent (I := I) x ((chartModelBasis E) i : TangentSpace I x))
          (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
          (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x from
        dLaCovKernel_apply_extend (I := I) g₁ g_bg x _ _ _]
      rw [show (connDiffCovDerivOp (I := I) g₁ g_bg x
          ((chartModelBasis E) j : TangentSpace I x)
          (smoothOrthoFrame (I := I) g₁ x a x)
          (smoothOrthoFrame (I := I) g₁ x b x)) =
        deTurckConnDiffCovDeriv (I := I) g₁ g_bg
          (smoothExtensionTangent (I := I) x ((chartModelBasis E) j : TangentSpace I x))
          (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
          (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x from
        dLaCovKernel_apply_extend (I := I) g₁ g_bg x _ _ _]
      ring
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hterm a b))]
    rw [double_frame_bilin_trace_eq_fixed (I := I) g₁ x K Dd
      (fun a => smoothOrthoFrame (I := I) g₁ x a x)
      (fun a b => smoothOrthoFrame_orthonormal_at_center (I := I) g₁ x a b)]
    refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun ml _ => ?_))
    refine congrArg (fun t : ℝ => chartInvGramMatrix (I := I) g₁ x x m ml * t) ?_
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun kl _ => ?_))
    refine congrArg (fun t : ℝ => chartInvGramMatrix (I := I) g₁ x x k kl * t) ?_
    rw [hK, frameDLaKernel_apply]
    rw [lieCorr0_dLa_inner_basis (I := I) (M := M) g₁ g_bg x i j m k,
      lieCorr0_dLa_inner_basis (I := I) (M := M) g₁ g_bg x j i m k]
    rw [hDdev]
    rw [show unitModel (I := I) (M := M) g₀ 2 W₀ x
        (fun j' => if j' = 0 then ((chartModelBasis E) ml : TangentSpace I x)
          else ((chartModelBasis E) kl : TangentSpace I x)) =
      realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x ml kl (extChartAt I x x) from by
      rw [lieCorr0_ite_pair_eq (I := I) x _ _]
      rw [hW₀]
      exact lieCorr0_icg0_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x ml kl]
  rw [hDLa]
  refine congrArg (fun t : ℝ => -(∑ m : Fin (Module.finrank ℝ E),
    ∑ ml : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g₁ x x m ml *
        (∑ k : Fin (Module.finrank ℝ E), ∑ kl : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g₁ x x k kl *
            (((∑ p : Fin (Module.finrank ℝ E),
                lieCorr0CovASc (I := I) (M := M) g₁ g_bg x i m k p *
                  chartGramMatrix (I := I) g₁ x x p j)
              + (∑ p : Fin (Module.finrank ℝ E),
                lieCorr0CovASc (I := I) (M := M) g₁ g_bg x j m k p *
                  chartGramMatrix (I := I) g₁ x x p i)) *
              realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x ml kl
                (extChartAt I x x)))) + t) ?_
  have hW1 : unitModel (I := I) (M := M) g₀ 2 W₀ x
      (fun j' => if j' = 0 then
        deTurckVFCovDeriv (I := I) g₁ g_bg
          (smoothExtensionTangent (I := I) x ((chartModelBasis E) i : TangentSpace I x)) x
        else ((chartModelBasis E) j : TangentSpace I x)) =
      ∑ p : Fin (Module.finrank ℝ E),
        lieCorr0CovWSc (I := I) (M := M) g₁ g_bg x i p *
          realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p j (extChartAt I x x) := by
    rw [lieCorr0_ite_pair_eq (I := I) x _ _]
    rw [lieCorr0_covW_basis (I := I) (M := M) g₁ g_bg x i]
    rw [show ((∑ p : Fin (Module.finrank ℝ E),
        lieCorr0CovWSc (I := I) (M := M) g₁ g_bg x i p •
          ((chartModelBasis E) p : TangentSpace I x) : TangentSpace I x) : E) =
      (∑ p : Fin (Module.finrank ℝ E),
        lieCorr0CovWSc (I := I) (M := M) g₁ g_bg x i p • (chartModelBasis E) p : E) from rfl]
    rw [lieCorr0_cmm2_expand_slot0 (unitModel (I := I) (M := M) g₀ 2 W₀ x)
      (fun p => lieCorr0CovWSc (I := I) (M := M) g₁ g_bg x i p) ((chartModelBasis E) j)]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    refine congrArg (fun t : ℝ => lieCorr0CovWSc (I := I) (M := M) g₁ g_bg x i p * t) ?_
    rw [hW₀]
    exact lieCorr0_icg0_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p j
  have hW2 : unitModel (I := I) (M := M) g₀ 2 W₀ x
      (fun j' => if j' = 0 then ((chartModelBasis E) i : TangentSpace I x)
        else deTurckVFCovDeriv (I := I) g₁ g_bg
          (smoothExtensionTangent (I := I) x ((chartModelBasis E) j : TangentSpace I x)) x) =
      ∑ p : Fin (Module.finrank ℝ E),
        lieCorr0CovWSc (I := I) (M := M) g₁ g_bg x j p *
          realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i p (extChartAt I x x) := by
    rw [lieCorr0_ite_pair_eq (I := I) x _ _]
    rw [lieCorr0_covW_basis (I := I) (M := M) g₁ g_bg x j]
    rw [show ((∑ p : Fin (Module.finrank ℝ E),
        lieCorr0CovWSc (I := I) (M := M) g₁ g_bg x j p •
          ((chartModelBasis E) p : TangentSpace I x) : TangentSpace I x) : E) =
      (∑ p : Fin (Module.finrank ℝ E),
        lieCorr0CovWSc (I := I) (M := M) g₁ g_bg x j p • (chartModelBasis E) p : E) from rfl]
    rw [lieCorr0_cmm2_expand_slot1 (unitModel (I := I) (M := M) g₀ 2 W₀ x)
      (fun p => lieCorr0CovWSc (I := I) (M := M) g₁ g_bg x j p) ((chartModelBasis E) i)]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    refine congrArg (fun t : ℝ => lieCorr0CovWSc (I := I) (M := M) g₁ g_bg x j p * t) ?_
    rw [hW₀]
    exact lieCorr0_icg0_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i p
  rw [hW1, hW2]

private lemma lieCorr0_phi0b_value_split (_hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (_hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) (s : ℝ) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
          (deTurckLieCoeffField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg +
            deTurckLieRemainderField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
          (iteratedCovGrad (I := I) g₀ 0 2 0 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x
        ![((chartModelBasis E) i : TangentSpace I x), ((chartModelBasis E) j : TangentSpace I x)] =
      unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
          (deTurckLieCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
          (iteratedCovGrad (I := I) g₀ 0 2 0 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x
        ![((chartModelBasis E) i : TangentSpace I x), ((chartModelBasis E) j : TangentSpace I x)]
      + Tensor0SSpace.toModel
          (deTurckLieRemainderTotalFib (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
              (iteratedCovGrad (I := I) g₀ 0 2 0
                (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))).toSection x)
              (unitTensor (I := I) (M := M) x)))
          ![(chartModelBasis E) i, (chartModelBasis E) j] := by
  classical
  set g₁ : SmoothRiemannianMetric I M := realizedFam (I := I) g₀ T T' hδ hδ' s with hg₁
  set W₀ : SmoothCcTensor g₀ 0 2 :=
    iteratedCovGrad (I := I) g₀ 0 2 0 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) with hW₀
  set D₀ : Tensor0SSpace 2 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W₀.toSection x)
      (unitTensor (I := I) (M := M) x) with hD₀
  have hunfold : ∀ (Φ : SmoothCcTensor g₀ 2 2),
      unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2 Φ W₀) x
        ![((chartModelBasis E) i : TangentSpace I x),
          ((chartModelBasis E) j : TangentSpace I x)] =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from Φ.toSection x) D₀)
        ![(chartModelBasis E) i, (chartModelBasis E) j] := by
    intro Φ
    rw [unitModel, appCc_toSection]
    rfl
  rw [hunfold, hunfold]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg +
        deTurckLieRemainderField (I := I) (M := M) g₀ g₁ g_bg).toSection x) D₀) =
    ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg).toSection x) D₀) +
    (deTurckLieRemainderTotalFib (I := I) g₀ g₁ g_bg x D₀) from by
    rw [smoothCcTensor_toSection_add_apply (I := I) (M := M) g₀
      (deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg)
      (deTurckLieRemainderField (I := I) (M := M) g₀ g₁ g_bg) x]
    rfl]
  rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (arm2ReadoutCovDerivPair arm1ReadoutCovDeriv arm1ReadoutCovDeriv_center_eq arm2ReadoutCovDerivPair_center_eq partialDeriv_realizedGramDeriv_eq_half_sum_euclidPartial)
open DifferentialGeometry.Analysis.Sobolev.Chart (chartPushedRaw chartPushedRaw_apply_of_mem chartTargetEuclid chartTargetEuclid_isOpen)
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity (euclidPartial euclidPartial_def chartChristoffelEuclid chartChristoffelEuclid_def chartPushedRaw_tensorChartComponentRaw_contDiffOn)

private lemma lieCorr0_raw_readout (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (c d : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
        (I := I) (M := M) g₀ 0 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![] ![c, d] x =
      realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c d (extChartAt I x x) := by
  have hev := lieArm_scalarOnE_symmS_eventuallyEq_realizedGramDeriv (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' x c d
  have hpt := hev.self_of_nhds
  rw [DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_def] at hpt
  have hx_src : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source (I := I)]; exact mem_chart_source H x
  rw [(extChartAt I x).left_inv hx_src] at hpt
  exact hpt

private lemma lieCorr0_arm1Readout_center (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (a b c : Fin (Module.finrank ℝ E)) :
    arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x
        ![a, b, c] =
      (- ∑ r : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₀ x a b r (extChartAt I x x) *
            realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r c (extChartAt I x x))
      + (- ∑ r : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₀ x a c r (extChartAt I x x) *
            realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x b r
              (extChartAt I x x)) := by
  rw [arm1ReadoutCovDeriv_center_eq (I := I) (M := M) g₀
    (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x a b c]
  refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) ?_ ?_
  · refine congrArg Neg.neg (Finset.sum_congr rfl (fun r _ => ?_))
    rw [lieCorr0_raw_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r c]
  · refine congrArg Neg.neg (Finset.sum_congr rfl (fun r _ => ?_))
    rw [lieCorr0_raw_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x b r]

private lemma lieCorr0_euclid_christoffel_bridge (g : SmoothRiemannianMetric I M) (x : M)
    (m a b r : Fin (Module.finrank ℝ E)) :
    euclidPartial (E := E) m
        (chartChristoffelEuclid (I := I) g x a b r)
        (toEuclidean (E := E) (extChartAt I x x)) =
      partialDeriv (E := E) m (chartChristoffel (I := I) g x a b r) (extChartAt I x x) := by
  classical
  have hy_int : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E) :=
    DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
      (I := I) x (mem_extChartAt_target x)
  have hdiff : DifferentiableAt ℝ (chartChristoffel (I := I) g x a b r) (extChartAt I x x) :=
    ((DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel_contDiffOn_interior
      (I := I) g x a b r).contDiffAt
      (isOpen_interior.mem_nhds hy_int)).differentiableAt (by simp)
  rw [euclidPartial_def, DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv]
  have hcomp : (chartChristoffelEuclid (I := I) g x a b r) =
      (chartChristoffel (I := I) g x a b r) ∘ (toEuclidean (E := E)).symm := rfl
  rw [hcomp]
  rw [fderiv_comp (toEuclidean (E := E) (extChartAt I x x))
    (by
      rw [(toEuclidean (E := E)).symm_apply_apply]
      exact hdiff)
    (toEuclidean (E := E)).symm.differentiableAt]
  rw [(toEuclidean (E := E)).symm.fderiv]
  rw [ContinuousLinearMap.comp_apply]
  rw [(toEuclidean (E := E)).symm_apply_apply]
  refine congrArg (fun t => fderiv ℝ (chartChristoffel (I := I) g x a b r)
    (extChartAt I x x) t) ?_
  rw [ContinuousLinearEquiv.coe_coe]
  rw [chartModelBasis_apply]

private lemma lieCorr0_euclid_f_bridge (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (m r d : Fin (Module.finrank ℝ E)) :
    euclidPartial (E := E) m
        (chartPushedRaw I x
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
            (I := I) (M := M) g₀ 0 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![] ![r, d]))
        (toEuclidean (E := E) (extChartAt I x x)) =
      partialDeriv (E := E) m
        (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r d)
        (extChartAt I x x) := by
  classical
  have hcenter : (toEuclidean (E := E)) (extChartAt I x x) ∈
      chartTargetEuclid (I := I) (M := M) x :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.toEuclidean_extChartAt_mem_chartTargetEuclid
      (I := I) (M := M) x (mem_chart_source H x)
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) x) :=
    chartTargetEuclid_isOpen (I := I) (M := M) x
  have hev : (chartPushedRaw I x
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
        (I := I) (M := M) g₀ 0 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![] ![r, d]))
      =ᶠ[𝓝 ((toEuclidean (E := E)) (extChartAt I x x))]
      (fun y => (1 / 2 : ℝ) * chartPushedRaw I x
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
            (I := I) (M := M) g₀ 0 2 (T - T') x ![] ![r, d]) y +
        (1 / 2 : ℝ) * chartPushedRaw I x
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
            (I := I) (M := M) g₀ 0 2 (T - T') x ![] ![d, r]) y) := by
    filter_upwards [hopen.mem_nhds hcenter] with y hy
    rw [chartPushedRaw_apply_of_mem (I := I) (M := M) x _ hy,
      chartPushedRaw_apply_of_mem (I := I) (M := M) x _ hy,
      chartPushedRaw_apply_of_mem (I := I) (M := M) x _ hy]
    have hb : (extChartAt I x).symm ((toEuclidean (E := E)).symm y) ∈
        (chartAt H x).source := by
      obtain ⟨z, hz, rfl⟩ := hy
      rw [(toEuclidean (E := E)).symm_apply_apply, ← extChartAt_source (I := I)]
      exact (extChartAt I x).map_target hz
    rw [lieArm_symmS_rawComponent (I := I) (M := M) g₀ (T - T') x r d hb]
    ring
  rw [show euclidPartial (E := E) m
      (chartPushedRaw I x
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
          (I := I) (M := M) g₀ 0 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![] ![r, d]))
      (toEuclidean (E := E) (extChartAt I x x)) =
    euclidPartial (E := E) m
      (fun y => (1 / 2 : ℝ) * chartPushedRaw I x
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
            (I := I) (M := M) g₀ 0 2 (T - T') x ![] ![r, d]) y +
        (1 / 2 : ℝ) * chartPushedRaw I x
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
            (I := I) (M := M) g₀ 0 2 (T - T') x ![] ![d, r]) y)
      (toEuclidean (E := E) (extChartAt I x x)) from by
    rw [euclidPartial_def, euclidPartial_def, hev.fderiv_eq]]
  have hd1 : DifferentiableAt ℝ (chartPushedRaw I x
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
        (I := I) (M := M) g₀ 0 2 (T - T') x ![] ![r, d]))
      (toEuclidean (E := E) (extChartAt I x x)) :=
    ((chartPushedRaw_tensorChartComponentRaw_contDiffOn (I := I) (M := M) g₀ 0 2
      (T - T') x ![] ![r, d]).contDiffAt (hopen.mem_nhds hcenter)).differentiableAt (by simp)
  have hd2 : DifferentiableAt ℝ (chartPushedRaw I x
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
        (I := I) (M := M) g₀ 0 2 (T - T') x ![] ![d, r]))
      (toEuclidean (E := E) (extChartAt I x x)) :=
    ((chartPushedRaw_tensorChartComponentRaw_contDiffOn (I := I) (M := M) g₀ 0 2
      (T - T') x ![] ![d, r]).contDiffAt (hopen.mem_nhds hcenter)).differentiableAt (by simp)
  rw [euclidPartial_def]
  rw [fderiv_fun_add (hd1.const_mul (1 / 2 : ℝ)) (hd2.const_mul (1 / 2 : ℝ))]
  rw [ContinuousLinearMap.add_apply]
  rw [fderiv_const_mul hd1 (1 / 2 : ℝ), fderiv_const_mul hd2 (1 / 2 : ℝ)]
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply]
  rw [partialDeriv_realizedGramDeriv_eq_half_sum_euclidPartial (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' x m r d]
  rw [euclidPartial_def, euclidPartial_def]
  simp only [smul_eq_mul]

private lemma lieCorr0_R4_center (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (a b c d : Fin (Module.finrank ℝ E)) :
    arm2ReadoutCovDerivPair (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x
        ![a, b, c, d] =
      (((- ∑ r : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) a (chartChristoffel (I := I) g₀ x c b r)
                  (extChartAt I x x) *
                realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r d
                  (extChartAt I x x))
          + (- ∑ r : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) a (chartChristoffel (I := I) g₀ x d b r)
                  (extChartAt I x x) *
                realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c r
                  (extChartAt I x x)))
        + ((- ∑ r : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g₀ x c b r (extChartAt I x x) *
                partialDeriv (E := E) a
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r d)
                  (extChartAt I x x))
          + (- ∑ r : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g₀ x d b r (extChartAt I x x) *
                partialDeriv (E := E) a
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c r)
                  (extChartAt I x x))))
      + ((- ∑ r : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g₀ x a b r (extChartAt I x x) *
              (partialDeriv (E := E) r
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c d)
                  (extChartAt I x x)
                + ((- ∑ t : Fin (Module.finrank ℝ E),
                      chartChristoffel (I := I) g₀ x r c t (extChartAt I x x) *
                        realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x t d
                          (extChartAt I x x))
                  + (- ∑ t : Fin (Module.finrank ℝ E),
                      chartChristoffel (I := I) g₀ x r d t (extChartAt I x x) *
                        realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c t
                          (extChartAt I x x)))))
        + ((- ∑ r : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g₀ x a c r (extChartAt I x x) *
                (partialDeriv (E := E) b
                    (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r d)
                    (extChartAt I x x)
                  + ((- ∑ t : Fin (Module.finrank ℝ E),
                        chartChristoffel (I := I) g₀ x b r t (extChartAt I x x) *
                          realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x t d
                            (extChartAt I x x))
                    + (- ∑ t : Fin (Module.finrank ℝ E),
                        chartChristoffel (I := I) g₀ x b d t (extChartAt I x x) *
                          realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r t
                            (extChartAt I x x)))))
          + (- ∑ r : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g₀ x a d r (extChartAt I x x) *
                (partialDeriv (E := E) b
                    (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c r)
                    (extChartAt I x x)
                  + ((- ∑ t : Fin (Module.finrank ℝ E),
                        chartChristoffel (I := I) g₀ x b c t (extChartAt I x x) *
                          realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x t r
                            (extChartAt I x x))
                    + (- ∑ t : Fin (Module.finrank ℝ E),
                        chartChristoffel (I := I) g₀ x b r t (extChartAt I x x) *
                          realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c t
                            (extChartAt I x x))))))) := by
  classical
  rw [arm2ReadoutCovDerivPair_center_eq (I := I) (M := M) g₀
    (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x a b c d]
  refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) (congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) ?_ ?_)
    (congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) ?_ (congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) ?_ ?_))
  · refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) ?_ ?_
    · refine congrArg Neg.neg (Finset.sum_congr rfl (fun r _ => ?_))
      rw [lieCorr0_euclid_christoffel_bridge (I := I) g₀ x a c b r,
        lieCorr0_raw_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r d]
    · refine congrArg Neg.neg (Finset.sum_congr rfl (fun r _ => ?_))
      rw [lieCorr0_euclid_christoffel_bridge (I := I) g₀ x a d b r,
        lieCorr0_raw_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c r]
  · refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) ?_ ?_
    · refine congrArg Neg.neg (Finset.sum_congr rfl (fun r _ => ?_))
      rw [lieCorr0_euclid_f_bridge (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a r d]
    · refine congrArg Neg.neg (Finset.sum_congr rfl (fun r _ => ?_))
      rw [lieCorr0_euclid_f_bridge (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a c r]
  · refine congrArg Neg.neg (Finset.sum_congr rfl (fun r _ => ?_))
    refine congrArg (fun t : ℝ =>
      chartChristoffel (I := I) g₀ x a b r (extChartAt I x x) * t) ?_
    refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) ?_ ?_
    · rw [lieCorr0_euclid_f_bridge (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r c d]
    · refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) ?_ ?_
      · refine congrArg Neg.neg (Finset.sum_congr rfl (fun t _ => ?_))
        rw [lieCorr0_raw_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x t d]
      · refine congrArg Neg.neg (Finset.sum_congr rfl (fun t _ => ?_))
        rw [lieCorr0_raw_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c t]
  · refine congrArg Neg.neg (Finset.sum_congr rfl (fun r _ => ?_))
    refine congrArg (fun t : ℝ =>
      chartChristoffel (I := I) g₀ x a c r (extChartAt I x x) * t) ?_
    refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) ?_ ?_
    · rw [lieCorr0_euclid_f_bridge (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x b r d]
    · refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) ?_ ?_
      · refine congrArg Neg.neg (Finset.sum_congr rfl (fun t _ => ?_))
        rw [lieCorr0_raw_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x t d]
      · refine congrArg Neg.neg (Finset.sum_congr rfl (fun t _ => ?_))
        rw [lieCorr0_raw_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r t]
  · refine congrArg Neg.neg (Finset.sum_congr rfl (fun r _ => ?_))
    refine congrArg (fun t : ℝ =>
      chartChristoffel (I := I) g₀ x a d r (extChartAt I x x) * t) ?_
    refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) ?_ ?_
    · rw [lieCorr0_euclid_f_bridge (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x b c r]
    · refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) ?_ ?_
      · refine congrArg Neg.neg (Finset.sum_congr rfl (fun t _ => ?_))
        rw [lieCorr0_raw_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x t r]
      · refine congrArg Neg.neg (Finset.sum_congr rfl (fun t _ => ?_))
        rw [lieCorr0_raw_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c t]

private lemma lieCorr0_pd_christoffel_sub (gA gB : SmoothRiemannianMetric I M) (x : M)
    (m a b k : Fin (Module.finrank ℝ E)) :
    partialDeriv (E := E) m
        (fun y => chartChristoffel (I := I) gA x a b k y -
          chartChristoffel (I := I) gB x a b k y) (extChartAt I x x) =
      partialDeriv (E := E) m (chartChristoffel (I := I) gA x a b k) (extChartAt I x x) -
        partialDeriv (E := E) m (chartChristoffel (I := I) gB x a b k) (extChartAt I x x) := by
  have hy_int : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E) :=
    DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
      (I := I) x (mem_extChartAt_target x)
  have hA : DifferentiableAt ℝ (chartChristoffel (I := I) gA x a b k) (extChartAt I x x) :=
    ((DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel_contDiffOn_interior
      (I := I) gA x a b k).contDiffAt
      (isOpen_interior.mem_nhds hy_int)).differentiableAt (by simp)
  have hB : DifferentiableAt ℝ (chartChristoffel (I := I) gB x a b k) (extChartAt I x x) :=
    ((DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel_contDiffOn_interior
      (I := I) gB x a b k).contDiffAt
      (isOpen_interior.mem_nhds hy_int)).differentiableAt (by simp)
  exact PDE.DeTurck.RicciLinearization.partialDeriv_sub (i := m) _ _ hA hB

private lemma lieCorr0_pd_vfcomp_center (gA gB : SmoothRiemannianMetric I M) (x : M)
    (m k : Fin (Module.finrank ℝ E)) :
    partialDeriv (E := E) m
        (fun y => PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) gA gB x k y)
        (extChartAt I x x) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) m
            (DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramOnE (I := I) gA x a b)
            (extChartAt I x x) *
          (chartChristoffel (I := I) gA x a b k (extChartAt I x x) -
            chartChristoffel (I := I) gB x a b k (extChartAt I x x)) +
        chartInvGramMatrix (I := I) gA x x a b *
          (partialDeriv (E := E) m (chartChristoffel (I := I) gA x a b k)
              (extChartAt I x x) -
            partialDeriv (E := E) m (chartChristoffel (I := I) gB x a b k)
              (extChartAt I x x))) := by
  have hy_int : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E) :=
    DifferentialGeometry.Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
      (I := I) x (mem_extChartAt_target x)
  rw [show partialDeriv (E := E) m
      (fun y => PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) gA gB x k y)
      (extChartAt I x x) =
    partialDeriv (E := E) m
      (PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) gA gB x k)
      (extChartAt I x x) from rfl]
  rw [DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients.partialDeriv_chartDeTurckVFComp_eq
    (I := I) gA gB x m k hy_int]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [lieArm_chartInvGramOnE_center (I := I) gA x a b]

end LieCorr0Value

end LieCorr0Joint

section LieCorr0MasterValue

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open DifferentialGeometry.Integral.DivergenceTheorem (chartInvGramMatrix partialDeriv chartChristoffel chartGramOnE chartInvGramOnE chartRiemannTensor chartChristoffel_symm chartGramOnE_symm chartInvGramOnE_symm partialDeriv_chartInvGramOnE_eq extChartAt_target_subset_interior_of_boundaryless)
open DifferentialGeometry.Integral.Measure (chartGramMatrix)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (ccTensor02Symm unitModel unitTensor deTurckLieCoeffField arm2ReadoutCovDerivPair arm1ReadoutCovDeriv)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (realizedGramDeriv realizedFam)
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients (gramBracket gramBracketDeriv chartChristoffel_eq_sum_invGramOnE_bracket partialDeriv_chartChristoffel_eq partialDeriv_gramBracket_eq)

private noncomputable def lc0Ig (g₁ : SmoothRiemannianMetric I M) (x : M) :
    Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
  fun a b => chartInvGramMatrix (I := I) g₁ x x a b

private noncomputable def lc0Cg (g₁ : SmoothRiemannianMetric I M) (x : M) :
    Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
  fun a b => chartGramMatrix (I := I) g₁ x x a b

private noncomputable def lc0Ev (x : M)
    (F : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → E → ℝ) :
    Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
  fun a b => F a b (extChartAt I x x)

private noncomputable def lc0Pd (x : M)
    (F : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → E → ℝ) :
    Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
  fun m a b => partialDeriv (E := E) m (F a b) (extChartAt I x x)

private noncomputable def lc0Dg (g₁ : SmoothRiemannianMetric I M) (x : M) :
    Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
  fun m a b => partialDeriv (E := E) m (chartGramOnE (I := I) g₁ x a b) (extChartAt I x x)

private noncomputable def lc0DDg (g₁ : SmoothRiemannianMetric I M) (x : M) :
    Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ :=
  fun m k a b => partialDeriv (E := E) m
    (partialDeriv (E := E) k (chartGramOnE (I := I) g₁ x a b)) (extChartAt I x x)

private noncomputable def lc0Dig (g₁ : SmoothRiemannianMetric I M) (x : M) :
    Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
  fun m a b => partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ x a b) (extChartAt I x x)

private noncomputable def lc0Ga (g : SmoothRiemannianMetric I M) (x : M) :
    Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
  fun a b k => chartChristoffel (I := I) g x a b k (extChartAt I x x)

private noncomputable def lc0DGa (g : SmoothRiemannianMetric I M) (x : M) :
    Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ :=
  fun m a b k => partialDeriv (E := E) m (chartChristoffel (I := I) g x a b k)
    (extChartAt I x x)

private noncomputable def lc0Gb (g₁ : SmoothRiemannianMetric I M) (x : M) :
    Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
  fun a b l => gramBracket (I := I) g₁ x a b l (extChartAt I x x)

private noncomputable def lc0DGb (g₁ : SmoothRiemannianMetric I M) (x : M) :
    Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ :=
  fun m a b l => partialDeriv (E := E) m (gramBracket (I := I) g₁ x a b l)
    (extChartAt I x x)

private lemma lc0_center_interior (x : M) :
    extChartAt I x x ∈ interior ((extChartAt I x).target : Set E) :=
  extChartAt_target_subset_interior_of_boundaryless (I := I) x (mem_extChartAt_target x)

private lemma lc0_vfcomp_center (g₁ gP : SmoothRiemannianMetric I M) (x : M)
    (k : Fin (Module.finrank ℝ E)) :
    PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) g₁ gP x k
        (extChartAt I x x) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x a b *
          (chartChristoffel (I := I) g₁ x a b k (extChartAt I x x) -
            chartChristoffel (I := I) gP x a b k (extChartAt I x x)) := by
  rw [PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp_def]
  exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by
    rw [lieArm_chartInvGramOnE_center (I := I) g₁ x a b]))

private lemma lc0_gramBracket_symm (g₁ : SmoothRiemannianMetric I M) (x : M)
    (a b l : Fin (Module.finrank ℝ E)) (y : E) :
    gramBracket (I := I) g₁ x a b l y = gramBracket (I := I) g₁ x b a l y := by
  unfold DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients.gramBracket
  rw [show chartGramOnE (I := I) g₁ x a b = chartGramOnE (I := I) g₁ x b a from
    funext fun y' => chartGramOnE_symm (I := I) g₁ x a b y']
  ring

private lemma lc0_hga1e (g₁ : SmoothRiemannianMetric I M) (x : M)
    (a b k : Fin (Module.finrank ℝ E)) :
    chartChristoffel (I := I) g₁ x a b k (extChartAt I x x) =
      (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k l *
          gramBracket (I := I) g₁ x a b l (extChartAt I x x) := by
  rw [chartChristoffel_eq_sum_invGramOnE_bracket (I := I) g₁ x a b k (extChartAt I x x)]
  refine congrArg (fun t : ℝ => (1 / 2 : ℝ) * t)
    (Finset.sum_congr rfl (fun l _ => ?_))
  rw [lieArm_chartInvGramOnE_center (I := I) g₁ x k l]

private lemma lc0_hdga1e (g₁ : SmoothRiemannianMetric I M) (x : M)
    (m a b k : Fin (Module.finrank ℝ E)) :
    partialDeriv (E := E) m (chartChristoffel (I := I) g₁ x a b k) (extChartAt I x x) =
      (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ x k l) (extChartAt I x x) *
            gramBracket (I := I) g₁ x a b l (extChartAt I x x) +
          chartInvGramMatrix (I := I) g₁ x x k l *
            partialDeriv (E := E) m (gramBracket (I := I) g₁ x a b l)
              (extChartAt I x x)) := by
  rw [partialDeriv_chartChristoffel_eq (I := I) g₁ x m a b k (lc0_center_interior (I := I) x)]
  refine congrArg (fun t : ℝ => (1 / 2 : ℝ) * t)
    (Finset.sum_congr rfl (fun l _ => ?_))
  rw [lieArm_chartInvGramOnE_center (I := I) g₁ x k l,
    partialDeriv_gramBracket_eq (I := I) g₁ x m a b l (lc0_center_interior (I := I) x)]

private lemma lc0_hdige (g₁ : SmoothRiemannianMetric I M) (x : M)
    (m a b : Fin (Module.finrank ℝ E)) :
    partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ x a b) (extChartAt I x x) =
      -∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x a p * chartInvGramMatrix (I := I) g₁ x x q b *
          partialDeriv (E := E) m (chartGramOnE (I := I) g₁ x p q) (extChartAt I x x) := by
  rw [partialDeriv_chartInvGramOnE_eq (I := I) g₁ x (extChartAt I x x) m a b
    (lc0_center_interior (I := I) x)]
  refine congrArg Neg.neg ?_
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
  rw [lieArm_chartInvGramOnE_center (I := I) g₁ x a p,
    lieArm_chartInvGramOnE_center (I := I) g₁ x q b]

private lemma lc0_hdgbe (g₁ : SmoothRiemannianMetric I M) (x : M)
    (m a b l : Fin (Module.finrank ℝ E)) :
    partialDeriv (E := E) m (gramBracket (I := I) g₁ x a b l) (extChartAt I x x) =
      partialDeriv (E := E) m
          (partialDeriv (E := E) a (chartGramOnE (I := I) g₁ x l b)) (extChartAt I x x) +
        partialDeriv (E := E) m
          (partialDeriv (E := E) b (chartGramOnE (I := I) g₁ x l a)) (extChartAt I x x) -
        partialDeriv (E := E) m
          (partialDeriv (E := E) l (chartGramOnE (I := I) g₁ x a b)) (extChartAt I x x) := by
  rw [partialDeriv_gramBracket_eq (I := I) g₁ x m a b l (lc0_center_interior (I := I) x)]
  rfl

variable (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
variable {δ δ' : ℝ}

private lemma lc0_covASc_raw (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (a m k p : Fin (Module.finrank ℝ E)) :
    lieCorr0CovASc (I := I) (M := M) g₁ g_bg x a m k p =
      (partialDeriv (E := E) a (chartChristoffel (I := I) g₁ x k m p) (extChartAt I x x) -
          partialDeriv (E := E) a (chartChristoffel (I := I) g_bg x k m p)
            (extChartAt I x x)) +
        (∑ c : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₁ x a c p (extChartAt I x x) *
            (chartChristoffel (I := I) g₁ x k m c (extChartAt I x x) -
              chartChristoffel (I := I) g_bg x k m c (extChartAt I x x))) -
        (∑ c : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₁ x a m c (extChartAt I x x) *
            (chartChristoffel (I := I) g₁ x k c p (extChartAt I x x) -
              chartChristoffel (I := I) g_bg x k c p (extChartAt I x x))) -
        (∑ c : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₁ x a k c (extChartAt I x x) *
            (chartChristoffel (I := I) g₁ x c m p (extChartAt I x x) -
              chartChristoffel (I := I) g_bg x c m p (extChartAt I x x))) := by
  simp only [lieCorr0CovASc]
  rw [lieCorr0_pd_christoffel_sub (I := I) g₁ g_bg x a k m p]

private lemma lc0_covWSc_raw (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (a p : Fin (Module.finrank ℝ E)) :
    lieCorr0CovWSc (I := I) (M := M) g₁ g_bg x a p =
      (∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) a (chartInvGramOnE (I := I) g₁ x a' b')
              (extChartAt I x x) *
            (chartChristoffel (I := I) g₁ x a' b' p (extChartAt I x x) -
              chartChristoffel (I := I) g_bg x a' b' p (extChartAt I x x)) +
          chartInvGramMatrix (I := I) g₁ x x a' b' *
            (partialDeriv (E := E) a (chartChristoffel (I := I) g₁ x a' b' p)
                (extChartAt I x x) -
              partialDeriv (E := E) a (chartChristoffel (I := I) g_bg x a' b' p)
                (extChartAt I x x)))) +
      ∑ c : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g₁ x a c p (extChartAt I x x) *
          (∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g₁ x x a' b' *
              (chartChristoffel (I := I) g₁ x a' b' c (extChartAt I x x) -
                chartChristoffel (I := I) g_bg x a' b' c (extChartAt I x x))) := by
  simp only [lieCorr0CovWSc]
  rw [lieCorr0_pd_vfcomp_center (I := I) g₁ g_bg x a p]
  refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) rfl
    (Finset.sum_congr rfl (fun c _ => ?_))
  rw [lc0_vfcomp_center (I := I) g₁ g_bg x c]

private lemma lc0_nscalar_raw (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (i p : Fin (Module.finrank ℝ E)) :
    lieCorr0NScalar (I := I) (M := M) g₀ g₁ g_bg x i p =
      M0Abstract.nscB (lc0Ig (I := I) g₁ x) (lc0Dig (I := I) g₁ x)
        (lc0Ga (I := I) g₁ x) (lc0Ga (I := I) g₀ x) (lc0Ga (I := I) g_bg x)
        (lc0DGa (I := I) g₁ x) (lc0DGa (I := I) g₀ x) i p := by
  simp only [M0Abstract.nscB, lc0Ig, lc0Dig, lc0Ga, lc0DGa]
  simp only [lieCorr0NScalar]
  rw [lieCorr0_pd_vfcomp_center (I := I) g₁ g₀ x i p]
  refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ - t₂)
    (congrArg₂ (fun t₁ t₂ : ℝ => t₁ - t₂)
      (Finset.sum_congr rfl (fun m _ => ?_))
      (Finset.sum_congr rfl (fun m _ => ?_)))
    (congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) rfl
      (Finset.sum_congr rfl (fun m _ => ?_)))
  · rw [lc0_vfcomp_center (I := I) g₁ g₀ x m]
  · rw [lc0_vfcomp_center (I := I) g₁ g_bg x m]
  · rw [lc0_vfcomp_center (I := I) g₁ g₀ x m]

private lemma lc0_D0_readout (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (c d : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          (iteratedCovGrad (I := I) g₀ 0 2 0
            (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))).toSection x)
          (unitTensor (I := I) (M := M) x))
        ![(chartModelBasis E) c, (chartModelBasis E) d] =
      realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c d (extChartAt I x x) :=
  lieCorr0_icg0_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c d

private lemma lc0_chrCorr_center (g₁ : SmoothRiemannianMetric I M) (x : M)
    (F : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → E → ℝ)
    (a b k : Fin (Module.finrank ℝ E)) :
    PDE.DeTurck.DeTurckLinearization.christoffelFirstOrderCorrRaw (I := I) g₁ x F a b k
        (extChartAt I x x) =
      (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g₁ x x k p * F p q (extChartAt I x x) *
              chartInvGramMatrix (I := I) g₁ x x q l)) *
          gramBracket (I := I) g₁ x a b l (extChartAt I x x) := by
  simp only [PDE.DeTurck.DeTurckLinearization.christoffelFirstOrderCorrRaw]
  refine congrArg (fun t : ℝ => (1 / 2 : ℝ) * t)
    (Finset.sum_congr rfl (fun l _ => ?_))
  refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) (congrArg Neg.neg
    (Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun p _ => ?_)))) rfl
  rw [lieArm_chartInvGramOnE_center (I := I) g₁ x k p,
    lieArm_chartInvGramOnE_center (I := I) g₁ x q l]

private lemma lc0_wc_center (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (F : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → E → ℝ)
    (k : Fin (Module.finrank ℝ E)) :
    PDE.DeTurck.DeTurckLinearization.deTurckVFFirstOrderCorrRaw (I := I) g₁ g_bg x F k
        (extChartAt I x x) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        ((-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g₁ x x a p * F p q (extChartAt I x x) *
              chartInvGramMatrix (I := I) g₁ x x q b)) *
          (chartChristoffel (I := I) g₁ x a b k (extChartAt I x x) -
            chartChristoffel (I := I) g_bg x a b k (extChartAt I x x)) +
        chartInvGramMatrix (I := I) g₁ x x a b *
          ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
            (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g₁ x x k p * F p q (extChartAt I x x) *
                  chartInvGramMatrix (I := I) g₁ x x q l)) *
              gramBracket (I := I) g₁ x a b l (extChartAt I x x))) := by
  simp only [PDE.DeTurck.DeTurckLinearization.deTurckVFFirstOrderCorrRaw]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂)
    (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) (congrArg Neg.neg
      (Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun p _ => ?_)))) rfl)
    (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) ?_ ?_)
  · rw [lieArm_chartInvGramOnE_center (I := I) g₁ x a p,
      lieArm_chartInvGramOnE_center (I := I) g₁ x q b]
  · exact lieArm_chartInvGramOnE_center (I := I) g₁ x a b
  · exact lc0_chrCorr_center (I := I) g₁ x F a b k

private lemma lc0_d0_center (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (F : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → E → ℝ)
    (m k : Fin (Module.finrank ℝ E)) :
    PDE.DeTurck.DeTurckLinearization.deTurckVFFirstOrderCorrDeriv0Raw (I := I) g₁ g_bg x
        F m k (extChartAt I x x) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        ((-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
            (partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ x a p)
                  (extChartAt I x x) * F p q (extChartAt I x x) *
                chartInvGramMatrix (I := I) g₁ x x q b +
              chartInvGramMatrix (I := I) g₁ x x a p * F p q (extChartAt I x x) *
                partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ x q b)
                  (extChartAt I x x)))) *
          (chartChristoffel (I := I) g₁ x a b k (extChartAt I x x) -
            chartChristoffel (I := I) g_bg x a b k (extChartAt I x x)) +
        (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g₁ x x a p * F p q (extChartAt I x x) *
              chartInvGramMatrix (I := I) g₁ x x q b)) *
          (partialDeriv (E := E) m (chartChristoffel (I := I) g₁ x a b k)
              (extChartAt I x x) -
            partialDeriv (E := E) m (chartChristoffel (I := I) g_bg x a b k)
              (extChartAt I x x)) +
        partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ x a b) (extChartAt I x x) *
          ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
            (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g₁ x x k p * F p q (extChartAt I x x) *
                  chartInvGramMatrix (I := I) g₁ x x q l)) *
              gramBracket (I := I) g₁ x a b l (extChartAt I x x)) +
        chartInvGramMatrix (I := I) g₁ x x a b *
          ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
            ((-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
                (partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ x k p)
                      (extChartAt I x x) * F p q (extChartAt I x x) *
                    chartInvGramMatrix (I := I) g₁ x x q l +
                  chartInvGramMatrix (I := I) g₁ x x k p * F p q (extChartAt I x x) *
                    partialDeriv (E := E) m (chartInvGramOnE (I := I) g₁ x q l)
                      (extChartAt I x x)))) *
              gramBracket (I := I) g₁ x a b l (extChartAt I x x) +
            (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g₁ x x k p * F p q (extChartAt I x x) *
                  chartInvGramMatrix (I := I) g₁ x x q l)) *
              partialDeriv (E := E) m (gramBracket (I := I) g₁ x a b l)
                (extChartAt I x x)))) := by
  simp only [PDE.DeTurck.DeTurckLinearization.deTurckVFFirstOrderCorrDeriv0Raw]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) (congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂)
    (congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) ?_ ?_) ?_) ?_
  · refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) (congrArg Neg.neg
      (Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun p _ => ?_)))) rfl
    refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) ?_ ?_
    · rw [lieArm_chartInvGramOnE_center (I := I) g₁ x q b]
    · rw [lieArm_chartInvGramOnE_center (I := I) g₁ x a p]
  · refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) (congrArg Neg.neg
      (Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun p _ => ?_)))) ?_
    · rw [lieArm_chartInvGramOnE_center (I := I) g₁ x a p,
        lieArm_chartInvGramOnE_center (I := I) g₁ x q b]
    · exact lieCorr0_pd_christoffel_sub (I := I) g₁ g_bg x m a b k
  · refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl ?_
    exact lc0_chrCorr_center (I := I) g₁ x F a b k
  · refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂)
      (lieArm_chartInvGramOnE_center (I := I) g₁ x a b)
      (congrArg (fun t : ℝ => (1 / 2 : ℝ) * t)
        (Finset.sum_congr rfl (fun l _ => ?_)))
    refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂)
      (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) (congrArg Neg.neg
        (Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun p _ => ?_)))) rfl)
      (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) (congrArg Neg.neg
        (Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun p _ => ?_)))) rfl)
    · refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) ?_ ?_
      · rw [lieArm_chartInvGramOnE_center (I := I) g₁ x q l]
      · rw [lieArm_chartInvGramOnE_center (I := I) g₁ x k p]
    · rw [lieArm_chartInvGramOnE_center (I := I) g₁ x k p,
        lieArm_chartInvGramOnE_center (I := I) g₁ x q l]

private lemma lc0_O0_center (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (F : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → E → ℝ)
    (i j : Fin (Module.finrank ℝ E)) :
    PDE.DeTurck.DeTurckLinearization.order0PartRaw (I := I) g₁ g_bg x F i j
        (extChartAt I x x) =
      M0Abstract.O0F (lc0Ig (I := I) g₁ x) (lc0Cg (I := I) g₁ x) (lc0Ev (I := I) x F)
        (lc0Dg (I := I) g₁ x) (lc0Dig (I := I) g₁ x) (lc0Ga (I := I) g₀ x)
        (lc0Ga (I := I) g₁ x) (lc0Ga (I := I) g_bg x) (lc0Gb (I := I) g₁ x)
        (lc0Pd (I := I) x F) (lc0DDg (I := I) g₁ x) (lc0DGa (I := I) g₀ x)
        (lc0DGa (I := I) g₁ x) (lc0DGa (I := I) g_bg x) (lc0DGb (I := I) g₁ x) i j := by
  simp only [M0Abstract.O0F, M0Abstract.wcF, M0Abstract.d0F, M0Abstract.dvfbF,
    M0Abstract.chrCorrF, lc0Ig, lc0Cg, lc0Ev, lc0Dg, lc0Dig, lc0Ga,
    lc0DGa, lc0Gb, lc0DGb]
  simp only [PDE.DeTurck.DeTurckLinearization.order0PartRaw]
  refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂)
    (congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂)
      (congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂)
        (congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) ?_ ?_) ?_) ?_) ?_
  · refine Finset.sum_congr rfl (fun k _ => congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) ?_ rfl)
    exact lc0_wc_center (I := I) g₁ g_bg x F k
  · refine Finset.sum_congr rfl (fun k _ => congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl ?_)
    exact lieCorr0_pd_vfcomp_center (I := I) g₁ g_bg x i k
  · refine Finset.sum_congr rfl (fun k _ => congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl ?_)
    exact lieCorr0_pd_vfcomp_center (I := I) g₁ g_bg x j k
  · refine Finset.sum_congr rfl (fun k _ => congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) ?_ ?_)
    · exact lieArm_chartGramOnE_center (I := I) g₁ x k j
    · exact lc0_d0_center (I := I) g₁ g_bg x F i k
  · refine Finset.sum_congr rfl (fun k _ => congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) ?_ ?_)
    · exact lieArm_chartGramOnE_center (I := I) g₁ x i k
    · exact lc0_d0_center (I := I) g₁ g_bg x F j k

private lemma lc0_tail2 (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (gA : SmoothRiemannianMetric I M) (x : M) (i j : Fin (Module.finrank ℝ E)) :
    (∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) gA x x k₁ l *
          (arm2ReadoutCovDerivPair (I := I) (M := M) g₀
              (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![i, l, j, k₁]
            + arm2ReadoutCovDerivPair (I := I) (M := M) g₀
              (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![j, l, i, k₁]
            - arm2ReadoutCovDerivPair (I := I) (M := M) g₀
              (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![i, j, l, k₁])) =
      M0Abstract.t2F (lc0Ig (I := I) gA x) (lc0Ga (I := I) g₀ x)
        (lc0DGa (I := I) g₀ x)
        (lc0Ev (I := I) x (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x))
        (lc0Pd (I := I) x (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x))
        i j := by
  simp only [M0Abstract.t2F, M0Abstract.r4F, lc0Ig, lc0Ga, lc0DGa, lc0Ev, lc0Pd]
  refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ => ?_))
  refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl ?_
  rw [lieCorr0_R4_center (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i l j k₁,
    lieCorr0_R4_center (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j l i k₁,
    lieCorr0_R4_center (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i j l k₁]

private lemma lc0_tailpf (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (gA : SmoothRiemannianMetric I M) (x : M) (i j : Fin (Module.finrank ℝ E)) :
    (∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) gA x x k₁ l *
        ((-(∑ r : Fin (Module.finrank ℝ E),
            (chartChristoffel (I := I) g₀ x l j r (extChartAt I x x) *
                partialDeriv (E := E) i
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r k₁)
                  (extChartAt I x x)
              + chartChristoffel (I := I) g₀ x l k₁ r (extChartAt I x x) *
                partialDeriv (E := E) i
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j r)
                  (extChartAt I x x)
              + chartChristoffel (I := I) g₀ x i l r (extChartAt I x x) *
                partialDeriv (E := E) r
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j k₁)
                  (extChartAt I x x)
              + chartChristoffel (I := I) g₀ x i j r (extChartAt I x x) *
                partialDeriv (E := E) l
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r k₁)
                  (extChartAt I x x)
              + chartChristoffel (I := I) g₀ x i k₁ r (extChartAt I x x) *
                partialDeriv (E := E) l
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j r)
                  (extChartAt I x x))))
         + (-(∑ r : Fin (Module.finrank ℝ E),
            (chartChristoffel (I := I) g₀ x l i r (extChartAt I x x) *
                partialDeriv (E := E) j
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r k₁)
                  (extChartAt I x x)
              + chartChristoffel (I := I) g₀ x l k₁ r (extChartAt I x x) *
                partialDeriv (E := E) j
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i r)
                  (extChartAt I x x)
              + chartChristoffel (I := I) g₀ x j l r (extChartAt I x x) *
                partialDeriv (E := E) r
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k₁)
                  (extChartAt I x x)
              + chartChristoffel (I := I) g₀ x j i r (extChartAt I x x) *
                partialDeriv (E := E) l
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r k₁)
                  (extChartAt I x x)
              + chartChristoffel (I := I) g₀ x j k₁ r (extChartAt I x x) *
                partialDeriv (E := E) l
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i r)
                  (extChartAt I x x))))
         - (-(∑ r : Fin (Module.finrank ℝ E),
            (chartChristoffel (I := I) g₀ x j l r (extChartAt I x x) *
                partialDeriv (E := E) i
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r k₁)
                  (extChartAt I x x)
              + chartChristoffel (I := I) g₀ x j k₁ r (extChartAt I x x) *
                partialDeriv (E := E) i
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l r)
                  (extChartAt I x x)
              + chartChristoffel (I := I) g₀ x i j r (extChartAt I x x) *
                partialDeriv (E := E) r
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l k₁)
                  (extChartAt I x x)
              + chartChristoffel (I := I) g₀ x i l r (extChartAt I x x) *
                partialDeriv (E := E) j
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r k₁)
                  (extChartAt I x x)
              + chartChristoffel (I := I) g₀ x i k₁ r (extChartAt I x x) *
                partialDeriv (E := E) j
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l r)
                  (extChartAt I x x)))))) =
      M0Abstract.tpfF (lc0Ig (I := I) gA x) (lc0Ga (I := I) g₀ x)
        (lc0Pd (I := I) x (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x))
        i j := by
  simp only [M0Abstract.tpfF, M0Abstract.r4pfB, lc0Ig, lc0Ga, lc0Pd]

private lemma lc0_master_inst (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (F : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → E → ℝ)
    (hFsym : ∀ a b, F a b = F b a)
    (i j : Fin (Module.finrank ℝ E)) :
    M0Abstract.V0F (lc0Ig (I := I) g₁ x) (lc0Cg (I := I) g₁ x) (lc0Ev (I := I) x F)
        (lc0Dg (I := I) g₁ x) (lc0Dig (I := I) g₁ x) (lc0Ga (I := I) g₀ x)
        (lc0Ga (I := I) g₁ x) (lc0Ga (I := I) g_bg x) (lc0Gb (I := I) g₁ x)
        (lc0Pd (I := I) x F) (lc0DDg (I := I) g₁ x) (lc0DGa (I := I) g₀ x)
        (lc0DGa (I := I) g₁ x) (lc0DGa (I := I) g_bg x) (lc0DGb (I := I) g₁ x) i j
      + M0Abstract.insertB (lc0Ig (I := I) g₁ x) (lc0Dig (I := I) g₁ x)
        (lc0Ga (I := I) g₁ x) (lc0Ga (I := I) g₀ x) (lc0Ga (I := I) g_bg x)
        (lc0DGa (I := I) g₁ x) (lc0DGa (I := I) g₀ x) (lc0Ev (I := I) x F) i j
      + M0Abstract.vbB (lc0Ig (I := I) g₁ x) (lc0Cg (I := I) g₁ x)
        (lc0Ga (I := I) g₁ x) (lc0Ga (I := I) g₀ x) (lc0Ev (I := I) x F) i j
      + (2 : ℝ) * (M0Abstract.amixHalfB (lc0Ig (I := I) g₁ x) (lc0Cg (I := I) g₁ x)
          (lc0Ga (I := I) g₁ x) (lc0Ga (I := I) g₀ x) (lc0Ga (I := I) g_bg x)
          (lc0Ev (I := I) x F) i j
        + M0Abstract.amixHalfB (lc0Ig (I := I) g₁ x) (lc0Cg (I := I) g₁ x)
          (lc0Ga (I := I) g₁ x) (lc0Ga (I := I) g₀ x) (lc0Ga (I := I) g_bg x)
          (lc0Ev (I := I) x F) j i)
      + M0Abstract.p5B (lc0Ig (I := I) g₁ x) (lc0Ga (I := I) g₀ x)
        (lc0DGa (I := I) g₀ x) (lc0Ev (I := I) x F) i j
    = M0Abstract.O0F (lc0Ig (I := I) g₁ x) (lc0Cg (I := I) g₁ x) (lc0Ev (I := I) x F)
        (lc0Dg (I := I) g₁ x) (lc0Dig (I := I) g₁ x) (lc0Ga (I := I) g₀ x)
        (lc0Ga (I := I) g₁ x) (lc0Ga (I := I) g_bg x) (lc0Gb (I := I) g₁ x)
        (lc0Pd (I := I) x F) (lc0DDg (I := I) g₁ x) (lc0DGa (I := I) g₀ x)
        (lc0DGa (I := I) g₁ x) (lc0DGa (I := I) g_bg x) (lc0DGb (I := I) g₁ x) i j
      - (M0Abstract.t2F (lc0Ig (I := I) g₁ x) (lc0Ga (I := I) g₀ x)
          (lc0DGa (I := I) g₀ x) (lc0Ev (I := I) x F) (lc0Pd (I := I) x F) i j
        - M0Abstract.tpfF (lc0Ig (I := I) g₁ x) (lc0Ga (I := I) g₀ x)
          (lc0Pd (I := I) x F) i j)
      - M0Abstract.D1RF (lc0Ig (I := I) g₁ x) (lc0Cg (I := I) g₁ x) (lc0Ev (I := I) x F)
        (lc0Dg (I := I) g₁ x) (lc0Dig (I := I) g₁ x) (lc0Ga (I := I) g₀ x)
        (lc0Ga (I := I) g₁ x) (lc0Ga (I := I) g_bg x) (lc0Gb (I := I) g₁ x)
        (lc0Pd (I := I) x F) (lc0DDg (I := I) g₁ x) (lc0DGa (I := I) g₀ x)
        (lc0DGa (I := I) g₁ x) (lc0DGa (I := I) g_bg x) (lc0DGb (I := I) g₁ x) i j :=
  M0Abstract.m0_master _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun a b => lieArm_chartInvGramMatrix_symm (I := I) g₁ x a b)
    (fun a b => lieArm_chartGramMatrix_symm (I := I) g₁ x a b)
    (fun a b => congrFun (hFsym a b) (extChartAt I x x))
    (fun m a b => congrArg (fun G => partialDeriv (E := E) m G (extChartAt I x x))
      (funext fun y => chartGramOnE_symm (I := I) g₁ x a b y))
    (fun a b k => chartChristoffel_symm (I := I) g₀ x a b k (extChartAt I x x))
    (fun a b k => chartChristoffel_symm (I := I) g₁ x a b k (extChartAt I x x))
    (fun a b k => chartChristoffel_symm (I := I) g_bg x a b k (extChartAt I x x))
    (fun m a b k => congrArg (fun G => partialDeriv (E := E) m G (extChartAt I x x))
      (funext fun y => chartChristoffel_symm (I := I) g₀ x a b k y))
    (fun m a b k => congrArg (fun G => partialDeriv (E := E) m G (extChartAt I x x))
      (funext fun y => chartChristoffel_symm (I := I) g₁ x a b k y))
    (fun m a b k => congrArg (fun G => partialDeriv (E := E) m G (extChartAt I x x))
      (funext fun y => chartChristoffel_symm (I := I) g_bg x a b k y))
    (fun m k a b => congrArg
      (fun G => partialDeriv (E := E) m (partialDeriv (E := E) k G) (extChartAt I x x))
      (funext fun y => chartGramOnE_symm (I := I) g₁ x a b y))
    (fun m a b => congrArg (fun G => partialDeriv (E := E) m G (extChartAt I x x))
      (hFsym a b))
    (fun a b l => lc0_gramBracket_symm (I := I) g₁ x a b l (extChartAt I x x))
    (fun m a b l => congrArg (fun G => partialDeriv (E := E) m G (extChartAt I x x))
      (funext fun y => lc0_gramBracket_symm (I := I) g₁ x a b l y))
    (fun m a b => congrArg (fun G => partialDeriv (E := E) m G (extChartAt I x x))
      (funext fun y => DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramOnE_symm (I := I) g₁ x a b y))
    (fun l e => lieArm_gram_invGram_collapse (I := I) g₁ x l e)
    (fun a b k => lc0_hga1e (I := I) g₁ x a b k)
    (fun m a b k => lc0_hdga1e (I := I) g₁ x m a b k)
    (fun m a b => lc0_hdige (I := I) g₁ x m a b)
    (fun _a _b _l => rfl)
    (fun m a b l => lc0_hdgbe (I := I) g₁ x m a b l)
    i j

private lemma lc0_insert_piece (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) (i j : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel
        (deTurckLieRemainderEndoSlotInsertFib (I := I) g₀ g₁ g_bg x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (iteratedCovGrad (I := I) g₀ 0 2 0
              (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))).toSection x)
            (unitTensor (I := I) (M := M) x)))
        ![(chartModelBasis E) i, (chartModelBasis E) j] =
      M0Abstract.insertB (lc0Ig (I := I) g₁ x) (lc0Dig (I := I) g₁ x)
        (lc0Ga (I := I) g₁ x) (lc0Ga (I := I) g₀ x) (lc0Ga (I := I) g_bg x)
        (lc0DGa (I := I) g₁ x) (lc0DGa (I := I) g₀ x)
        (lc0Ev (I := I) x (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x))
        i j := by
  rw [lieCorr0InsertFib_basis_value (I := I) g₀ g₁ g_bg x _ i j]
  simp only [M0Abstract.insertB, lc0Ev]
  refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂)
    (Finset.sum_congr rfl (fun p _ => ?_)) (Finset.sum_congr rfl (fun p _ => ?_))
  · exact congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂)
      (lc0_nscalar_raw (I := I) g₀ g₁ g_bg x i p)
      (lc0_D0_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p j)
  · exact congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂)
      (lc0_nscalar_raw (I := I) g₀ g₁ g_bg x j p)
      (lc0_D0_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i p)

private lemma lc0_vb_piece (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g₁ : SmoothRiemannianMetric I M) (x : M) (i j : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel
        (lieCorr0VBFib (I := I) g₀ g₁ x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (iteratedCovGrad (I := I) g₀ 0 2 0
              (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))).toSection x)
            (unitTensor (I := I) (M := M) x)))
        ![(chartModelBasis E) i, (chartModelBasis E) j] =
      M0Abstract.vbB (lc0Ig (I := I) g₁ x) (lc0Cg (I := I) g₁ x)
        (lc0Ga (I := I) g₁ x) (lc0Ga (I := I) g₀ x)
        (lc0Ev (I := I) x (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x))
        i j := by
  rw [lieCorr0VBFib_basis_value (I := I) g₀ g₁ x _ i j]
  simp only [M0Abstract.vbB, lc0Ig, lc0Cg, lc0Ga, lc0Ev]
  refine congrArg (fun t : ℝ => 2 * t)
    (Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_)))
  refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
    (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
      (Finset.sum_congr rfl (fun ρ _ => ?_)))
  exact congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂)
    (lc0_vfcomp_center (I := I) g₁ g₀ x ρ)
    (lc0_D0_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x ρ k)

private lemma lc0_amixhalf_piece (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) (i j : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel
        (lieCorr0AMixHalfFib (I := I) g₀ g₁ g_bg x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (iteratedCovGrad (I := I) g₀ 0 2 0
              (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))).toSection x)
            (unitTensor (I := I) (M := M) x)))
        ![(chartModelBasis E) i, (chartModelBasis E) j] =
      M0Abstract.amixHalfB (lc0Ig (I := I) g₁ x) (lc0Cg (I := I) g₁ x)
        (lc0Ga (I := I) g₁ x) (lc0Ga (I := I) g₀ x) (lc0Ga (I := I) g_bg x)
        (lc0Ev (I := I) x (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x))
        i j := by
  rw [lieCorr0AMixHalfFib_basis_value (I := I) g₀ g₁ g_bg x _ i j]
  simp only [M0Abstract.amixHalfB, lc0Ig, lc0Cg, lc0Ga, lc0Ev]
  refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun ml _ => ?_))
  refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
    (Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun al _ => ?_)))
  refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
    (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂)
      (Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun kl _ => ?_))) rfl)
  refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
    (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂)
      (lc0_D0_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x k ml) rfl)

private lemma lc0_riem_piece (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g₁ : SmoothRiemannianMetric I M) (x : M) (i j : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel
        (deTurckLieRemainderCurvatureFib (I := I) g₀ g₁ x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (iteratedCovGrad (I := I) g₀ 0 2 0
              (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))).toSection x)
            (unitTensor (I := I) (M := M) x)))
        ![(chartModelBasis E) i, (chartModelBasis E) j] =
      M0Abstract.p5B (lc0Ig (I := I) g₁ x) (lc0Ga (I := I) g₀ x)
        (lc0DGa (I := I) g₀ x)
        (lc0Ev (I := I) x (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x))
        i j := by
  rw [lieCorr0RiemFib_basis_value (I := I) g₀ g₁ x _ i j]
  simp only [M0Abstract.p5B, M0Abstract.rchB, lc0Ig, lc0Ga, lc0DGa, lc0Ev]
  refine congrArg Neg.neg
    (Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun ml _ => ?_)))
  refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
    (Finset.sum_congr rfl (fun ρ _ => ?_))
  refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) ?_
    (lc0_D0_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x ρ m)
  rfl

private lemma lc0_committed (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) (s : ℝ) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
          (deTurckLieCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
          (iteratedCovGrad (I := I) g₀ 0 2 0 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x
        ![((chartModelBasis E) i : TangentSpace I x), ((chartModelBasis E) j : TangentSpace I x)] =
      M0Abstract.V0F (lc0Ig (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x)
        (lc0Cg (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x)
        (lc0Ev (I := I) x (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x))
        (lc0Dg (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x)
        (lc0Dig (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x)
        (lc0Ga (I := I) g₀ x)
        (lc0Ga (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x)
        (lc0Ga (I := I) g_bg x)
        (lc0Gb (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x)
        (lc0Pd (I := I) x (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x))
        (lc0DDg (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x)
        (lc0DGa (I := I) g₀ x)
        (lc0DGa (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x)
        (lc0DGa (I := I) g_bg x)
        (lc0DGb (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x) i j := by
  refine (lieCorr0_committed_value (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' g_bg s x i j).trans ?_
  simp only [M0Abstract.V0F, M0Abstract.covAF, M0Abstract.covWF, M0Abstract.dvfbF,
    M0Abstract.vfbF, lc0Ig, lc0Cg, lc0Ev, lc0Dig, lc0Ga, lc0DGa, 
]
  refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) (congrArg Neg.neg
    (Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun ml _ => ?_))))
    (congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂)
      (Finset.sum_congr rfl (fun p _ => ?_))
      (Finset.sum_congr rfl (fun p _ => ?_)))
  · refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
      (Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun kl _ => ?_)))
    refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
      (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂)
        (congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂)
          (Finset.sum_congr rfl (fun p _ => ?_))
          (Finset.sum_congr rfl (fun p _ => ?_))) rfl)
    · exact congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂)
        (lc0_covASc_raw (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i m k p)
        rfl
    · exact congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂)
        (lc0_covASc_raw (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x j m k p)
        rfl
  · exact congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂)
      (lc0_covWSc_raw (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i p) rfl
  · exact congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂)
      (lc0_covWSc_raw (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x j p) rfl

private lemma lc0_d1r (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) (s : ℝ) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ((∑ w : Fin (Module.finrank ℝ E), PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x w (extChartAt I x x) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![w, i, j])
      + ((∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![i, m, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁))))
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![i, m, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q j))))
        - (∑ w : Fin (Module.finrank ℝ E), (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b * (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b w (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x a b w (extChartAt I x x))) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![i, j, w])
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![m, j, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁))))
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![p, q, k₁]))
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![m, j, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))))
      + ((∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![j, m, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁))))
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![j, m, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q i))))
        - (∑ w : Fin (Module.finrank ℝ E), (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b * (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b w (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x a b w (extChartAt I x x))) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![j, i, w])
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![m, i, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁))))
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i j q (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![p, q, k₁]))
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![m, i, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))))
      + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![q, p, k₁]))) =
      M0Abstract.D1RF (lc0Ig (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x) (lc0Cg (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x)
        (lc0Ev (I := I) x (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x))
        (lc0Dg (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x) (lc0Dig (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x)
        (lc0Ga (I := I) g₀ x) (lc0Ga (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x) (lc0Ga (I := I) g_bg x)
        (lc0Gb (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x)
        (lc0Pd (I := I) x (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x))
        (lc0DDg (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x) (lc0DGa (I := I) g₀ x)
        (lc0DGa (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x) (lc0DGa (I := I) g_bg x)
        (lc0DGb (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x) i j := by
  simp only [M0Abstract.D1RF, M0Abstract.vfbF, M0Abstract.r3B, lc0Ig, lc0Cg, lc0Ev,
    lc0Ga]
  refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂)
    (congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂)
      (congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) ?_
        (congrArg₂ (fun t₁ t₂ : ℝ => t₁ - t₂)
          (congrArg₂ (fun t₁ t₂ : ℝ => t₁ - t₂)
            (congrArg₂ (fun t₁ t₂ : ℝ => t₁ - t₂)
              (congrArg₂ (fun t₁ t₂ : ℝ => t₁ - t₂)
                (congrArg₂ (fun t₁ t₂ : ℝ => t₁ - t₂) ?_ ?_) ?_) ?_) ?_) ?_))
      (congrArg₂ (fun t₁ t₂ : ℝ => t₁ - t₂)
        (congrArg₂ (fun t₁ t₂ : ℝ => t₁ - t₂)
          (congrArg₂ (fun t₁ t₂ : ℝ => t₁ - t₂)
            (congrArg₂ (fun t₁ t₂ : ℝ => t₁ - t₂)
              (congrArg₂ (fun t₁ t₂ : ℝ => t₁ - t₂) ?_ ?_) ?_) ?_) ?_) ?_)) ?_
  · refine Finset.sum_congr rfl (fun w _ => ?_)
    exact congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂)
      (lc0_vfcomp_center (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x w)
      (lieCorr0_arm1Readout_center (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x w i j)
  · refine Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun l1 _ => Finset.sum_congr rfl (fun m _ => ?_))))
    refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
      (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
        (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂)
          (lieCorr0_arm1Readout_center (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i m p) rfl))
  · refine Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun l1 _ => Finset.sum_congr rfl (fun m _ => ?_))))
    refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
      (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
        (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂)
          (lieCorr0_arm1Readout_center (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i m p) rfl))
  · refine Finset.sum_congr rfl (fun w _ => ?_)
    exact congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
      (lieCorr0_arm1Readout_center (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i j w)
  · refine Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun l1 _ => Finset.sum_congr rfl (fun m _ => ?_))))
    refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
      (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
        (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂)
          (lieCorr0_arm1Readout_center (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x m j p) rfl))
  · refine Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun p _ => ?_))
    refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
      (Finset.sum_congr rfl (fun q _ => ?_))
    exact congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
      (lieCorr0_arm1Readout_center (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p q k1)
  · refine Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun l1 _ => Finset.sum_congr rfl (fun m _ => ?_))))
    refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
      (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
        (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂)
          (lieCorr0_arm1Readout_center (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x m j p) rfl))
  · refine Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun l1 _ => Finset.sum_congr rfl (fun m _ => ?_))))
    refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
      (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
        (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂)
          (lieCorr0_arm1Readout_center (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j m p) rfl))
  · refine Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun l1 _ => Finset.sum_congr rfl (fun m _ => ?_))))
    refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
      (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
        (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂)
          (lieCorr0_arm1Readout_center (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j m p) rfl))
  · refine Finset.sum_congr rfl (fun w _ => ?_)
    exact congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
      (lieCorr0_arm1Readout_center (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j i w)
  · refine Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun l1 _ => Finset.sum_congr rfl (fun m _ => ?_))))
    refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
      (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
        (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂)
          (lieCorr0_arm1Readout_center (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x m i p) rfl))
  · refine Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun p _ => ?_))
    refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
      (Finset.sum_congr rfl (fun q _ => ?_))
    exact congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
      (lieCorr0_arm1Readout_center (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p q k1)
  · refine Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun l1 _ => Finset.sum_congr rfl (fun m _ => ?_))))
    refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
      (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
        (congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂)
          (lieCorr0_arm1Readout_center (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x m i p) rfl))
  · refine Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun p _ => ?_))
    refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
      (Finset.sum_congr rfl (fun q _ => ?_))
    exact congrArg₂ (fun t₁ t₂ : ℝ => t₁ * t₂) rfl
      (lieCorr0_arm1Readout_center (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x q p k1)

private lemma lc0_amix_piece (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) (i j : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel
        (lieCorr0AMixFib (I := I) g₀ g₁ g_bg x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (iteratedCovGrad (I := I) g₀ 0 2 0
              (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))).toSection x)
            (unitTensor (I := I) (M := M) x)))
        ![(chartModelBasis E) i, (chartModelBasis E) j] =
      (2 : ℝ) * (M0Abstract.amixHalfB (lc0Ig (I := I) g₁ x) (lc0Cg (I := I) g₁ x)
          (lc0Ga (I := I) g₁ x) (lc0Ga (I := I) g₀ x) (lc0Ga (I := I) g_bg x)
          (lc0Ev (I := I) x (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x)) i j
        + M0Abstract.amixHalfB (lc0Ig (I := I) g₁ x) (lc0Cg (I := I) g₁ x)
          (lc0Ga (I := I) g₁ x) (lc0Ga (I := I) g₀ x) (lc0Ga (I := I) g_bg x)
          (lc0Ev (I := I) x (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x)) j i) := by
  rw [lieCorr0AMixFib_basis_value (I := I) g₀ g₁ g_bg x _ i j]
  exact congrArg (fun t : ℝ => 2 * t)
    (congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂)
      (lc0_amixhalf_piece (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' g₁ g_bg x i j)
      (lc0_amixhalf_piece (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' g₁ g_bg x j i))

private lemma lc0_totalfib_split (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) (i j : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel (deTurckLieRemainderTotalFib (I := I) g₀ g₁ g_bg x D)
        ![(chartModelBasis E) i, (chartModelBasis E) j] =
      Tensor0SSpace.toModel (deTurckLieRemainderEndoSlotInsertFib (I := I) g₀ g₁ g_bg x D)
          ![(chartModelBasis E) i, (chartModelBasis E) j]
        + Tensor0SSpace.toModel (lieCorr0VBFib (I := I) g₀ g₁ x D)
          ![(chartModelBasis E) i, (chartModelBasis E) j]
        + Tensor0SSpace.toModel (lieCorr0AMixFib (I := I) g₀ g₁ g_bg x D)
          ![(chartModelBasis E) i, (chartModelBasis E) j]
        + Tensor0SSpace.toModel (deTurckLieRemainderCurvatureFib (I := I) g₀ g₁ x D)
          ![(chartModelBasis E) i, (chartModelBasis E) j] := by
  rw [deTurckLieRemainderTotalFib]
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.add_apply]
  rw [Tensor0SSpace.toModel_add, Tensor0SSpace.toModel_add, Tensor0SSpace.toModel_add]
  rw [ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.add_apply,
    ContinuousMultilinearMap.add_apply]

set_option maxHeartbeats 6400000 in
private lemma lieCorr0_value_eq_order0Raw_sub_tails (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) (s : ℝ) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
          (deTurckLieCoeffField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg +
            deTurckLieRemainderField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
          (iteratedCovGrad (I := I) g₀ 0 2 0 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x
        ![((chartModelBasis E) i : TangentSpace I x), ((chartModelBasis E) j : TangentSpace I x)] =
      PDE.DeTurck.DeTurckLinearization.order0PartRaw (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x
          (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) i j (extChartAt I x x)
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ l *
              (arm2ReadoutCovDerivPair (I := I) (M := M) g₀
                  (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![i, l, j, k₁]
                + arm2ReadoutCovDerivPair (I := I) (M := M) g₀
                  (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![j, l, i, k₁]
                - arm2ReadoutCovDerivPair (I := I) (M := M) g₀
                  (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![i, j, l, k₁]))
        - (((∑ w : Fin (Module.finrank ℝ E), PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x w (extChartAt I x x) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![w, i, j])
      + ((∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![i, m, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁))))
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![i, m, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q j))))
        - (∑ w : Fin (Module.finrank ℝ E), (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b * (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b w (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x a b w (extChartAt I x x))) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![i, j, w])
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![m, j, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁))))
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![p, q, k₁]))
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![m, j, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))))
      + ((∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![j, m, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁))))
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![j, m, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q i))))
        - (∑ w : Fin (Module.finrank ℝ E), (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b * (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b w (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x a b w (extChartAt I x x))) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![j, i, w])
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![m, i, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁))))
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i j q (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![p, q, k₁]))
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![m, i, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))))
      + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ (T - T')) x ![q, p, k₁])))
          - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ l *
        ((-(∑ r : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l j r (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) i (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r k₁) (extChartAt I x x)
          + DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l k₁ r (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) i (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j r) (extChartAt I x x)
          + DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i l r (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) r (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j k₁) (extChartAt I x x)
          + DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i j r (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) l (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r k₁) (extChartAt I x x)
          + DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i k₁ r (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) l (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j r) (extChartAt I x x))))
         + (-(∑ r : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l i r (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) j (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r k₁) (extChartAt I x x)
          + DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l k₁ r (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) j (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i r) (extChartAt I x x)
          + DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j l r (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) r (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k₁) (extChartAt I x x)
          + DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i r (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) l (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r k₁) (extChartAt I x x)
          + DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j k₁ r (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) l (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i r) (extChartAt I x x))))
         - (-(∑ r : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j l r (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) i (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r k₁) (extChartAt I x x)
          + DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j k₁ r (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) i (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l r) (extChartAt I x x)
          + DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i j r (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) r (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l k₁) (extChartAt I x x)
          + DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i l r (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) j (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r k₁) (extChartAt I x x)
          + DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i k₁ r (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) j (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l r) (extChartAt I x x))))))) := by
  refine (lieCorr0_phi0b_value_split (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' g_bg s x
    i j).trans ?_
  rw [lc0_totalfib_split (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x _ i j]
  rw [lc0_committed (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' g_bg s x i j]
  rw [lc0_insert_piece (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i j]
  rw [lc0_vb_piece (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j]
  rw [lc0_amix_piece (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i j]
  rw [lc0_riem_piece (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j]
  rw [lc0_O0_center (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x
    (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) i j]
  rw [lc0_tail2 (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j]
  rw [lc0_d1r (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' g_bg s x i j]
  rw [lc0_tailpf (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j]
  linear_combination lc0_master_inst (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x
    (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x)
    (fun a b => lieArm_realizedGramDeriv_symm (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b)
    i j

end LieCorr0MasterValue

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
lemma lieArm_chartSlope_center_value_eq_threeArm
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (x : M) (i j : Fin (Module.finrank ℝ E)) :
    lieDeTurckChartSlope (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' g_bg x i j s
        (extChartAt I x x) =
      unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
            (deTurckLieCoeffField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
              + deTurckLieRemainderField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
            (iteratedCovGrad (I := I) g₀ 0 2 0 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))
          + operatorFieldApply (I := I) (M := M) g₀ 3 2
            (deTurckLieArm1Coeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
            (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))
          + operatorFieldApply (I := I) (M := M) g₀ 4 2
            (deTurckLieArm2PrincipalCoeff (I := I) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x
        ![(chartModelBasis E) i, (chartModelBasis E) j] := by
  classical
  have hy : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E) :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x (mem_extChartAt_target x)
  have hsplit := lieDeTurckChartSlope_eq_orderSplit (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' g_bg x i j s hy
  have h0 := lieCorr0_value_eq_order0Raw_sub_tails (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' g_bg s x i j
  have h1 := lieArm_arm1_value_eq_order1Raw_add_tail (I := I) g₀ g_bg T T'
    hδ_lt hδ hδ'_lt hδ' s x i j
  have h2 := lieArm_arm2_value_eq_principal_add_tail (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i j
  refine hsplit.trans ?_
  rw [unitModel_add_local (I := I) g₀ 2 _ _ x, unitModel_add_local (I := I) g₀ 2 _ _ x,
    ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.add_apply]
  linear_combination -h0 - h1 - h2

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem realizedDeTurckLie_threeArm_symmAbsorbed_perm_data
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ (σ'₀ : Equiv.Perm (Fin 2)) (σ'₁ : Equiv.Perm (Fin 3)) (σ'₂ : Equiv.Perm (Fin 4)),
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2
        (fun s => symmAbsorbedCoeff (I := I) (M := M) g₀ 0
          (deTurckLieCoeffField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
            + deTurckLieRemainderField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) σ'₀)
        (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3
        (fun s => symmAbsorbedCoeff (I := I) (M := M) g₀ 1
          (deTurckLieArm1Coeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) σ'₁)
        (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4
        (fun s => symmAbsorbedCoeff (I := I) (M := M) g₀ 2
          (deTurckLieArm2PrincipalCoeff (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) σ'₂)
        (δ := δ) (δ' := δ') ∧
      ∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 →
        ∀ (x : M) (v : Fin 2 → TangentSpace I x),
          (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) j *
              deriv (fun s : ℝ =>
                DeTurckCoefficients.chartLieDeTurckComp (I := I)
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i j (extChartAt I x x)) s) =
            unitModel (I := I) (M := M) g₀ 2
              (operatorFieldApply (I := I) (M := M) g₀ 2 2
                  (symmAbsorbedCoeff (I := I) (M := M) g₀ 0
                    (deTurckLieCoeffField (I := I) (M := M) g₀
                        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
                      + deTurckLieRemainderField (I := I) (M := M) g₀
                        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) σ'₀)
                  (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
                + operatorFieldApply (I := I) (M := M) g₀ 3 2
                  (symmAbsorbedCoeff (I := I) (M := M) g₀ 1
                    (deTurckLieArm1Coeff (I := I) (M := M) g₀
                      (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) σ'₁)
                  (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
                + operatorFieldApply (I := I) (M := M) g₀ 4 2
                  (symmAbsorbedCoeff (I := I) (M := M) g₀ 2
                    (deTurckLieArm2PrincipalCoeff (I := I) g₀
                      (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) σ'₂)
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  classical
  obtain ⟨σ'₀, hσ'₀⟩ :=
    exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) (T - T') 0
  obtain ⟨σ'₁, hσ'₁⟩ :=
    exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) (T - T') 1
  obtain ⟨σ'₂, hσ'₂⟩ :=
    exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) (T - T') 2
  refine ⟨σ'₀, σ'₁, σ'₂,
    lieArm_hjAbsorb (I := I) g₀ 0 _ σ'₀
      (deTurckLieCoeffField_add_deTurckLieRemainderField_realizedFam_jointSmooth (I := I) g₀ T T' hδ hδ' g_bg),
    lieArm_hjAbsorb (I := I) g₀ 1 _ σ'₁
      (deTurckLieArm1Coeff_realizedFam_jointSmooth (I := I) g₀ T T' hδ hδ' g_bg),
    lieArm_hjAbsorb (I := I) g₀ 2 _ σ'₂
      (deTurckLieArm2PrincipalCoeff_realizedFam_jointSmooth (I := I) g₀ T T' hδ hδ' g_bg),
    ?_⟩
  intro s hs x v
  have hcomp : ∀ i j : Fin (Module.finrank ℝ E),
      deriv (fun s : ℝ =>
        DeTurckCoefficients.chartLieDeTurckComp (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i j (extChartAt I x x)) s =
      unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
            (deTurckLieCoeffField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
              + deTurckLieRemainderField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
            (iteratedCovGrad (I := I) g₀ 0 2 0 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))
          + operatorFieldApply (I := I) (M := M) g₀ 3 2
            (deTurckLieArm1Coeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
            (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))
          + operatorFieldApply (I := I) (M := M) g₀ 4 2
            (deTurckLieArm2PrincipalCoeff (I := I) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x
        ![(chartModelBasis E) i, (chartModelBasis E) j] := by
    intro i j
    rw [deriv_realizedFam_chartLieDeTurckComp_eq_chartSlope (I := I) g₀ T T'
      hδ_lt hδ hδ'_lt hδ' g_bg x i j hs]
    exact lieArm_chartSlope_center_value_eq_threeArm (I := I) g₀ g_bg T T'
      hδ_lt hδ hδ'_lt hδ' s x i j
  set Wbase : SmoothCcTensor g₀ 0 2 :=
    operatorFieldApply (I := I) (M := M) g₀ 2 2
        (deTurckLieCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
          + deTurckLieRemainderField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
        (iteratedCovGrad (I := I) g₀ 0 2 0 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))
      + operatorFieldApply (I := I) (M := M) g₀ 3 2
        (deTurckLieArm1Coeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
        (iteratedCovGrad (I := I) g₀ 0 2 1 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))
      + operatorFieldApply (I := I) (M := M) g₀ 4 2
        (deTurckLieArm2PrincipalCoeff (I := I) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
        (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) with hWbase
  have hexpand : (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) j *
        deriv (fun s : ℝ =>
          DeTurckCoefficients.chartLieDeTurckComp (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i j (extChartAt I x x)) s) =
      unitModel (I := I) (M := M) g₀ 2 Wbase x v := by
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
  rw [hexpand]
  have habs0 := symmAbsorbedCoeff_appCc_eq (I := I) (M := M) g₀ 0 (T - T')
    (deTurckLieCoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
      + deTurckLieRemainderField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) σ'₀ hσ'₀ x v
  have habs1 := symmAbsorbedCoeff_appCc_eq (I := I) (M := M) g₀ 1 (T - T')
    (deTurckLieArm1Coeff (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) σ'₁ hσ'₁ x v
  have habs2 := symmAbsorbedCoeff_appCc_eq (I := I) (M := M) g₀ 2 (T - T')
    (deTurckLieArm2PrincipalCoeff (I := I) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) σ'₂ hσ'₂ x v
  rw [hWbase]
  rw [unitModel_add_local (I := I) g₀ 2 _ _ x, unitModel_add_local (I := I) g₀ 2 _ _ x,
    unitModel_add_local (I := I) g₀ 2 _ _ x, unitModel_add_local (I := I) g₀ 2 _ _ x,
    ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.add_apply,
    ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.add_apply]
  rw [habs0, habs1, habs2]

theorem realizedDeTurckLie_threeArm_covariant_identity
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ (Φ₀L : ℝ → SmoothCcTensor g₀ 2 2) (Φ₁L : ℝ → SmoothCcTensor g₀ 3 2)
      (Φ₂L : ℝ → SmoothCcTensor g₀ 4 2),
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 Φ₀L (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3 Φ₁L (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4 Φ₂L (δ := δ) (δ' := δ') ∧
      ∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 →
        ∀ (x : M) (v : Fin 2 → TangentSpace I x),
          (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) j *
              deriv (fun s : ℝ =>
                DeTurckCoefficients.chartLieDeTurckComp (I := I)
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x i j (extChartAt I x x)) s) =
            unitModel (I := I) (M := M) g₀ 2
              (operatorFieldApply (I := I) (M := M) g₀ 2 2 (Φ₀L s)
                  (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
                + operatorFieldApply (I := I) (M := M) g₀ 3 2 (Φ₁L s)
                  (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
                + operatorFieldApply (I := I) (M := M) g₀ 4 2 (Φ₂L s)
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  classical
  obtain ⟨_, _, _, hj0, hj1, hj2, hident⟩ :=
    realizedDeTurckLie_threeArm_symmAbsorbed_perm_data (I := I) g₀ g_bg T T'
      hδ_lt hδ hδ'_lt hδ'
  exact ⟨_, _, _, hj0, hj1, hj2, hident⟩

end

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
