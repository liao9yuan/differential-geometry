import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitz.Base
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitz.O1Alg

/-!
# Lie-correction joint smoothness, chart evaluation and value layer

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

section

open DifferentialGeometry.Integral.DivergenceTheorem (chartInvGramMatrix)

open DifferentialGeometry.PDE.DeTurck.RicciLinearization (lieDeTurckChartSlope deriv_realizedFam_chartLieDeTurckComp_eq_chartSlope lieDeTurckChartSlope_eq_orderSplit contMDiffOn_clm_section_of_pointwise_jointMR)

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck (cometricLmodel)

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (reindexCoeffGen reindexCoeffFibGen reindexCoeffFibGen_apply reindexCoeffGen_toSection deTurckLieArm2PrincipalCoeff deTurckLieArm1Coeff deTurckLieCoeffField deTurckLieArm2PrincipalCoeff_realizedFam_jointSmooth deTurckLieArm1Coeff_realizedFam_jointSmooth deTurckLieCoeffField_realizedFam_jointSmooth deTurckLieArm2PrincipalCoeff_appCc_eq cometricFinBasisTrace_eq_chartInvGram_bilin unitModel4SlotBilin unitModel4SlotBilin_apply)

set_option linter.style.setOption false

set_option backward.isDefEq.respectTransparency false

open DifferentialGeometry.PDE.DeTurck.RicciLinearization (realizedGramDeriv)

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (domDomCongrSection_unitModel unitModel_basisChart_eq_tensorChartComponentRaw tensorChartComponentRaw tensorChartComponentRaw_add tensorChartComponentRaw_smul arm2ReadoutCovDerivPair arm1ReadoutCovDeriv iteratedCovGrad2_chartComponent_readout iteratedCovGrad1_chartComponent_readout partialDeriv2_realizedGramDeriv_eq_half_sum_euclidPartial2 partialDeriv_realizedGramDeriv_eq_half_sum_euclidPartial realizedGramDeriv_eventuallyEq_symm_scalarOnE_raw eP2_swap covDerivLowerOrderTerm02_center_eq covDerivLowerOrderTerm03_center_eq euclidPartial2_chartPushedRaw_eq_partialDeriv2_scalarOnE partialDeriv_scalarOnE_eq_euclidPartial_local toEuclidean_extChartAt_mem_chartTargetEuclid symm_toEuclidean_symm_toEuclidean_extChartAt)

open DifferentialGeometry.Analysis.Sobolev.Chart (chartPushedRaw chartPushedRaw_apply_of_mem chartTargetEuclid chartTargetEuclid_isOpen)

open DifferentialGeometry.Analysis.Laplacian.TensorRegularity (tensorChartComponentRaw_eq_chartFrame chartFrameBasisModel covDerivLowerOrderTerm euclidPartial euclidPartial_def covDerivComponent_lowerOrder_contDiffOn euclidPartial_chartPushedRaw_contDiffOn chartPushedRaw_tensorChartComponentRaw_contDiffOn)

open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization (chartDeTurckCorrPrincipalSymbolExprRaw chartDeTurckCorrHessBlockRaw)

open DifferentialGeometry.Integral.DivergenceTheorem (partialDeriv chartGramOnE chartInvGramOnE)

open DifferentialGeometry.Integral.Measure (chartGramMatrix)

open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization (chartDeTurckCorrPrincipalSymbolExprRaw chartDeTurckCorrHessBlockRaw)

open DifferentialGeometry.Integral.DivergenceTheorem (partialDeriv chartGramOnE chartInvGramOnE)

open DifferentialGeometry.Integral.Measure (chartGramMatrix)

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (deTurckLieArm2PrincipalCoeff deTurckLieArm2PrincipalCoeff_appCc_eq cometricFinBasisTrace_eq_chartInvGram_bilin unitModel4SlotBilin unitModel4SlotBilin_apply)

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (unitModel3SlotBilin metricConnDiffLoweredTrilin metricConnDiffLoweredTrilin_apply deTurckLieArm1Coeff deTurckLieArm1Coeff_appCc_eq)

namespace DeTurckRemainderTameLipschitz

set_option linter.unusedSectionVars false in
lemma lieArm_chartGramMatrix_symm (g : SmoothRiemannianMetric I M) (x : M)
    (a b : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) g x x a b
    = DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) g x x b a := by
  rw [DifferentialGeometry.Integral.Measure.chartGramMatrix_apply,
    DifferentialGeometry.Integral.Measure.chartGramMatrix_apply]
  exact g.symm _ _ _

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
lemma lieArm_realizedGramDeriv_symm (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (a b : Fin (Module.finrank ℝ E)) :
    realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b
    = realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x b a := by
  funext y
  show DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I)
      (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x a b y
    - DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I)
      (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x a b y
    = DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I)
      (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x b a y
    - DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE (I := I)
      (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x b a y
  rw [DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE_symm (I := I) _ x a b,
    DifferentialGeometry.Integral.DivergenceTheorem.chartGramOnE_symm (I := I) _ x a b]

end DeTurckRemainderTameLipschitz

set_option linter.unusedSectionVars false in
private lemma lieArm_chartChristoffel_center (g : SmoothRiemannianMetric I M) (x : M)
    (a b k : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g x a b k (extChartAt I x x)
    = (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x k l *
          DeTurckCoefficients.gramBracket (I := I) g x a b l (extChartAt I x x) := by
  rw [DeTurckCoefficients.chartChristoffel_eq_sum_invGramOnE_bracket (I := I) g x a b k (extChartAt I x x)]
  refine congrArg (HMul.hMul (1 / 2 : ℝ)) (Finset.sum_congr rfl (fun l _ => ?_))
  rw [lieArm_chartInvGramOnE_center (I := I) g x k l]

set_option linter.unusedSectionVars false in
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

set_option linter.unusedSectionVars false in
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
set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
private lemma lieArm_o1raw_center_eq (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
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

namespace DeTurckRemainderTameLipschitz

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
lemma lieArm_arm1_value_eq_order1Raw_add_tail (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (x : M) (i j : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 3 2
          (deTurckLieArm1Coeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
          (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T')))) x
        ![chartModelBasis E i, chartModelBasis E j]
    = PDE.DeTurck.DeTurckLinearization.lieDeTurckOrder1Raw (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x
        (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) i j (extChartAt I x x)
      + (((∑ w : Fin (Module.finrank ℝ E), PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x w (extChartAt I x x) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![w, i, j])
      + ((∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![i, m, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁))))
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![i, m, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q j))))
        - (∑ w : Fin (Module.finrank ℝ E), (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b * (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b w (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x a b w (extChartAt I x x))) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![i, j, w])
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![m, j, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁))))
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![p, q, k₁]))
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![m, j, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))))
      + ((∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![j, m, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁))))
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![j, m, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q i))))
        - (∑ w : Fin (Module.finrank ℝ E), (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b * (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b w (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x a b w (extChartAt I x x))) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![j, i, w])
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![m, i, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁))))
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i j q (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![p, q, k₁]))
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![m, i, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))))
      + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![q, p, k₁])))
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
  have hs1 : (∑ w : Fin (Module.finrank ℝ E), PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x w (extChartAt I x x) * unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E w, chartModelBasis E i, chartModelBasis E j]) = (∑ w : Fin (Module.finrank ℝ E), PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x w (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) w (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i j) (extChartAt I x x)) + (∑ w : Fin (Module.finrank ℝ E), PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x w (extChartAt I x x) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![w, i, j]) := by
    rw [show (∑ w : Fin (Module.finrank ℝ E), PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x w (extChartAt I x x) * unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E w, chartModelBasis E i, chartModelBasis E j]) = ∑ w : Fin (Module.finrank ℝ E), (PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x w (extChartAt I x x) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) w (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i j) (extChartAt I x x) + PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x w (extChartAt I x x) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![w, i, j]) from
      Finset.sum_congr rfl (fun w _ => by
        rw [lieArm_U3_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x w i j]
        ring)]
    simp only [Finset.sum_add_distrib]
  have hs2 : (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E i, chartModelBasis E m, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) = (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) i (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x m p) (extChartAt I x x) *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![i, m, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) := by
    rw [show (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E i, chartModelBasis E m, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁))))
        = ∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) i (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x m p) (extChartAt I x x) * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))
           + chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![i, m, p] * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) from
      Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => by
          rw [lieArm_U3_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i m p]
          ring))))]
    simp only [Finset.sum_add_distrib]
  have hs3 : (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E i, chartModelBasis E m, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q j)))) = (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) i (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x m p) (extChartAt I x x) *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q j)))) + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![i, m, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q j)))) := by
    rw [show (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E i, chartModelBasis E m, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q j))))
        = ∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) i (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x m p) (extChartAt I x x) * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q j)))
           + chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![i, m, p] * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q j)))) from
      Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => by
          rw [lieArm_U3_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i m p]
          ring))))]
    simp only [Finset.sum_add_distrib]
  have hs4 : (∑ w : Fin (Module.finrank ℝ E), PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x w (extChartAt I x x) * unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E i, chartModelBasis E j, chartModelBasis E w]) = (∑ w : Fin (Module.finrank ℝ E), (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b * (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b w (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x a b w (extChartAt I x x))) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) i (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j w) (extChartAt I x x)) + (∑ w : Fin (Module.finrank ℝ E), (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b * (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b w (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x a b w (extChartAt I x x))) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![i, j, w]) := by
    rw [show (∑ w : Fin (Module.finrank ℝ E), PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x w (extChartAt I x x) * unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E i, chartModelBasis E j, chartModelBasis E w]) = ∑ w : Fin (Module.finrank ℝ E), ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b * (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b w (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x a b w (extChartAt I x x))) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) i (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j w) (extChartAt I x x) + (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b * (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b w (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x a b w (extChartAt I x x))) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![i, j, w]) from
      Finset.sum_congr rfl (fun w _ => by
        rw [lieArm_U3_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i j w,
          lieArm_chartDeTurckVFComp_center (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x w]
        ring)]
    simp only [Finset.sum_add_distrib]
  have hs5 : (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E m, chartModelBasis E j, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁)))) = (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j p) (extChartAt I x x) *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁)))) + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![m, j, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁)))) := by
    rw [show (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E m, chartModelBasis E j, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁))))
        = ∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j p) (extChartAt I x x) * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁)))
           + chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![m, j, p] * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁)))) from
      Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => by
          rw [lieArm_U3_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x m j p]
          ring))))]
    simp only [Finset.sum_add_distrib]
  have hs6 : (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E p, chartModelBasis E q, chartModelBasis E k₁])) = (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) p (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x q k₁) (extChartAt I x x))) + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![p, q, k₁])) := by
    rw [show (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E p, chartModelBasis E q, chartModelBasis E k₁]))
        = ∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) p (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x q k₁) (extChartAt I x x))
           + chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![p, q, k₁])) from
      Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ => by
        rw [show (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E p, chartModelBasis E q, chartModelBasis E k₁])
            = ∑ q : Fin (Module.finrank ℝ E), ((DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) p (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x q k₁) (extChartAt I x x) + (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![p, q, k₁]) from
          Finset.sum_congr rfl (fun q _ => by
            rw [lieArm_U3_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p q k₁]
            ring)]
        rw [Finset.sum_add_distrib, mul_add]))]
    simp only [Finset.sum_add_distrib]
  have hs7 : (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E m, chartModelBasis E j, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) = (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j p) (extChartAt I x x) *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![m, j, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) := by
    rw [show (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E m, chartModelBasis E j, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁))))
        = ∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j p) (extChartAt I x x) * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))
           + chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![m, j, p] * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) from
      Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => by
          rw [lieArm_U3_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x m j p]
          ring))))]
    simp only [Finset.sum_add_distrib]
  have hs8 : (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E j, chartModelBasis E m, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) = (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) j (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x m p) (extChartAt I x x) *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![j, m, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) := by
    rw [show (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E j, chartModelBasis E m, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁))))
        = ∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) j (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x m p) (extChartAt I x x) * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))
           + chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![j, m, p] * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ i q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) from
      Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => by
          rw [lieArm_U3_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j m p]
          ring))))]
    simp only [Finset.sum_add_distrib]
  have hs9 : (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E j, chartModelBasis E m, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q i)))) = (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) j (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x m p) (extChartAt I x x) *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q i)))) + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![j, m, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q i)))) := by
    rw [show (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E j, chartModelBasis E m, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q i))))
        = ∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) j (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x m p) (extChartAt I x x) * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q i)))
           + chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![j, m, p] * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ l₁ q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g_bg x k₁ l₁ q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q i)))) from
      Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => by
          rw [lieArm_U3_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j m p]
          ring))))]
    simp only [Finset.sum_add_distrib]
  have hs10 : (∑ w : Fin (Module.finrank ℝ E), PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x w (extChartAt I x x) * unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E j, chartModelBasis E i, chartModelBasis E w]) = (∑ w : Fin (Module.finrank ℝ E), (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b * (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b w (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x a b w (extChartAt I x x))) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) j (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i w) (extChartAt I x x)) + (∑ w : Fin (Module.finrank ℝ E), (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b * (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b w (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x a b w (extChartAt I x x))) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![j, i, w]) := by
    rw [show (∑ w : Fin (Module.finrank ℝ E), PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x w (extChartAt I x x) * unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E j, chartModelBasis E i, chartModelBasis E w]) = ∑ w : Fin (Module.finrank ℝ E), ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b * (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b w (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x a b w (extChartAt I x x))) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) j (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i w) (extChartAt I x x) + (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b * (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x a b w (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x a b w (extChartAt I x x))) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![j, i, w]) from
      Finset.sum_congr rfl (fun w _ => by
        rw [lieArm_U3_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j i w,
          lieArm_chartDeTurckVFComp_center (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x w]
        ring)]
    simp only [Finset.sum_add_distrib]
  have hs11 : (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E m, chartModelBasis E i, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁)))) = (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i p) (extChartAt I x x) *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁)))) + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![m, i, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁)))) := by
    rw [show (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E m, chartModelBasis E i, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁))))
        = ∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i p) (extChartAt I x x) * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁)))
           + chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![m, i, p] * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x k₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q l₁)))) from
      Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => by
          rw [lieArm_U3_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x m i p]
          ring))))]
    simp only [Finset.sum_add_distrib]
  have hs12 : (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i j q (extChartAt I x x)) * unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E p, chartModelBasis E q, chartModelBasis E k₁])) = (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i j q (extChartAt I x x)) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) p (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x q k₁) (extChartAt I x x))) + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i j q (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![p, q, k₁])) := by
    rw [show (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i j q (extChartAt I x x)) * unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E p, chartModelBasis E q, chartModelBasis E k₁]))
        = ∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i j q (extChartAt I x x)) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) p (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x q k₁) (extChartAt I x x))
           + chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i j q (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![p, q, k₁])) from
      Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ => by
        rw [show (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i j q (extChartAt I x x)) * unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E p, chartModelBasis E q, chartModelBasis E k₁])
            = ∑ q : Fin (Module.finrank ℝ E), ((DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i j q (extChartAt I x x)) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) p (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x q k₁) (extChartAt I x x) + (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x i j q (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![p, q, k₁]) from
          Finset.sum_congr rfl (fun q _ => by
            rw [lieArm_U3_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p q k₁]
            ring)]
        rw [Finset.sum_add_distrib, mul_add]))]
    simp only [Finset.sum_add_distrib]
  have hs13 : (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E m, chartModelBasis E i, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) = (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i p) (extChartAt I x x) *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![m, i, p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) := by
    rw [show (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E m, chartModelBasis E i, chartModelBasis E p] *
          (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁))))
        = ∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E), ∑ l₁ : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) m (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i p) (extChartAt I x x) * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))
           + chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x l₁ m * (arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![m, i, p] * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x l₁ j q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x l₁ j q (extChartAt I x x)) * DifferentialGeometry.Integral.Measure.chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q k₁)))) from
      Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun l₁ _ => Finset.sum_congr rfl (fun m _ => by
          rw [lieArm_U3_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x m i p]
          ring))))]
    simp only [Finset.sum_add_distrib]
  have hs14 : (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E q, chartModelBasis E p, chartModelBasis E k₁])) = (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) q (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p k₁) (extChartAt I x x))) + (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![q, p, k₁])) := by
    rw [show (∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E q, chartModelBasis E p, chartModelBasis E k₁]))
        = ∑ k₁ : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
          (chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) q (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p k₁) (extChartAt I x x))
           + chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![q, p, k₁])) from
      Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun p _ => by
        rw [show (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T'))) x ![chartModelBasis E q, chartModelBasis E p, chartModelBasis E k₁])
            = ∑ q : Fin (Module.finrank ℝ E), ((DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv (E := E) q (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p k₁) (extChartAt I x x) + (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![q, p, k₁]) from
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

end DeTurckRemainderTameLipschitz

set_option linter.unusedSectionVars false in
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

namespace DeTurckRemainderTameLipschitz

set_option linter.unusedSectionVars false in
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

end DeTurckRemainderTameLipschitz

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
  have hCLM := contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
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

namespace DeTurckRemainderTameLipschitz

theorem lieArm_hjAbsorb (g₀ : SmoothRiemannianMetric I M) {δ δ' : ℝ}
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

end DeTurckRemainderTameLipschitz

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (deTurckLieWEndo deTurckLieWEndo_apply deTurckLieWEndo_homSection_contMDiff deTurckLieCovDerivW connDiffOp_homSection_contMDiff metricConnDiffLoweredFib metricConnDiffLoweredFib_toModel metricConnDiffLoweredFib_contMDiff domDomCongrFibRank domDomCongrFibRank_apply tensor0SProdKappaFib tensor0SProdKappaFib_apply)
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck (cometricDoubleTraceFib cometricDoubleTraceFib_toModel cometricDoubleTraceFib_contMDiff)

namespace DeTurckRemainderTameLipschitz

noncomputable def lieCorr0NEndo (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
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
        (lieCorr0NEndo (I := I) g₀ g₁ g_bg x)) := by
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

noncomputable def lieCorr0InsertFib (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  slotInsertEndoFib (I := I) (M := M) 2 0 x (lieCorr0NEndo (I := I) g₀ g₁ g_bg x) +
    slotInsertEndoFib (I := I) (M := M) 2 1 x (lieCorr0NEndo (I := I) g₀ g₁ g_bg x)

theorem lieCorr0InsertFib_toModel (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (lieCorr0InsertFib (I := I) g₀ g₁ g_bg x D) v =
      Tensor0SSpace.toModel D
          (Function.update v 0 (lieCorr0NEndo (I := I) g₀ g₁ g_bg x (v 0))) +
        Tensor0SSpace.toModel D
          (Function.update v 1 (lieCorr0NEndo (I := I) g₀ g₁ g_bg x (v 1))) := by
  rw [lieCorr0InsertFib, ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add,
    ContinuousMultilinearMap.add_apply,
    slotInsertEndoFib_apply_eval, slotInsertEndoFib_apply_eval]

end DeTurckRemainderTameLipschitz

private theorem lieCorr0InsertFib_contMDiff (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (lieCorr0InsertFib (I := I) g₀ g₁ g_bg x))) := by
  classical
  have h0 := slotInsertEndoFib_contMDiff (I := I) (M := M) g₀ 2 0
    (fun x => lieCorr0NEndo (I := I) g₀ g₁ g_bg x)
    (lieCorr0NEndo_homSection_contMDiff (I := I) g₀ g₁ g_bg)
  have h1 := slotInsertEndoFib_contMDiff (I := I) (M := M) g₀ 2 1
    (fun x => lieCorr0NEndo (I := I) g₀ g₁ g_bg x)
    (lieCorr0NEndo_homSection_contMDiff (I := I) g₀ g₁ g_bg)
  have hadd := ContMDiff.add_section
    (s := fun x => (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x
        (lieCorr0NEndo (I := I) g₀ g₁ g_bg x))))
    (t := fun x => (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 1 x
        (lieCorr0NEndo (I := I) g₀ g₁ g_bg x))))
    h0 h1
  refine hadd.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) x) ?_
  rw [lieCorr0InsertFib]
  rfl

namespace DeTurckRemainderTameLipschitz

noncomputable def lieCorr0TraceStep (g : SmoothRiemannianMetric I M) (p : ℕ)
    (σ : Equiv.Perm (Fin (p + 2))) (x : M) :
    Tensor0SSpace (p + 2) I x →L[ℝ] Tensor0SSpace p I x :=
  (cometricDoubleTraceFib (I := I) g p x).comp
    (domDomCongrFibRank (I := I) (p + 2) σ x)

def lieCorr0VBPerm : Equiv.Perm (Fin 4) :=
  ⟨![1, 2, 3, 0], ![3, 0, 1, 2], by decide, by decide⟩

noncomputable def lieCorr0VBFib (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  (2 : ℝ) • ((lieCorr0TraceStep (I := I) g₁ 2 lieCorr0VBPerm x).comp
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
  (lieCorr0TraceStep (I := I) g₁ 2 lieCorr0AMixPerm2 x).comp
    ((lieCorr0TraceStep (I := I) g₁ 4 lieCorr0AMixPerm1 x).comp
      ((tensor0SProdKappaFib (I := I) (p := 3) (q := 3) x
          (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)).comp
        ((lieCorr0TraceStep (I := I) g₁ 3 lieCorr0AMixPermQ x).comp
          (tensor0SProdKappaFib (I := I) (p := 2) (q := 3) x
            (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)))))

noncomputable def lieCorr0AMixFib (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  (2 : ℝ) • (lieCorr0AMixHalfFib (I := I) g₀ g₁ g_bg x +
    (domDomCongrFibRank (I := I) 2 (Equiv.swap 0 1) x).comp
      (lieCorr0AMixHalfFib (I := I) g₀ g₁ g_bg x))

end DeTurckRemainderTameLipschitz

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

namespace DeTurckRemainderTameLipschitz

noncomputable def lieCorr0RiemLoweredFib (g₀ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 4 I x :=
  Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
    (lieCorr0Quadlin4ToModel (TangentSpace I x) (lieCorr0RiemQuadlin (I := I) g₀ x))

end DeTurckRemainderTameLipschitz

private theorem lieCorr0RiemLoweredFib_toModel (g₀ : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 4 → TangentSpace I x) :
    Tensor0SSpace.toModel (lieCorr0RiemLoweredFib (I := I) g₀ x) v =
      g₀.inner x (Integral.Connection.riemannOp (LeviCivita (I := I) g₀) x
        (v 0) (v 1) (v 2)) (v 3) := by
  rw [lieCorr0RiemLoweredFib, Tensor0SSpace.toModel_ofModel]
  exact lieCorr0Quadlin4ToModel_apply (TangentSpace I x) (lieCorr0RiemQuadlin (I := I) g₀ x) v

namespace DeTurckRemainderTameLipschitz

def lieCorr0RiemPerm1 : Equiv.Perm (Fin 6) :=
  ⟨![1, 5, 2, 3, 4, 0], ![5, 0, 2, 3, 4, 1], by decide, by decide⟩

def lieCorr0RiemPerm2 : Equiv.Perm (Fin 4) :=
  ⟨![2, 3, 0, 1], ![2, 3, 0, 1], by decide, by decide⟩

noncomputable def lieCorr0RiemFib (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  (-1 : ℝ) • ((lieCorr0TraceStep (I := I) g₁ 2 lieCorr0RiemPerm2 x).comp
    ((lieCorr0TraceStep (I := I) g₀ 4 lieCorr0RiemPerm1 x).comp
      (tensor0SProdKappaFib (I := I) (p := 2) (q := 4) x
        (lieCorr0RiemLoweredFib (I := I) g₀ x))))

end DeTurckRemainderTameLipschitz

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

namespace DeTurckRemainderTameLipschitz

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
        (lieCorr0TraceStep (I := I) g p σ x (Z x))) := by
  have hZρ := lieCorr0_ddc_section_contMDiff (I := I) σ (fun x => Z x) hZ
  have hfield := ContMDiff.clm_bundle_apply (b := id)
    (cometricDoubleTraceFib_contMDiff (I := I) g p) hZρ
  refine hfield.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel p ℝ E)
    (E := fun z : M => Tensor0SSpace p I z) x t) ?_
  rw [lieCorr0TraceStep, ContinuousLinearMap.comp_apply, domDomCongrFibRank_apply]
  rfl

end DeTurckRemainderTameLipschitz

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
        ((2 : ℝ) • lieCorr0TraceStep (I := I) g₁ 2 lieCorr0VBPerm x
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
    (fun x => lieCorr0TraceStep (I := I) g₁ 3 lieCorr0AMixPermQ x
      (tensor0SProdKappaFib (I := I) x (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x) (Y x)))
    (fun x => metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
    htr1 (metricConnDiffLoweredFib_contMDiff (I := I) g₁ g₁ g_bg)
  have htr2 := lieCorr0TraceStep_section_contMDiff (I := I) g₁ 4 lieCorr0AMixPerm1
    (fun x => tensor0SProdKappaFib (I := I) x (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
      (lieCorr0TraceStep (I := I) g₁ 3 lieCorr0AMixPermQ x
        (tensor0SProdKappaFib (I := I) x
          (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x) (Y x)))) hprod2
  have htr3 := lieCorr0TraceStep_section_contMDiff (I := I) g₁ 2 lieCorr0AMixPerm2
    (fun x => lieCorr0TraceStep (I := I) g₁ 4 lieCorr0AMixPerm1 x
      (tensor0SProdKappaFib (I := I) x (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
        (lieCorr0TraceStep (I := I) g₁ 3 lieCorr0AMixPermQ x
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

namespace DeTurckRemainderTameLipschitz

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

end DeTurckRemainderTameLipschitz

private theorem lieCorr0RiemFib_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (lieCorr0RiemFib (I := I) g₀ g₁ x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun x : M => Tensor0SSpace 2 I x)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun x => lieCorr0RiemFib (I := I) g₀ g₁ x)
  intro Y
  have hprod := lieCorr0_prod_section_contMDiff (I := I) (p := 2) (q := 4)
    (fun x => Y x) (fun x => lieCorr0RiemLoweredFib (I := I) g₀ x)
    Y.contMDiff (lieCorr0RiemLoweredFib_section_contMDiff (I := I) g₀)
  have htr1 := lieCorr0TraceStep_section_contMDiff (I := I) g₀ 4 lieCorr0RiemPerm1
    (fun x => tensor0SProdKappaFib (I := I) x (lieCorr0RiemLoweredFib (I := I) g₀ x) (Y x))
    hprod
  have htr2 := lieCorr0TraceStep_section_contMDiff (I := I) g₁ 2 lieCorr0RiemPerm2
    (fun x => lieCorr0TraceStep (I := I) g₀ 4 lieCorr0RiemPerm1 x
      (tensor0SProdKappaFib (I := I) x (lieCorr0RiemLoweredFib (I := I) g₀ x) (Y x))) htr1
  have hsmul : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        ((-1 : ℝ) • lieCorr0TraceStep (I := I) g₁ 2 lieCorr0RiemPerm2 x
          (lieCorr0TraceStep (I := I) g₀ 4 lieCorr0RiemPerm1 x
            (tensor0SProdKappaFib (I := I) x
              (lieCorr0RiemLoweredFib (I := I) g₀ x) (Y x))))) :=
    ContMDiff.smul_section contMDiff_const htr2
  refine hsmul.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x t) ?_
  rw [lieCorr0RiemFib]
  rfl

namespace DeTurckRemainderTameLipschitz

noncomputable def lieCorr0TotalFib (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  lieCorr0InsertFib (I := I) g₀ g₁ g_bg x + lieCorr0VBFib (I := I) g₀ g₁ x +
    lieCorr0AMixFib (I := I) g₀ g₁ g_bg x + lieCorr0RiemFib (I := I) g₀ g₁ x

end DeTurckRemainderTameLipschitz

private theorem lieCorr0TotalFib_contMDiff (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (lieCorr0TotalFib (I := I) g₀ g₁ g_bg x))) := by
  classical
  have h12 := ContMDiff.add_section
    (s := fun x => (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (lieCorr0InsertFib (I := I) g₀ g₁ g_bg x)))
    (t := fun x => (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (lieCorr0VBFib (I := I) g₀ g₁ x)))
    (lieCorr0InsertFib_contMDiff (I := I) g₀ g₁ g_bg)
    (lieCorr0VBFib_contMDiff (I := I) g₀ g₁)
  have h123 := ContMDiff.add_section
    (s := fun x => (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (lieCorr0InsertFib (I := I) g₀ g₁ g_bg x)) +
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (lieCorr0VBFib (I := I) g₀ g₁ x)))
    (t := fun x => (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (lieCorr0AMixFib (I := I) g₀ g₁ g_bg x)))
    h12 (lieCorr0AMixFib_contMDiff (I := I) g₀ g₁ g_bg)
  have h1234 := ContMDiff.add_section
    (s := fun x => ((show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (lieCorr0InsertFib (I := I) g₀ g₁ g_bg x)) +
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (lieCorr0VBFib (I := I) g₀ g₁ x))) +
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (lieCorr0AMixFib (I := I) g₀ g₁ g_bg x)))
    (t := fun x => (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (lieCorr0RiemFib (I := I) g₀ g₁ x)))
    h123 (lieCorr0RiemFib_contMDiff (I := I) g₀ g₁)
  refine h1234.congr (fun x => ?_)
  refine congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) x) ?_
  rw [lieCorr0TotalFib]
  rfl

namespace DeTurckRemainderTameLipschitz

noncomputable def lieCorr0Field (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (lieCorr0TotalFib (I := I) g₀ g₁ g_bg x))
      contMDiff_toFun := lieCorr0TotalFib_contMDiff (I := I) g₀ g₁ g_bg }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

end DeTurckRemainderTameLipschitz

private theorem lieCorr0Field_toSection (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    (lieCorr0Field (I := I) (M := M) g₀ g₁ g_bg).toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (lieCorr0TotalFib (I := I) g₀ g₁ g_bg x)) :=
  rfl

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (deTurckVF_realizedFam_jointContMDiffOn metricConnDiffLowered_selfFam_jointContMDiffOn metricConnDiffLowered_bgFam_jointContMDiffOn jointTensor0SProd_local deTurckLieWEndo_realizedFam_jointContMDiffOn deTurckLieCoeffField deTurckLieCoeffField_realizedFam_jointSmooth linearizedRicciThreeArmHjoint)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (interiorProductField_jointContMDiffOn_vecJoint inverseMetricSharpField_realizedFam_jointContMDiffOn domDomCongrField_jointContMDiffOn cometricDoubleTraceFib_realizedFam_jointContMDiffOn slotInsertEndo0Field_apply_jointContMDiffOn slotInsertEndo1Field_apply_jointContMDiffOn contMDiffOn_clm_section_of_pointwise_jointMR)
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
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
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
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (gP : SmoothRiemannianMetric I M) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) p.1
        (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g₀ p.1
          ((PDE.DeTurck.deTurckVF (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) gP :
              Π b : M, TangentSpace I b) p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
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
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) p.1
        (lieCorr0NEndo (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1))
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
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (Z : ∀ pp : M × ℝ, Tensor0SSpace (p + 2) I pp.1)
    (hZ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel (p + 2) ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel (p + 2) ℝ E)
        (E := fun z : M => Tensor0SSpace (p + 2) I z) pp.1 (Z pp))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ'))) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel p ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel p ℝ E)
        (E := fun z : M => Tensor0SSpace p I z) pp.1
        (lieCorr0TraceStep (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) p σ pp.1 (Z pp)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hddc := domDomCongrField_jointContMDiffOn (I := I) σ
    (S := realizedSmallSet (δ := δ) (δ' := δ')) Z hZ
  have htr := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := p)
    g₀ T T' hδ hδ' _ hddc
  refine htr.congr (fun pp _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel p ℝ E)
    (E := fun z : M => Tensor0SSpace p I z) pp.1 t) ?_
  rw [lieCorr0TraceStep, ContinuousLinearMap.comp_apply, domDomCongrFibRank_apply]

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
        (lieCorr0TraceStep (I := I) g p σ pp.1 (Z pp)))
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
  rw [lieCorr0TraceStep, ContinuousLinearMap.comp_apply, domDomCongrFibRank_apply]

private theorem lieCorr0InsertFib_apply_jointContMDiffOn
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) pp.1
        (lieCorr0InsertFib (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) g_bg pp.1
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
      lieCorr0NEndo (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) g_bg pp.1) hΛ
    (A := fun pp : M × ℝ => Y pp.1) hY
  have h1 := slotInsertEndo1Field_apply_jointContMDiffOn (I := I) (M := M) (d := 0)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) g₀
    (Λ := fun pp : M × ℝ =>
      lieCorr0NEndo (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) g_bg pp.1) hΛ
    (A := fun pp : M × ℝ => Y pp.1) hY
  have hsum := lieCorr0_j0S_add_local (I := I) (d := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) _ _ h0 h1
  refine hsum.congr (fun pp _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) pp.1 t) ?_
  rw [lieCorr0InsertFib, ContinuousLinearMap.add_apply]

private theorem lieCorr0VBFib_apply_jointContMDiffOn
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
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
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
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
    (fun pp : M × ℝ => lieCorr0TraceStep (I := I)
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
          (lieCorr0TraceStep (I := I)
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
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
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
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) pp.1
        (lieCorr0RiemFib (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) pp.1 (Y pp.1)))
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
  rw [lieCorr0RiemFib]
  rfl

private theorem lieCorr0TotalFib_apply_jointContMDiffOn
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun pp : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) pp.1
        (lieCorr0TotalFib (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) g_bg pp.1
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
  rw [lieCorr0TotalFib]
  rfl

namespace DeTurckRemainderTameLipschitz

theorem lieCorr0Field_realizedFam_jointSmooth
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2
      (fun s => lieCorr0Field (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) (δ := δ) (δ' := δ') := by
  rw [linearizedRicciThreeArmHjoint]
  have hCLM := contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SModel 2 ℝ E)
    (V₁ := fun x : M => Tensor0SSpace 2 I x)
    (F₂ := Tensor0SModel 2 ℝ E)
    (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun pp : M × ℝ =>
      lieCorr0TotalFib (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' pp.2) g_bg pp.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun Y => lieCorr0TotalFib_apply_jointContMDiffOn (I := I) g₀ T T' hδ hδ' g_bg Y)
  refine hCLM.congr (fun pp _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) pp.1 t) ?_
  rw [lieCorr0Field_toSection]
  rfl

theorem lieCorr0Phi0b_jointSmooth
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2
      (fun s => deTurckLieCoeffField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg +
        lieCorr0Field (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) (δ := δ) (δ' := δ') := by
  have h1 := deTurckLieCoeffField_realizedFam_jointSmooth (I := I) g₀ T T' hδ hδ' g_bg
  have h2 := lieCorr0Field_realizedFam_jointSmooth (I := I) g₀ T T' hδ hδ' g_bg
  rw [linearizedRicciThreeArmHjoint] at h1 h2 ⊢
  have hadd := lieArm_jointRS_add_local (I := I) (r := 2) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => (deTurckLieCoeffField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg).toSection p.1)
    (fun p : M × ℝ => (lieCorr0Field (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg).toSection p.1)
    h1 h2
  refine hadd.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) p.1 t) ?_
  rw [smoothCcTensor_toSection_add_apply]

end DeTurckRemainderTameLipschitz

section LieCorr0Eval

open DifferentialGeometry.Integral.DivergenceTheorem (chartInvGramMatrix partialDeriv chartChristoffel)
open DifferentialGeometry.Integral.Measure (chartGramMatrix)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (deTurckLieCovDerivW_chartBasis_eq)

variable (g₀ g₁ g_bg : SmoothRiemannianMetric I M)

namespace DeTurckRemainderTameLipschitz

noncomputable def lieCorr0NScalar (x : M) (i p : Fin (Module.finrank ℝ E)) : ℝ :=
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

end DeTurckRemainderTameLipschitz

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
    lieCorr0NEndo (I := I) g₀ g₁ g_bg x ((chartModelBasis E) i : TangentSpace I x) =
      ∑ p : Fin (Module.finrank ℝ E),
        lieCorr0NScalar (I := I) (M := M) g₀ g₁ g_bg x i p •
          ((chartModelBasis E) p : TangentSpace I x) := by
  classical
  rw [lieCorr0NEndo]
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

namespace DeTurckRemainderTameLipschitz

lemma lieCorr0InsertFib_basis_value (x : M) (D : Tensor0SSpace 2 I x)
    (i j : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel (lieCorr0InsertFib (I := I) g₀ g₁ g_bg x D)
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
      (lieCorr0NEndo (I := I) g₀ g₁ g_bg x
        ((![(chartModelBasis E) i, (chartModelBasis E) j] : Fin 2 → E) 0)) =
      ![(lieCorr0NEndo (I := I) g₀ g₁ g_bg x
          ((chartModelBasis E) i : TangentSpace I x) : E), (chartModelBasis E) j] := by
    rw [lieCorr0_upd0]
    rfl
  have h1 : Function.update
      (![(chartModelBasis E) i, (chartModelBasis E) j] : Fin 2 → E) (1 : Fin 2)
      (lieCorr0NEndo (I := I) g₀ g₁ g_bg x
        ((![(chartModelBasis E) i, (chartModelBasis E) j] : Fin 2 → E) 1)) =
      ![(chartModelBasis E) i, (lieCorr0NEndo (I := I) g₀ g₁ g_bg x
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

end DeTurckRemainderTameLipschitz

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (unitModel4SlotBilin unitModel4SlotBilin_apply cometricFinBasisTrace_eq_chartInvGram_bilin)

private lemma lieCorr0TraceStep_toModel (g : SmoothRiemannianMetric I M) (p : ℕ)
    (σ : Equiv.Perm (Fin (p + 2))) (x : M) (T : Tensor0SSpace (p + 2) I x)
    (u : Fin p → E) :
    Tensor0SSpace.toModel (lieCorr0TraceStep (I := I) g p σ x T) u =
      ∑ k : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel T
          (fun i => (Fin.cons (DeTurck.cometricLmodel (I := I) g x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))
            (Fin.cons ((Module.finBasis ℝ E) k) u) : Fin (p + 2) → E) (σ i)) := by
  classical
  rw [lieCorr0TraceStep, ContinuousLinearMap.comp_apply, domDomCongrFibRank_apply,
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

namespace DeTurckRemainderTameLipschitz

lemma lieCorr0VBFib_basis_value (x : M) (D : Tensor0SSpace 2 I x)
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
      (2 : ℝ) • lieCorr0TraceStep (I := I) g₁ 2 lieCorr0VBPerm x
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
      unitModel4SlotBilin (E := E) (Tensor0SSpace.toModel P4) 3 0 (by decide)
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

end DeTurckRemainderTameLipschitz

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
        (lieCorr0TraceStep (I := I) g₁ 3 lieCorr0AMixPermQ x
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
        (lieCorr0TraceStep (I := I) g₁ 4 lieCorr0AMixPerm1 x
          (tensor0SProdKappaFib (I := I) x
            (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
            (lieCorr0TraceStep (I := I) g₁ 3 lieCorr0AMixPermQ x
              (tensor0SProdKappaFib (I := I) x
                (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x) D)))) w =
      ∑ j : Fin (Module.finrank ℝ E), ∑ jl : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x j jl *
          (Tensor0SSpace.toModel
              (lieCorr0TraceStep (I := I) g₁ 3 lieCorr0AMixPermQ x
                (tensor0SProdKappaFib (I := I) x
                  (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x) D))
              ![w 0, (chartModelBasis E) jl, w 1] *
            Tensor0SSpace.toModel (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x)
              ![(chartModelBasis E) j, w 2, w 3]) := by
  classical
  set QD : Tensor0SSpace 3 I x :=
    lieCorr0TraceStep (I := I) g₁ 3 lieCorr0AMixPermQ x
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

namespace DeTurckRemainderTameLipschitz

lemma lieCorr0AMixHalfFib_basis_value (x : M) (D : Tensor0SSpace 2 I x)
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
    lieCorr0TraceStep (I := I) g₁ 3 lieCorr0AMixPermQ x
      (tensor0SProdKappaFib (I := I) x
        (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x) D) with hQD
  set T4 : Tensor0SSpace 4 I x :=
    lieCorr0TraceStep (I := I) g₁ 4 lieCorr0AMixPerm1 x
      (tensor0SProdKappaFib (I := I) x
        (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x) QD) with hT4
  rw [show lieCorr0AMixHalfFib (I := I) g₀ g₁ g_bg x D =
      lieCorr0TraceStep (I := I) g₁ 2 lieCorr0AMixPerm2 x T4 from by
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

end DeTurckRemainderTameLipschitz

private lemma lieCorr0_swapArg (v0 v1 : E) :
    (fun i : Fin 2 => (![v0, v1] : Fin 2 → E) ((Equiv.swap (0 : Fin 2) 1) i)) =
      ![v1, v0] := by
  funext i
  fin_cases i <;> simp

namespace DeTurckRemainderTameLipschitz

lemma lieCorr0AMixFib_basis_value (x : M) (D : Tensor0SSpace 2 I x)
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

end DeTurckRemainderTameLipschitz

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
        (lieCorr0TraceStep (I := I) g₀ 4 lieCorr0RiemPerm1 x
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

namespace DeTurckRemainderTameLipschitz

lemma lieCorr0RiemFib_basis_value (x : M) (D : Tensor0SSpace 2 I x)
    (i j : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel (lieCorr0RiemFib (I := I) g₀ g₁ x D)
        ![(chartModelBasis E) i, (chartModelBasis E) j] =
      -(∑ m : Fin (Module.finrank ℝ E), ∑ ml : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x m ml *
          ∑ ρ : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Integral.DivergenceTheorem.chartRiemannTensor (I := I) g₀ x
                ml i j ρ (extChartAt I x x) *
              Tensor0SSpace.toModel D ![(chartModelBasis E) ρ, (chartModelBasis E) m]) := by
  classical
  set T4 : Tensor0SSpace 4 I x :=
    lieCorr0TraceStep (I := I) g₀ 4 lieCorr0RiemPerm1 x
      (tensor0SProdKappaFib (I := I) x (lieCorr0RiemLoweredFib (I := I) g₀ x) D) with hT4
  rw [show lieCorr0RiemFib (I := I) g₀ g₁ x D =
      (-1 : ℝ) • lieCorr0TraceStep (I := I) g₁ 2 lieCorr0RiemPerm2 x T4 from by
    rw [lieCorr0RiemFib, hT4]
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

end DeTurckRemainderTameLipschitz

end LieCorr0AMixEval

end LieCorr0Eval

section LieCorr0Value

open DifferentialGeometry.Integral.DivergenceTheorem (chartInvGramMatrix partialDeriv chartChristoffel)
open DifferentialGeometry.Integral.Measure (chartGramMatrix)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (symmS unitModel unitTensor deTurckLieCoeffField deTurckLieCoeffField_appCc_eq deTurckLieCovDerivA deTurckLieCovDerivW deTurckLieCovDerivW_chartBasis_eq deTurckLieCovDerivA_chartBasis_eq dLaCovKernel dLaCovKernel_apply_extend frameDLaKernel frameDLaKernel_apply double_frame_bilin_trace_eq_fixed unitModel_basisChart_eq_tensorChartComponentRaw tensorChartComponentRaw)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (realizedGramDeriv realizedFam)

variable (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
variable {δ δ' : ℝ}

private lemma lieCorr0_f_readout (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (c d : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 2 (symmS (I := I) (M := M) g₀ (T - T')) x
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
    (symmS (I := I) (M := M) g₀ (T - T')) x ![c, d]]
  exact hpt

namespace DeTurckRemainderTameLipschitz

noncomputable def lieCorr0CovASc (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
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

end DeTurckRemainderTameLipschitz

private lemma lieCorr0_dLa_inner_basis (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (a b m k : Fin (Module.finrank ℝ E)) :
    g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x
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

namespace DeTurckRemainderTameLipschitz

noncomputable def lieCorr0CovWSc (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (a p : Fin (Module.finrank ℝ E)) : ℝ :=
  partialDeriv (E := E) a
      (fun y => PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) g₁ g_bg x p y)
      (extChartAt I x x) +
    ∑ c : Fin (Module.finrank ℝ E),
      chartChristoffel (I := I) g₁ x a c p (extChartAt I x x) *
        PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) g₁ g_bg x c
          (extChartAt I x x)

end DeTurckRemainderTameLipschitz

private lemma lieCorr0_covW_basis (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (a : Fin (Module.finrank ℝ E)) :
    deTurckLieCovDerivW (I := I) g₁ g_bg
        (smoothExtensionTangent (I := I) x ((chartModelBasis E) a : TangentSpace I x)) x =
      ∑ p : Fin (Module.finrank ℝ E),
        lieCorr0CovWSc (I := I) (M := M) g₁ g_bg x a p •
          ((chartModelBasis E) p : TangentSpace I x) := by
  rw [deTurckLieCovDerivW_chartBasis_eq (I := I) g₁ g_bg x a]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [DifferentialGeometry.Integral.Connection.chartBasisVecFiber_self (I := I) x p]
  rfl

namespace DeTurckRemainderTameLipschitz

lemma lieCorr0_icg0_readout (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (c d : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 2
        (iteratedCovGrad (I := I) g₀ 0 2 0 (symmS (I := I) (M := M) g₀ (T - T'))) x
        ![(chartModelBasis E) c, (chartModelBasis E) d] =
      realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c d (extChartAt I x x) := by
  rw [iteratedCovGrad_zero]
  exact lieCorr0_f_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c d

end DeTurckRemainderTameLipschitz

private lemma lieCorr0_ite_pair_eq (x : M) (u w : TangentSpace I x) :
    (fun j : Fin 2 => if j = 0 then u else w) = ![u, w] := by
  funext j
  fin_cases j <;> rfl

namespace DeTurckRemainderTameLipschitz

lemma lieCorr0_committed_value (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) (s : ℝ) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2
          (deTurckLieCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
          (iteratedCovGrad (I := I) g₀ 0 2 0 (symmS (I := I) (M := M) g₀ (T - T')))) x
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
    iteratedCovGrad (I := I) g₀ 0 2 0 (symmS (I := I) (M := M) g₀ (T - T')) with hW₀
  rw [deTurckLieCoeffField_appCc_eq (I := I) (M := M) g₀ g₁ g_bg W₀ x
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
            (deTurckLieCovDerivA (I := I) g₁ g_bg
              (smoothExtensionTangent (I := I) x ((chartModelBasis E) i : TangentSpace I x))
              (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
              (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x)
            ((chartModelBasis E) j : TangentSpace I x)
          + g₁.inner x
            (deTurckLieCovDerivA (I := I) g₁ g_bg
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
      frameDLaKernel (I := I) g₁ g_bg x
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
              (deTurckLieCovDerivA (I := I) g₁ g_bg
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i : TangentSpace I x))
                (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x)
              ((chartModelBasis E) j : TangentSpace I x)
            + g₁.inner x
              (deTurckLieCovDerivA (I := I) g₁ g_bg
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) j : TangentSpace I x))
                (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x)
              ((chartModelBasis E) i : TangentSpace I x)) =
        K (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x) *
          Dd (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x) := by
      intro a b
      rw [hK, frameDLaKernel_apply]
      rw [hDdev]
      rw [show (dLaCovKernel (I := I) g₁ g_bg x
          ((chartModelBasis E) i : TangentSpace I x)
          (smoothOrthoFrame (I := I) g₁ x a x)
          (smoothOrthoFrame (I := I) g₁ x b x)) =
        deTurckLieCovDerivA (I := I) g₁ g_bg
          (smoothExtensionTangent (I := I) x ((chartModelBasis E) i : TangentSpace I x))
          (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
          (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x from
        dLaCovKernel_apply_extend (I := I) g₁ g_bg x _ _ _]
      rw [show (dLaCovKernel (I := I) g₁ g_bg x
          ((chartModelBasis E) j : TangentSpace I x)
          (smoothOrthoFrame (I := I) g₁ x a x)
          (smoothOrthoFrame (I := I) g₁ x b x)) =
        deTurckLieCovDerivA (I := I) g₁ g_bg
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
        deTurckLieCovDerivW (I := I) g₁ g_bg
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
        else deTurckLieCovDerivW (I := I) g₁ g_bg
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

lemma lieCorr0_phi0b_value_split (_hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (_hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) (s : ℝ) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2
          (deTurckLieCoeffField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg +
            lieCorr0Field (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
          (iteratedCovGrad (I := I) g₀ 0 2 0 (symmS (I := I) (M := M) g₀ (T - T')))) x
        ![((chartModelBasis E) i : TangentSpace I x), ((chartModelBasis E) j : TangentSpace I x)] =
      unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2
          (deTurckLieCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
          (iteratedCovGrad (I := I) g₀ 0 2 0 (symmS (I := I) (M := M) g₀ (T - T')))) x
        ![((chartModelBasis E) i : TangentSpace I x), ((chartModelBasis E) j : TangentSpace I x)]
      + Tensor0SSpace.toModel
          (lieCorr0TotalFib (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
              (iteratedCovGrad (I := I) g₀ 0 2 0
                (symmS (I := I) (M := M) g₀ (T - T'))).toSection x)
              (unitTensor (I := I) (M := M) x)))
          ![(chartModelBasis E) i, (chartModelBasis E) j] := by
  classical
  set g₁ : SmoothRiemannianMetric I M := realizedFam (I := I) g₀ T T' hδ hδ' s with hg₁
  set W₀ : SmoothCcTensor g₀ 0 2 :=
    iteratedCovGrad (I := I) g₀ 0 2 0 (symmS (I := I) (M := M) g₀ (T - T')) with hW₀
  set D₀ : Tensor0SSpace 2 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W₀.toSection x)
      (unitTensor (I := I) (M := M) x) with hD₀
  have hunfold : ∀ (Φ : SmoothCcTensor g₀ 2 2),
      unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2 Φ W₀) x
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
        lieCorr0Field (I := I) (M := M) g₀ g₁ g_bg).toSection x) D₀) =
    ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg).toSection x) D₀) +
    (lieCorr0TotalFib (I := I) g₀ g₁ g_bg x D₀) from by
    rw [smoothCcTensor_toSection_add_apply (I := I) (M := M) g₀
      (deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg)
      (lieCorr0Field (I := I) (M := M) g₀ g₁ g_bg) x]
    rfl]
  rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]

end DeTurckRemainderTameLipschitz

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (arm2ReadoutCovDerivPair arm1ReadoutCovDeriv arm1ReadoutCovDeriv_center_eq arm2ReadoutCovDerivPair_center_eq partialDeriv_realizedGramDeriv_eq_half_sum_euclidPartial)
open DifferentialGeometry.Analysis.Sobolev.Chart (chartPushedRaw chartPushedRaw_apply_of_mem chartTargetEuclid chartTargetEuclid_isOpen)
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity (euclidPartial euclidPartial_def chartChristoffelEuclid chartChristoffelEuclid_def chartPushedRaw_tensorChartComponentRaw_contDiffOn)

private lemma lieCorr0_raw_readout (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (c d : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
        (I := I) (M := M) g₀ 0 2 (symmS (I := I) (M := M) g₀ (T - T')) x ![] ![c, d] x =
      realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x c d (extChartAt I x x) := by
  have hev := lieArm_scalarOnE_symmS_eventuallyEq_realizedGramDeriv (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' x c d
  have hpt := hev.self_of_nhds
  rw [DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_def] at hpt
  have hx_src : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source (I := I)]; exact mem_chart_source H x
  rw [(extChartAt I x).left_inv hx_src] at hpt
  exact hpt

namespace DeTurckRemainderTameLipschitz

lemma lieCorr0_arm1Readout_center (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (a b c : Fin (Module.finrank ℝ E)) :
    arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x
        ![a, b, c] =
      (- ∑ r : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₀ x a b r (extChartAt I x x) *
            realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r c (extChartAt I x x))
      + (- ∑ r : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₀ x a c r (extChartAt I x x) *
            realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x b r
              (extChartAt I x x)) := by
  rw [arm1ReadoutCovDeriv_center_eq (I := I) (M := M) g₀
    (symmS (I := I) (M := M) g₀ (T - T')) x a b c]
  refine congrArg₂ (fun t₁ t₂ : ℝ => t₁ + t₂) ?_ ?_
  · refine congrArg Neg.neg (Finset.sum_congr rfl (fun r _ => ?_))
    rw [lieCorr0_raw_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x r c]
  · refine congrArg Neg.neg (Finset.sum_congr rfl (fun r _ => ?_))
    rw [lieCorr0_raw_readout (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x b r]

end DeTurckRemainderTameLipschitz

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
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (m r d : Fin (Module.finrank ℝ E)) :
    euclidPartial (E := E) m
        (chartPushedRaw I x
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
            (I := I) (M := M) g₀ 0 2 (symmS (I := I) (M := M) g₀ (T - T')) x ![] ![r, d]))
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
        (I := I) (M := M) g₀ 0 2 (symmS (I := I) (M := M) g₀ (T - T')) x ![] ![r, d]))
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
          (I := I) (M := M) g₀ 0 2 (symmS (I := I) (M := M) g₀ (T - T')) x ![] ![r, d]))
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

namespace DeTurckRemainderTameLipschitz

lemma lieCorr0_R4_center (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (a b c d : Fin (Module.finrank ℝ E)) :
    arm2ReadoutCovDerivPair (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x
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
    (symmS (I := I) (M := M) g₀ (T - T')) x a b c d]
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

lemma lieCorr0_pd_christoffel_sub (gA gB : SmoothRiemannianMetric I M) (x : M)
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

lemma lieCorr0_pd_vfcomp_center (gA gB : SmoothRiemannianMetric I M) (x : M)
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

end DeTurckRemainderTameLipschitz

end LieCorr0Value

end LieCorr0Joint

end

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
