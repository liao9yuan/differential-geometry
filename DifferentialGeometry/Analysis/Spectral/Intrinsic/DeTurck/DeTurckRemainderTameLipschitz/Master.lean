import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitz.LieValue
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitz.M0Gen2

/-!
# The Lie-correction order-zero master value identity

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

set_option linter.style.setOption false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1600000

set_option synthInstance.maxHeartbeats 1600000

set_option linter.unusedSectionVars false

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (deTurckLieWEndo deTurckLieWEndo_apply deTurckLieWEndo_homSection_contMDiff deTurckLieCovDerivW connDiffOp_homSection_contMDiff metricConnDiffLoweredFib metricConnDiffLoweredFib_toModel metricConnDiffLoweredFib_contMDiff domDomCongrFibRank domDomCongrFibRank_apply tensor0SProdKappaFib tensor0SProdKappaFib_apply)

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck (cometricDoubleTraceFib cometricDoubleTraceFib_toModel cometricDoubleTraceFib_contMDiff)

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (deTurckVF_realizedFam_jointContMDiffOn metricConnDiffLowered_selfFam_jointContMDiffOn metricConnDiffLowered_bgFam_jointContMDiffOn jointTensor0SProd_local deTurckLieWEndo_realizedFam_jointContMDiffOn deTurckLieCoeffField deTurckLieCoeffField_realizedFam_jointSmooth linearizedRicciThreeArmHjoint)

open DifferentialGeometry.PDE.DeTurck.RicciLinearization (interiorProductField_jointContMDiffOn_vecJoint inverseMetricSharpField_realizedFam_jointContMDiffOn domDomCongrField_jointContMDiffOn cometricDoubleTraceFib_realizedFam_jointContMDiffOn slotInsertEndo0Field_apply_jointContMDiffOn slotInsertEndo1Field_apply_jointContMDiffOn contMDiffOn_clm_section_of_pointwise_jointMR)

open DifferentialGeometry.Integral.L2 (SmoothCcTensor)

section LieCorr0MasterValue

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open DifferentialGeometry.Integral.DivergenceTheorem (chartInvGramMatrix partialDeriv chartChristoffel chartGramOnE chartInvGramOnE chartRiemannTensor chartChristoffel_symm chartGramOnE_symm chartInvGramOnE_symm partialDeriv_chartInvGramOnE_eq extChartAt_target_subset_interior_of_boundaryless)
open DifferentialGeometry.Integral.Measure (chartGramMatrix)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (symmS unitModel unitTensor deTurckLieCoeffField arm2ReadoutCovDerivPair arm1ReadoutCovDeriv)
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
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (c d : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          (iteratedCovGrad (I := I) g₀ 0 2 0
            (symmS (I := I) (M := M) g₀ (T - T'))).toSection x)
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
    M0Abstract.chrCorrF, lc0Ig, lc0Cg, lc0Ev, lc0Pd, lc0Dg, lc0DDg, lc0Dig, lc0Ga,
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
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (gA : SmoothRiemannianMetric I M) (x : M) (i j : Fin (Module.finrank ℝ E)) :
    (∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) gA x x k₁ l *
          (arm2ReadoutCovDerivPair (I := I) (M := M) g₀
              (symmS (I := I) (M := M) g₀ (T - T')) x ![i, l, j, k₁]
            + arm2ReadoutCovDerivPair (I := I) (M := M) g₀
              (symmS (I := I) (M := M) g₀ (T - T')) x ![j, l, i, k₁]
            - arm2ReadoutCovDerivPair (I := I) (M := M) g₀
              (symmS (I := I) (M := M) g₀ (T - T')) x ![i, j, l, k₁])) =
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
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
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
    (fun a b l => rfl)
    (fun m a b l => lc0_hdgbe (I := I) g₁ x m a b l)
    i j

private lemma lc0_insert_piece (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) (i j : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel
        (lieCorr0InsertFib (I := I) g₀ g₁ g_bg x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (iteratedCovGrad (I := I) g₀ 0 2 0
              (symmS (I := I) (M := M) g₀ (T - T'))).toSection x)
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
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g₁ : SmoothRiemannianMetric I M) (x : M) (i j : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel
        (lieCorr0VBFib (I := I) g₀ g₁ x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (iteratedCovGrad (I := I) g₀ 0 2 0
              (symmS (I := I) (M := M) g₀ (T - T'))).toSection x)
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
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) (i j : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel
        (lieCorr0AMixHalfFib (I := I) g₀ g₁ g_bg x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (iteratedCovGrad (I := I) g₀ 0 2 0
              (symmS (I := I) (M := M) g₀ (T - T'))).toSection x)
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
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g₁ : SmoothRiemannianMetric I M) (x : M) (i j : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel
        (lieCorr0RiemFib (I := I) g₀ g₁ x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (iteratedCovGrad (I := I) g₀ 0 2 0
              (symmS (I := I) (M := M) g₀ (T - T'))).toSection x)
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
    M0Abstract.vfbF, lc0Ig, lc0Cg, lc0Ev, lc0Pd, lc0Dg, lc0Dig, lc0Ga, lc0DGa, lc0Gb,
    lc0DGb, lc0DDg]
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
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g_bg : SmoothRiemannianMetric I M) (s : ℝ) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ((∑ w : Fin (Module.finrank ℝ E), PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x w (extChartAt I x x) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![w, i, j])
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
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ p * (∑ q : Fin (Module.finrank ℝ E), (DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j i q (extChartAt I x x) - DifferentialGeometry.Integral.DivergenceTheorem.chartChristoffel (I := I) g₀ x j i q (extChartAt I x x)) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![q, p, k₁]))) =
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
    lc0Pd, lc0Dg, lc0Dig, lc0Ga, lc0DGa, lc0Gb, lc0DGb, lc0DDg]
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
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) (i j : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel
        (lieCorr0AMixFib (I := I) g₀ g₁ g_bg x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (iteratedCovGrad (I := I) g₀ 0 2 0
              (symmS (I := I) (M := M) g₀ (T - T'))).toSection x)
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
    Tensor0SSpace.toModel (lieCorr0TotalFib (I := I) g₀ g₁ g_bg x D)
        ![(chartModelBasis E) i, (chartModelBasis E) j] =
      Tensor0SSpace.toModel (lieCorr0InsertFib (I := I) g₀ g₁ g_bg x D)
          ![(chartModelBasis E) i, (chartModelBasis E) j]
        + Tensor0SSpace.toModel (lieCorr0VBFib (I := I) g₀ g₁ x D)
          ![(chartModelBasis E) i, (chartModelBasis E) j]
        + Tensor0SSpace.toModel (lieCorr0AMixFib (I := I) g₀ g₁ g_bg x D)
          ![(chartModelBasis E) i, (chartModelBasis E) j]
        + Tensor0SSpace.toModel (lieCorr0RiemFib (I := I) g₀ g₁ x D)
          ![(chartModelBasis E) i, (chartModelBasis E) j] := by
  rw [lieCorr0TotalFib]
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.add_apply]
  rw [Tensor0SSpace.toModel_add, Tensor0SSpace.toModel_add, Tensor0SSpace.toModel_add]
  rw [ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.add_apply,
    ContinuousMultilinearMap.add_apply]

set_option maxHeartbeats 6400000 in
private lemma lieCorr0_value_eq_order0Raw_sub_tails (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδ'_lt : δ' < 1)
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
      PDE.DeTurck.DeTurckLinearization.order0PartRaw (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x
          (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x) i j (extChartAt I x x)
        - (∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ l *
              (arm2ReadoutCovDerivPair (I := I) (M := M) g₀
                  (symmS (I := I) (M := M) g₀ (T - T')) x ![i, l, j, k₁]
                + arm2ReadoutCovDerivPair (I := I) (M := M) g₀
                  (symmS (I := I) (M := M) g₀ (T - T')) x ![j, l, i, k₁]
                - arm2ReadoutCovDerivPair (I := I) (M := M) g₀
                  (symmS (I := I) (M := M) g₀ (T - T')) x ![i, j, l, k₁]))
        - (((∑ w : Fin (Module.finrank ℝ E), PDE.DeTurck.DeTurckLinearization.chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x w (extChartAt I x x) * arm1ReadoutCovDeriv (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ (T - T')) x ![w, i, j])
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

namespace DeTurckRemainderTameLipschitz

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
lemma lieArm_chartSlope_center_value_eq_threeArm
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (x : M) (i j : Fin (Module.finrank ℝ E)) :
    lieDeTurckChartSlope (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' g_bg x i j s
        (extChartAt I x x) =
      unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2
            (deTurckLieCoeffField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
              + lieCorr0Field (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
            (iteratedCovGrad (I := I) g₀ 0 2 0 (symmS (I := I) (M := M) g₀ (T - T')))
          + appCc (I := I) (M := M) g₀ 3 2
            (deTurckLieArm1Coeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
            (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T')))
          + appCc (I := I) (M := M) g₀ 4 2
            (deTurckLieArm2PrincipalCoeff (I := I) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ (T - T')))) x
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
set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
theorem realizedDeTurckLie_threeArm_symmAbsorbed_perm_data
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ (σ'₀ : Equiv.Perm (Fin 2)) (σ'₁ : Equiv.Perm (Fin 3)) (σ'₂ : Equiv.Perm (Fin 4)),
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2
        (fun s => symmAbsorbedCoeff (I := I) (M := M) g₀ 0
          (deTurckLieCoeffField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
            + lieCorr0Field (I := I) (M := M) g₀
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
              (appCc (I := I) (M := M) g₀ 2 2
                  (symmAbsorbedCoeff (I := I) (M := M) g₀ 0
                    (deTurckLieCoeffField (I := I) (M := M) g₀
                        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
                      + lieCorr0Field (I := I) (M := M) g₀
                        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) σ'₀)
                  (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
                + appCc (I := I) (M := M) g₀ 3 2
                  (symmAbsorbedCoeff (I := I) (M := M) g₀ 1
                    (deTurckLieArm1Coeff (I := I) (M := M) g₀
                      (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) σ'₁)
                  (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
                + appCc (I := I) (M := M) g₀ 4 2
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
      (lieCorr0Phi0b_jointSmooth (I := I) g₀ T T' hδ hδ' g_bg),
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
        (appCc (I := I) (M := M) g₀ 2 2
            (deTurckLieCoeffField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
              + lieCorr0Field (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
            (iteratedCovGrad (I := I) g₀ 0 2 0 (symmS (I := I) (M := M) g₀ (T - T')))
          + appCc (I := I) (M := M) g₀ 3 2
            (deTurckLieArm1Coeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
            (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T')))
          + appCc (I := I) (M := M) g₀ 4 2
            (deTurckLieArm2PrincipalCoeff (I := I) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ (T - T')))) x
        ![(chartModelBasis E) i, (chartModelBasis E) j] := by
    intro i j
    rw [deriv_realizedFam_chartLieDeTurckComp_eq_chartSlope (I := I) g₀ T T'
      hδ_lt hδ hδ'_lt hδ' g_bg x i j hs]
    exact lieArm_chartSlope_center_value_eq_threeArm (I := I) g₀ g_bg T T'
      hδ_lt hδ hδ'_lt hδ' s x i j
  set Wbase : SmoothCcTensor g₀ 0 2 :=
    appCc (I := I) (M := M) g₀ 2 2
        (deTurckLieCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
          + lieCorr0Field (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
        (iteratedCovGrad (I := I) g₀ 0 2 0 (symmS (I := I) (M := M) g₀ (T - T')))
      + appCc (I := I) (M := M) g₀ 3 2
        (deTurckLieArm1Coeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
        (iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ (T - T')))
      + appCc (I := I) (M := M) g₀ 4 2
        (deTurckLieArm2PrincipalCoeff (I := I) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
        (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ (T - T'))) with hWbase
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
      + lieCorr0Field (I := I) (M := M) g₀
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
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
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
              (appCc (I := I) (M := M) g₀ 2 2 (Φ₀L s)
                  (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
                + appCc (I := I) (M := M) g₀ 3 2 (Φ₁L s)
                  (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
                + appCc (I := I) (M := M) g₀ 4 2 (Φ₂L s)
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  classical
  obtain ⟨_, _, _, hj0, hj1, hj2, hident⟩ :=
    realizedDeTurckLie_threeArm_symmAbsorbed_perm_data (I := I) g₀ g_bg T T'
      hδ_lt hδ hδ'_lt hδ'
  exact ⟨_, _, _, hj0, hj1, hj2, hident⟩

end DeTurckRemainderTameLipschitz

end

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
