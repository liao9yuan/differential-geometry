import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitz.Master

/-!
# Order-zero Lie-correction operator bounds, sections A-D

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

private theorem realizedDeTurckLie_threeArm_lowerOrder_residual
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
          deriv (realizedDeTurckLieChartSum (I := I) g₀ g_bg T T' hδ hδ' x (v 0) (v 1)) s =
            unitModel (I := I) (M := M) g₀ 2
              (appCc (I := I) (M := M) g₀ 2 2 (Φ₀L s)
                  (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
                + appCc (I := I) (M := M) g₀ 3 2 (Φ₁L s)
                  (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
                + appCc (I := I) (M := M) g₀ 4 2 (Φ₂L s)
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  obtain ⟨Φ₀L, Φ₁L, Φ₂L, hj0, hj1, hj2, hident⟩ :=
    realizedDeTurckLie_threeArm_covariant_identity (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
  refine ⟨Φ₀L, Φ₁L, Φ₂L, hj0, hj1, hj2, fun s hs x v => ?_⟩
  rw [(hasDerivAt_realizedDeTurckLieChartSum_general (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
    x (v 0) (v 1) hs).deriv]
  exact hident s hs x v

section LieCorr0BoundsAll

set_option linter.style.setOption false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (deTurckLieWEndo deTurckLieWEndo_apply deTurckLieWEndo_homSection_contMDiff deTurckLieCovDerivW connDiffOp_homSection_contMDiff metricConnDiffLoweredFib metricConnDiffLoweredFib_toModel metricConnDiffLoweredFib_contMDiff domDomCongrFibRank domDomCongrFibRank_apply tensor0SProdKappaFib tensor0SProdKappaFib_apply)
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck (cometricDoubleTraceFib cometricDoubleTraceFib_toModel cometricDoubleTraceFib_contMDiff)

section LieCorr0BoundsA

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable (g₀ g_bg : SmoothRiemannianMetric I M)

private theorem lc0b_fn_of_bounded (N : ℕ) (Q : ℕ → ℝ → Prop)
    (h : ∀ k, k ≤ N → ∃ c : ℝ, 0 ≤ c ∧ Q k c) :
    ∃ f : ℕ → ℝ, (∀ k, 0 ≤ f k) ∧ ∀ k, k ≤ N → Q k (f k) := by
  induction N with
  | zero =>
    obtain ⟨c, hc0, hc⟩ := h 0 le_rfl
    refine ⟨fun _ => c, fun _ => hc0, ?_⟩
    intro k hk
    rw [Nat.le_zero.mp hk]
    exact hc
  | succ N ih =>
    obtain ⟨f, hf0, hf⟩ := ih (fun k hk => h k (le_trans hk (Nat.le_succ N)))
    obtain ⟨c, hc0, hc⟩ := h (N + 1) le_rfl
    refine ⟨Function.update f (N + 1) c, ?_, ?_⟩
    · intro k
      by_cases hk : k = N + 1
      · rw [hk, Function.update_self]; exact hc0
      · rw [Function.update_of_ne hk]; exact hf0 k
    · intro k hk
      by_cases hkN : k = N + 1
      · rw [hkN, Function.update_self]; exact hc
      · rw [Function.update_of_ne hkN]
        exact hf k (by omega)

namespace DeTurckRemainderTameLipschitz

theorem lc0b_icg_smul (g : SmoothRiemannianMetric I M) (r s j : ℕ) (c : ℝ)
    (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) = c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih => rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih,
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_smul]

end DeTurckRemainderTameLipschitz

private theorem lc0b_covGrad_zero (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    covGrad (I := I) (M := M) g r s (0 : SmoothCcTensor g r s) = 0 := by
  have h := DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_smul
    (I := I) (M := M) (g := g) (r := r) (s := s) (0 : ℝ) (0 : SmoothCcTensor g r s)
  rw [zero_smul, zero_smul] at h
  exact h

namespace DeTurckRemainderTameLipschitz

theorem lc0b_normSq_icg_add_le (g : SmoothRiemannianMetric I M) (r s q : ℕ)
    (A B : SmoothCcTensor g r s) :
    ‖iteratedCovGrad (I := I) g r s q (A + B)‖ ^ 2 ≤
      2 * ‖iteratedCovGrad (I := I) g r s q A‖ ^ 2 +
        2 * ‖iteratedCovGrad (I := I) g r s q B‖ ^ 2 := by
  have htri : ‖iteratedCovGrad (I := I) g r s q (A + B)‖ ≤
      ‖iteratedCovGrad (I := I) g r s q A‖ + ‖iteratedCovGrad (I := I) g r s q B‖ := by
    rw [iteratedCovGrad_add]
    exact norm_add_le _ _
  nlinarith [htri, norm_nonneg (iteratedCovGrad (I := I) g r s q (A + B)),
    norm_nonneg (iteratedCovGrad (I := I) g r s q A),
    norm_nonneg (iteratedCovGrad (I := I) g r s q B),
    sq_nonneg (‖iteratedCovGrad (I := I) g r s q A‖ - ‖iteratedCovGrad (I := I) g r s q B‖)]

theorem lc0b_rfns_toSection_add_le (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (A B : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r s x ((A + B).toSection x) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g r s x (A.toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g r s x (B.toSection x) := by
  rw [show (A + B).toSection x = A.toSection x + B.toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  exact riemannianFiberNormSq_add_le (I := I) (M := M) g r s x _ _

theorem lc0b_normSq_eq_integral (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W : SmoothCcTensor g r s) :
    ‖W‖ ^ 2 = ∫ x, riemannianFiberNormSq (I := I) (M := M) g r s x (W.toSection x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [SmoothCcTensor.norm_def]
  exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g r s W

theorem lc0b_rfns_smul (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (c : ℝ) (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (c • v) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (c • v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v,
    TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
  ring

end DeTurckRemainderTameLipschitz

private theorem lc0b_rfns_icg_symmS_le (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (2 + j) x
        ((iteratedCovGrad (I := I) g 0 2 j (symmS (I := I) (M := M) g T)).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g 0 (2 + j) x
        ((iteratedCovGrad (I := I) g 0 2 j T).toSection x) := by
  have hsymm : iteratedCovGrad (I := I) g 0 2 j (symmS (I := I) (M := M) g T) =
      (1 / 2 : ℝ) • iteratedCovGrad (I := I) g 0 2 j T +
        (1 / 2 : ℝ) • iteratedCovGrad (I := I) g 0 2 j
          (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) T) := by
    rw [show symmS (I := I) (M := M) g T = (1 / 2 : ℝ) •
        (T + domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) T) from rfl]
    rw [lc0b_icg_smul, iteratedCovGrad_add, smul_add]
  rw [hsymm]
  have hadd : riemannianFiberNormSq (I := I) (M := M) g 0 (2 + j) x
      (((1 / 2 : ℝ) • iteratedCovGrad (I := I) g 0 2 j T +
        (1 / 2 : ℝ) • iteratedCovGrad (I := I) g 0 2 j
          (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) T)).toSection x) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g 0 (2 + j) x
        (((1 / 2 : ℝ) • iteratedCovGrad (I := I) g 0 2 j T).toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g 0 (2 + j) x
          (((1 / 2 : ℝ) • iteratedCovGrad (I := I) g 0 2 j
            (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) T)).toSection x) :=
    lc0b_rfns_toSection_add_le (I := I) (M := M) g 0 (2 + j) _ _ x
  refine le_trans hadd ?_
  have h1 : riemannianFiberNormSq (I := I) (M := M) g 0 (2 + j) x
      (((1 / 2 : ℝ) • iteratedCovGrad (I := I) g 0 2 j T).toSection x) =
      (1 / 2 : ℝ) ^ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 (2 + j) x
        ((iteratedCovGrad (I := I) g 0 2 j T).toSection x) := by
    rw [show ((1 / 2 : ℝ) • iteratedCovGrad (I := I) g 0 2 j T).toSection x =
        (1 / 2 : ℝ) • (iteratedCovGrad (I := I) g 0 2 j T).toSection x from rfl]
    exact lc0b_rfns_smul (I := I) (M := M) g 0 (2 + j) x _ _
  have h2 : riemannianFiberNormSq (I := I) (M := M) g 0 (2 + j) x
      (((1 / 2 : ℝ) • iteratedCovGrad (I := I) g 0 2 j
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) T)).toSection x) =
      (1 / 2 : ℝ) ^ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 (2 + j) x
        ((iteratedCovGrad (I := I) g 0 2 j T).toSection x) := by
    rw [show ((1 / 2 : ℝ) • iteratedCovGrad (I := I) g 0 2 j
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) T)).toSection x =
        (1 / 2 : ℝ) • (iteratedCovGrad (I := I) g 0 2 j
          (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) T)).toSection x from rfl]
    rw [lc0b_rfns_smul (I := I) (M := M) g 0 (2 + j) x _ _]
    rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g
      (Equiv.swap (0 : Fin 2) 1) T j x]
  rw [h1, h2]
  have hnn := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (2 + j) x
    ((iteratedCovGrad (I := I) g 0 2 j T).toSection x)
  nlinarith [hnn]

namespace DeTurckRemainderTameLipschitz

lemma lc0b_normSq_icg_symmS_le (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) (j : ℕ) :
    ‖iteratedCovGrad (I := I) g 0 2 j (symmS (I := I) (M := M) g T)‖ ^ 2 ≤
      ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 := by
  rw [lc0b_normSq_eq_integral, lc0b_normSq_eq_integral]
  refine MeasureTheory.integral_mono ?_ ?_
    (fun x => lc0b_rfns_icg_symmS_le (I := I) (M := M) g T j x)
  · exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g 0 (2 + j)
      (iteratedCovGrad (I := I) g 0 2 j (symmS (I := I) (M := M) g T))
  · exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g 0 (2 + j)
      (iteratedCovGrad (I := I) g 0 2 j T)

theorem lc0b_normSq_icg_raise_eq (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : SmoothCcTensor g 0 (s + 2)) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g 1 (s + 1) i
        (cometricRaiseSlot0Field (I := I) (M := M) g s W)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g 0 (s + 2) i W‖ ^ 2 := by
  rw [lc0b_normSq_eq_integral, lc0b_normSq_eq_integral]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact rfns_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g s W i x

end DeTurckRemainderTameLipschitz

private lemma lc0b_rfns_symmS_zero_le (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hbound : gFibreOpBound (I := I) (M := M) g (ccTensorBilinSymm (I := I) g T) δ)
    (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 2 x
        ((symmS (I := I) (M := M) g T).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * δ ^ 2 := by
  classical
  obtain ⟨n, e, bse, hn, hbse, horth, _hpars, _hrepr, _hsum⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  rw [rfns_rs_eq_sum_componentSq_of_basis (I := I) (M := M) g 0 2 x
    ((symmS (I := I) (M := M) g T).toSection x) e bse hnE hbse horth]
  have hcof : coframeS (I := I) (M := M) g x 0 e = fun _ : Fin 0 → Fin n =>
      unitTensor (I := I) (M := M) x := by
    funext K
    apply Tensor0SSpace.toModel_injective
    apply ContinuousMultilinearMap.ext
    intro v
    rw [show Tensor0SSpace.toModel (coframeS (I := I) (M := M) g x 0 e K) v =
        coframeS (I := I) (M := M) g x 0 e K v from rfl]
    rw [coframeS_apply (I := I) (M := M) g x 0 e K v]
    rw [show Tensor0SSpace.toModel (unitTensor (I := I) (M := M) x) v =
        unitTensor (I := I) (M := M) x v from rfl]
    rw [Fin.prod_univ_zero]
    rw [unitTensor, Tensor0SSpace.ofModel]
    rfl
  have hcomp : ∀ (K : Fin 0 → Fin n) (J : Fin 2 → Fin n),
      (fiberNormSqComponent (I := I) (M := M) g x 0 2
        ((symmS (I := I) (M := M) g T).toSection x) n e K J) ^ 2 ≤ δ ^ 2 := by
    intro K J
    have hval : fiberNormSqComponent (I := I) (M := M) g x 0 2
        ((symmS (I := I) (M := M) g T).toSection x) n e K J =
        ccTensorBilinSymm (I := I) g T x (e (J 0)) (e (J 1)) := by
      rw [show fiberNormSqComponent (I := I) (M := M) g x 0 2
          ((symmS (I := I) (M := M) g T).toSection x) n e K J =
          Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
              (symmS (I := I) (M := M) g T).toSection x)
              (coframeS (I := I) (M := M) g x 0 e K))
            (fun i : Fin 2 => (e (J i) : E)) from rfl]
      rw [hcof]
      rw [show Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (symmS (I := I) (M := M) g T).toSection x)
            (unitTensor (I := I) (M := M) x))
          (fun i : Fin 2 => (e (J i) : E)) =
          unitModel (I := I) (M := M) g 2 (symmS (I := I) (M := M) g T) x
            ![e (J 0), e (J 1)] from by
        rw [unitModel]
        refine congrArg _ ?_
        funext k
        fin_cases k <;> rfl]
      rw [show unitModel (I := I) (M := M) g 2 (symmS (I := I) (M := M) g T) x
            ![e (J 0), e (J 1)] =
          ccTensorBilin (I := I) g (symmS (I := I) (M := M) g T) x (e (J 0)) (e (J 1)) from
        unitModel_eq_ccTensorBilin_local (I := I) (M := M) g
          (symmS (I := I) (M := M) g T) x (e (J 0)) (e (J 1))]
      rw [ccTensorBilin_symmS (I := I) (M := M) g T x (e (J 0)) (e (J 1))]
    rw [hval]
    have habs := hbound x (e (J 0)) (e (J 1))
    have h00 : g.inner x (e (J 0)) (e (J 0)) = 1 := by
      rw [horth (J 0) (J 0), if_pos rfl]
    have h11 : g.inner x (e (J 1)) (e (J 1)) = 1 := by
      rw [horth (J 1) (J 1), if_pos rfl]
    rw [h00, h11, Real.sqrt_one, mul_one, mul_one] at habs
    have := abs_nonneg (ccTensorBilinSymm (I := I) g T x (e (J 0)) (e (J 1)))
    nlinarith [habs, sq_abs (ccTensorBilinSymm (I := I) g T x (e (J 0)) (e (J 1)))]
  calc (∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x 0 2
          ((symmS (I := I) (M := M) g T).toSection x) n e K J) ^ 2)
      ≤ ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n, δ ^ 2 :=
        Finset.sum_le_sum fun K _ => Finset.sum_le_sum fun J _ => hcomp K J
    _ = (Fintype.card (Fin 0 → Fin n) : ℝ) * ((Fintype.card (Fin 2 → Fin n) : ℝ) * δ ^ 2) := by
        rw [Finset.sum_const, Finset.sum_const]
        simp only [Finset.card_univ, nsmul_eq_mul]
    _ ≤ (Module.finrank ℝ E : ℝ) ^ 2 * δ ^ 2 := by
        have hc0 : (Fintype.card (Fin 0 → Fin n) : ℝ) = 1 := by simp
        have hc2 : (Fintype.card (Fin 2 → Fin n) : ℝ) = (n : ℝ) ^ 2 := by
          simp only [Fintype.card_fun, Fintype.card_fin]
          push_cast
          ring
        rw [hc0, hc2, one_mul, hnE]

namespace DeTurckRemainderTameLipschitz

theorem lc0b_WB_feed (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R : ℝ}
    {δ₀ : ℝ} (P : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
    (hPball : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) :
    (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
        ((cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (symmS (I := I) (M := M) g₀ P)).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * max δ₀ 0 ^ 2) ∧
    (∀ l : ℕ, l ≤ a →
      ‖iteratedCovGrad (I := I) g₀ 1 1 l
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (symmS (I := I) (M := M) g₀ P))‖ ^ 2 ≤ R ^ 2) := by
  constructor
  · intro x
    have h0 := rfns_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 0
      (symmS (I := I) (M := M) g₀ P) 0 x
    simp only [iteratedCovGrad_zero] at h0
    rw [h0]
    refine le_trans (lc0b_rfns_symmS_zero_le (I := I) (M := M) g₀ P hδ0 hδ x) ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hδmax : δ ≤ max δ₀ 0 := le_trans hδ_le (le_max_left _ _)
    exact pow_le_pow_left₀ hδ0 hδmax 2
  · intro l hl
    rw [lc0b_normSq_icg_raise_eq (I := I) (M := M) g₀ 0 (symmS (I := I) (M := M) g₀ P) l]
    refine le_trans (lc0b_normSq_icg_symmS_le (I := I) (M := M) g₀ P l) ?_
    have h1 := hPball l (by omega)
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2

theorem lc0b_twoArm_fn (g₀ : SmoothRiemannianMetric I M) (r₁ r₂ s₁ s₂ : ℕ) :
    ∃ C2 : ℕ → ℝ, (∀ k, 0 ≤ C2 k) ∧ ∀ k : ℕ,
      ∀ (S : SmoothCcTensor g₀ r₁ s₁) (T : SmoothCcTensor g₀ r₂ s₂)
        (ΛS ΛT : ℝ), 0 ≤ ΛS → 0 ≤ ΛT →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ r₁ s₁ x (S.toSection x) ≤ ΛS ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ r₂ s₂ x (T.toSection x) ≤ ΛT ^ 2) →
        MeasureTheory.Integrable
            (fun x => ∑ n ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ r₁ (s₁ + n) x
                  ((iteratedCovGrad (I := I) g₀ r₁ s₁ n S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ r₂ (s₂ + l) x
                      ((iteratedCovGrad (I := I) g₀ r₂ s₂ l T).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
          (∫ x, (∑ n ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ r₁ (s₁ + n) x
                  ((iteratedCovGrad (I := I) g₀ r₁ s₁ n S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ r₂ (s₂ + l) x
                      ((iteratedCovGrad (I := I) g₀ r₂ s₂ l T).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            C2 k * (ΛT ^ 2 * ∑ n ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g₀ r₁ s₁ n S‖ ^ 2
                + ΛS ^ 2 * ∑ l ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g₀ r₂ s₂ l T‖ ^ 2) := by
  have h : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g₀ r₁ s₁) (T : SmoothCcTensor g₀ r₂ s₂)
        (ΛS ΛT : ℝ), 0 ≤ ΛS → 0 ≤ ΛT →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ r₁ s₁ x (S.toSection x) ≤ ΛS ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ r₂ s₂ x (T.toSection x) ≤ ΛT ^ 2) →
        MeasureTheory.Integrable
            (fun x => ∑ n ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ r₁ (s₁ + n) x
                  ((iteratedCovGrad (I := I) g₀ r₁ s₁ n S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ r₂ (s₂ + l) x
                      ((iteratedCovGrad (I := I) g₀ r₂ s₂ l T).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
          (∫ x, (∑ n ∈ Finset.range (k + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ r₁ (s₁ + n) x
                  ((iteratedCovGrad (I := I) g₀ r₁ s₁ n S).toSection x)
                * ∑ l ∈ Finset.range (k + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ r₂ (s₂ + l) x
                      ((iteratedCovGrad (I := I) g₀ r₂ s₂ l T).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            C * (ΛT ^ 2 * ∑ n ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g₀ r₁ s₁ n S‖ ^ 2
                + ΛS ^ 2 * ∑ l ∈ Finset.range (k + 1),
                  ‖iteratedCovGrad (I := I) g₀ r₂ s₂ l T‖ ^ 2) := by
    intro k
    obtain ⟨C, hC_nn, hC⟩ :=
      exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
        (I := I) (M := M) g₀ r₁ r₂ s₁ s₂ k
    exact ⟨C, hC_nn, fun S T ΛS ΛT h1 h2 h3 h4 => hC S T ΛS ΛT h1 h2 h3 h4⟩
  choose C2 hC2_nn hC2 using h
  exact ⟨C2, hC2_nn, hC2⟩

theorem lc0b_appCcRS_normSq_le (g₀ : SmoothRiemannianMetric I M)
    (p a b : ℕ) (Φ : SmoothCcTensor g₀ a b) (W : SmoothCcTensor g₀ p a) (q : ℕ)
    (C2q ΛΦ ΛW FΦq FWq : ℝ) (hC2q : 0 ≤ C2q) (hΛΦ : 0 ≤ ΛΦ) (hΛW : 0 ≤ ΛW)
    (hΦ0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ a b x (Φ.toSection x) ≤ ΛΦ)
    (hW0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ p a x (W.toSection x) ≤ ΛW)
    (hFΦ : ∑ n ∈ Finset.range (q + 1), ‖iteratedCovGrad (I := I) g₀ a b n Φ‖ ^ 2 ≤ FΦq)
    (hFW : ∑ l ∈ Finset.range (q + 1), ‖iteratedCovGrad (I := I) g₀ p a l W‖ ^ 2 ≤ FWq)
    (htwo : ∀ (S : SmoothCcTensor g₀ a b) (T : SmoothCcTensor g₀ p a)
        (ΛS ΛT : ℝ), 0 ≤ ΛS → 0 ≤ ΛT →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ a b x (S.toSection x) ≤ ΛS ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ p a x (T.toSection x) ≤ ΛT ^ 2) →
        MeasureTheory.Integrable
            (fun x => ∑ n ∈ Finset.range (q + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ a (b + n) x
                  ((iteratedCovGrad (I := I) g₀ a b n S).toSection x)
                * ∑ l ∈ Finset.range (q + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ p (a + l) x
                      ((iteratedCovGrad (I := I) g₀ p a l T).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
          (∫ x, (∑ n ∈ Finset.range (q + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ a (b + n) x
                  ((iteratedCovGrad (I := I) g₀ a b n S).toSection x)
                * ∑ l ∈ Finset.range (q + 1 - n),
                    riemannianFiberNormSq (I := I) (M := M) g₀ p (a + l) x
                      ((iteratedCovGrad (I := I) g₀ p a l T).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            C2q * (ΛT ^ 2 * ∑ n ∈ Finset.range (q + 1),
                  ‖iteratedCovGrad (I := I) g₀ a b n S‖ ^ 2
                + ΛS ^ 2 * ∑ l ∈ Finset.range (q + 1),
                  ‖iteratedCovGrad (I := I) g₀ p a l T‖ ^ 2)) :
    ‖iteratedCovGrad (I := I) g₀ p b q (appCcRS (I := I) (M := M) g₀ p a b Φ W)‖ ^ 2 ≤
      appCcGdiag (E := E) q * (C2q * (ΛW * FΦq + ΛΦ * FWq)) := by
  have hΦ0' : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ a b x (Φ.toSection x) ≤
      (Real.sqrt ΛΦ) ^ 2 := by
    intro x
    rw [Real.sq_sqrt hΛΦ]
    exact hΦ0 x
  have hW0' : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ p a x (W.toSection x) ≤
      (Real.sqrt ΛW) ^ 2 := by
    intro x
    rw [Real.sq_sqrt hΛW]
    exact hW0 x
  obtain ⟨hgi, hgb⟩ := htwo Φ W (Real.sqrt ΛΦ) (Real.sqrt ΛW)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hΦ0' hW0'
  have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ p (b + q)
    (iteratedCovGrad (I := I) g₀ p b q (appCcRS (I := I) (M := M) g₀ p a b Φ W))
    (fun x => appCcGdiag (E := E) q *
      ∑ n ∈ Finset.range (q + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ a (b + n) x
            ((iteratedCovGrad (I := I) g₀ a b n Φ).toSection x)
          * ∑ l ∈ Finset.range (q + 1 - n),
              riemannianFiberNormSq (I := I) (M := M) g₀ p (a + l) x
                ((iteratedCovGrad (I := I) g₀ p a l W).toSection x))
    (hgi.const_mul (appCcGdiag (E := E) q))
    (fun x => rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
      (I := I) (M := M) g₀ q p a b Φ W x)
  refine le_trans hkey ?_
  rw [MeasureTheory.integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) q)
  refine le_trans hgb ?_
  refine mul_le_mul_of_nonneg_left ?_ hC2q
  rw [Real.sq_sqrt hΛΦ, Real.sq_sqrt hΛW]
  have e1 := mul_le_mul_of_nonneg_left hFΦ hΛW
  have e2 := mul_le_mul_of_nonneg_left hFW hΛΦ
  linarith [e1, e2]

end DeTurckRemainderTameLipschitz

end LieCorr0BoundsA

section LieCorr0BoundsB

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck (cometricRaiseSlot0Fib)

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

namespace DeTurckRemainderTameLipschitz

lemma lc0b_interior_product_toModel_eval (s : ℕ) (x : M) (v : TangentSpace I x)
    (D : Tensor0SSpace (s + 1) I x) (w : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x v D) w =
      Tensor0SSpace.toModel D (Fin.cons (show E from v) (fun k => (show E from w k))) := by
  have h1 : Tensor0SSpace.toModel
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x v D) =
      Tensor0SBundle.model_interior_product (𝕜 := ℝ) (E := E) s (show E from v)
        (Tensor0SSpace.toModel D) := rfl
  rw [h1]
  rfl

def lc0KappaField (g₁ gB : SmoothRiemannianMetric I M) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 3 :=
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
  ⟨fun x => metricConnDiffLoweredFib (I := I) g₁ g₁ gB x,
    metricConnDiffLoweredFib_contMDiff (I := I) g₁ g₁ gB⟩

def lc0Kappa (g₀ g₁ gB : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 3 where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ (lc0KappaField (I := I) (M := M) g₁ gB)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

lemma lc0Kappa_unitModel_apply (g₀ g₁ gB : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (lc0Kappa (I := I) (M := M) g₀ g₁ gB) x m =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ gB x (m 0) (m 1)) (m 2) := by
  rw [unitModel]
  rw [show (lc0Kappa (I := I) (M := M) g₀ g₁ gB).toSection x
      (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (lc0KappaField (I := I) (M := M) g₁ gB x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  exact metricConnDiffLoweredFib_toModel (I := I) g₁ g₁ gB x m

end DeTurckRemainderTameLipschitz

private def lc0LowFixField (g₀ gB : SmoothRiemannianMetric I M) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 3 :=
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
  ⟨fun x => metricConnDiffLoweredFib (I := I) g₀ g₀ gB x,
    metricConnDiffLoweredFib_contMDiff (I := I) g₀ g₀ gB⟩

namespace DeTurckRemainderTameLipschitz

def lc0LowFix (g₀ gB : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 3 where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ (lc0LowFixField (I := I) (M := M) g₀ gB)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

end DeTurckRemainderTameLipschitz

private lemma lc0LowFix_unitModel_apply (g₀ gB : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (lc0LowFix (I := I) (M := M) g₀ gB) x m =
      g₀.inner x (PDE.DeTurck.connDiff (I := I) g₀ gB x (m 0) (m 1)) (m 2) := by
  rw [unitModel]
  rw [show (lc0LowFix (I := I) (M := M) g₀ gB).toSection x
      (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (lc0LowFixField (I := I) (M := M) g₀ gB x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  exact metricConnDiffLoweredFib_toModel (I := I) g₀ g₀ gB x m

private def lc0PbLowField (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (gA gB : SmoothRiemannianMetric I M) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 3 :=
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
  ⟨fun x => ccBilinConnDiffLoweredFib (I := I) g₀ P gA gB x,
    ccBilinConnDiffLoweredFib_contMDiff (I := I) g₀ P gA gB⟩

namespace DeTurckRemainderTameLipschitz

def lc0PbLow (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (gA gB : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 3 where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ (lc0PbLowField (I := I) (M := M) g₀ P gA gB)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

end DeTurckRemainderTameLipschitz

private lemma lc0PbLow_unitModel_apply (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (lc0PbLow (I := I) (M := M) g₀ P gA gB) x m =
      ccTensorBilinSymm (I := I) g₀ P x
        (PDE.DeTurck.connDiff (I := I) gA gB x (m 0) (m 1)) (m 2) := by
  rw [unitModel]
  rw [show (lc0PbLow (I := I) (M := M) g₀ P gA gB).toSection x
      (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (lc0PbLowField (I := I) (M := M) g₀ P gA gB x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  exact ccBilinConnDiffLoweredFib_toModel (I := I) g₀ P gA gB x m

private lemma lc0b_connDiffLowered_unitModel_apply (g₀ g₁ : SmoothRiemannianMetric I M)
    (x : M) (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x m =
      g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) (m 1)) (m 2) := by
  rw [unitModel]
  rw [show (connDiffLoweredCc (I := I) g₀ g₁).toSection x (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (connDiffLoweredField (I := I) g₀ g₁ x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rfl

private lemma lc0b_unitModel_add (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : SmoothCcTensor g₀ 0 s) (x : M) (m : Fin s → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ s (A + B) x m =
      unitModel (I := I) (M := M) g₀ s A x m + unitModel (I := I) (M := M) g₀ s B x m := by
  rw [unitModel, unitModel, unitModel]
  rw [show ((A + B).toSection x) = A.toSection x + B.toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
      (A.toSection x + B.toSection x)) (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from A.toSection x)
          (unitTensor (I := I) (M := M) x) +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from B.toSection x)
          (unitTensor (I := I) (M := M) x) from rfl]
  rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]

namespace DeTurckRemainderTameLipschitz

theorem lc0b_kappa_decomp (g₀ g₁ gB : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w) :
    lc0Kappa (I := I) (M := M) g₀ g₁ gB =
      connDiffLoweredCc (I := I) g₀ g₁ + lc0LowFix (I := I) (M := M) g₀ gB
        + lc0PbLow (I := I) (M := M) g₀ P g₁ g₀
        + lc0PbLow (I := I) (M := M) g₀ P g₀ gB := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  apply ContinuousMultilinearMap.ext
  intro m
  rw [lc0b_unitModel_add (I := I) (M := M) g₀ 3 _ _ x m,
    lc0b_unitModel_add (I := I) (M := M) g₀ 3 _ _ x m,
    lc0b_unitModel_add (I := I) (M := M) g₀ 3 _ _ x m]
  rw [lc0Kappa_unitModel_apply (I := I) (M := M) g₀ g₁ gB x m,
    lc0b_connDiffLowered_unitModel_apply (I := I) (M := M) g₀ g₁ x m,
    lc0LowFix_unitModel_apply (I := I) (M := M) g₀ gB x m,
    lc0PbLow_unitModel_apply (I := I) (M := M) g₀ P g₁ g₀ x m,
    lc0PbLow_unitModel_apply (I := I) (M := M) g₀ P g₀ gB x m]
  rw [htie x (PDE.DeTurck.connDiff (I := I) g₁ gB x (m 0) (m 1)) (m 2)]
  rw [PDE.DeTurck.connDiff_cocycle (I := I) g₀ g₁ gB x (m 0) (m 1)]
  rw [map_add (g₀.inner x), map_add (ccTensorBilinSymm (I := I) g₀ P x)]
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply]
  ring

def lc0FixCd (g₀ gB : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 1 2 where
  toSection := (connDiffSection (I := I) g₀ gB).toSection
  hasCompactSupport := (connDiffSection (I := I) g₀ gB).hasCompactSupport

end DeTurckRemainderTameLipschitz

private lemma lc0b_connDiffSection_eq_raise_lowered (g₀ g₁ : SmoothRiemannianMetric I M) :
    connDiffSection (I := I) g₁ g₀ =
      cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
        (domDomCongrSection (I := I) g₀ (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁)) := by
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [connDiffSection_toSection, cometricRaiseSlot0Field_toSection]
  apply tensorRSSpace_ext 1 2 x
  intro om
  apply ContinuousMultilinearMap.ext
  intro YZ
  set u : TangentSpace I x := inverseMetricSharpFib (I := I) g₀ x om with hu
  set D : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (domDomCongrSection (I := I) g₀ (finRotate 3)
        (connDiffLoweredCc (I := I) g₀ g₁)).toSection x)
      (unitTensor (I := I) (M := M) x) with hDdef
  have hLHS : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        connDiffFib (I := I) g₁ g₀ x) om YZ =
      g₀.inner x u (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) := by
    rw [connDiffFib_apply_eval]
    rw [show om (fun _ : Fin 1 => PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) =
        cotangentToDual (I := I) (x := x) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) from
      (cotangentToDual_apply (I := I) om _).symm]
    rw [show cotangentToDual (I := I) (x := x) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) =
        cotangentToDualLinear (I := I) (x := x) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) from rfl]
    rw [← inverseMetricSharpFib_inner (I := I) g₀ x om
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)), ← hu]
  have hRHS : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        cometricRaiseSlot0Fib (I := I) g₀ 1 x D) om YZ =
      Tensor0SSpace.toModel D (Fin.cons (show E from u) (fun k => (show E from YZ k))) := by
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 1 x D om]
    rw [show (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (1 + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) D YZ : ℝ) =
        Tensor0SSpace.toModel
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (1 + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) D) YZ from rfl]
    rw [lc0b_interior_product_toModel_eval (I := I) (M := M) (1 + 1) x
      (inverseMetricSharpFib (I := I) g₀ x om) D YZ, ← hu]
  rw [hLHS, hRHS]
  have hum : unitModel (I := I) (M := M) g₀ 3
      (domDomCongrSection (I := I) g₀ (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁)) x =
      Tensor0SSpace.toModel D := rfl
  rw [show Tensor0SSpace.toModel D (Fin.cons (show E from u) (fun k => (show E from YZ k))) =
        unitModel (I := I) (M := M) g₀ 3
          (domDomCongrSection (I := I) g₀ (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁)) x
          ![u, YZ 0, YZ 1] from by
    rw [hum]; congr 1; funext k; fin_cases k <;> rfl]
  rw [domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i => (![u, YZ 0, YZ 1] : Fin 3 → TangentSpace I x) ((finRotate 3) i)) =
        ![YZ 0, YZ 1, u] from by
    funext i; fin_cases i <;> simp [finRotate_succ_apply]]
  rw [lc0b_connDiffLowered_unitModel_apply (I := I) (M := M) g₀ g₁ x ![YZ 0, YZ 1, u]]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  rw [g₀.symm x u (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1))]

private lemma lc0b_rfns_icg_lowered_eq_connDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (n : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g₁)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 2 n (connDiffSection (I := I) g₁ g₀)).toSection x) := by
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g₁)).toSection x)
      = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
          ((iteratedCovGrad (I := I) g₀ 0 3 n
            (domDomCongrSection (I := I) g₀ (finRotate 3)
              (connDiffLoweredCc (I := I) g₀ g₁))).toSection x) :=
        (riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
          (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁) n x).symm
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
              (domDomCongrSection (I := I) g₀ (finRotate 3)
                (connDiffLoweredCc (I := I) g₀ g₁)))).toSection x) :=
        (rfns_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 1
          (domDomCongrSection (I := I) g₀ (finRotate 3)
            (connDiffLoweredCc (I := I) g₀ g₁)) n x).symm
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n (connDiffSection (I := I) g₁ g₀)).toSection x) := by
        rw [lc0b_connDiffSection_eq_raise_lowered (I := I) (M := M) g₀ g₁]

namespace DeTurckRemainderTameLipschitz

lemma lc0b_normSq_icg_lowered_eq (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g₁)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ 1 2 n (connDiffSection (I := I) g₁ g₀)‖ ^ 2 := by
  rw [lc0b_normSq_eq_integral, lc0b_normSq_eq_integral]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact lc0b_rfns_icg_lowered_eq_connDiff (I := I) (M := M) g₀ g₁ n x

end DeTurckRemainderTameLipschitz

private lemma lc0b_pbLow_raise_eq (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M)
    (Ψc : SmoothCcTensor g₀ 1 2)
    (hΨc : ∀ x : M, Ψc.toSection x = connDiffFib (I := I) gA gB x) :
    cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
        (domDomCongrSection (I := I) g₀ (finRotate 3)
          (lc0PbLow (I := I) (M := M) g₀ P gA gB)) =
      appCcRS (I := I) (M := M) g₀ 1 1 2 Ψc
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (symmS (I := I) (M := M) g₀ P)) := by
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [cometricRaiseSlot0Field_toSection, appCcRS_toSection]
  apply tensorRSSpace_ext 1 2 x
  intro om
  apply ContinuousMultilinearMap.ext
  intro YZ
  set u : TangentSpace I x := inverseMetricSharpFib (I := I) g₀ x om with hu
  set D : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (domDomCongrSection (I := I) g₀ (finRotate 3)
        (lc0PbLow (I := I) (M := M) g₀ P gA gB)).toSection x)
      (unitTensor (I := I) (M := M) x) with hDdef
  have hLHS : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        cometricRaiseSlot0Fib (I := I) g₀ 1 x D) om YZ =
      Tensor0SSpace.toModel D (Fin.cons (show E from u) (fun k => (show E from YZ k))) := by
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 1 x D om]
    rw [show (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (1 + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) D YZ : ℝ) =
        Tensor0SSpace.toModel
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (1 + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) D) YZ from rfl]
    rw [lc0b_interior_product_toModel_eval (I := I) (M := M) (1 + 1) x
      (inverseMetricSharpFib (I := I) g₀ x om) D YZ, ← hu]
  have hLHSval : Tensor0SSpace.toModel D
      (Fin.cons (show E from u) (fun k => (show E from YZ k))) =
      ccTensorBilinSymm (I := I) g₀ P x
        (PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1)) u := by
    have hum : unitModel (I := I) (M := M) g₀ 3
        (domDomCongrSection (I := I) g₀ (finRotate 3)
          (lc0PbLow (I := I) (M := M) g₀ P gA gB)) x =
        Tensor0SSpace.toModel D := rfl
    rw [show Tensor0SSpace.toModel D
          (Fin.cons (show E from u) (fun k => (show E from YZ k))) =
        unitModel (I := I) (M := M) g₀ 3
          (domDomCongrSection (I := I) g₀ (finRotate 3)
            (lc0PbLow (I := I) (M := M) g₀ P gA gB)) x ![u, YZ 0, YZ 1] from by
      rw [hum]; congr 1; funext k; fin_cases k <;> rfl]
    rw [domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
    rw [show (fun i => (![u, YZ 0, YZ 1] : Fin 3 → TangentSpace I x) ((finRotate 3) i)) =
          ![YZ 0, YZ 1, u] from by
      funext i; fin_cases i <;> simp [finRotate_succ_apply]]
    rw [lc0PbLow_unitModel_apply (I := I) (M := M) g₀ P gA gB x ![YZ 0, YZ 1, u]]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
  have hRHS : ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        Ψc.toSection x).comp
        (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (symmS (I := I) (M := M) g₀ P)).toSection x)) om YZ =
      ccTensorBilinSymm (I := I) g₀ P x
        (PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1)) u := by
    rw [ContinuousLinearMap.comp_apply]
    set om' : Tensor0SSpace 1 I x :=
      (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (symmS (I := I) (M := M) g₀ P)).toSection x) om with hom'
    rw [hΨc x]
    rw [connDiffFib_apply_eval (I := I) gA gB x om' YZ]
    rw [show om' (fun _ : Fin 1 =>
        PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1)) =
        Tensor0SSpace.toModel om' (fun _ : Fin 1 => (show E from
          PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1))) from rfl]
    rw [hom']
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (symmS (I := I) (M := M) g₀ P)).toSection x) om) =
        cometricRaiseSlot0Fib (I := I) g₀ 0 x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (symmS (I := I) (M := M) g₀ P).toSection x)
            (unitTensor (I := I) (M := M) x)) om from by
      rw [cometricRaiseSlot0Field_toSection]]
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 0 x _ om]
    rw [show Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (0 + 1) x
          (inverseMetricSharpFib (I := I) g₀ x om)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (symmS (I := I) (M := M) g₀ P).toSection x)
            (unitTensor (I := I) (M := M) x)))
        (fun _ : Fin 1 => (show E from
          PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1))) =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (symmS (I := I) (M := M) g₀ P).toSection x)
            (unitTensor (I := I) (M := M) x))
          (Fin.cons (show E from u)
            (fun _ : Fin 1 => (show E from
              PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1)))) from by
      rw [lc0b_interior_product_toModel_eval (I := I) (M := M) (0 + 1) x
        (inverseMetricSharpFib (I := I) g₀ x om) _ _, ← hu]]
    rw [show Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          (symmS (I := I) (M := M) g₀ P).toSection x)
          (unitTensor (I := I) (M := M) x))
        (Fin.cons (show E from u)
          (fun _ : Fin 1 => (show E from
            PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1)))) =
        unitModel (I := I) (M := M) g₀ 2 (symmS (I := I) (M := M) g₀ P) x
          ![u, PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1)] from by
      rw [unitModel]
      congr 1
      funext k
      fin_cases k <;> rfl]
    rw [unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀
      (symmS (I := I) (M := M) g₀ P) x u
      (PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1))]
    rw [ccTensorBilin_symmS (I := I) (M := M) g₀ P x u
      (PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1))]
    exact ccTensorBilinSymm_symm (I := I) g₀ P x u
      (PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1))
  rw [hLHS, hLHSval]
  exact hRHS.symm

private lemma lc0b_rfns_icg_pbLow_eq (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M)
    (Ψc : SmoothCcTensor g₀ 1 2)
    (hΨc : ∀ x : M, Ψc.toSection x = connDiffFib (I := I) gA gB x) (n : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n
          (lc0PbLow (I := I) (M := M) g₀ P gA gB)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 2 n
          (appCcRS (I := I) (M := M) g₀ 1 1 2 Ψc
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
              (symmS (I := I) (M := M) g₀ P)))).toSection x) := by
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n
          (lc0PbLow (I := I) (M := M) g₀ P gA gB)).toSection x)
      = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
          ((iteratedCovGrad (I := I) g₀ 0 3 n
            (domDomCongrSection (I := I) g₀ (finRotate 3)
              (lc0PbLow (I := I) (M := M) g₀ P gA gB))).toSection x) :=
        (riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
          (finRotate 3) (lc0PbLow (I := I) (M := M) g₀ P gA gB) n x).symm
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
              (domDomCongrSection (I := I) g₀ (finRotate 3)
                (lc0PbLow (I := I) (M := M) g₀ P gA gB)))).toSection x) :=
        (rfns_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 1
          (domDomCongrSection (I := I) g₀ (finRotate 3)
            (lc0PbLow (I := I) (M := M) g₀ P gA gB)) n x).symm
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n
            (appCcRS (I := I) (M := M) g₀ 1 1 2 Ψc
              (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
                (symmS (I := I) (M := M) g₀ P)))).toSection x) := by
        rw [lc0b_pbLow_raise_eq (I := I) (M := M) g₀ P gA gB Ψc hΨc]

namespace DeTurckRemainderTameLipschitz

lemma lc0b_normSq_icg_pbLow_eq (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M)
    (Ψc : SmoothCcTensor g₀ 1 2)
    (hΨc : ∀ x : M, Ψc.toSection x = connDiffFib (I := I) gA gB x) (n : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 0 3 n (lc0PbLow (I := I) (M := M) g₀ P gA gB)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ 1 2 n
        (appCcRS (I := I) (M := M) g₀ 1 1 2 Ψc
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (symmS (I := I) (M := M) g₀ P)))‖ ^ 2 := by
  rw [lc0b_normSq_eq_integral, lc0b_normSq_eq_integral]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact lc0b_rfns_icg_pbLow_eq (I := I) (M := M) g₀ P gA gB Ψc hΨc n x

end DeTurckRemainderTameLipschitz

end LieCorr0BoundsB

section LieCorr0BoundsC

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert (gInvRaisedEndo gInvRaisedEndo_apply
  gInvRaisedEndo_eq_diff_add_id inverseMetricSharpFib_g0FlatCLM cotangentToDual_g0FlatCLM
  g0FlatCLM gInvDiffRaisedEndo)

namespace DeTurckRemainderTameLipschitz

lemma lc0b_toModel_om_single (x : M) (om : Tensor0SSpace 1 I x) (m : Fin 1 → E) :
    Tensor0SSpace.toModel om m = cotangentToDual (I := I) (x := x) om (m 0) := by
  rw [cotangentToDual_apply]
  rw [show (om (fun _ : Fin 1 => (m 0 : TangentSpace I x)) : ℝ) =
      Tensor0SSpace.toModel om (fun _ : Fin 1 => m 0) from rfl]
  congr 1
  funext k
  rw [show k = (0 : Fin 1) from Subsingleton.elim k 0]

end DeTurckRemainderTameLipschitz

private lemma lc0b_g0_inner_sharp_mixed (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (v : TangentSpace I x) :
    g₀.inner x (inverseMetricSharpFib (I := I) g₁ x om) v =
      cotangentToDual (I := I) (x := x) om (gInvRaisedEndo (I := I) g₀ g₁ x v) := by
  have h1 : ∀ w : TangentSpace I x,
      g₁.inner x (gInvRaisedEndo (I := I) g₀ g₁ x v) w = g₀.inner x v w := by
    intro w
    rw [gInvRaisedEndo_apply]
    rw [inverseMetricSharpFib_inner (I := I) g₁ x (g0FlatCLM (I := I) g₀ x v) w]
    rw [cotangentToDualLinear_apply]
    exact cotangentToDual_g0FlatCLM (I := I) g₀ x v w
  have h2 : cotangentToDual (I := I) (x := x) om (gInvRaisedEndo (I := I) g₀ g₁ x v) =
      g₁.inner x (inverseMetricSharpFib (I := I) g₁ x om)
        (gInvRaisedEndo (I := I) g₀ g₁ x v) := by
    rw [inverseMetricSharpFib_inner (I := I) g₁ x om (gInvRaisedEndo (I := I) g₀ g₁ x v)]
    rfl
  rw [h2]
  rw [g₁.symm x (inverseMetricSharpFib (I := I) g₁ x om) (gInvRaisedEndo (I := I) g₀ g₁ x v)]
  rw [h1 (inverseMetricSharpFib (I := I) g₁ x om)]
  exact g₀.symm x (inverseMetricSharpFib (I := I) g₁ x om) v

namespace DeTurckRemainderTameLipschitz

lemma lc0b_sharpFlat_eq_slotInsert_fullRaised (g₀ g₁ : SmoothRiemannianMetric I M) :
    sharpFlatEndoCc (I := I) g₀ g₁ =
      slotInsertEndoCc (I := I) (M := M) g₀ 0 (fullRaisedEndoField (I := I) (M := M) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro om
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (sharpFlatEndoCc (I := I) g₀ g₁).toSection x) om) =
      (g0FlatCLM (I := I) g₀ x) (inverseMetricSharpFib (I := I) g₁ x om) from rfl]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₁)).toSection x) om) =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (fullRaisedEndoField (I := I) (M := M) g₀ g₁ x) om from rfl]
  rw [slotInsertEndoFib_apply_eval]
  rw [lc0b_toModel_om_single (I := I) (M := M) x om
    (Function.update m 0 (fullRaisedEndoField (I := I) (M := M) g₀ g₁ x (m 0)))]
  rw [Function.update_self]
  rw [lc0b_toModel_om_single (I := I) (M := M) x
    ((g0FlatCLM (I := I) g₀ x) (inverseMetricSharpFib (I := I) g₁ x om)) m]
  rw [cotangentToDual_g0FlatCLM]
  rw [lc0b_g0_inner_sharp_mixed (I := I) (M := M) g₀ g₁ x om (m 0)]
  rw [fullRaisedEndoField_apply]

lemma lc0b_fullRaised_diff_split (g₀ g₁ : SmoothRiemannianMetric I M) :
    fullRaisedEndoField (I := I) (M := M) g₀ g₁ =
      gInvDiffRaisedEndoField (I := I) g₀ g₁ +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀ := by
  apply ContMDiffSection.ext
  intro x
  rw [show ((gInvDiffRaisedEndoField (I := I) g₀ g₁ +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀) x) =
      gInvDiffRaisedEndoField (I := I) g₀ g₁ x +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀ x from by
    rw [ContMDiffSection.coe_add]; rfl]
  apply ContinuousLinearMap.ext
  intro v
  rw [fullRaisedEndoField_apply, ContinuousLinearMap.add_apply]
  rw [show (gInvDiffRaisedEndoField (I := I) g₀ g₁ x) = gInvDiffRaisedEndo (I := I) g₀ g₁ x
    from rfl]
  rw [fullRaisedEndoField_apply]
  rw [gInvRaisedEndo_eq_diff_add_id (I := I) g₀ g₁ x v]
  rw [show gInvRaisedEndo (I := I) g₀ g₀ x v = v from by
    rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM]]

lemma lc0b_slotInsert_add (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    slotInsertEndoCc (I := I) (M := M) g₀ s (A + B) =
      slotInsertEndoCc (I := I) (M := M) g₀ s A +
        slotInsertEndoCc (I := I) (M := M) g₀ s B := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((slotInsertEndoCc (I := I) (M := M) g₀ s A +
        slotInsertEndoCc (I := I) (M := M) g₀ s B).toSection x) =
      (slotInsertEndoCc (I := I) (M := M) g₀ s A).toSection x +
        (slotInsertEndoCc (I := I) (M := M) g₀ s B).toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [ContinuousLinearMap.add_apply]
  simp only [slotInsertEndoCc_toSection]
  rw [show ((A + B) x) = A x + B x from by rw [ContMDiffSection.coe_add]; rfl]
  rw [slotInsertEndoFib_add_left, ContinuousLinearMap.add_apply]

theorem lc0b_sharpFlat_feed (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (F : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
            ((sharpFlatEndoCc (I := I) g₀ g₁).toSection x) ≤ Λ) ∧
        (∀ i : ℕ, i ≤ a →
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 1 1 q (sharpFlatEndoCc (I := I) g₀ g₁)‖ ^ 2 ≤ F i) := by
  classical
  obtain ⟨Cb, hCb_nn, hCb⟩ :=
    rfns_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨Km, hKm_nn, hKm⟩ :=
    diagonalProductGrid_riemannianFiberNormSq_integral_ballUniform
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  set IdIns : SmoothCcTensor g₀ 1 1 :=
    slotInsertEndoCc (I := I) (M := M) g₀ 0
      (fullRaisedEndoField (I := I) (M := M) g₀ g₀) with hIdIns_def
  obtain ⟨S0, hS0_nn, hS0⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 1 1 IdIns
  refine ⟨2 * Cb 0 + 2 * S0,
    fun i => ∑ q ∈ Finset.range (i + 1),
      (2 * (Cb q * Km q) + 2 * ‖iteratedCovGrad (I := I) g₀ 1 1 q IdIns‖ ^ 2),
    by have := hCb_nn 0; linarith,
    fun i => Finset.sum_nonneg fun q _ => add_nonneg
      (mul_nonneg (by norm_num) (mul_nonneg (hCb_nn q) (hKm_nn q)))
      (mul_nonneg (by norm_num) (sq_nonneg _)), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  set DiffIns : SmoothCcTensor g₀ 1 1 :=
    slotInsertEndoCc (I := I) (M := M) g₀ 0 (gInvDiffRaisedEndoField (I := I) g₀ g₁)
    with hDiffIns_def
  have hdecomp : sharpFlatEndoCc (I := I) g₀ g₁ = DiffIns + IdIns := by
    rw [lc0b_sharpFlat_eq_slotInsert_fullRaised (I := I) (M := M) g₀ g₁,
      lc0b_fullRaised_diff_split (I := I) (M := M) g₀ g₁,
      lc0b_slotInsert_add (I := I) (M := M) g₀ 0]
  refine ⟨?_, ?_⟩
  · intro x
    have hsplit : riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
        ((sharpFlatEndoCc (I := I) g₀ g₁).toSection x) ≤
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (DiffIns.toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (IdIns.toSection x) := by
      rw [hdecomp]
      exact lc0b_rfns_toSection_add_le (I := I) (M := M) g₀ 1 1 _ _ x
    have hD0 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
        (DiffIns.toSection x) ≤ Cb 0 := by
      have h2 := hCb g₁ P htie hδ_le hδ0 hδ 0 x
      simp only [iteratedCovGrad_zero] at h2
      have hgrid0 : (∑ n ∈ Finset.range (0 + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n 0,
          ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) = 1 := by
        simp
      rw [hgrid0, mul_one] at h2
      exact h2
    linarith [hsplit, hD0, hS0 x]
  · intro i hi
    refine Finset.sum_le_sum fun q hq => ?_
    have hq_le : q ≤ a := by have := Finset.mem_range.mp hq; omega
    obtain ⟨hgi, hgb⟩ := hKm P hPball q hq_le
    have hDq : ‖iteratedCovGrad (I := I) g₀ 1 1 q DiffIns‖ ^ 2 ≤ Cb q * Km q := by
      have hint : MeasureTheory.Integrable
          (fun x => Cb q *
            (∑ n ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n q,
              ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)))
          (riemannianVolumeMeasure (I := I) (M := M) g₀) := hgi.const_mul _
      have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀
        1 (1 + q) (iteratedCovGrad (I := I) g₀ 1 1 q DiffIns) _ hint
        (fun x => hCb g₁ P htie hδ_le hδ0 hδ q x)
      refine le_trans hkey ?_
      rw [MeasureTheory.integral_const_mul]
      exact mul_le_mul_of_nonneg_left hgb (hCb_nn q)
    have htri : ‖iteratedCovGrad (I := I) g₀ 1 1 q (sharpFlatEndoCc (I := I) g₀ g₁)‖ ≤
        ‖iteratedCovGrad (I := I) g₀ 1 1 q DiffIns‖ +
          ‖iteratedCovGrad (I := I) g₀ 1 1 q IdIns‖ := by
      rw [hdecomp, iteratedCovGrad_add]
      exact norm_add_le _ _
    nlinarith [htri, hDq,
      norm_nonneg (iteratedCovGrad (I := I) g₀ 1 1 q DiffIns),
      norm_nonneg (iteratedCovGrad (I := I) g₀ 1 1 q IdIns),
      norm_nonneg (iteratedCovGrad (I := I) g₀ 1 1 q (sharpFlatEndoCc (I := I) g₀ g₁)),
      sq_nonneg (‖iteratedCovGrad (I := I) g₀ 1 1 q DiffIns‖ -
        ‖iteratedCovGrad (I := I) g₀ 1 1 q IdIns‖)]

theorem lc0b_cds_feed (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (F : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
            ((connDiffSection (I := I) g₁ g₀).toSection x) ≤ Λ) ∧
        (∀ i : ℕ, i ≤ a →
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 1 2 q (connDiffSection (I := I) g₁ g₀)‖ ^ 2 ≤ F i) := by
  classical
  obtain ⟨ΛK, FK, hΛK_nn, hFK_nn, hK⟩ :=
    raisedKoszul_order0sup_jetL2_ballUniform_generic (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨Λsf, Fsf, hΛsf_nn, hFsf_nn, hsf⟩ :=
    lc0b_sharpFlat_feed (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨C2, hC2_nn, hC2⟩ := lc0b_twoArm_fn (I := I) (M := M) g₀ 1 1 2 1
  refine ⟨ΛK ^ 2 * Λsf,
    fun i => ∑ q ∈ Finset.range (i + 1),
      appCcGdiag (E := E) q * (C2 q * (Λsf * FK q + ΛK ^ 2 * Fsf q)),
    mul_nonneg (sq_nonneg _) hΛsf_nn,
    fun i => Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
      (mul_nonneg (hC2_nn q) (add_nonneg (mul_nonneg hΛsf_nn (hFK_nn q))
        (mul_nonneg (sq_nonneg _) (hFsf_nn q)))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  obtain ⟨hKsup, hKsum⟩ := hK g₁ P hδ_le hδ htie hPball
  obtain ⟨hsfsup, hsfsum⟩ := hsf g₁ P htie hδ_le hδ0 hδ hPball
  have hid : connDiffSection (I := I) g₁ g₀ =
      appCcRS (I := I) (M := M) g₀ 1 1 2 (raisedKoszul (I := I) g₀ g₁)
        (sharpFlatEndoCc (I := I) g₀ g₁) :=
    connDiffSection_eq_appCcRS_raisedKoszul_sharpFlatEndoCc (I := I) (M := M) g₀ g₁
  refine ⟨?_, ?_⟩
  · intro x
    rw [hid, appCcRS_toSection]
    refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 1 1 2 x
      (show TensorRSSpace 1 2 I x from (raisedKoszul (I := I) g₀ g₁).toSection x)
      (show TensorRSSpace 1 1 I x from (sharpFlatEndoCc (I := I) g₀ g₁).toSection x)) ?_
    exact mul_le_mul (hKsup x) (hsfsup x)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 1 x _) (sq_nonneg ΛK)
  · intro i hi
    refine Finset.sum_le_sum fun q hq => ?_
    have hq_le : q ≤ a := by have := Finset.mem_range.mp hq; omega
    rw [hid]
    exact lc0b_appCcRS_normSq_le (I := I) (M := M) g₀ 1 1 2
      (raisedKoszul (I := I) g₀ g₁) (sharpFlatEndoCc (I := I) g₀ g₁) q
      (C2 q) (ΛK ^ 2) Λsf (FK q) (Fsf q)
      (hC2_nn q) (sq_nonneg ΛK) hΛsf_nn hKsup hsfsup (hKsum q hq_le) (hsfsum q hq_le)
      (hC2 q)

theorem lc0b_kappa_feed (g₀ gB : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (F : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
            ((lc0Kappa (I := I) (M := M) g₀ g₁ gB).toSection x) ≤ Λ) ∧
        (∀ i : ℕ, i ≤ a →
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 3 q
              (lc0Kappa (I := I) (M := M) g₀ g₁ gB)‖ ^ 2 ≤ F i) := by
  classical
  obtain ⟨Λcd, Fcd, hΛcd_nn, hFcd_nn, hcd⟩ :=
    lc0b_cds_feed (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨Λlow, hΛlow_nn, hΛlow⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 0 3
      (lc0LowFix (I := I) (M := M) g₀ gB)
  obtain ⟨Λfx, hΛfx_nn, hΛfx⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 1 2
      (lc0FixCd (I := I) (M := M) g₀ gB)
  obtain ⟨C2b, hC2b_nn, hC2b⟩ := lc0b_twoArm_fn (I := I) (M := M) g₀ 1 1 2 1
  set nQ : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * max δ₀ 0 ^ 2 with hnQ_def
  have hnQ_nn : 0 ≤ nQ := by rw [hnQ_def]; positivity
  set FB : ℕ → ℝ := fun i => ∑ q ∈ Finset.range (i + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 3 q (lc0LowFix (I := I) (M := M) g₀ gB)‖ ^ 2
    with hFB_def
  have hFB_nn : ∀ i, 0 ≤ FB i := fun i => Finset.sum_nonneg fun q _ => sq_nonneg _
  set Ffx : ℕ → ℝ := fun q => ∑ l ∈ Finset.range (q + 1),
    ‖iteratedCovGrad (I := I) g₀ 1 2 l (lc0FixCd (I := I) (M := M) g₀ gB)‖ ^ 2
    with hFfx_def
  have hFfx_nn : ∀ q, 0 ≤ Ffx q := fun q => Finset.sum_nonneg fun l _ => sq_nonneg _
  set FC : ℕ → ℝ := fun i => ∑ q ∈ Finset.range (i + 1),
    appCcGdiag (E := E) q * (C2b q * (nQ * Fcd q + Λcd * (((q : ℝ) + 1) * R ^ 2)))
    with hFC_def
  have hFC_nn : ∀ i, 0 ≤ FC i := by
    intro i
    refine Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
      (mul_nonneg (hC2b_nn q) (add_nonneg (mul_nonneg hnQ_nn (hFcd_nn q))
        (mul_nonneg hΛcd_nn (by positivity))))
  set FD : ℕ → ℝ := fun i => ∑ q ∈ Finset.range (i + 1),
    appCcGdiag (E := E) q * (C2b q * (nQ * Ffx q + Λfx * (((q : ℝ) + 1) * R ^ 2)))
    with hFD_def
  have hFD_nn : ∀ i, 0 ≤ FD i := by
    intro i
    refine Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
      (mul_nonneg (hC2b_nn q) (add_nonneg (mul_nonneg hnQ_nn (hFfx_nn q))
        (mul_nonneg hΛfx_nn (by positivity))))
  refine ⟨8 * Λcd + 8 * Λlow + 4 * (Λcd * nQ) + 2 * (Λfx * nQ),
    fun i => 8 * Fcd i + 8 * FB i + 4 * FC i + 2 * FD i,
    by
      have e1 := mul_nonneg hΛcd_nn hnQ_nn
      have e2 := mul_nonneg hΛfx_nn hnQ_nn
      linarith [hΛcd_nn, hΛlow_nn, e1, e2],
    fun i => by
      have := hFcd_nn i
      have := hFB_nn i
      have := hFC_nn i
      have := hFD_nn i
      linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  obtain ⟨hWB0, hWBL2⟩ :=
    lc0b_WB_feed (I := I) (M := M) g₀ a P hδ_le hδ0 hδ hPball
  obtain ⟨hcd0, hcdL2⟩ := hcd g₁ P htie hδ_le hδ0 hδ hPball
  have hκeq := lc0b_kappa_decomp (I := I) (M := M) g₀ g₁ gB P htie
  have hΨcC : ∀ x : M, (connDiffSection (I := I) g₁ g₀).toSection x =
      connDiffFib (I := I) g₁ g₀ x := fun x => rfl
  have hΨcD : ∀ x : M, (lc0FixCd (I := I) (M := M) g₀ gB).toSection x =
      connDiffFib (I := I) g₀ gB x := fun x => rfl
  have hWBsum : ∀ q : ℕ, q ≤ a →
      ∑ l ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 1 1 l
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (symmS (I := I) (M := M) g₀ P))‖ ^ 2 ≤ ((q : ℝ) + 1) * R ^ 2 := by
    intro q hq
    refine le_trans (Finset.sum_le_sum fun l hl =>
      hWBL2 l (le_trans (by have := Finset.mem_range.mp hl; omega : l ≤ q) hq)) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    exact le_refl _
  refine ⟨?_, ?_⟩
  · intro x
    have hsec : (lc0Kappa (I := I) (M := M) g₀ g₁ gB).toSection x =
        ((connDiffLoweredCc (I := I) g₀ g₁ + lc0LowFix (I := I) (M := M) g₀ gB
          + lc0PbLow (I := I) (M := M) g₀ P g₁ g₀
          + lc0PbLow (I := I) (M := M) g₀ P g₀ gB).toSection x) := by
      rw [hκeq]
    rw [hsec]
    have h1 := lc0b_rfns_toSection_add_le (I := I) (M := M) g₀ 0 3
      (connDiffLoweredCc (I := I) g₀ g₁ + lc0LowFix (I := I) (M := M) g₀ gB
        + lc0PbLow (I := I) (M := M) g₀ P g₁ g₀)
      (lc0PbLow (I := I) (M := M) g₀ P g₀ gB) x
    have h2 := lc0b_rfns_toSection_add_le (I := I) (M := M) g₀ 0 3
      (connDiffLoweredCc (I := I) g₀ g₁ + lc0LowFix (I := I) (M := M) g₀ gB)
      (lc0PbLow (I := I) (M := M) g₀ P g₁ g₀) x
    have h3 := lc0b_rfns_toSection_add_le (I := I) (M := M) g₀ 0 3
      (connDiffLoweredCc (I := I) g₀ g₁) (lc0LowFix (I := I) (M := M) g₀ gB) x
    have hA0 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
        ((connDiffLoweredCc (I := I) g₀ g₁).toSection x) ≤ Λcd := by
      have h := lc0b_rfns_icg_lowered_eq_connDiff (I := I) (M := M) g₀ g₁ 0 x
      simp only [iteratedCovGrad_zero] at h
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
            ((connDiffLoweredCc (I := I) g₀ g₁).toSection x)
          = riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
              ((connDiffSection (I := I) g₁ g₀).toSection x) := h
        _ ≤ Λcd := hcd0 x
    have hB0 := hΛlow x
    have hC0 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
        ((lc0PbLow (I := I) (M := M) g₀ P g₁ g₀).toSection x) ≤ Λcd * nQ := by
      have h := lc0b_rfns_icg_pbLow_eq (I := I) (M := M) g₀ P g₁ g₀
        (connDiffSection (I := I) g₁ g₀) hΨcC 0 x
      simp only [iteratedCovGrad_zero] at h
      rw [h, appCcRS_toSection]
      refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 1 1 2 x
        (show TensorRSSpace 1 2 I x from (connDiffSection (I := I) g₁ g₀).toSection x)
        (show TensorRSSpace 1 1 I x from
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (symmS (I := I) (M := M) g₀ P)).toSection x)) ?_
      exact mul_le_mul (hcd0 x) (hWB0 x)
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 1 x _) hΛcd_nn
    have hD0 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
        ((lc0PbLow (I := I) (M := M) g₀ P g₀ gB).toSection x) ≤ Λfx * nQ := by
      have h := lc0b_rfns_icg_pbLow_eq (I := I) (M := M) g₀ P g₀ gB
        (lc0FixCd (I := I) (M := M) g₀ gB) hΨcD 0 x
      simp only [iteratedCovGrad_zero] at h
      rw [h, appCcRS_toSection]
      refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 1 1 2 x
        (show TensorRSSpace 1 2 I x from
          (lc0FixCd (I := I) (M := M) g₀ gB).toSection x)
        (show TensorRSSpace 1 1 I x from
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (symmS (I := I) (M := M) g₀ P)).toSection x)) ?_
      exact mul_le_mul (hΛfx x) (hWB0 x)
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 1 x _) hΛfx_nn
    linarith [h1, h2, h3, hA0, hB0, hC0, hD0]
  · intro i hi
    have hstep : ∀ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 3 q
          (lc0Kappa (I := I) (M := M) g₀ g₁ gB)‖ ^ 2 ≤
        8 * ‖iteratedCovGrad (I := I) g₀ 0 3 q (connDiffLoweredCc (I := I) g₀ g₁)‖ ^ 2 +
          8 * ‖iteratedCovGrad (I := I) g₀ 0 3 q (lc0LowFix (I := I) (M := M) g₀ gB)‖ ^ 2 +
          4 * ‖iteratedCovGrad (I := I) g₀ 0 3 q
            (lc0PbLow (I := I) (M := M) g₀ P g₁ g₀)‖ ^ 2 +
          2 * ‖iteratedCovGrad (I := I) g₀ 0 3 q
            (lc0PbLow (I := I) (M := M) g₀ P g₀ gB)‖ ^ 2 := by
      intro q _
      have hnorm : ‖iteratedCovGrad (I := I) g₀ 0 3 q
          (lc0Kappa (I := I) (M := M) g₀ g₁ gB)‖ ^ 2 =
          ‖iteratedCovGrad (I := I) g₀ 0 3 q
            (connDiffLoweredCc (I := I) g₀ g₁ + lc0LowFix (I := I) (M := M) g₀ gB
              + lc0PbLow (I := I) (M := M) g₀ P g₁ g₀
              + lc0PbLow (I := I) (M := M) g₀ P g₀ gB)‖ ^ 2 := by
        rw [hκeq]
      rw [hnorm]
      have k1 := lc0b_normSq_icg_add_le (I := I) (M := M) g₀ 0 3 q
        (connDiffLoweredCc (I := I) g₀ g₁ + lc0LowFix (I := I) (M := M) g₀ gB
          + lc0PbLow (I := I) (M := M) g₀ P g₁ g₀)
        (lc0PbLow (I := I) (M := M) g₀ P g₀ gB)
      have k2 := lc0b_normSq_icg_add_le (I := I) (M := M) g₀ 0 3 q
        (connDiffLoweredCc (I := I) g₀ g₁ + lc0LowFix (I := I) (M := M) g₀ gB)
        (lc0PbLow (I := I) (M := M) g₀ P g₁ g₀)
      have k3 := lc0b_normSq_icg_add_le (I := I) (M := M) g₀ 0 3 q
        (connDiffLoweredCc (I := I) g₀ g₁) (lc0LowFix (I := I) (M := M) g₀ gB)
      linarith [k1, k2, k3]
    refine le_trans (Finset.sum_le_sum hstep) ?_
    have hsplit : ∑ q ∈ Finset.range (i + 1),
        (8 * ‖iteratedCovGrad (I := I) g₀ 0 3 q (connDiffLoweredCc (I := I) g₀ g₁)‖ ^ 2 +
          8 * ‖iteratedCovGrad (I := I) g₀ 0 3 q (lc0LowFix (I := I) (M := M) g₀ gB)‖ ^ 2 +
          4 * ‖iteratedCovGrad (I := I) g₀ 0 3 q
            (lc0PbLow (I := I) (M := M) g₀ P g₁ g₀)‖ ^ 2 +
          2 * ‖iteratedCovGrad (I := I) g₀ 0 3 q
            (lc0PbLow (I := I) (M := M) g₀ P g₀ gB)‖ ^ 2) =
        8 * ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 3 q (connDiffLoweredCc (I := I) g₀ g₁)‖ ^ 2 +
          8 * ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 3 q
              (lc0LowFix (I := I) (M := M) g₀ gB)‖ ^ 2 +
          4 * ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 3 q
              (lc0PbLow (I := I) (M := M) g₀ P g₁ g₀)‖ ^ 2 +
          2 * ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 3 q
              (lc0PbLow (I := I) (M := M) g₀ P g₀ gB)‖ ^ 2 := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hsplit]
    have hBsum : ∑ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 3 q
          (lc0LowFix (I := I) (M := M) g₀ gB)‖ ^ 2 ≤ FB i := le_rfl
    have hAsum : ∑ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 3 q (connDiffLoweredCc (I := I) g₀ g₁)‖ ^ 2 ≤ Fcd i := by
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun q _ =>
        lc0b_normSq_icg_lowered_eq (I := I) (M := M) g₀ g₁ q)) ?_
      exact hcdL2 i hi
    have hCsum : ∑ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 3 q
          (lc0PbLow (I := I) (M := M) g₀ P g₁ g₀)‖ ^ 2 ≤ FC i := by
      rw [hFC_def]
      refine Finset.sum_le_sum fun q hq => ?_
      have hq_le : q ≤ a := by have := Finset.mem_range.mp hq; omega
      rw [lc0b_normSq_icg_pbLow_eq (I := I) (M := M) g₀ P g₁ g₀
        (connDiffSection (I := I) g₁ g₀) hΨcC q]
      exact lc0b_appCcRS_normSq_le (I := I) (M := M) g₀ 1 1 2
        (connDiffSection (I := I) g₁ g₀)
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0 (symmS (I := I) (M := M) g₀ P)) q
        (C2b q) Λcd nQ (Fcd q) (((q : ℝ) + 1) * R ^ 2)
        (hC2b_nn q) hΛcd_nn hnQ_nn hcd0 hWB0 (hcdL2 q hq_le) (hWBsum q hq_le)
        (hC2b q)
    have hDsum : ∑ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 3 q
          (lc0PbLow (I := I) (M := M) g₀ P g₀ gB)‖ ^ 2 ≤ FD i := by
      rw [hFD_def]
      refine Finset.sum_le_sum fun q hq => ?_
      have hq_le : q ≤ a := by have := Finset.mem_range.mp hq; omega
      rw [lc0b_normSq_icg_pbLow_eq (I := I) (M := M) g₀ P g₀ gB
        (lc0FixCd (I := I) (M := M) g₀ gB) hΨcD q]
      refine lc0b_appCcRS_normSq_le (I := I) (M := M) g₀ 1 1 2
        (lc0FixCd (I := I) (M := M) g₀ gB)
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0 (symmS (I := I) (M := M) g₀ P)) q
        (C2b q) Λfx nQ (Ffx q) (((q : ℝ) + 1) * R ^ 2)
        (hC2b_nn q) hΛfx_nn hnQ_nn hΛfx hWB0 le_rfl (hWBsum q hq_le)
        (hC2b q)
    linarith [hAsum, hCsum, hDsum, hBsum]

end DeTurckRemainderTameLipschitz

end LieCorr0BoundsC

section LieCorr0BoundsD

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert (gInvRaisedEndo gInvRaisedEndo_apply
  g0FlatCLM cotangentToDual_g0FlatCLM)
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck (cometricDoubleTraceField
  cometricDoubleTraceField_covGrad_eq_zero modelDoubleTrace_apply cometricLmodel
  cometric_dualTrace_eq_orthoFrame_diag)

namespace DeTurckRemainderTameLipschitz

theorem lc0b_fixedField_rfns_jet (g₀ : SmoothRiemannianMetric I M)
    (r s : ℕ) (F : SmoothCcTensor g₀ r s) :
    ∃ c : ℕ → ℝ, (∀ j, 0 ≤ c j) ∧ ∀ (j : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + j) x
        ((iteratedCovGrad (I := I) g₀ r s j F).toSection x) ≤ c j := by
  have h : ∀ j : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + j) x
        ((iteratedCovGrad (I := I) g₀ r s j F).toSection x) ≤ c := fun j =>
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ r (s + j)
      (iteratedCovGrad (I := I) g₀ r s j F)
  choose c hc0 hc using h
  exact ⟨c, hc0, fun j x => hc j x⟩

theorem lc0b_normSq_le_scaled_of_pointwise (g₀ : SmoothRiemannianMetric I M)
    (r₁ s₁ r₂ s₂ : ℕ) (X : SmoothCcTensor g₀ r₁ s₁) (Y : SmoothCcTensor g₀ r₂ s₂)
    (c : ℝ) (hc : 0 ≤ c)
    (hpt : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ r₁ s₁ x (X.toSection x) ≤
      c * riemannianFiberNormSq (I := I) (M := M) g₀ r₂ s₂ x (Y.toSection x)) :
    ‖X‖ ^ 2 ≤ c * ‖Y‖ ^ 2 := by
  rw [lc0b_normSq_eq_integral, lc0b_normSq_eq_integral]
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_mono ?_ ?_ hpt
  · exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ r₁ s₁ X
  · exact (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ r₂ s₂ Y).const_mul c

end DeTurckRemainderTameLipschitz

private lemma lc0b_icg_succ_cometricDT_zero (g₀ : SmoothRiemannianMetric I M) (s m : ℕ) :
    iteratedCovGrad (I := I) g₀ (s + 2) s (m + 1)
      (cometricDoubleTraceField (I := I) g₀ s) = 0 := by
  induction m with
  | zero =>
      rw [iteratedCovGrad_succ, iteratedCovGrad_zero]
      exact cometricDoubleTraceField_covGrad_eq_zero (I := I) g₀ s
  | succ m' ih =>
      rw [iteratedCovGrad_succ, ih, lc0b_covGrad_zero]

namespace DeTurckRemainderTameLipschitz

lemma lc0b_toModel_cons_sum_smul (x : M) {n : ℕ}
    (Zm : Tensor0SModel (n + 1) ℝ E) (d : ℕ) (t : Fin d → ℝ)
    (u : Fin d → E) (rest : Fin n → E) :
    Zm (Fin.cons (∑ c, t c • u c) rest) =
      ∑ c, t c * Zm (Fin.cons (u c) rest) := by
  classical
  have h1 : ∀ v : E, (Fin.cons v rest : Fin (n + 1) → E) =
      Function.update (Fin.cons (0 : E) rest) 0 v := by
    intro v
    rw [Fin.update_cons_zero]
  have hgen : ∀ ss : Finset (Fin d),
      Zm (Function.update (Fin.cons (0 : E) rest) 0 (∑ c ∈ ss, t c • u c)) =
        ∑ c ∈ ss, t c * Zm (Function.update (Fin.cons (0 : E) rest) 0 (u c)) := by
    intro ss
    induction ss using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        rw [show (0 : E) = ((0 : ℝ) • (0 : E)) from (zero_smul ℝ (0 : E)).symm]
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [zero_smul]
    | @insert a ss ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        rw [ContinuousMultilinearMap.map_update_add]
        rw [ih]
        congr 1
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [smul_eq_mul]
  have h2 := hgen Finset.univ
  rw [h1, h2]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← h1 (u c)]

end DeTurckRemainderTameLipschitz

private lemma lc0b_toModel_cons_cons_sum_smul (x : M) {n : ℕ}
    (Zm : Tensor0SModel (n + 2) ℝ E) (aa : E) (d : ℕ) (t : Fin d → ℝ)
    (u : Fin d → E) (rest : Fin n → E) :
    Zm (Fin.cons aa (Fin.cons (∑ c, t c • u c) rest)) =
      ∑ c, t c * Zm (Fin.cons aa (Fin.cons (u c) rest)) := by
  classical
  have h1 : ∀ v : E, (Fin.cons aa (Fin.cons v rest) : Fin (n + 2) → E) =
      Function.update (Fin.cons aa (Fin.cons (0 : E) rest)) 1 v := by
    intro v
    rw [show (1 : Fin (n + 2)) = Fin.succ 0 from rfl]
    rw [← Fin.cons_update]
    rw [Fin.update_cons_zero]
  have hgen : ∀ ss : Finset (Fin d),
      Zm (Function.update (Fin.cons aa (Fin.cons (0 : E) rest)) 1 (∑ c ∈ ss, t c • u c)) =
        ∑ c ∈ ss, t c * Zm (Function.update (Fin.cons aa (Fin.cons (0 : E) rest)) 1 (u c)) := by
    intro ss
    induction ss using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        rw [show (0 : E) = ((0 : ℝ) • (0 : E)) from (zero_smul ℝ (0 : E)).symm]
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [zero_smul]
    | @insert a ss ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        rw [ContinuousMultilinearMap.map_update_add]
        rw [ih]
        congr 1
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [smul_eq_mul]
  have h2 := hgen Finset.univ
  rw [h1, h2]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← h1 (u c)]

namespace DeTurckRemainderTameLipschitz

lemma lc0b_orthoFrame_center_repr (g : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    v = ∑ i : Fin (Module.finrank ℝ E),
      g.inner x (smoothOrthoFrame (I := I) g x i x) v • smoothOrthoFrame (I := I) g x i x := by
  classical
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  haveI : Nonempty (Fin (Module.finrank ℝ E)) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))⟩⟩
  set B : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g x i x with hB_def
  have horth : ∀ i j, g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  have hlin : LinearIndependent ℝ B := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have hpair : g.inner x (∑ i, c i • B i) (B j) = 0 := by
      rw [hc]
      simp
    rw [map_sum, ContinuousLinearMap.sum_apply] at hpair
    have hsimp : ∀ i, g.inner x (c i • B i) (B j) = c i * (if i = j then (1 : ℝ) else 0) := by
      intro i
      rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, horth i j]
    rw [Finset.sum_congr rfl (fun i _ => hsimp i)] at hpair
    have hcol : (∑ i, c i * (if i = j then (1 : ℝ) else 0)) = c j := by simp
    rw [hcol] at hpair
    exact hpair
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) =
      Module.finrank ℝ (TangentSpace I x) := by
    rw [Fintype.card_fin]
    rfl
  set bB : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    basisOfLinearIndependentOfCardEqFinrank hlin hcard with hbB_def
  have hbB_coe : ∀ i, bB i = B i := by
    intro i
    rw [hbB_def]
    change (basisOfLinearIndependentOfCardEqFinrank hlin hcard :
        Fin (Module.finrank ℝ E) → TangentSpace I x) i = B i
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  have hrepr : ∀ (w : TangentSpace I x) (j : Fin (Module.finrank ℝ E)),
      bB.repr w j = g.inner x (B j) w := by
    intro w j
    conv_rhs => rw [← bB.sum_repr w]
    rw [map_sum]
    have hsimp : ∀ i, g.inner x (B j) (bB.repr w i • bB i) =
        bB.repr w i * (if j = i then (1 : ℝ) else 0) := by
      intro i
      rw [map_smul, smul_eq_mul, hbB_coe i, horth j i]
    rw [Finset.sum_congr rfl (fun i _ => hsimp i)]
    simp
  conv_lhs => rw [← bB.sum_repr v]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hrepr v i, hbB_coe i]

end DeTurckRemainderTameLipschitz

private lemma lc0b_g1_inner_gInvRaisedEndo_left (g₀ g₁ : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    g₁.inner x (gInvRaisedEndo (I := I) g₀ g₁ x v) w = g₀.inner x v w := by
  rw [gInvRaisedEndo_apply]
  rw [inverseMetricSharpFib_inner (I := I) g₁ x (g0FlatCLM (I := I) g₀ x v) w]
  rw [cotangentToDualLinear_apply]
  exact cotangentToDual_g0FlatCLM (I := I) g₀ x v w

namespace DeTurckRemainderTameLipschitz

def lc0PureDT (g₀ g₁ : SmoothRiemannianMetric I M) (s : ℕ) :
    SmoothCcTensor g₀ (s + 2) s where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace (s + 2) s I x from cometricDoubleTraceFib (I := I) g₁ s x)
      contMDiff_toFun := cometricDoubleTraceFib_contMDiff (I := I) g₁ s }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option maxHeartbeats 12800000 in
lemma lc0PureDT_eq_trace_fullRaised (g₀ g₁ : SmoothRiemannianMetric I M)
    (s : ℕ) :
    lc0PureDT (I := I) (M := M) g₀ g₁ s =
      appCcRS (I := I) (M := M) g₀ (s + 2) (s + 2) s
        (cometricDoubleTraceField (I := I) g₀ s)
        (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
          (fullRaisedEndoField (I := I) (M := M) g₀ g₁)) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro Z
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro mm
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
        (lc0PureDT (I := I) (M := M) g₀ g₁ s).toSection x) Z) mm =
      ∑ c : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel Z
          (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E) mm)) := by
    rw [show ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
        (lc0PureDT (I := I) (M := M) g₀ g₁ s).toSection x) Z) =
        cometricDoubleTraceFib (I := I) g₁ s x Z from rfl]
    rw [cometricDoubleTraceFib_toModel (I := I) g₁ s x Z]
    rw [modelDoubleTrace_apply (E := E) s (cometricLmodel (I := I) g₁ x)]
    rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₁ x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x) (Tensor0SSpace.toModel Z) mm]
  rw [hLHS]
  have hRHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
        (appCcRS (I := I) (M := M) g₀ (s + 2) (s + 2) s
          (cometricDoubleTraceField (I := I) g₀ s)
          (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) Z) mm =
      ∑ a : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel Z
          (Fin.cons (show E from gInvRaisedEndo (I := I) g₀ g₁ x
              (smoothOrthoFrame (I := I) g₀ x a x))
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)) := by
    rw [show ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
        (appCcRS (I := I) (M := M) g₀ (s + 2) (s + 2) s
          (cometricDoubleTraceField (I := I) g₀ s)
          (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) Z) =
        cometricDoubleTraceFib (I := I) g₀ s x
          (slotInsertEndoFib (I := I) (M := M) (s + 2) 0 x
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁ x) Z) from by
      rw [appCcRS_toSection]
      rfl]
    rw [cometricDoubleTraceFib_toModel (I := I) g₀ s x]
    rw [modelDoubleTrace_apply (E := E) s (cometricLmodel (I := I) g₀ x)]
    rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₀ x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
      (Tensor0SSpace.toModel
        (slotInsertEndoFib (I := I) (M := M) (s + 2) 0 x
          (fullRaisedEndoField (I := I) (M := M) g₀ g₁ x) Z)) mm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [slotInsertEndoFib_apply_eval]
    rw [Fin.update_cons_zero]
    rfl
  rw [hRHS]
  have hGrep : ∀ a : Fin (Module.finrank ℝ E),
      (show E from gInvRaisedEndo (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x)) =
        ∑ c : Fin (Module.finrank ℝ E),
          (g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x) (smoothOrthoFrame (I := I) g₁ x c x)) •
            (smoothOrthoFrame (I := I) g₁ x c x : E) := by
    intro a
    have h1 := lc0b_orthoFrame_center_repr (I := I) (M := M) g₁ x
      (gInvRaisedEndo (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x))
    rw [show (show E from gInvRaisedEndo (I := I) g₀ g₁ x
        (smoothOrthoFrame (I := I) g₀ x a x)) =
        gInvRaisedEndo (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x) from rfl]
    conv_lhs => rw [h1]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    rw [g₁.symm x (smoothOrthoFrame (I := I) g₁ x c x)
      (gInvRaisedEndo (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x))]
    rw [lc0b_g1_inner_gInvRaisedEndo_left (I := I) (M := M) g₀ g₁ x
      (smoothOrthoFrame (I := I) g₀ x a x) (smoothOrthoFrame (I := I) g₁ x c x)]
  symm
  calc (∑ a : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel Z
          (Fin.cons (show E from gInvRaisedEndo (I := I) g₀ g₁ x
              (smoothOrthoFrame (I := I) g₀ x a x))
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)))
      = ∑ a : Fin (Module.finrank ℝ E), ∑ c : Fin (Module.finrank ℝ E),
          (g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₁ x c x)) *
          Tensor0SSpace.toModel Z
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
              (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hGrep a]
        exact lc0b_toModel_cons_sum_smul (E := E) x (Tensor0SSpace.toModel Z)
          (Module.finrank ℝ E)
          (fun c => g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₁ x c x))
          (fun c => (smoothOrthoFrame (I := I) g₁ x c x : E))
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)
    _ = ∑ c : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
          (g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₁ x c x)) *
          Tensor0SSpace.toModel Z
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
              (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)) :=
        Finset.sum_comm
    _ = ∑ c : Fin (Module.finrank ℝ E),
          Tensor0SSpace.toModel Z
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
              (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E) mm)) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        have hsum := lc0b_toModel_cons_cons_sum_smul (E := E) x (Tensor0SSpace.toModel Z)
          ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
          (Module.finrank ℝ E)
          (fun a => g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₁ x c x))
          (fun a => (smoothOrthoFrame (I := I) g₀ x a x : E)) mm
        rw [← hsum]
        congr 2
        have hrep0 := lc0b_orthoFrame_center_repr (I := I) (M := M) g₀ x
          (smoothOrthoFrame (I := I) g₁ x c x)
        rw [show (∑ a : Fin (Module.finrank ℝ E),
            g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
              (smoothOrthoFrame (I := I) g₁ x c x) •
              (smoothOrthoFrame (I := I) g₀ x a x : E)) =
            ((∑ a : Fin (Module.finrank ℝ E),
              g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
                (smoothOrthoFrame (I := I) g₁ x c x) •
                smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) from rfl]
        rw [← hrep0]

theorem lc0b_pureDT_feed (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (F : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) s x
            ((lc0PureDT (I := I) (M := M) g₀ g₁ s).toSection x) ≤ Λ) ∧
        (∀ i : ℕ, i ≤ a →
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ (s + 2) s q
              (lc0PureDT (I := I) (M := M) g₀ g₁ s)‖ ^ 2 ≤ F i) := by
  classical
  obtain ⟨Λsf, Fsf, hΛsf_nn, hFsf_nn, hsf⟩ :=
    lc0b_sharpFlat_feed (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨c0, hc0_nn, hc0⟩ := lc0b_fixedField_rfns_jet (I := I) (M := M) g₀ (s + 2) s
    (cometricDoubleTraceField (I := I) g₀ s)
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  have hfrpow_nn : 0 ≤ fr ^ (s + 1) := by positivity
  refine ⟨c0 0 * (fr ^ (s + 1) * Λsf),
    fun i => ∑ q ∈ Finset.range (i + 1),
      appCcGdiag (E := E) q * (c0 0 * (((q : ℝ) + 1) * (fr ^ (s + 1) * Fsf i))),
    mul_nonneg (hc0_nn 0) (mul_nonneg hfrpow_nn hΛsf_nn),
    fun i => Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
      (mul_nonneg (hc0_nn 0) (mul_nonneg (by positivity)
        (mul_nonneg hfrpow_nn (hFsf_nn i)))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  obtain ⟨hsfsup, hsfsum⟩ := hsf g₁ P htie hδ_le hδ0 hδ hPball
  have hid := lc0PureDT_eq_trace_fullRaised (I := I) (M := M) g₀ g₁ s
  set W : SmoothCcTensor g₀ (s + 2) (s + 2) :=
    slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
      (fullRaisedEndoField (I := I) (M := M) g₀ g₁) with hW_def
  have hWpt : ∀ (l : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
        ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W).toSection x) ≤
      fr ^ (s + 1) * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
        ((iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) := by
    intro l x
    have h := rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g₀ (s + 1)
      (fullRaisedEndoField (I := I) (M := M) g₀ g₁) l x
    rw [← hfr_def] at h
    refine le_trans h ?_
    rw [← lc0b_sharpFlat_eq_slotInsert_fullRaised (I := I) (M := M) g₀ g₁]
  have hWsup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + 2) x (W.toSection x) ≤
      fr ^ (s + 1) * Λsf := by
    intro x
    have h := hWpt 0 x
    simp only [iteratedCovGrad_zero] at h
    refine le_trans h ?_
    exact mul_le_mul_of_nonneg_left (hsfsup x) hfrpow_nn
  have hWsum : ∀ i : ℕ, i ≤ a → ∀ l : ℕ, l ≤ i →
      ‖iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W‖ ^ 2 ≤ fr ^ (s + 1) * Fsf i := by
    intro i hi l hl
    have h1 : ‖iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W‖ ^ 2 ≤
        fr ^ (s + 1) * ‖iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁)‖ ^ 2 :=
      lc0b_normSq_le_scaled_of_pointwise (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) 1 (1 + l)
        (iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W)
        (iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁))
        (fr ^ (s + 1)) hfrpow_nn (fun x => hWpt l x)
    refine le_trans h1 (mul_le_mul_of_nonneg_left ?_ hfrpow_nn)
    have hsingle : ‖iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁)‖ ^ 2 ≤
        ∑ q ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 1 1 q (sharpFlatEndoCc (I := I) g₀ g₁)‖ ^ 2 :=
      Finset.single_le_sum (f := fun q =>
        ‖iteratedCovGrad (I := I) g₀ 1 1 q (sharpFlatEndoCc (I := I) g₀ g₁)‖ ^ 2)
        (fun q _ => sq_nonneg _) (Finset.mem_range.mpr (by omega))
    exact le_trans hsingle (hsfsum i hi)
  have hpt : ∀ (q : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + q) x
        ((iteratedCovGrad (I := I) g₀ (s + 2) s q
          (lc0PureDT (I := I) (M := M) g₀ g₁ s)).toSection x) ≤
      appCcGdiag (E := E) q * (c0 0 *
        ∑ l ∈ Finset.range (q + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
            ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W).toSection x)) := by
    intro q x
    rw [hid]
    refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
      (I := I) (M := M) g₀ q (s + 2) (s + 2) s
      (cometricDoubleTraceField (I := I) g₀ s) W x) ?_
    refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) q)
    have hzero : ∀ i' ∈ Finset.range (q + 1), i' ≠ 0 →
        riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + i') x
            ((iteratedCovGrad (I := I) g₀ (s + 2) s i'
              (cometricDoubleTraceField (I := I) g₀ s)).toSection x) *
          ∑ l ∈ Finset.range (q + 1 - i'),
            riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
              ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W).toSection x) = 0 := by
      intro i' _ hi'0
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi'0
      rw [lc0b_icg_succ_cometricDT_zero (I := I) (M := M) g₀ s m]
      rw [show ((0 : SmoothCcTensor g₀ (s + 2) (s + (m + 1))).toSection x) =
          (0 : TensorRSSpace (s + 2) (s + (m + 1)) I x) from by
        rw [SmoothCcTensor.toSection_zero]; rfl]
      rw [riemannianFiberNormSq_zero (I := I) (M := M) g₀ (s + 2) (s + (m + 1)) x]
      rw [zero_mul]
    have hsum_eq : (∑ i' ∈ Finset.range (q + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + i') x
            ((iteratedCovGrad (I := I) g₀ (s + 2) s i'
              (cometricDoubleTraceField (I := I) g₀ s)).toSection x) *
          ∑ l ∈ Finset.range (q + 1 - i'),
            riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
              ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W).toSection x)) =
        riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + 0) x
            ((iteratedCovGrad (I := I) g₀ (s + 2) s 0
              (cometricDoubleTraceField (I := I) g₀ s)).toSection x) *
          ∑ l ∈ Finset.range (q + 1 - 0),
            riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
              ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W).toSection x) := by
      refine Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega)) ?_
      intro i' hi' hi'0
      exact hzero i' hi' hi'0
    rw [hsum_eq]
    have hsum_nn : 0 ≤ ∑ l ∈ Finset.range (q + 1 - 0),
        riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
          ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W).toSection x) :=
      Finset.sum_nonneg fun l _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x _
    exact mul_le_mul_of_nonneg_right (hc0 0 x) hsum_nn
  refine ⟨?_, ?_⟩
  · intro x
    have h := hpt 0 x
    simp only [iteratedCovGrad_zero] at h
    have h2 : (∑ l ∈ Finset.range (0 + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
          ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W).toSection x)) =
        riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + 0) x
          ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) 0 W).toSection x) := by
      rw [Finset.sum_range_one]
    rw [h2] at h
    simp only [iteratedCovGrad_zero] at h
    have h3 : riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + 2) x (W.toSection x) ≤
        fr ^ (s + 1) * Λsf := hWsup x
    have happ : appCcGdiag (E := E) 0 = 1 := by
      rw [appCcGdiag, pow_zero]
    calc riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) s x
          ((lc0PureDT (I := I) (M := M) g₀ g₁ s).toSection x)
        ≤ appCcGdiag (E := E) 0 * (c0 0 *
            riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + 2) x (W.toSection x)) := h
      _ = c0 0 * riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + 2) x
            (W.toSection x) := by rw [happ, one_mul]
      _ ≤ c0 0 * (fr ^ (s + 1) * Λsf) := mul_le_mul_of_nonneg_left h3 (hc0_nn 0)
  · intro i hi
    refine Finset.sum_le_sum fun q hq => ?_
    have hq_le : q ≤ i := by have := Finset.mem_range.mp hq; omega
    have hint : MeasureTheory.Integrable
        (fun x => appCcGdiag (E := E) q * (c0 0 *
          ∑ l ∈ Finset.range (q + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
              ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W).toSection x)))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) := by
      refine MeasureTheory.Integrable.const_mul ?_ _
      refine MeasureTheory.Integrable.const_mul ?_ _
      exact MeasureTheory.integrable_finset_sum (Finset.range (q + 1)) fun l _ =>
        integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ (s + 2) ((s + 2) + l)
          (iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W)
    have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀
      (s + 2) (s + q)
      (iteratedCovGrad (I := I) g₀ (s + 2) s q (lc0PureDT (I := I) (M := M) g₀ g₁ s))
      (fun x => appCcGdiag (E := E) q * (c0 0 *
        ∑ l ∈ Finset.range (q + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
            ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W).toSection x)))
      hint (fun x => hpt q x)
    refine le_trans hkey ?_
    rw [MeasureTheory.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) q)
    rw [MeasureTheory.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (hc0_nn 0)
    rw [MeasureTheory.integral_finset_sum (Finset.range (q + 1)) (fun l _ =>
      integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ (s + 2) ((s + 2) + l)
        (iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W))]
    have hterm : ∀ l ∈ Finset.range (q + 1),
        (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
          ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤ fr ^ (s + 1) * Fsf i := by
      intro l hl
      have hleq : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
          ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
          ‖iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W‖ ^ 2 :=
        (lc0b_normSq_eq_integral (I := I) (M := M) g₀ (s + 2) ((s + 2) + l)
          (iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W)).symm
      rw [hleq]
      exact hWsum i hi l (le_trans (by have := Finset.mem_range.mp hl; omega) hq_le)
    calc (∑ l ∈ Finset.range (q + 1),
          ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
            ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀))
        ≤ ∑ l ∈ Finset.range (q + 1), fr ^ (s + 1) * Fsf i := Finset.sum_le_sum hterm
      _ = ((q : ℝ) + 1) * (fr ^ (s + 1) * Fsf i) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring

end DeTurckRemainderTameLipschitz

end LieCorr0BoundsD

end LieCorr0BoundsAll

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
