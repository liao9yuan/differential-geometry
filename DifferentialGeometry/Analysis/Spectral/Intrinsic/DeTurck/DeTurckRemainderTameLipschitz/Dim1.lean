import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitz.Refold

/-!
# One-dimensional degeneracies and the fibre-norm budget layer

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

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma dim1_smul_rep (h1 : Module.finrank ℝ E = 1) (e : E) (he : e ≠ 0) (v : E) :
    ∃ c : ℝ, c • e = v :=
  exists_smul_eq_of_finrank_eq_one (K := ℝ) (V := E) h1 he v

namespace DeTurckRemainderTameLipschitz

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
lemma dim1_domDomCongr_eq (h1 : Module.finrank ℝ E = 1) {d : ℕ}
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin d => E) ℝ) (ρ : Equiv.Perm (Fin d)) :
    ContinuousMultilinearMap.domDomCongr ρ f = f := by
  classical
  have hpos : 0 < Module.finrank ℝ E := h1 ▸ Nat.one_pos
  set b := Module.finBasis ℝ E with hb
  set e : E := b ⟨0, hpos⟩ with he_def
  have he : e ≠ 0 := b.ne_zero _
  apply ContinuousMultilinearMap.ext
  intro v
  have hrep : ∀ i : Fin d, ∃ c : ℝ, c • e = v i := fun i => dim1_smul_rep h1 e he (v i)
  choose c hc using hrep
  have hv : v = fun i => c i • e := by
    funext i
    exact (hc i).symm
  rw [ContinuousMultilinearMap.domDomCongr_apply, hv]
  have hL : (f fun i => c (ρ i) • e) = (∏ i, c (ρ i)) • f (fun _ => e) :=
    f.map_smul_univ (fun i => c (ρ i)) (fun _ => e)
  have hR : (f fun i => c i • e) = (∏ i, c i) • f (fun _ => e) :=
    f.map_smul_univ c (fun _ => e)
  rw [hL, hR, Equiv.prod_comp ρ c]

end DeTurckRemainderTameLipschitz

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private lemma dim1_slotPermCLM_eq (h1 : Module.finrank ℝ E = 1) {d : ℕ}
    (ρ : Equiv.Perm (Fin d)) (x : M) (D : Tensor0SBundle.Tensor0SSpace d I x) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM (I := I) ρ x D = D := by
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM_apply]
  rw [dim1_domDomCongr_eq h1 (Tensor0SBundle.Tensor0SSpace.toModel D) ρ]
  exact Tensor0SBundle.Tensor0SSpace.ofModel_toModel (𝕜 := ℝ) D

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private lemma dim1_ricciCometricFourTraceCLM_eq_zero (h1 : Module.finrank ℝ E = 1)
    (g₁ : SmoothRiemannianMetric I M) (x : M) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCLM
      (I := I) g₁ x = 0 := by
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCLM]
  have hF : ∀ ρ₁ ρ₂ ρ₃ : Equiv.Perm (Fin 4),
      (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.cometricDoubleTraceFib
            (I := I) g₁ 2 x).comp
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM (I := I) ρ₁ x)
        + (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.cometricDoubleTraceFib
            (I := I) g₁ 2 x).comp
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM (I := I) ρ₂ x)
        - DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.cometricDoubleTraceFib
            (I := I) g₁ 2 x
        - (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.cometricDoubleTraceFib
            (I := I) g₁ 2 x).comp
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM (I := I) ρ₃ x)
        = 0 := by
    intro ρ₁ ρ₂ ρ₃
    apply ContinuousLinearMap.ext
    intro Z
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    rw [dim1_slotPermCLM_eq (I := I) h1 ρ₁ x Z, dim1_slotPermCLM_eq (I := I) h1 ρ₂ x Z,
      dim1_slotPermCLM_eq (I := I) h1 ρ₃ x Z]
    rw [ContinuousLinearMap.zero_apply]
    abel
  rw [hF]
  rw [smul_zero]

namespace DeTurckRemainderTameLipschitz

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
lemma dim1_linearizedRicciConnDiffOrder0CoeffField_eq_zero
    (h1 : Module.finrank ℝ E = 1) (g₀ g₁ : SmoothRiemannianMetric I M) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
      (I := I) (M := M) g₀ g₁ = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField_toSection]
  show (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0Fib
      (I := I) g₀ g₁ x) = _
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0Fib]
  rw [dim1_ricciCometricFourTraceCLM_eq_zero (I := I) h1 g₁ x]
  rw [ContinuousLinearMap.zero_comp]
  rfl

end DeTurckRemainderTameLipschitz

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma dim1_riemannOp_first_two_eq_zero (h1 : Module.finrank ℝ E = 1)
    (g₁ : SmoothRiemannianMetric I M) (x : M) (v w u : TangentSpace I x)
    (hw : w ≠ 0) :
    DifferentialGeometry.Integral.Connection.riemannOp
      (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g₁) x v w u = 0 := by
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one (K := ℝ) (V := TangentSpace I x)
    (show Module.finrank ℝ (TangentSpace I x) = 1 from h1) hw v
  have hself : DifferentialGeometry.Integral.Connection.riemannOp
      (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g₁) x w w u = 0 := by
    have hsw := DifferentialGeometry.Integral.Connection.riemannOp_swap
      (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g₁) x w w u
    have h2 : (2 : ℝ) • (DifferentialGeometry.Integral.Connection.riemannOp
        (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g₁) x w w u) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [hsw]
      abel
    have h2ne : (2 : ℝ) ≠ 0 := two_ne_zero
    exact (smul_eq_zero.mp h2).resolve_left h2ne
  rw [← hc]
  rw [(DifferentialGeometry.Integral.Connection.riemannOp
    (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g₁) x).map_smul c w]
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply]
  rw [hself, smul_zero]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma dim1_smoothOrthoFrame_ne_zero (g₁ : SmoothRiemannianMetric I M) (x : M)
    (a : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Integral.Connection.smoothOrthoFrame (I := I) g₁ x a x ≠ 0 := by
  intro h0
  have horth := DifferentialGeometry.Integral.Connection.smoothOrthoFrame_orthonormal_at_center
    (I := I) g₁ x a a
  rw [if_pos rfl] at horth
  rw [h0] at horth
  rw [map_zero] at horth
  exact one_ne_zero horth.symm

namespace DeTurckRemainderTameLipschitz

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
lemma dim1_ricciArmOrder0RiemannCoeff_eq_zero (h1 : Module.finrank ℝ E = 1)
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
      (I := I) (M := M) g₀ g₁ = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff_toSection]
  show (Tensor0SBundle.TensorRSSpace.ofCLM
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFib (I := I) g₁ x)) = _
  have hfib : DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFib
      (I := I) g₁ x = 0 := by
    rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFib]
    apply ContinuousLinearMap.ext
    intro D
    apply Tensor0SBundle.Tensor0SSpace.toModel_injective (𝕜 := ℝ)
    apply ContinuousMultilinearMap.ext
    intro v
    rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFibFixedFrame_toModel]
    have hz : ∀ a b : Fin (Module.finrank ℝ E),
        (g₁.inner x) (DifferentialGeometry.Integral.Connection.riemannOp
            (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g₁) x (v 0)
            (DifferentialGeometry.Integral.Connection.smoothOrthoFrame (I := I) g₁ x a x)
            (DifferentialGeometry.Integral.Connection.smoothOrthoFrame (I := I) g₁ x b x))
          (v 1) *
          D.toModel ![DifferentialGeometry.Integral.Connection.smoothOrthoFrame (I := I) g₁ x a x,
            DifferentialGeometry.Integral.Connection.smoothOrthoFrame (I := I) g₁ x b x] = 0 := by
      intro a b
      rw [dim1_riemannOp_first_two_eq_zero (I := I) h1 g₁ x (v 0) _ _
        (dim1_smoothOrthoFrame_ne_zero (I := I) g₁ x a)]
      rw [map_zero, ContinuousLinearMap.zero_apply, zero_mul]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hz a b))]
    rw [Finset.sum_const, Finset.sum_const]
    simp only [smul_zero, mul_zero]
    have : (Tensor0SBundle.Tensor0SSpace.toModel (𝕜 := ℝ)
        ((0 : Tensor0SBundle.TensorRSSpace 2 2 I x) D)) v = 0 := by
      show (Tensor0SBundle.Tensor0SSpace.toModel (𝕜 := ℝ)
        ((0 : Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x) D)) v = 0
      rw [ContinuousLinearMap.zero_apply]
      rw [show (Tensor0SBundle.Tensor0SSpace.toModel (𝕜 := ℝ)
        (0 : Tensor0SBundle.Tensor0SSpace 2 I x)) = 0 from map_zero _]
      rfl
    rw [this]
  rw [hfib]
  rfl

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
lemma rfns_tl_icg_zero (g : SmoothRiemannianMetric I M) (r s j : ℕ) :
    iteratedCovGrad (I := I) g r s j (0 : SmoothCcTensor g r s) = 0 := by
  have h := iteratedCovGrad_add (I := I) g r s j 0 0
  rw [add_zero] at h
  exact (add_left_cancel (a := iteratedCovGrad (I := I) g r s j 0)
    (by rw [← h, add_zero])).symm

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
lemma rfns_tl_toSection_zero (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) :
    ((0 : SmoothCcTensor g r s).toSection x) = 0 := by
  have h : ((0 : SmoothCcTensor g r s) + 0).toSection x =
      (0 : SmoothCcTensor g r s).toSection x + (0 : SmoothCcTensor g r s).toSection x := by
    rw [SmoothCcTensor.toSection_add]
    rfl
  rw [add_zero] at h
  exact (add_left_cancel (a := (0 : SmoothCcTensor g r s).toSection x)
    (by rw [← h, add_zero])).symm

end DeTurckRemainderTameLipschitz

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma rfns_tl_add_le_sq_sqrt (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (a b : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (a + b) ≤
      (Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x a)
        + Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x b)) ^ 2 := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (a + b),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x a,
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x b]
  rw [TensorRSSpace.toModel_add]
  rw [tensorInnerPointwise_add_left, tensorInnerPointwise_add_right,
    tensorInnerPointwise_add_right]
  set A := tensorInnerPointwise (I := I) (M := M) g r s x
    (TensorRSSpace.toModel (𝕜 := ℝ) a) (TensorRSSpace.toModel (𝕜 := ℝ) a) with hA
  set B := tensorInnerPointwise (I := I) (M := M) g r s x
    (TensorRSSpace.toModel (𝕜 := ℝ) b) (TensorRSSpace.toModel (𝕜 := ℝ) b) with hB
  set C := tensorInnerPointwise (I := I) (M := M) g r s x
    (TensorRSSpace.toModel (𝕜 := ℝ) a) (TensorRSSpace.toModel (𝕜 := ℝ) b) with hC
  have hsymm : tensorInnerPointwise (I := I) (M := M) g r s x
      (TensorRSSpace.toModel (𝕜 := ℝ) b) (TensorRSSpace.toModel (𝕜 := ℝ) a) = C := by
    rw [hC, tensorInnerPointwise_symm]
  rw [hsymm]
  have hA0 : 0 ≤ A := tensorInnerPointwise_nonneg (I := I) (M := M) g r s x _
  have hB0 : 0 ≤ B := tensorInnerPointwise_nonneg (I := I) (M := M) g r s x _
  have hC2 : C ^ 2 ≤ A * B := tensorInnerPointwise_sq_le_mul (I := I) (M := M) g r s x _ _
  have hCle : C ≤ Real.sqrt A * Real.sqrt B := by
    calc C ≤ |C| := le_abs_self C
      _ = Real.sqrt (C ^ 2) := (Real.sqrt_sq_eq_abs C).symm
      _ ≤ Real.sqrt (A * B) := Real.sqrt_le_sqrt hC2
      _ = Real.sqrt A * Real.sqrt B := Real.sqrt_mul hA0 B
  have hsA : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA0
  have hsB : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB0
  nlinarith [hCle, hsA, hsB]

namespace DeTurckRemainderTameLipschitz

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
lemma rfns_tl_young_sq (u v θ : ℝ) (hθ : 0 < θ) :
    (u + v) ^ 2 ≤ (1 + θ) * u ^ 2 + (1 + θ⁻¹) * v ^ 2 := by
  have hθ' : 0 < θ⁻¹ := inv_pos.mpr hθ
  have hkey : 2 * (u * v) ≤ θ * u ^ 2 + θ⁻¹ * v ^ 2 := by
    have h0 : 0 ≤ (θ * u - v) ^ 2 := sq_nonneg _
    have hexp : θ * (θ * u ^ 2 + θ⁻¹ * v ^ 2 - 2 * (u * v)) = (θ * u - v) ^ 2 := by
      field_simp
      ring
    nlinarith [mul_pos hθ hθ]
  nlinarith [hkey]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
lemma rfns_tl_fibreConst_one (h1 : Module.finrank ℝ E = 1) :
    deTurckArmFibreConst (Module.finrank ℝ E) = 1 := by
  rw [h1]
  rw [deTurckArmFibreConst]
  rw [Nat.cast_one, one_pow, Real.sqrt_one]

end DeTurckRemainderTameLipschitz

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private lemma rfns_tl_sqrt_mul_self_eq_fibreConst (n : ℕ) :
    Real.sqrt n * n = deTurckArmFibreConst n := by
  rw [deTurckArmFibreConst]
  rw [show ((n : ℝ)) ^ 3 = (n : ℝ) * (n : ℝ) ^ 2 from by ring]
  rw [Real.sqrt_mul (Nat.cast_nonneg n)]
  rw [Real.sqrt_sq (Nat.cast_nonneg n)]

namespace DeTurckRemainderTameLipschitz

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
lemma rfns_tl_budgetDualCap (n : ℕ) (hn : 2 ≤ n) {δ₀ : ℝ}
    (hδ₀ : δ₀ < 1) (hδ₀half : δ₀ ≤ 1 / 2) {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 13 / 2) :
    27 * Real.sqrt n * (1 - δ₀) * (c * n * (1 / (1 - δ₀)) ^ 2) ≤
      2 * (32 * deTurckArmFibreConst n ^ 3 - 28 * deTurckArmFibreConst n ^ 2) := by
  have h1δ : (0 : ℝ) < 1 - δ₀ := by linarith
  have hhalf : 1 / (1 - δ₀) ≤ 2 := by
    rw [div_le_iff₀ h1δ]
    linarith
  have hhalf0 : 0 < 1 / (1 - δ₀) := by positivity
  set f := deTurckArmFibreConst n with hf_def
  have hf0 : 0 ≤ f := deTurckArmFibreConst_nonneg n
  have hf2 : f ^ 2 = (n : ℝ) ^ 3 := sq_deTurckArmFibreConst n
  have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hf2ge : (8 : ℝ) ≤ f ^ 2 := by
    rw [hf2]
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ (n : ℝ) ^ 3 := by nlinarith [hn', sq_nonneg ((n : ℝ) - 2), sq_nonneg ((n : ℝ) + 2)]
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2lb : (1.414 : ℝ) ≤ Real.sqrt 2 := by
    have : (1.414 : ℝ) = Real.sqrt (1.414 ^ 2) := by
      rw [Real.sqrt_sq (by norm_num)]
    rw [this]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hs2ub : Real.sqrt 2 ≤ (1.415 : ℝ) := by
    have h : Real.sqrt 2 ≤ Real.sqrt (1.415 ^ 2) := Real.sqrt_le_sqrt (by norm_num)
    rw [Real.sqrt_sq (by norm_num)] at h
    exact h
  have hfge : 2 * Real.sqrt 2 ≤ f := by
    have h8 : Real.sqrt 8 ≤ Real.sqrt (f ^ 2) := Real.sqrt_le_sqrt hf2ge
    have h8' : Real.sqrt 8 = 2 * Real.sqrt 2 := by
      rw [show (8 : ℝ) = 2 ^ 2 * 2 from by norm_num]
      rw [Real.sqrt_mul (by norm_num)]
      rw [Real.sqrt_sq (by norm_num)]
    rw [h8', Real.sqrt_sq hf0] at h8
    exact h8
  have hLHS : 27 * Real.sqrt n * (1 - δ₀) * (c * n * (1 / (1 - δ₀)) ^ 2) =
      27 * c * (Real.sqrt n * n) * ((1 - δ₀) * (1 / (1 - δ₀)) ^ 2) := by
    ring
  rw [rfns_tl_sqrt_mul_self_eq_fibreConst n] at hLHS
  have hδfac : (1 - δ₀) * (1 / (1 - δ₀)) ^ 2 = 1 / (1 - δ₀) := by
    field_simp
  rw [hLHS, hδfac]
  have hstep : 27 * c * f * (1 / (1 - δ₀)) ≤ 54 * c * f := by
    have hcf : 0 ≤ 27 * c * f := by positivity
    calc 27 * c * f * (1 / (1 - δ₀)) ≤ 27 * c * f * 2 :=
          mul_le_mul_of_nonneg_left hhalf hcf
      _ = 54 * c * f := by ring
  refine le_trans hstep ?_
  have hcore : 27 * c ≤ 32 * f ^ 2 - 28 * f := by
    nlinarith [hfge, hs2, hs2lb, hs2ub, hf0, sq_nonneg (f - 2 * Real.sqrt 2)]
  nlinarith [hcore, hf0, mul_nonneg hc0 hf0, hfge, hs2lb, hs2]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
lemma b1_rfns_smul_value (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (c : ℝ) (a : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (c • a) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x a := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (c • a),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x a]
  rw [TensorRSSpace.toModel_smul]
  rw [tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
  ring

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
lemma b1_rfns_icg_symmS_le (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) (k : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
        ((iteratedCovGrad (I := I) g₀ 0 2 k (symmS (I := I) (M := M) g₀ P)).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
        ((iteratedCovGrad (I := I) g₀ 0 2 k P).toSection x) := by
  rw [iteratedCovGrad_symmS_eq (I := I) (M := M) g₀ P k]
  rw [show (((1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 k P
      + (1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 k
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) P)).toSection x) =
      ((1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 k P).toSection x
        + ((1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 k
            (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) P)).toSection x from by
    rw [SmoothCcTensor.toSection_add]
    rfl]
  refine le_trans (rfns_tl_add_le_sq_sqrt (I := I) (M := M) g₀ 0 (2 + k) x _ _) ?_
  rw [show (((1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 k P).toSection x) =
      (1 / 2 : ℝ) • (iteratedCovGrad (I := I) g₀ 0 2 k P).toSection x from by
    rw [SmoothCcTensor.toSection_smul]
    rfl]
  rw [show (((1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 k
      (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) P)).toSection x) =
      (1 / 2 : ℝ) • (iteratedCovGrad (I := I) g₀ 0 2 k
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) P)).toSection x from by
    rw [SmoothCcTensor.toSection_smul]
    rfl]
  rw [b1_rfns_smul_value (I := I) (M := M) g₀ 0 (2 + k) x (1 / 2)
    ((iteratedCovGrad (I := I) g₀ 0 2 k P).toSection x)]
  rw [b1_rfns_smul_value (I := I) (M := M) g₀ 0 (2 + k) x (1 / 2)
    ((iteratedCovGrad (I := I) g₀ 0 2 k
      (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) P)).toSection x)]
  rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
    (Equiv.swap (0 : Fin 2) 1) P k x]
  set A := riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
    ((iteratedCovGrad (I := I) g₀ 0 2 k P).toSection x) with hA_def
  have hA0 : 0 ≤ A := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + k) x _
  have hs : Real.sqrt ((1 / 2 : ℝ) ^ 2 * A) = (1 / 2 : ℝ) * Real.sqrt A := by
    rw [Real.sqrt_mul (by positivity) A]
    rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [hs]
  have hsq : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA0
  nlinarith [Real.sqrt_nonneg A]

end DeTurckRemainderTameLipschitz

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma b1_unitModel_sub (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : SmoothCcTensor g 0 s) (x : M) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g s
        (A - B) x =
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g s
          A x -
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g s
          B x := by
  simp only [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel]
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    ContinuousLinearMap.sub_apply, Tensor0SBundle.Tensor0SSpace.toModel_sub]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private theorem b1_appCc_sub_left (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ₁ Φ₂ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    appCc (I := I) (M := M) g r s (Φ₁ - Φ₂) W =
      appCc (I := I) (M := M) g r s Φ₁ W - appCc (I := I) (M := M) g r s Φ₂ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((appCc (I := I) (M := M) g r s Φ₁ W
      - appCc (I := I) (M := M) g r s Φ₂ W).toSection x) =
      (appCc (I := I) (M := M) g r s Φ₁ W).toSection x -
        (appCc (I := I) (M := M) g r s Φ₂ W).toSection x from rfl]
  rw [appCc_toSection, appCc_toSection, appCc_toSection]
  rw [show ((Φ₁ - Φ₂).toSection x : TensorRSSpace r s I x) =
      Φ₁.toSection x - Φ₂.toSection x from by
    rw [SmoothCcTensor.toSection_sub]
    rfl]
  rw [ContinuousLinearMap.sub_comp]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private theorem b1_symmS_eq_self (g₀ : SmoothRiemannianMetric I M)
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
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M)
            g₀ 2 S x ![u, w] =
          DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M)
            g₀ 2 S x ![w, u] := by
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
  have htwo : S + S = (2 : ℝ) • S := (two_smul ℝ S).symm
  rw [symmS, hswap, htwo, smul_smul,
    show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma b1_metricCcTensor_unitModel_apply (g₀ g : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 2 → E) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ 2
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensor (I := I)
          (M := M) g₀ g) x m =
      g.inner x (m 0) (m 1) := by
  have hbase : DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I)
      (M := M) g₀ 2
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensor (I := I)
        (M := M) g₀ g) x =
      Tensor0SSpace.toModel
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensorFib (I := I)
          g x) := by
    rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel]
    change Tensor0SSpace.toModel
        ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensorFib (I := I)
            g x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x)
            (1 : ℝ))) =
      Tensor0SSpace.toModel
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensorFib (I := I)
          g x)
    rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
      ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rw [hbase]
  rfl

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private theorem b1_perturbation_eq_metricDifference (g₀ g₁ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (hPsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ P x v w = ccTensorBilin (I := I) g₀ P x w v) :
    P = DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor
      (I := I) (M := M) g₀ g₁ := by
  have hsymm : symmS (I := I) (M := M) g₀ P = P :=
    b1_symmS_eq_self (I := I) (M := M) g₀ P hPsymm
  have hmd : DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor
      (I := I) (M := M) g₀ g₁ =
      symmS (I := I) (M := M) g₀ P := by
    refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀ (fun x => ?_)
    refine ContinuousMultilinearMap.ext (fun m => ?_)
    rw [show DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor
        (I := I) (M := M) g₀ g₁ =
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensor (I := I)
          (M := M) g₀ g₁ -
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensor (I := I)
          (M := M) g₀ g₀
        from rfl]
    rw [b1_unitModel_sub (I := I) (M := M) g₀ 2
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensor (I := I)
        (M := M) g₀ g₁)
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensor (I := I)
        (M := M) g₀ g₀) x]
    rw [ContinuousMultilinearMap.sub_apply]
    rw [b1_metricCcTensor_unitModel_apply (I := I) (M := M) g₀ g₁ x m,
      b1_metricCcTensor_unitModel_apply (I := I) (M := M) g₀ g₀ x m]
    rw [show DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I)
        (M := M) g₀ 2 (symmS (I := I) (M := M) g₀ P) x m =
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M)
          g₀ 2 (symmS (I := I) (M := M) g₀ P) x ![m 0, m 1] from by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl]
    rw [unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀
      (symmS (I := I) (M := M) g₀ P) x (m 0) (m 1)]
    rw [ccTensorBilin_symmS (I := I) (M := M) g₀ P x (m 0) (m 1)]
    rw [htie x (m 0) (m 1)]
    ring
  rw [hmd, hsymm]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private theorem b1_ccTensor22_ext_of_appCc (g₀ : SmoothRiemannianMetric I M)
    (C D : SmoothCcTensor g₀ 2 2)
    (h : ∀ W : SmoothCcTensor g₀ 0 2,
      appCc (I := I) (M := M) g₀ 2 2 C W = appCc (I := I) (M := M) g₀ 2 2 D W) : C = D := by
  classical
  refine SmoothCcTensor.ext ?_
  refine ContMDiffSection.ext (fun x => ?_)
  refine tensorRSSpace_ext 2 2 x (fun u => ?_)
  set V : TensorRSSpace 0 2 I x :=
    (show TensorRSSpace 0 2 I x from
      ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight u))
    with hV_def
  obtain ⟨σW, hσW⟩ := ContMDiffSection.exists_eq_at
    (I := I) (n := (⊤ : ℕ∞)) (F := TensorRSModel 0 2 ℝ E)
    (V := fun z : M => TensorRSSpace 0 2 I z) x V
  set W₀ : SmoothCcTensor g₀ 0 2 :=
    { toSection := σW
      hasCompactSupport := HasCompactSupport.of_compactSpace _ } with hW₀_def
  have h1 : (appCc (I := I) (M := M) g₀ 2 2 C W₀).toSection x =
      (appCc (I := I) (M := M) g₀ 2 2 D W₀).toSection x := by
    rw [h W₀]
  have h2 : (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from C.toSection x)
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W₀.toSection x)
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitTensor (I := I)
          (M := M) x)) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from D.toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W₀.toSection x)
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitTensor (I := I)
            (M := M) x)) := by
    have h1' := congrArg (fun (T : TensorRSSpace 0 2 I x) =>
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from T)
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitTensor (I := I)
          (M := M) x)) h1
    exact h1'
  have hWval : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W₀.toSection x)
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitTensor (I := I)
        (M := M) x) = u := by
    rw [show W₀.toSection x = V from hσW, hV_def]
    change ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight u)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x)
          (1 : ℝ)) = u
    rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
      ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rw [hWval] at h2
  exact h2

namespace DeTurckRemainderTameLipschitz

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
theorem b1_halfRiemannBackgroundDifference_eq_residualFieldSum_add_kernelContraction
    (g₀ g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (hPsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ P x v w = ccTensorBilin (I := I) g₀ P x w v) :
    (1 / 2 : ℝ) •
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
            (I := I) (M := M) g₀ g₁
          - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
            (I := I) (M := M) g₀ g₀) =
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0AACommCoeffField
          (I := I) (M := M) g₀ g₁
        + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.bgRDiffRefoldRemainderField
            (I := I) (M := M) g₀ g₁
        + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionField
            (I := I) (M := M) g₀ g₁
            (iteratedCovGrad (I := I) g₀ 0 2 2 P)
            (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
            (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1 := by
  classical
  have hP := b1_perturbation_eq_metricDifference (I := I) (M := M) g₀ g₁ P htie hPsymm
  rw [hP]
  refine b1_ccTensor22_ext_of_appCc (I := I) (M := M) g₀ _ _ (fun W => ?_)
  have hprim :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannHalfBackgroundDifference_appCc_eq_residualFieldSum_add_refoldKernelSecondGradient
      (I := I) (M := M) g₀ g₁ P htie hPsymm W
  rw [hP] at hprim
  rw [appCc_smul_left (I := I) (M := M) g₀ 2 2, b1_appCc_sub_left (I := I) (M := M) g₀ 2 2]
  rw [hprim]
  rw [show (appCcRS (I := I) (M := M) g₀ 2 2 2
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0BgRCommCoeffField
            (I := I) (M := M) g₀ g₁
          - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0BgRCommCoeffField
            (I := I) (M := M) g₀ g₀)
        (ccSlotSwapField (I := I) (M := M) g₀)
      + (1 / 2 : ℝ) •
          DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmSharpGradKoszulResidualField
            (I := I) (M := M) g₀ g₁
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor
              (I := I) (M := M) g₀ g₁)
      - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmRicciFoldRemainderField
          (I := I) (M := M) g₀ g₁
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor
            (I := I) (M := M) g₀ g₁)) =
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.bgRDiffRefoldRemainderField
        (I := I) (M := M) g₀ g₁ from rfl]
  rw [appCc_add_left (I := I) (M := M) g₀ 2 2
    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0AACommCoeffField
      (I := I) (M := M) g₀ g₁)
    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.bgRDiffRefoldRemainderField
      (I := I) (M := M) g₀ g₁) W]
  rw [appCc_add_left (I := I) (M := M) g₀ 2 2
    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0AACommCoeffField
        (I := I) (M := M) g₀ g₁
      + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.bgRDiffRefoldRemainderField
        (I := I) (M := M) g₀ g₁)
    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionField
      (I := I) (M := M) g₀ g₁
      (iteratedCovGrad (I := I) g₀ 0 2 2
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor
          (I := I) (M := M) g₀ g₁))
      (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1) W]
  rw [appCc_add_left (I := I) (M := M) g₀ 2 2
    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0AACommCoeffField
      (I := I) (M := M) g₀ g₁)
    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.bgRDiffRefoldRemainderField
      (I := I) (M := M) g₀ g₁) W]
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.appCc_refoldKernelContractionField
    (I := I) (M := M) g₀ g₁
    (iteratedCovGrad (I := I) g₀ 0 2 2
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor
        (I := I) (M := M) g₀ g₁))
    (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
    (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1 W]

end DeTurckRemainderTameLipschitz

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private lemma b1_sqrt_add_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have hkey : x + y ≤ (Real.sqrt x + Real.sqrt y) ^ 2 := by
    nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy, Real.sqrt_nonneg x, Real.sqrt_nonneg y,
      mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]
  calc Real.sqrt (x + y) ≤ Real.sqrt ((Real.sqrt x + Real.sqrt y) ^ 2) :=
        Real.sqrt_le_sqrt hkey
    _ = Real.sqrt x + Real.sqrt y :=
        Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y))

namespace DeTurckRemainderTameLipschitz

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
lemma b1_toSection_add (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (A B : SmoothCcTensor g r s) (x : M) :
    ((A + B).toSection x) = A.toSection x + B.toSection x := by
  rw [SmoothCcTensor.toSection_add]
  rfl

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
lemma b1_toSection_sub (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (A B : SmoothCcTensor g r s) (x : M) :
    ((A - B).toSection x) = A.toSection x - B.toSection x := by
  rw [SmoothCcTensor.toSection_sub]
  rfl

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
lemma b1_toSection_smul (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (A : SmoothCcTensor g r s) (x : M) :
    ((c • A).toSection x) = c • A.toSection x := by
  rw [SmoothCcTensor.toSection_smul]
  rfl

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
theorem b1_iteratedCovGrad_smul (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (c : ℝ) (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) =
      c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih =>
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih,
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_smul]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
theorem b1_fixedField_jet_bound (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : SmoothCcTensor g₀ r s) :
    ∃ c : ℕ → ℝ, (∀ i, 0 ≤ c i) ∧ ∀ (i : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x
        ((iteratedCovGrad (I := I) g₀ r s i F).toSection x) ≤ c i := by
  refine ⟨fun i => (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M)
      g₀ r (s + i) (iteratedCovGrad (I := I) g₀ r s i F)).choose,
    fun i => (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M)
      g₀ r (s + i) (iteratedCovGrad (I := I) g₀ r s i F)).choose_spec.1,
    fun i x => (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M)
      g₀ r (s + i) (iteratedCovGrad (I := I) g₀ r s i F)).choose_spec.2 x⟩

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in
theorem b1_bgRDiff_window (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ}
    (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.bgRDiffRefoldRemainderField
                (I := I) (M := M) g₀ g₁)).toSection x) ≤
          C i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := by
  classical
  obtain ⟨CB, hCB_nn, hCB⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.rfns_iteratedCovGrad_ricciArmOrder0BgRCommCoeffFieldDifference_boundedFactorGridWindow_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨CS, hCS_nn, hCS⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.rfns_iteratedCovGrad_ricciArmSharpGradKoszulResidualFieldMetricDifference_boundedFactorGridWindow_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨CR, hCR_nn, hCR⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.rfns_iteratedCovGrad_ricciArmRicciFoldRemainderFieldMetricDifference_boundedFactorGridWindow_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨SW, hSW_nn, hSW⟩ := b1_fixedField_jet_bound (I := I) (M := M) g₀ 2 2
    (ccSlotSwapField (I := I) (M := M) g₀)
  refine ⟨fun i => 4 * (appCcGdiag (E := E) i *
      ∑ i' ∈ Finset.range (i + 1), CB i' * ∑ l ∈ Finset.range (i + 1 - i'), SW l)
      + 4 * ((1 / 2 : ℝ) ^ 2 * CS i) + 2 * CR i,
    fun i => by
      have h1 : (0 : ℝ) ≤ appCcGdiag (E := E) i *
          ∑ i' ∈ Finset.range (i + 1), CB i' * ∑ l ∈ Finset.range (i + 1 - i'), SW l :=
        mul_nonneg (appCcGdiag_nonneg (E := E) i)
          (Finset.sum_nonneg fun i' _ => mul_nonneg (hCB_nn i')
            (Finset.sum_nonneg fun l _ => hSW_nn l))
      have h2 := hCS_nn i
      have h3 := hCR_nn i
      positivity, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb_nn : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  set w : ℝ := Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) with hw_def
  have hw_nn : 0 ≤ w := Combinatorics.boundedFactorGridWindow_nonneg b hb_nn (i + 1) (i + 3)
  have hbg_eq : DifferentialGeometry.Analysis.Parabolic.TensorSpectral.bgRDiffRefoldRemainderField
      (I := I) (M := M) g₀ g₁ =
      appCcRS (I := I) (M := M) g₀ 2 2 2
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0BgRCommCoeffField
            (I := I) (M := M) g₀ g₁
          - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0BgRCommCoeffField
            (I := I) (M := M) g₀ g₀)
        (ccSlotSwapField (I := I) (M := M) g₀)
      + (1 / 2 : ℝ) •
          DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmSharpGradKoszulResidualField
            (I := I) (M := M) g₀ g₁
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor
              (I := I) (M := M) g₀ g₁)
      - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmRicciFoldRemainderField
          (I := I) (M := M) g₀ g₁
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor
            (I := I) (M := M) g₀ g₁) := rfl
  rw [hbg_eq]
  rw [iteratedCovGrad_sub (I := I) g₀ 2 2 i, iteratedCovGrad_add (I := I) g₀ 2 2 i]
  rw [b1_toSection_sub (I := I) (M := M) g₀ 2 (2 + i), b1_toSection_add (I := I) (M := M) g₀ 2 (2 + i)]
  refine le_trans (riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
  have hsplit2 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x
    ((iteratedCovGrad (I := I) g₀ 2 2 i
      (appCcRS (I := I) (M := M) g₀ 2 2 2
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0BgRCommCoeffField
            (I := I) (M := M) g₀ g₁
          - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0BgRCommCoeffField
            (I := I) (M := M) g₀ g₀)
        (ccSlotSwapField (I := I) (M := M) g₀))).toSection x)
    ((iteratedCovGrad (I := I) g₀ 2 2 i
      ((1 / 2 : ℝ) •
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmSharpGradKoszulResidualField
          (I := I) (M := M) g₀ g₁
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor
            (I := I) (M := M) g₀ g₁))).toSection x)
  have hA : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (appCcRS (I := I) (M := M) g₀ 2 2 2
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0BgRCommCoeffField
              (I := I) (M := M) g₀ g₁
            - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0BgRCommCoeffField
              (I := I) (M := M) g₀ g₀)
          (ccSlotSwapField (I := I) (M := M) g₀))).toSection x) ≤
      (appCcGdiag (E := E) i *
        ∑ i' ∈ Finset.range (i + 1), CB i' * ∑ l ∈ Finset.range (i + 1 - i'), SW l) * w := by
    refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
      (I := I) (M := M) g₀ i 2 2 2
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0BgRCommCoeffField
          (I := I) (M := M) g₀ g₁
        - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0BgRCommCoeffField
          (I := I) (M := M) g₀ g₀)
      (ccSlotSwapField (I := I) (M := M) g₀) x) ?_
    have hrhs : (appCcGdiag (E := E) i *
        ∑ i' ∈ Finset.range (i + 1), CB i' * ∑ l ∈ Finset.range (i + 1 - i'), SW l) * w =
        appCcGdiag (E := E) i *
        ∑ i' ∈ Finset.range (i + 1), (CB i' * w) * ∑ l ∈ Finset.range (i + 1 - i'), SW l := by
      rw [mul_assoc, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl (fun i' _ => ?_)
      ring
    rw [hrhs]
    refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) i)
    refine Finset.sum_le_sum (fun i' hi' => ?_)
    have hi'le : i' ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi')
    have hBGi' : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i') x
        ((iteratedCovGrad (I := I) g₀ 2 2 i'
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0BgRCommCoeffField
              (I := I) (M := M) g₀ g₁
            - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0BgRCommCoeffField
              (I := I) (M := M) g₀ g₀)).toSection x) ≤ CB i' * w := by
      refine le_trans (hCB g₁ P htie hδ_le hδ0 hbound i' x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCB_nn i')
      rw [hw_def]
      exact Combinatorics.boundedFactorGridWindow_mono b hb_nn
        (by omega) (by omega)
    refine mul_le_mul hBGi' ?_ ?_ (mul_nonneg (hCB_nn i') hw_nn)
    · refine Finset.sum_le_sum (fun l _ => hSW l x)
    · exact Finset.sum_nonneg (fun l _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (2 + l) x _)
  have hS : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        ((1 / 2 : ℝ) •
          DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmSharpGradKoszulResidualField
            (I := I) (M := M) g₀ g₁
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor
              (I := I) (M := M) g₀ g₁))).toSection x) ≤
      ((1 / 2 : ℝ) ^ 2 * CS i) * w := by
    rw [b1_iteratedCovGrad_smul (I := I) (M := M) g₀ 2 2 i (1 / 2)]
    rw [show (((1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 2 2 i
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmSharpGradKoszulResidualField
          (I := I) (M := M) g₀ g₁
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor
            (I := I) (M := M) g₀ g₁))).toSection x) =
        (1 / 2 : ℝ) • (iteratedCovGrad (I := I) g₀ 2 2 i
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmSharpGradKoszulResidualField
            (I := I) (M := M) g₀ g₁
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor
              (I := I) (M := M) g₀ g₁))).toSection x from by
      rw [SmoothCcTensor.toSection_smul]
      rfl]
    rw [b1_rfns_smul_value (I := I) (M := M) g₀ 2 (2 + i) x (1 / 2) _]
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact hCS g₁ P htie hδ_le hδ0 hbound i x
  have hR : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmRicciFoldRemainderField
          (I := I) (M := M) g₀ g₁
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor
            (I := I) (M := M) g₀ g₁))).toSection x) ≤ CR i * w :=
    hCR g₁ P htie hδ_le hδ0 hbound i x
  nlinarith [hsplit2, hA, hS, hR, hw_nn]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
lemma b1_sqrt_rfns_add_le (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (a b : TensorRSSpace r s I x) :
    Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x (a + b)) ≤
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x a)
        + Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x b) := by
  have h := rfns_tl_add_le_sq_sqrt (I := I) (M := M) g r s x a b
  calc Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x (a + b))
      ≤ Real.sqrt ((Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x a)
          + Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x b)) ^ 2) :=
        Real.sqrt_le_sqrt h
    _ = _ := Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
lemma b1_sqrt_le_of_le {T B : ℝ} (h : T ≤ B) :
    Real.sqrt T ≤ Real.sqrt B := Real.sqrt_le_sqrt h

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
lemma b1_sqrt_head_split {e2 btop K w : ℝ} (he2 : 0 ≤ e2) (hbtop : 0 ≤ btop)
    (hK : 0 ≤ K) (hw : 0 ≤ w) {T : ℝ} (hT : T ≤ e2 ^ 2 * btop + K * w) :
    Real.sqrt T ≤ e2 * Real.sqrt btop + Real.sqrt (K * w) := by
  refine le_trans (b1_sqrt_le_of_le hT) ?_
  refine le_trans (b1_sqrt_add_le (e2 ^ 2 * btop) (K * w)
    (by positivity) (by positivity)) ?_
  have h1 : Real.sqrt (e2 ^ 2 * btop) = e2 * Real.sqrt btop := by
    rw [Real.sqrt_mul (by positivity) btop]
    rw [Real.sqrt_sq he2]
  rw [h1]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
lemma b1_young_assembly {T e1 e2 btop K1 K2 K3 K4 K5 w : ℝ}
    (hbtop : 0 ≤ btop) (hw : 0 ≤ w) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2)
    (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hK3 : 0 ≤ K3) (hK4 : 0 ≤ K4) (hK5 : 0 ≤ K5)
    (hT0 : 0 ≤ T)
    (hT : Real.sqrt T ≤ (e1 + e2) * Real.sqrt btop
      + (Real.sqrt (K1 * w) + Real.sqrt (K2 * w) + Real.sqrt (K3 * w)
        + Real.sqrt (K4 * w) + Real.sqrt (K5 * w))) :
    T ≤ ((201 / 200) * (e1 + e2)) ^ 2 * btop
      + (505 * (K1 + K2 + K3 + K4 + K5)) * w := by
  set u : ℝ := (e1 + e2) * Real.sqrt btop with hu_def
  set v : ℝ := Real.sqrt (K1 * w) + Real.sqrt (K2 * w) + Real.sqrt (K3 * w)
    + Real.sqrt (K4 * w) + Real.sqrt (K5 * w) with hv_def
  have hu0 : 0 ≤ u := mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  have hv0 : 0 ≤ v := by
    have := Real.sqrt_nonneg (K1 * w)
    have := Real.sqrt_nonneg (K2 * w)
    have := Real.sqrt_nonneg (K3 * w)
    have := Real.sqrt_nonneg (K4 * w)
    have := Real.sqrt_nonneg (K5 * w)
    linarith
  have hTuv : T ≤ (u + v) ^ 2 := by
    have hsq : Real.sqrt T ^ 2 ≤ (u + v) ^ 2 := by
      have huv0 : 0 ≤ u + v := by linarith
      nlinarith [hT, Real.sqrt_nonneg T]
    rw [Real.sq_sqrt hT0] at hsq
    exact hsq
  have hyoung := rfns_tl_young_sq u v (1 / 100) (by norm_num)
  have hu2 : u ^ 2 = (e1 + e2) ^ 2 * btop := by
    rw [hu_def, mul_pow, Real.sq_sqrt hbtop]
  have hv2 : v ^ 2 ≤ 5 * (K1 * w + K2 * w + K3 * w + K4 * w + K5 * w) := by
    have h1 : Real.sqrt (K1 * w) ^ 2 = K1 * w := Real.sq_sqrt (by positivity)
    have h2 : Real.sqrt (K2 * w) ^ 2 = K2 * w := Real.sq_sqrt (by positivity)
    have h3 : Real.sqrt (K3 * w) ^ 2 = K3 * w := Real.sq_sqrt (by positivity)
    have h4 : Real.sqrt (K4 * w) ^ 2 = K4 * w := Real.sq_sqrt (by positivity)
    have h5 : Real.sqrt (K5 * w) ^ 2 = K5 * w := Real.sq_sqrt (by positivity)
    rw [hv_def]
    nlinarith [sq_nonneg (Real.sqrt (K1 * w) - Real.sqrt (K2 * w)),
      sq_nonneg (Real.sqrt (K1 * w) - Real.sqrt (K3 * w)),
      sq_nonneg (Real.sqrt (K1 * w) - Real.sqrt (K4 * w)),
      sq_nonneg (Real.sqrt (K1 * w) - Real.sqrt (K5 * w)),
      sq_nonneg (Real.sqrt (K2 * w) - Real.sqrt (K3 * w)),
      sq_nonneg (Real.sqrt (K2 * w) - Real.sqrt (K4 * w)),
      sq_nonneg (Real.sqrt (K2 * w) - Real.sqrt (K5 * w)),
      sq_nonneg (Real.sqrt (K3 * w) - Real.sqrt (K4 * w)),
      sq_nonneg (Real.sqrt (K3 * w) - Real.sqrt (K5 * w)),
      sq_nonneg (Real.sqrt (K4 * w) - Real.sqrt (K5 * w))]
  have hone : (1 + (1 / 100 : ℝ)) * u ^ 2 ≤ ((201 / 200) * (e1 + e2)) ^ 2 * btop := by
    rw [hu2]
    nlinarith [sq_nonneg (e1 + e2), hbtop]
  have hinv : ((1 : ℝ) / 100)⁻¹ = 100 := by norm_num
  rw [hinv] at hyoung
  calc T ≤ (u + v) ^ 2 := hTuv
    _ ≤ (1 + 1 / 100) * u ^ 2 + (1 + 100) * v ^ 2 := hyoung
    _ ≤ ((201 / 200) * (e1 + e2)) ^ 2 * btop
        + (1 + 100) * (5 * (K1 * w + K2 * w + K3 * w + K4 * w + K5 * w)) := by
        have hv2' : (1 + (100 : ℝ)) * v ^ 2 ≤
            (1 + 100) * (5 * (K1 * w + K2 * w + K3 * w + K4 * w + K5 * w)) := by
          nlinarith [hv2]
        linarith [hone, hv2']
    _ = ((201 / 200) * (e1 + e2)) ^ 2 * btop
        + (505 * (K1 + K2 + K3 + K4 + K5)) * w := by ring

end DeTurckRemainderTameLipschitz

set_option linter.style.setOption false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedSectionVars false in
private lemma b1_rfns_neg (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (-v) =
      riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  have h := b1_rfns_smul_value (I := I) (M := M) g r s x (-1) v
  rw [neg_one_smul] at h
  rw [h]
  norm_num

namespace DeTurckRemainderTameLipschitz

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedSectionVars false in
lemma b1_sqrt_rfns_sub_le (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (a b : TensorRSSpace r s I x) :
    Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x (a - b)) ≤
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x a)
        + Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x b) := by
  rw [sub_eq_add_neg]
  refine le_trans (b1_sqrt_rfns_add_le (I := I) (M := M) g r s x a (-b)) ?_
  rw [b1_rfns_neg (I := I) (M := M) g r s x b]

end DeTurckRemainderTameLipschitz

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedSectionVars false in
private lemma k1_unitModel_add (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : SmoothCcTensor g 0 s) (x : M) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g s
        (A + B) x =
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g s
          A x +
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g s
          B x := by
  simp only [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel]
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    ContinuousLinearMap.add_apply, Tensor0SBundle.Tensor0SSpace.toModel_add]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedSectionVars false in
private lemma k1_unitModel_smul (g : SmoothRiemannianMetric I M) (s : ℕ)
    (c : ℝ) (A : SmoothCcTensor g 0 s) (x : M) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g s
        (c • A) x =
      c • DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M)
        g s A x := by
  simp only [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel]
  rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.smul_apply, Tensor0SBundle.Tensor0SSpace.toModel_smul]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private lemma k1_domDomCongr_add {d : ℕ} (σ : Equiv.Perm (Fin d))
    (f g : ContinuousMultilinearMap ℝ (fun _ : Fin d => E) ℝ) :
    ContinuousMultilinearMap.domDomCongr σ (f + g) =
      ContinuousMultilinearMap.domDomCongr σ f + ContinuousMultilinearMap.domDomCongr σ g := by
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.add_apply]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private lemma k1_domDomCongr_smul {d : ℕ} (σ : Equiv.Perm (Fin d)) (c : ℝ)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin d => E) ℝ) :
    ContinuousMultilinearMap.domDomCongr σ (c • f) =
      c • ContinuousMultilinearMap.domDomCongr σ f := by
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.smul_apply]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedSectionVars false in
private lemma k1_domDomCongrSection_add (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (A B : SmoothCcTensor g 0 s) :
    domDomCongrSection (I := I) g σ (A + B) =
      domDomCongrSection (I := I) g σ A + domDomCongrSection (I := I) g σ B := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrSection_unitModel,
    k1_unitModel_add (I := I) (M := M) g s A B x, k1_domDomCongr_add,
    k1_unitModel_add (I := I) (M := M) g s
      (domDomCongrSection (I := I) g σ A) (domDomCongrSection (I := I) g σ B) x,
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrSection_unitModel,
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrSection_unitModel]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedSectionVars false in
private lemma k1_domDomCongrSection_smul (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (c : ℝ) (A : SmoothCcTensor g 0 s) :
    domDomCongrSection (I := I) g σ (c • A) =
      c • domDomCongrSection (I := I) g σ A := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrSection_unitModel,
    k1_unitModel_smul (I := I) (M := M) g s c A x, k1_domDomCongr_smul,
    k1_unitModel_smul (I := I) (M := M) g s c (domDomCongrSection (I := I) g σ A) x,
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrSection_unitModel]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedSectionVars false in
private lemma k1_domDomCongrSection_comp (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ τ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g 0 s) :
    domDomCongrSection (I := I) g σ (domDomCongrSection (I := I) g τ S) =
      domDomCongrSection (I := I) g (τ.trans σ) S := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrSection_unitModel,
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrSection_unitModel,
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrSection_unitModel]
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply]
  rfl

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedSectionVars false in
private lemma k1_domDomCongrSection_refl (g : SmoothRiemannianMetric I M) {s : ℕ}
    (S : SmoothCcTensor g 0 s) :
    domDomCongrSection (I := I) g (Equiv.refl (Fin s)) S = S := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrSection_unitModel]
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rfl

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedSectionVars false in
private lemma k1_symmS_eq_half (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) :
    symmS (I := I) (M := M) g₀ T =
      (1 / 2 : ℝ) • T +
        (1 / 2 : ℝ) • domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T := by
  have h := iteratedCovGrad_symmS_eq (I := I) (M := M) g₀ T 0
  rw [iteratedCovGrad_zero, iteratedCovGrad_zero, iteratedCovGrad_zero] at h
  exact h

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedSectionVars false in
private lemma k1_domDomCongrSection_symmS (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) :
    domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
        (symmS (I := I) (M := M) g₀ T) =
      symmS (I := I) (M := M) g₀ T := by
  conv_lhs => rw [k1_symmS_eq_half (I := I) (M := M) g₀ T]
  rw [k1_domDomCongrSection_add (I := I) (M := M) g₀ (Equiv.swap (0 : Fin 2) 1),
    k1_domDomCongrSection_smul (I := I) (M := M) g₀ (Equiv.swap (0 : Fin 2) 1) (1 / 2) T,
    k1_domDomCongrSection_smul (I := I) (M := M) g₀ (Equiv.swap (0 : Fin 2) 1) (1 / 2)
      (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T),
    k1_domDomCongrSection_comp (I := I) (M := M) g₀ (Equiv.swap (0 : Fin 2) 1)
      (Equiv.swap (0 : Fin 2) 1) T,
    show (Equiv.swap (0 : Fin 2) 1).trans (Equiv.swap (0 : Fin 2) 1) =
      Equiv.refl (Fin 2) from by decide,
    k1_domDomCongrSection_refl (I := I) (M := M) g₀ T,
    k1_symmS_eq_half (I := I) (M := M) g₀ T]
  abel

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedSectionVars false in
private lemma k1_zeroTensor_eq_smul_unitTensor (x : M)
    (D : Tensor0SBundle.Tensor0SSpace 0 I x) :
    D = (Tensor0SNabla.tensor0Iso I M x D) •
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitTensor (I := I) (M := M) x := by
  classical
  have hunit : Tensor0SNabla.tensor0Iso I M x
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitTensor (I := I) (M := M) x) =
      (1 : ℝ) := by
    have h := Tensor0SNabla.scalarFn_unitZero (I := I) (M := M)
    have hx := congrFun h x
    simpa [Tensor0SNabla.scalarFn_apply,
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitTensor] using hx
  apply (Tensor0SNabla.tensor0Iso I M x).injective
  rw [map_smul, hunit, smul_eq_mul, mul_one]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedSectionVars false in
private lemma k1_symmS_toModel_rel (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) :
    ∀ (y : M) (d : Tensor0SBundle.Tensor0SSpace 0 I y),
      Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I y from
            (symmS (I := I) (M := M) g₀ T).toSection y) d) =
        ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
          (Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I y from
              (symmS (I := I) (M := M) g₀ T).toSection y) d)) := by
  intro y d
  have hunit : DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I)
      (M := M) g₀ 2 (symmS (I := I) (M := M) g₀ T) y =
      ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M)
          g₀ 2 (symmS (I := I) (M := M) g₀ T) y) := by
    conv_lhs => rw [← k1_domDomCongrSection_symmS (I := I) (M := M) g₀ T]
    rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrSection_unitModel]
  rw [k1_zeroTensor_eq_smul_unitTensor (I := I) (M := M) y d]
  rw [ContinuousLinearMap.map_smul, Tensor0SBundle.Tensor0SSpace.toModel_smul,
    k1_domDomCongr_smul]
  simp only [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel] at hunit
  rw [← hunit]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedSectionVars false in
private lemma k1_symmSCovGrad3_swap12 (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) :
    domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2)
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmSCovGrad3 (I := I) g₀ T) =
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmSCovGrad3 (I := I) g₀ T := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongrSection_unitModel]
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  have hnat := DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_rs_toModel_domDomCongr
    (I := I) (M := M) g₀ 0 2 (Equiv.swap (0 : Fin 2) 1)
    (symmS (I := I) (M := M) g₀ T) (symmS (I := I) (M := M) g₀ T)
    (k1_symmS_toModel_rel (I := I) (M := M) g₀ T) x
    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitTensor (I := I) (M := M) x) v
  rw [show Equiv.Perm.decomposeFin.symm ((0 : Fin 3), Equiv.swap (0 : Fin 2) 1) =
    Equiv.swap (1 : Fin 3) 2 from by decide] at hnat
  rw [ContinuousMultilinearMap.domDomCongr_apply] at hnat
  simp only [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel,
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmSCovGrad3_def]
  exact hnat.symm

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedSectionVars false in
private lemma k1_rfns_add_expand (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (a b : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (a + b) =
      riemannianFiberNormSq (I := I) (M := M) g r s x a
        + riemannianFiberNormSq (I := I) (M := M) g r s x b
        + 2 * tensorInnerPointwise (I := I) (M := M) g r s x
            (TensorRSSpace.toModel (𝕜 := ℝ) a) (TensorRSSpace.toModel (𝕜 := ℝ) b) := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (a + b),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x a,
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x b]
  rw [TensorRSSpace.toModel_add]
  rw [tensorInnerPointwise_add_left, tensorInnerPointwise_add_right,
    tensorInnerPointwise_add_right]
  rw [show tensorInnerPointwise (I := I) (M := M) g r s x
      (TensorRSSpace.toModel (𝕜 := ℝ) b) (TensorRSSpace.toModel (𝕜 := ℝ) a) =
      tensorInnerPointwise (I := I) (M := M) g r s x
        (TensorRSSpace.toModel (𝕜 := ℝ) a) (TensorRSSpace.toModel (𝕜 := ℝ) b) from
    tensorInnerPointwise_symm (I := I) (M := M) g r s x _ _]
  ring

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedSectionVars false in
private lemma k1_rfns_addadd_expand (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (a b c : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (a + b + c) =
      riemannianFiberNormSq (I := I) (M := M) g r s x a
        + riemannianFiberNormSq (I := I) (M := M) g r s x b
        + riemannianFiberNormSq (I := I) (M := M) g r s x c
        + 2 * tensorInnerPointwise (I := I) (M := M) g r s x
            (TensorRSSpace.toModel (𝕜 := ℝ) a) (TensorRSSpace.toModel (𝕜 := ℝ) b)
        + 2 * tensorInnerPointwise (I := I) (M := M) g r s x
            (TensorRSSpace.toModel (𝕜 := ℝ) a) (TensorRSSpace.toModel (𝕜 := ℝ) c)
        + 2 * tensorInnerPointwise (I := I) (M := M) g r s x
            (TensorRSSpace.toModel (𝕜 := ℝ) b) (TensorRSSpace.toModel (𝕜 := ℝ) c) := by
  rw [k1_rfns_add_expand (I := I) (M := M) g r s x (a + b) c,
    k1_rfns_add_expand (I := I) (M := M) g r s x a b]
  rw [TensorRSSpace.toModel_add, tensorInnerPointwise_add_left]
  ring

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedSectionVars false in
private lemma k1_rfns_addsub_expand (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (a b c : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (a + b - c) =
      riemannianFiberNormSq (I := I) (M := M) g r s x a
        + riemannianFiberNormSq (I := I) (M := M) g r s x b
        + riemannianFiberNormSq (I := I) (M := M) g r s x c
        + 2 * tensorInnerPointwise (I := I) (M := M) g r s x
            (TensorRSSpace.toModel (𝕜 := ℝ) a) (TensorRSSpace.toModel (𝕜 := ℝ) b)
        - 2 * tensorInnerPointwise (I := I) (M := M) g r s x
            (TensorRSSpace.toModel (𝕜 := ℝ) a) (TensorRSSpace.toModel (𝕜 := ℝ) c)
        - 2 * tensorInnerPointwise (I := I) (M := M) g r s x
            (TensorRSSpace.toModel (𝕜 := ℝ) b) (TensorRSSpace.toModel (𝕜 := ℝ) c) := by
  have hsub : a + b - c = a + b + (-1 : ℝ) • c := by
    rw [neg_one_smul]
    abel
  rw [hsub]
  rw [k1_rfns_addadd_expand (I := I) (M := M) g r s x a b ((-1 : ℝ) • c)]
  rw [TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_right,
    tensorInnerPointwise_smul_right]
  rw [show riemannianFiberNormSq (I := I) (M := M) g r s x ((-1 : ℝ) • c) =
      riemannianFiberNormSq (I := I) (M := M) g r s x c from by
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x ((-1 : ℝ) • c),
      riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x c,
      TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left,
      tensorInnerPointwise_smul_right]
    ring]
  ring

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedSectionVars false in

theorem rfns_iteratedCovGrad_koszulCovecCc_symmS_le (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (u : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + u) x
        ((iteratedCovGrad (I := I) g₀ 0 3 u
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.koszulCovecCc
            (I := I) g₀ T)).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (u + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (u + 1)
          (symmS (I := I) (M := M) g₀ T)).toSection x) := by
  classical
  set B : SmoothCcTensor g₀ 0 3 :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmSCovGrad3 (I := I) g₀ T
    with hB_def
  have hπ : domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2) B = B :=
    k1_symmSCovGrad3_swap12 (I := I) (M := M) g₀ T
  have hkC : DifferentialGeometry.Analysis.Parabolic.TensorSpectral.koszulCovecCc
      (I := I) g₀ T =
      (1 / 2 : ℝ) •
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2) B
          + domDomCongrSection (I := I) g₀ (finRotate 3) B
          - B) := by
    have h0 : DifferentialGeometry.Analysis.Parabolic.TensorSpectral.koszulCovecCc
        (I := I) g₀ T =
        (1 / 2 : ℝ) •
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2) B
            + domDomCongrSection (I := I) g₀ (finRotate 3) B
            - domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2) B) := rfl
    rw [h0, hπ]
  have hE : domDomCongrSection (I := I) g₀ (finRotate 3) B =
      domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B := by
    rw [show (finRotate 3) =
      (Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap (0 : Fin 3) 1) from by decide]
    rw [← k1_domDomCongrSection_comp (I := I) (M := M) g₀ (Equiv.swap (0 : Fin 3) 1)
      (Equiv.swap (1 : Fin 3) 2) B]
    rw [hπ]
  have hab_sec : domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2)
      (B + domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B) =
      domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2) B
        + domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B := by
    rw [k1_domDomCongrSection_add (I := I) (M := M) g₀ (Equiv.swap (0 : Fin 3) 2) B
      (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B)]
    rw [k1_domDomCongrSection_comp (I := I) (M := M) g₀ (Equiv.swap (0 : Fin 3) 2)
      (Equiv.swap (0 : Fin 3) 1) B]
    rw [show (Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap (0 : Fin 3) 2) =
      finRotate 3 from by decide]
    rw [hE]
  have hbc_sec : domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1)
      (B + domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B) =
      domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B + B := by
    rw [k1_domDomCongrSection_add (I := I) (M := M) g₀ (Equiv.swap (0 : Fin 3) 1) B
      (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B)]
    rw [k1_domDomCongrSection_comp (I := I) (M := M) g₀ (Equiv.swap (0 : Fin 3) 1)
      (Equiv.swap (0 : Fin 3) 1) B]
    rw [show (Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap (0 : Fin 3) 1) =
      Equiv.refl (Fin 3) from by decide]
    rw [k1_domDomCongrSection_refl (I := I) (M := M) g₀ B]
  have hac_sec : domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2)
      (B + domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B) =
      B + domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2) B := by
    rw [k1_domDomCongrSection_add (I := I) (M := M) g₀ (Equiv.swap (1 : Fin 3) 2) B
      (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B)]
    rw [hπ]
    rw [k1_domDomCongrSection_comp (I := I) (M := M) g₀ (Equiv.swap (1 : Fin 3) 2)
      (Equiv.swap (0 : Fin 3) 1) B]
    rw [show (Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap (1 : Fin 3) 2) =
      (Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap (0 : Fin 3) 2) from by decide]
    rw [← k1_domDomCongrSection_comp (I := I) (M := M) g₀ (Equiv.swap (0 : Fin 3) 2)
      (Equiv.swap (1 : Fin 3) 2) B]
    rw [hπ]
  rw [hkC]
  rw [b1_iteratedCovGrad_smul (I := I) (M := M) g₀ 0 3 u]
  rw [iteratedCovGrad_sub (I := I) g₀ 0 3 u, iteratedCovGrad_add (I := I) g₀ 0 3 u]
  rw [b1_toSection_smul (I := I) (M := M) g₀ 0 (3 + u)]
  rw [b1_rfns_smul_value (I := I) (M := M) g₀ 0 (3 + u) x (1 / 2)]
  rw [b1_toSection_sub (I := I) (M := M) g₀ 0 (3 + u), b1_toSection_add (I := I) (M := M) g₀ 0 (3 + u)]
  rw [hE]
  have hexp := k1_rfns_addsub_expand (I := I) (M := M) g₀ 0 (3 + u) x
    ((iteratedCovGrad (I := I) g₀ 0 3 u
      (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2) B)).toSection x)
    ((iteratedCovGrad (I := I) g₀ 0 3 u
      (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B)).toSection x)
    ((iteratedCovGrad (I := I) g₀ 0 3 u B).toSection x)
  have habc := k1_rfns_addadd_expand (I := I) (M := M) g₀ 0 (3 + u) x
    ((iteratedCovGrad (I := I) g₀ 0 3 u
      (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2) B)).toSection x)
    ((iteratedCovGrad (I := I) g₀ 0 3 u
      (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B)).toSection x)
    ((iteratedCovGrad (I := I) g₀ 0 3 u B).toSection x)
  have hpos := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + u) x
    ((iteratedCovGrad (I := I) g₀ 0 3 u
      (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2) B)).toSection x
      + (iteratedCovGrad (I := I) g₀ 0 3 u
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B)).toSection x
      + (iteratedCovGrad (I := I) g₀ 0 3 u B).toSection x)
  have e_ab := k1_rfns_add_expand (I := I) (M := M) g₀ 0 (3 + u) x
    ((iteratedCovGrad (I := I) g₀ 0 3 u
      (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2) B)).toSection x)
    ((iteratedCovGrad (I := I) g₀ 0 3 u
      (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B)).toSection x)
  have e_bc := k1_rfns_add_expand (I := I) (M := M) g₀ 0 (3 + u) x
    ((iteratedCovGrad (I := I) g₀ 0 3 u
      (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B)).toSection x)
    ((iteratedCovGrad (I := I) g₀ 0 3 u B).toSection x)
  have e_ac := k1_rfns_add_expand (I := I) (M := M) g₀ 0 (3 + u) x
    ((iteratedCovGrad (I := I) g₀ 0 3 u
      (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2) B)).toSection x)
    ((iteratedCovGrad (I := I) g₀ 0 3 u B).toSection x)
  have f1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + u) x
      ((iteratedCovGrad (I := I) g₀ 0 3 u
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2) B)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + u) x
        ((iteratedCovGrad (I := I) g₀ 0 3 u B).toSection x) :=
    riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 3) 2) B u x
  have f2 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + u) x
      ((iteratedCovGrad (I := I) g₀ 0 3 u
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + u) x
        ((iteratedCovGrad (I := I) g₀ 0 3 u B).toSection x) :=
    riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 3) 1) B u x
  have g_ab : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + u) x
      ((iteratedCovGrad (I := I) g₀ 0 3 u
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2) B)).toSection x
        + (iteratedCovGrad (I := I) g₀ 0 3 u
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + u) x
        ((iteratedCovGrad (I := I) g₀ 0 3 u
          (B + domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B)).toSection x) := by
    rw [show (iteratedCovGrad (I := I) g₀ 0 3 u
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2) B)).toSection x
        + (iteratedCovGrad (I := I) g₀ 0 3 u
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B)).toSection x =
        (iteratedCovGrad (I := I) g₀ 0 3 u
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2) B
            + domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B)).toSection x from by
      rw [iteratedCovGrad_add (I := I) g₀ 0 3 u,
        b1_toSection_add (I := I) (M := M) g₀ 0 (3 + u)]]
    rw [← hab_sec]
    exact riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 3) 2)
      (B + domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B) u x
  have g_bc : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + u) x
      ((iteratedCovGrad (I := I) g₀ 0 3 u
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B)).toSection x
        + (iteratedCovGrad (I := I) g₀ 0 3 u B).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + u) x
        ((iteratedCovGrad (I := I) g₀ 0 3 u
          (B + domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B)).toSection x) := by
    rw [show (iteratedCovGrad (I := I) g₀ 0 3 u
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B)).toSection x
        + (iteratedCovGrad (I := I) g₀ 0 3 u B).toSection x =
        (iteratedCovGrad (I := I) g₀ 0 3 u
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B + B)).toSection x from by
      rw [iteratedCovGrad_add (I := I) g₀ 0 3 u,
        b1_toSection_add (I := I) (M := M) g₀ 0 (3 + u)]]
    rw [← hbc_sec]
    exact riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 3) 1)
      (B + domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B) u x
  have g_ac : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + u) x
      ((iteratedCovGrad (I := I) g₀ 0 3 u
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2) B)).toSection x
        + (iteratedCovGrad (I := I) g₀ 0 3 u B).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + u) x
        ((iteratedCovGrad (I := I) g₀ 0 3 u
          (B + domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B)).toSection x) := by
    rw [show (iteratedCovGrad (I := I) g₀ 0 3 u
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2) B)).toSection x
        + (iteratedCovGrad (I := I) g₀ 0 3 u B).toSection x =
        (iteratedCovGrad (I := I) g₀ 0 3 u
          (B + domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2) B)).toSection x from by
      rw [iteratedCovGrad_add (I := I) g₀ 0 3 u,
        b1_toSection_add (I := I) (M := M) g₀ 0 (3 + u)]
      exact add_comm _ _]
    rw [← hac_sec]
    exact riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (1 : Fin 3) 2)
      (B + domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1) B) u x
  have hNval : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + u) x
      ((iteratedCovGrad (I := I) g₀ 0 3 u B).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (u + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (u + 1)
          (symmS (I := I) (M := M) g₀ T)).toSection x) := by
    have hS3cov : B = iteratedCovGrad (I := I) g₀ 0 2 1 (symmS (I := I) (M := M) g₀ T) := by
      rw [hB_def]
      rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.symmSCovGrad3_def]
      rw [iteratedCovGrad_succ (I := I) g₀ 0 2 0, iteratedCovGrad_zero (I := I) g₀ 0 2]
    rw [hS3cov]
    have hcomp := rfns_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 2 1 u
      (symmS (I := I) (M := M) g₀ T) x
    rw [hcomp]
    rw [show 1 + u = u + 1 from Nat.add_comm 1 u]
  rw [show ((1 : ℝ) / 2) ^ 2 = 1 / 4 from by norm_num]
  linarith [hexp, habc, hpos, e_ab, e_bc, e_ac, f1, f2, g_ab, g_bc, g_ac, hNval]

namespace DeTurckRemainderTameLipschitz

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
def b3_kOut0Perm3201 : Equiv.Perm (Fin 4) :=
  ⟨![3, 2, 0, 1], ![2, 3, 1, 0], by decide, by decide⟩

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
def b3_kOut0Perm2301 : Equiv.Perm (Fin 4) :=
  ⟨![2, 3, 0, 1], ![2, 3, 0, 1], by decide, by decide⟩

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
def b3_kOut0Perm3102 : Equiv.Perm (Fin 4) :=
  ⟨![3, 1, 0, 2], ![2, 1, 3, 0], by decide, by decide⟩

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
def b3_kOut0Perm1302 : Equiv.Perm (Fin 4) :=
  ⟨![1, 3, 0, 2], ![2, 0, 3, 1], by decide, by decide⟩

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
def b3_kOut0Perm1203 : Equiv.Perm (Fin 4) :=
  ⟨![1, 2, 0, 3], ![2, 0, 1, 3], by decide, by decide⟩

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
def b3_kOut0Perm2103 : Equiv.Perm (Fin 4) :=
  ⟨![2, 1, 0, 3], ![2, 1, 0, 3], by decide, by decide⟩

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
def b3_kOut0Perm3012 : Equiv.Perm (Fin 4) :=
  ⟨![3, 0, 1, 2], ![1, 2, 3, 0], by decide, by decide⟩

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
def b3_kOut0Perm2013 : Equiv.Perm (Fin 4) :=
  ⟨![2, 0, 1, 3], ![1, 2, 0, 3], by decide, by decide⟩

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
def b3_kMid0Perm102 : Equiv.Perm (Fin 3) :=
  ⟨![1, 0, 2], ![1, 0, 2], by decide, by decide⟩

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
def b3_kMid0Perm120 : Equiv.Perm (Fin 3) :=
  ⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩

end DeTurckRemainderTameLipschitz

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedSectionVars false in
private theorem b3_b3_slotPermCc0Fib_contMDiff (g₀ : SmoothRiemannianMetric I M) {d : ℕ}
    (ρ : Equiv.Perm (Fin d)) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel d d ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel d d ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace d d I z) x
        (show Tensor0SBundle.TensorRSSpace d d I x from DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM (I := I) ρ x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel d ℝ E)
    (V₁ := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)
    (F₂ := Tensor0SBundle.Tensor0SModel d ℝ E)
    (V₂ := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)
    (φ := fun x : M => DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM (I := I) ρ x)
  intro Y
  have h := DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM_field_contMDiff (I := I) ρ (fun x => Y x) Y.contMDiff
  refine h.congr (fun x => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x t) rfl

namespace DeTurckRemainderTameLipschitz

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
def b3_slotPermCc0 (g₀ : SmoothRiemannianMetric I M) {d : ℕ} (ρ : Equiv.Perm (Fin d)) :
    SmoothCcTensor g₀ d d where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace d d I x from DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM (I := I) ρ x)
      contMDiff_toFun := b3_b3_slotPermCc0Fib_contMDiff (I := I) (M := M) g₀ ρ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedSectionVars false in
theorem b3_order0KernelField_eq_arm_combination (g₀ g₁ : SmoothRiemannianMetric I M) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0KernelField (I := I) g₀ g₁ =
      (appCcRS (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm3201)
          (appCcRS (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁)
            (appCcRS (I := I) (M := M) g₀ 2 3 3 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kMid0Perm102)
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁)))
        + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoeffGen (I := I) (M := M) g₀ 2 4
            (appCcRS (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm2301)
              (appCcRS (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁)
                (appCcRS (I := I) (M := M) g₀ 2 3 3
                  (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kMid0Perm102)
                  (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁)))) DifferentialGeometry.Analysis.Parabolic.TensorSpectral.innerCoreInPerm10
        + appCcRS (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm3102)
            (appCcRS (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁)
              (appCcRS (I := I) (M := M) g₀ 2 3 3
                (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kMid0Perm120)
                (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁)))
        + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoeffGen (I := I) (M := M) g₀ 2 4
            (appCcRS (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm1302)
              (appCcRS (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁)
                (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁))) DifferentialGeometry.Analysis.Parabolic.TensorSpectral.innerCoreInPerm10
        + appCcRS (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm1203)
            (appCcRS (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁)
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁))
        + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoeffGen (I := I) (M := M) g₀ 2 4
            (appCcRS (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm2103)
              (appCcRS (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁)
                (appCcRS (I := I) (M := M) g₀ 2 3 3
                  (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kMid0Perm120)
                  (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁)))) DifferentialGeometry.Analysis.Parabolic.TensorSpectral.innerCoreInPerm10)
      - appCcRS (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm3012)
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffGradContrInsertionField (I := I) g₀ g₁)
      - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoeffGen (I := I) (M := M) g₀ 2 4
          (appCcRS (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm2013)
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffGradContrInsertionField (I := I) g₀ g₁)) DifferentialGeometry.Analysis.Parabolic.TensorSpectral.innerCoreInPerm10 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rfl

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedSectionVars false in
theorem b3_armOuter24_rfns_eq (g₀ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (W : SmoothCcTensor g₀ 2 4) (q : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + q) x
        ((iteratedCovGrad (I := I) g₀ 2 4 q
          (appCcRS (I := I) (M := M) g₀ 2 4 4
            (b3_slotPermCc0 (I := I) (M := M) g₀ σ) W)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + q) x
        ((iteratedCovGrad (I := I) g₀ 2 4 q W).toSection x) := by
  refine rfns_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g₀ 2 4 σ
    W (appCcRS (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ σ) W)
    (fun y d => ?_) q x
  have hy : (show Tensor0SSpace 2 I y →L[ℝ] Tensor0SSpace 4 I y from
      (appCcRS (I := I) (M := M) g₀ 2 4 4
        (b3_slotPermCc0 (I := I) (M := M) g₀ σ) W).toSection y) d =
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM (I := I) σ y
        ((show Tensor0SSpace 2 I y →L[ℝ] Tensor0SSpace 4 I y from W.toSection y) d) := rfl
  rw [hy, DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedSectionVars false in
theorem b3_armOuter23_rfns_eq (g₀ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 3)) (W : SmoothCcTensor g₀ 2 3) (q : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + q) x
        ((iteratedCovGrad (I := I) g₀ 2 3 q
          (appCcRS (I := I) (M := M) g₀ 2 3 3
            (b3_slotPermCc0 (I := I) (M := M) g₀ σ) W)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + q) x
        ((iteratedCovGrad (I := I) g₀ 2 3 q W).toSection x) := by
  refine rfns_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g₀ 2 3 σ
    W (appCcRS (I := I) (M := M) g₀ 2 3 3 (b3_slotPermCc0 (I := I) (M := M) g₀ σ) W)
    (fun y d => ?_) q x
  have hy : (show Tensor0SSpace 2 I y →L[ℝ] Tensor0SSpace 3 I y from
      (appCcRS (I := I) (M := M) g₀ 2 3 3
        (b3_slotPermCc0 (I := I) (M := M) g₀ σ) W).toSection y) d =
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM (I := I) σ y
        ((show Tensor0SSpace 2 I y →L[ℝ] Tensor0SSpace 3 I y from W.toSection y) d) := rfl
  rw [hy, DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
lemma b4_sum_atg_eq_bfgWindow (b : ℕ → ℝ) {K W : ℕ} (hW : W ≤ K + 1) :
    ∑ k ∈ Finset.range W, Combinatorics.antidiagonalTupleGrid b k =
      Combinatorics.boundedFactorGridWindow b K W := by
  rw [Combinatorics.boundedFactorGridWindow]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [Finset.mem_range] at hk
  exact Combinatorics.antidiagonalTupleGrid_eq_boundedFactorGrid b (by omega)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedSectionVars false in
theorem b4_cDCIF_le (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + n) x
        ((iteratedCovGrad (I := I) g₀ 3 4 n
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField
            (I := I) g₀ g₁)).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n
            (connDiffSection (I := I) g₁ g₀)).toSection x) := by
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField_eq_reindex_slotExtend_two
    (I := I) (M := M) g₀ g₁]
  rw [rfns_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 3 4
    (slotExtend (I := I) (M := M) g₀ 2 3
      (slotExtend (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)))
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.coreInPerm201 n x]
  refine le_trans (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 2 3
    (slotExtend (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)) n x) ?_
  rw [show ((Module.finrank ℝ E : ℝ)) ^ 2 = (Module.finrank ℝ E : ℝ) *
    (Module.finrank ℝ E : ℝ) from pow_two (Module.finrank ℝ E : ℝ)]
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  exact rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 2
    (connDiffSection (I := I) g₁ g₀) n x

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedSectionVars false in
theorem b4_inner_le (g₀ g₁ : SmoothRiemannianMetric I M) (m : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + m) x
        ((iteratedCovGrad (I := I) g₀ 2 3 m
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField
            (I := I) g₀ g₁)).toSection x) ≤
      (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + m) x
          ((iteratedCovGrad (I := I) g₀ 1 2 m
            (connDiffSection (I := I) g₁ g₀)).toSection x) := by
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField_eq_reindex_slotExtend
    (I := I) (M := M) g₀ g₁]
  rw [rfns_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 2 3
    (slotExtend (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀))
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.innerCoreInPerm10 m x]
  exact rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 2
    (connDiffSection (I := I) g₁ g₀) m x

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedSectionVars false in
theorem b4_gradCore_le (g₀ g₁ : SmoothRiemannianMetric I M) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 4 i
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffGradContrInsertionField
            (I := I) g₀ g₁)).toSection x) ≤
      (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (i + 1)) x
          ((iteratedCovGrad (I := I) g₀ 1 2 (i + 1)
            (connDiffSection (I := I) g₁ g₀)).toSection x) := by
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffGradContrInsertionField_eq_reindex_slotExtend
    (I := I) (M := M) g₀ g₁]
  rw [rfns_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 2 4
    (slotExtend (I := I) (M := M) g₀ 1 3
      (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)))
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.innerCoreInPerm10 i x]
  refine le_trans (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 3
    (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)) i x) ?_
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  exact le_of_eq (rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 1 2 i
    (connDiffSection (I := I) g₁ g₀) x)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedSectionVars false in
theorem b4_quadArm_capped (g₀ : SmoothRiemannianMetric I M)
    (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j)
    (core : SmoothCcTensor g₀ 3 4) (W23 : SmoothCcTensor g₀ 2 3)
    (CA : ℕ → ℝ) (hCA_nn : ∀ j, 0 ≤ CA j) {fr : ℝ} (hfr : 0 ≤ fr)
    {i l : ℕ} (hl : l ≤ i) (x : M)
    (hcore : ∀ n, n ≤ l → riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + n) x
      ((iteratedCovGrad (I := I) g₀ 3 4 n core).toSection x) ≤
      fr ^ 2 * CA n * Combinatorics.boundedFactorGridWindow b (i + 1) (n + 2))
    (hW : ∀ m, m ≤ l → riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + m) x
      ((iteratedCovGrad (I := I) g₀ 2 3 m W23).toSection x) ≤
      fr * CA m * Combinatorics.boundedFactorGridWindow b (i + 1) (m + 2)) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 2 4 l
          (appCcRS (I := I) (M := M) g₀ 2 3 4 core W23)).toSection x) ≤
      (appCcGdiag (E := E) l *
          ∑ n ∈ Finset.range (l + 1), ∑ m ∈ Finset.range (l + 1 - n),
            fr ^ 3 * CA n * CA m *
              Combinatorics.windowPairCellCount (n + 2) (m + 2)) *
        Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
  refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
    (I := I) (M := M) g₀ l 2 3 4 core W23 x) ?_
  have hwin_nn : ∀ K W : ℕ, 0 ≤ Combinatorics.boundedFactorGridWindow b K W :=
    fun K W => Combinatorics.boundedFactorGridWindow_nonneg b hb K W
  have hterm : ∀ n ∈ Finset.range (l + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + n) x
          ((iteratedCovGrad (I := I) g₀ 3 4 n core).toSection x) *
        ∑ m ∈ Finset.range (l + 1 - n),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + m) x
            ((iteratedCovGrad (I := I) g₀ 2 3 m W23).toSection x) ≤
      (∑ m ∈ Finset.range (l + 1 - n),
        fr ^ 3 * CA n * CA m *
          Combinatorics.windowPairCellCount (n + 2) (m + 2)) *
        Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
    intro n hn
    rw [Finset.mem_range] at hn
    have h1 := hcore n (by omega)
    have h2 : (∑ m ∈ Finset.range (l + 1 - n),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + m) x
          ((iteratedCovGrad (I := I) g₀ 2 3 m W23).toSection x)) ≤
        ∑ m ∈ Finset.range (l + 1 - n),
          fr * CA m * Combinatorics.boundedFactorGridWindow b (i + 1) (m + 2) := by
      refine Finset.sum_le_sum (fun m hm => ?_)
      rw [Finset.mem_range] at hm
      exact hW m (by omega)
    have hprod : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + n) x
          ((iteratedCovGrad (I := I) g₀ 3 4 n core).toSection x) *
        (∑ m ∈ Finset.range (l + 1 - n),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + m) x
            ((iteratedCovGrad (I := I) g₀ 2 3 m W23).toSection x)) ≤
        (fr ^ 2 * CA n * Combinatorics.boundedFactorGridWindow b (i + 1) (n + 2)) *
          ∑ m ∈ Finset.range (l + 1 - n),
            fr * CA m * Combinatorics.boundedFactorGridWindow b (i + 1) (m + 2) :=
      mul_le_mul h1 h2
        (Finset.sum_nonneg (fun m _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (3 + m) x _))
        (mul_nonneg (mul_nonneg (pow_nonneg hfr 2) (hCA_nn n)) (hwin_nn (i + 1) (n + 2)))
    refine le_trans hprod ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_le_sum (fun m hm => ?_)
    rw [Finset.mem_range] at hm
    have hww := Combinatorics.boundedFactorGridWindow_mul_le b hb (i + 1) (n + 2) (m + 2)
      (by omega) (by omega)
    have hmono : Combinatorics.boundedFactorGridWindow b (i + 1) ((n + 2) + (m + 2) - 1) ≤
        Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) :=
      Combinatorics.boundedFactorGridWindow_mono b hb (le_refl (i + 1)) (by omega)
    have hc_nn : (0 : ℝ) ≤ fr ^ 3 * CA n * CA m :=
      mul_nonneg (mul_nonneg (pow_nonneg hfr 3) (hCA_nn n)) (hCA_nn m)
    calc (fr ^ 2 * CA n * Combinatorics.boundedFactorGridWindow b (i + 1) (n + 2)) *
            (fr * CA m * Combinatorics.boundedFactorGridWindow b (i + 1) (m + 2))
        = (fr ^ 3 * CA n * CA m) *
            (Combinatorics.boundedFactorGridWindow b (i + 1) (n + 2) *
              Combinatorics.boundedFactorGridWindow b (i + 1) (m + 2)) := by ring
      _ ≤ (fr ^ 3 * CA n * CA m) *
            (Combinatorics.windowPairCellCount (n + 2) (m + 2) *
              Combinatorics.boundedFactorGridWindow b (i + 1) ((n + 2) + (m + 2) - 1)) :=
          mul_le_mul_of_nonneg_left hww hc_nn
      _ ≤ (fr ^ 3 * CA n * CA m) *
            (Combinatorics.windowPairCellCount (n + 2) (m + 2) *
              Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hmono
              (Combinatorics.windowPairCellCount_nonneg (n + 2) (m + 2)))
            hc_nn
      _ = fr ^ 3 * CA n * CA m *
            Combinatorics.windowPairCellCount (n + 2) (m + 2) *
            Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by ring
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm)
    (appCcGdiag_nonneg (E := E) l)) ?_
  rw [← Finset.sum_mul]
  exact le_of_eq (by ring)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
lemma b4_coeff_into_sqrt {c X w : ℝ} (hc : 0 ≤ c) :
    c * Real.sqrt (X * w) = Real.sqrt ((c ^ 2 * X) * w) := by
  rw [show (c ^ 2 * X) * w = c ^ 2 * (X * w) from by ring]
  rw [Real.sqrt_mul (sq_nonneg c) (X * w), Real.sqrt_sq hc]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
lemma b4_sqrt_le_coeff_mul {A c B : ℝ} (hA : A ≤ c ^ 2 * B) (hc : 0 ≤ c) :
    Real.sqrt A ≤ c * Real.sqrt B := by
  refine le_trans (Real.sqrt_le_sqrt hA) ?_
  rw [Real.sqrt_mul (sq_nonneg c) B, Real.sqrt_sq hc]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
lemma b4_young_head3 {T e btop c1 c2 c3 w : ℝ}
    (hbtop : 0 ≤ btop) (hw : 0 ≤ w) (he : 0 ≤ e)
    (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hc3 : 0 ≤ c3) (hT0 : 0 ≤ T)
    (hT : Real.sqrt T ≤ e * Real.sqrt btop
      + (Real.sqrt (c1 * w) + Real.sqrt (c2 * w) + Real.sqrt (c3 * w))) :
    T ≤ (3 / 2) * e ^ 2 * btop + 9 * (c1 + c2 + c3) * w := by
  set u : ℝ := e * Real.sqrt btop with hu_def
  set v : ℝ := Real.sqrt (c1 * w) + Real.sqrt (c2 * w) + Real.sqrt (c3 * w) with hv_def
  have hu0 : 0 ≤ u := mul_nonneg he (Real.sqrt_nonneg _)
  have hv0 : 0 ≤ v := by
    have := Real.sqrt_nonneg (c1 * w)
    have := Real.sqrt_nonneg (c2 * w)
    have := Real.sqrt_nonneg (c3 * w)
    linarith
  have hTuv : T ≤ (u + v) ^ 2 := by
    have hsq : Real.sqrt T ^ 2 ≤ (u + v) ^ 2 := by
      nlinarith [hT, Real.sqrt_nonneg T]
    rw [Real.sq_sqrt hT0] at hsq
    exact hsq
  have hyoung := rfns_tl_young_sq u v (1 / 2) (by norm_num)
  have hu2 : u ^ 2 = e ^ 2 * btop := by
    rw [hu_def, mul_pow, Real.sq_sqrt hbtop]
  have hv2 : v ^ 2 ≤ 3 * (c1 * w + c2 * w + c3 * w) := by
    have h1 : Real.sqrt (c1 * w) ^ 2 = c1 * w := Real.sq_sqrt (by positivity)
    have h2 : Real.sqrt (c2 * w) ^ 2 = c2 * w := Real.sq_sqrt (by positivity)
    have h3 : Real.sqrt (c3 * w) ^ 2 = c3 * w := Real.sq_sqrt (by positivity)
    rw [hv_def]
    nlinarith [sq_nonneg (Real.sqrt (c1 * w) - Real.sqrt (c2 * w)),
      sq_nonneg (Real.sqrt (c1 * w) - Real.sqrt (c3 * w)),
      sq_nonneg (Real.sqrt (c2 * w) - Real.sqrt (c3 * w))]
  have hinv : ((1 : ℝ) / 2)⁻¹ = 2 := by norm_num
  rw [hinv] at hyoung
  calc T ≤ (u + v) ^ 2 := hTuv
    _ ≤ (1 + 1 / 2) * u ^ 2 + (1 + 2) * v ^ 2 := hyoung
    _ ≤ (3 / 2) * e ^ 2 * btop + 9 * (c1 + c2 + c3) * w := by
        rw [hu2]
        nlinarith [hv2]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedSectionVars false in
lemma b4_sqrt_eightArm (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (v1 v2 v3 v4 v5 v6 v7 v8 : TensorRSSpace r s I x) :
    Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x
        (v1 + v2 + v3 + v4 + v5 + v6 - v7 - v8)) ≤
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x v1)
        + Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x v2)
        + Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x v3)
        + Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x v4)
        + Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x v5)
        + Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x v6)
        + Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x v7)
        + Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x v8) := by
  have c1 := b1_sqrt_rfns_add_le (I := I) (M := M) g r s x v1 v2
  have c2 := b1_sqrt_rfns_add_le (I := I) (M := M) g r s x (v1 + v2) v3
  have c3 := b1_sqrt_rfns_add_le (I := I) (M := M) g r s x (v1 + v2 + v3) v4
  have c4 := b1_sqrt_rfns_add_le (I := I) (M := M) g r s x (v1 + v2 + v3 + v4) v5
  have c5 := b1_sqrt_rfns_add_le (I := I) (M := M) g r s x (v1 + v2 + v3 + v4 + v5) v6
  have c6 := b1_sqrt_rfns_sub_le (I := I) (M := M) g r s x (v1 + v2 + v3 + v4 + v5 + v6) v7
  have c7 := b1_sqrt_rfns_sub_le (I := I) (M := M) g r s x
    (v1 + v2 + v3 + v4 + v5 + v6 - v7) v8
  linarith [c1, c2, c3, c4, c5, c6, c7]

end DeTurckRemainderTameLipschitz

set_option linter.unusedSectionVars false in
private lemma k2_coframeS_one_eq_g0FlatCLM (g₀ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K : Fin 1 → Fin n) :
    coframeS (I := I) (M := M) g₀ x 1 e K = DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ x (e (K 0)) := by
  apply cotangentToDualLinear_injective (I := I) (x := x)
  apply LinearMap.ext
  intro w
  rw [cotangentToDualLinear_apply, cotangentToDualLinear_apply, cotangentToDual_apply,
    cotangentToDual_apply]
  rw [show coframeS (I := I) (M := M) g₀ x 1 e K (fun _ : Fin 1 => w) =
      ∏ k : Fin 1, g₀.inner x (e (K k)) w from coframeS_apply (I := I) (M := M) g₀ x 1 e K _]
  rw [Fin.prod_univ_one]
  rw [DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM_apply, dualToCotangent_apply]
  rfl

namespace DeTurckRemainderTameLipschitz

set_option linter.unusedSectionVars false in
lemma k2_fiberNormSqComponent_sharpFlatEndoCc
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) {n : ℕ}
    (e : Fin n → TangentSpace I x)
    (K : Fin 1 → Fin n) (J : Fin 1 → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g₀ x 1 1
        ((DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sharpFlatEndoCc (I := I) g₀ g₁).toSection x) n e K J =
      g₀.inner x
        (inverseMetricSharpFib (I := I) g₁ x
          (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ x (e (K 0)))) (e (J 0)) := by
  rw [show fiberNormSqComponent (I := I) (M := M) g₀ x 1 1
        ((DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sharpFlatEndoCc (I := I) g₀ g₁).toSection x) n e K J =
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sharpFlatEndoCc (I := I) g₀ g₁).toSection x)
        (coframeS (I := I) (M := M) g₀ x 1 e K))
        (fun k => e (J k)) from rfl]
  rw [k2_coframeS_one_eq_g0FlatCLM (I := I) (M := M) g₀ x e K]
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sharpFlatEndoCc_toSection]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        TensorRSSpace.ofCLM
          ((DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ x).comp (inverseMetricSharpFib (I := I) g₁ x)))
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ x (e (K 0))) =
      DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ x
        (inverseMetricSharpFib (I := I) g₁ x
          (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ x (e (K 0)))) from rfl]
  rw [show (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ x
        (inverseMetricSharpFib (I := I) g₁ x
          (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ x (e (K 0)))))
        (fun k => e (J k)) =
      cotangentToDual (I := I) (x := x)
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ x
          (inverseMetricSharpFib (I := I) g₁ x
            (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ x (e (K 0)))))
        (e (J 0)) from by
    rw [cotangentToDual_apply]
    rfl]
  rw [DifferentialGeometry.Analysis.Sobolev.TensorHilbert.cotangentToDual_g0FlatCLM (I := I) g₀ x
    (inverseMetricSharpFib (I := I) g₁ x (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ x (e (K 0)))) (e (J 0))]

set_option linter.unusedSectionVars false in
lemma k2_gram_sum_sq (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (d : Fin n → ℝ)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) :
    g.inner x (∑ j, d j • e j) (∑ l, d l • e l) = ∑ j, d j ^ 2 := by
  classical
  have hbil : g.inner x (∑ j, d j • e j) (∑ l, d l • e l)
      = ∑ j, ∑ l, (d j * d l) * g.inner x (e j) (e l) := by
    rw [show g.inner x (∑ j, d j • e j) = ∑ j, d j • g.inner x (e j) from by
      rw [map_sum]; refine Finset.sum_congr rfl (fun j _ => ?_); rw [map_smul]]
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [ContinuousLinearMap.smul_apply, map_sum, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [map_smul, smul_eq_mul]; ring
  rw [hbil]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_eq_single j]
  · rw [horth j j, if_pos rfl, mul_one]; ring
  · intro l _ hl; rw [horth j l, if_neg (fun h => hl h.symm), mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h
lemma k2_fiberNormSqComponent_compRS_eq
    (g : SmoothRiemannianMetric I M) (a b c : ℕ) (x : M)
    (Φx : TensorRSSpace b c I x) (Wx : TensorRSSpace a b I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (bse : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hbse : ∀ i : Fin n, bse i = e i)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (K : Fin a → Fin n) (J : Fin c → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g x a c
        (show TensorRSSpace a c I x from
          (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φx).comp
            (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from Wx)) n e K J =
      ∑ P : Fin b → Fin n,
        fiberNormSqComponent (I := I) (M := M) g x a b Wx n e K P *
          fiberNormSqComponent (I := I) (M := M) g x b c Φx n e P J := by
  classical
  change (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φx)
      ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from Wx)
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin a) ℝ).compContinuousLinearMap
          (fun k => g.inner x (e (K k)))))
      (fun k => e (J k)) = _
  set wval : Tensor0SSpace b I x :=
    (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from Wx)
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin a) ℝ).compContinuousLinearMap
        (fun k => g.inner x (e (K k)))) with hwval
  have hexp := tensorS_coframe_expansion (I := I) (M := M) g x b e bse hbse horth wval
  conv_lhs => rw [hexp]
  rw [map_sum]
  rw [show (∑ P : Fin b → Fin n,
        (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φx)
          ((wval (fun k : Fin b => e (P k))) • coframeS (I := I) (M := M) g x b e P)) =
      ∑ P : Fin b → Fin n, (wval (fun k : Fin b => e (P k))) •
        (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φx)
          (coframeS (I := I) (M := M) g x b e P) from by
    refine Finset.sum_congr rfl (fun P _ => ?_); rw [map_smul]]
  rw [show ((∑ P : Fin b → Fin n, (wval (fun k : Fin b => e (P k))) •
        (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φx)
          (coframeS (I := I) (M := M) g x b e P)) (fun k => e (J k)) : ℝ) =
      Tensor0SSpace.toModel (∑ P : Fin b → Fin n, (wval (fun k : Fin b => e (P k))) •
        (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φx)
          (coframeS (I := I) (M := M) g x b e P)) (fun k => e (J k)) from rfl]
  rw [← Tensor0SSpace.toModelL_apply, map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [Tensor0SSpace.toModelL_apply, Tensor0SSpace.toModel_smul,
    ContinuousMultilinearMap.smul_apply]
  have hΦcomp : Tensor0SSpace.toModel
      ((show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φx)
        (coframeS (I := I) (M := M) g x b e P)) (fun k => e (J k)) =
      fiberNormSqComponent (I := I) (M := M) g x b c Φx n e P J := rfl
  rw [hΦcomp]
  have hwcomp : wval (fun k : Fin b => e (P k)) =
      fiberNormSqComponent (I := I) (M := M) g x a b Wx n e K P := rfl
  rw [hwcomp, smul_eq_mul]

lemma k2_sum_fin1 {α : Type*} [AddCommMonoid α] {n : ℕ} (f : (Fin 1 → Fin n) → α) :
    ∑ K : Fin 1 → Fin n, f K = ∑ k : Fin n, f (fun _ => k) := by
  classical
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin n)) f (fun k => f (fun _ => k)) ?_
  intro K
  refine congrArg f ?_
  funext i
  rw [Subsingleton.elim i 0]
  rfl

end DeTurckRemainderTameLipschitz

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
