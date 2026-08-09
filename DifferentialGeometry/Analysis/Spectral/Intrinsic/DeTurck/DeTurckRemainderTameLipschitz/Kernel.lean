import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitz.Dim1

/-!
# Raised-slot and refold-kernel contraction operator bounds

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

set_option linter.style.setOption false

set_option maxHeartbeats 1600000

set_option synthInstance.maxHeartbeats 1600000

set_option backward.isDefEq.respectTransparency false

namespace DeTurckRemainderTameLipschitz
end DeTurckRemainderTameLipschitz

open DeTurckRemainderTameLipschitz

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedVariables false in

theorem rfns_appCcRS_sharpFlatEndoCc_contravariantSlot_op_le (g₀ g₁ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    {δ₀ δ : ℝ} (hδ₀ : δ₀ < 1) (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
    (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
    (c : ℕ) (D : SmoothCcTensor g₀ 1 c) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 c x
        ((appCcRS (I := I) (M := M) g₀ 1 1 c D
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sharpFlatEndoCc
            (I := I) g₀ g₁)).toSection x) ≤
      (1 / (1 - δ₀)) ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 c x (D.toSection x) := by
  classical
  have h1δ : (0 : ℝ) < 1 - δ := by linarith
  have h1δ₀ : (0 : ℝ) < 1 - δ₀ := by linarith
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hexpand, hrepr02⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  have hWop : ∀ u : TangentSpace I x,
      g₀.inner x (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo (I := I) g₀ g₁ x u)
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo (I := I) g₀ g₁ x u) ≤
      (1 / (1 - δ₀)) ^ 2 * g₀.inner x u u := by
    intro u
    have hs := DifferentialGeometry.Analysis.Sobolev.TensorHilbert.sqrt_inner_gInvRaisedEndo_le (I := I) (M := M) g₀ g₁
      (fun y => ccTensorBilinSymm (I := I) g₀ P y) htie
      (show δ < 1 from by linarith) hδ0 hbound x u
    have h0T : 0 ≤ g₀.inner x (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo (I := I) g₀ g₁ x u)
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo (I := I) g₀ g₁ x u) :=
      DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg (I := I) (M := M) g₀ x _
    have h0u : 0 ≤ g₀.inner x u u := DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg (I := I) (M := M) g₀ x u
    have hinv : 1 / (1 - δ) ≤ 1 / (1 - δ₀) := by
      rw [div_le_div_iff₀ h1δ h1δ₀]
      linarith
    have hsq := Real.sq_sqrt h0T
    have hsqu := Real.sq_sqrt h0u
    have h1 : Real.sqrt (g₀.inner x
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo (I := I) g₀ g₁ x u)
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo (I := I) g₀ g₁ x u)) ≤
        (1 / (1 - δ₀)) * Real.sqrt (g₀.inner x u u) :=
      le_trans hs (mul_le_mul_of_nonneg_right hinv (Real.sqrt_nonneg _))
    calc g₀.inner x
          (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo (I := I) g₀ g₁ x u)
          (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo (I := I) g₀ g₁ x u)
        = Real.sqrt (g₀.inner x
            (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo (I := I) g₀ g₁ x u)
            (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo (I := I) g₀ g₁ x u)) ^ 2 :=
          hsq.symm
      _ ≤ ((1 / (1 - δ₀)) * Real.sqrt (g₀.inner x u u)) ^ 2 :=
          by nlinarith [h1, Real.sqrt_nonneg (g₀.inner x
            (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo (I := I) g₀ g₁ x u)
            (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo (I := I) g₀ g₁ x u))]
      _ = (1 / (1 - δ₀)) ^ 2 * g₀.inner x u u := by
          rw [mul_pow, hsqu]
  rw [appCcRS_toSection (I := I) (M := M) g₀ 1 1 c D
    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sharpFlatEndoCc (I := I) g₀ g₁) x]
  rw [rfns_rs_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ 1 c x _ e bse hnE hbse horth]
  rw [rfns_rs_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ 1 c x
    (D.toSection x) e bse hnE hbse horth]
  have hcomp : ∀ (K : Fin 1 → Fin n) (J : Fin c → Fin n),
      fiberNormSqComponent (I := I) (M := M) g₀ x 1 c
          (show TensorRSSpace 1 c I x from
            (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace c I x from D.toSection x).comp
              (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
                (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sharpFlatEndoCc (I := I) g₀ g₁).toSection x)) n e K J =
        ∑ Pf : Fin 1 → Fin n,
          fiberNormSqComponent (I := I) (M := M) g₀ x 1 1
              ((DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sharpFlatEndoCc (I := I) g₀ g₁).toSection x) n e K Pf *
            fiberNormSqComponent (I := I) (M := M) g₀ x 1 c (D.toSection x) n e Pf J :=
    fun K J => k2_fiberNormSqComponent_compRS_eq (I := I) (M := M) g₀ 1 1 c x
      (D.toSection x) ((DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sharpFlatEndoCc (I := I) g₀ g₁).toSection x)
      e bse hbse horth K J
  refine le_trans (le_of_eq (Finset.sum_congr rfl (fun K _ =>
    Finset.sum_congr rfl (fun J _ => by rw [hcomp K J])))) ?_
  rw [Finset.sum_comm]
  rw [show (∑ K : Fin 1 → Fin n, ∑ J : Fin c → Fin n,
      (fiberNormSqComponent (I := I) (M := M) g₀ x 1 c (D.toSection x) n e K J) ^ 2) =
    ∑ J : Fin c → Fin n, ∑ K : Fin 1 → Fin n,
      (fiberNormSqComponent (I := I) (M := M) g₀ x 1 c (D.toSection x) n e K J) ^ 2 from
    Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun J _ => ?_)
  set y : Fin n → ℝ := fun p =>
    fiberNormSqComponent (I := I) (M := M) g₀ x 1 c (D.toSection x) n e (fun _ => p) J
    with hy_def
  set u : TangentSpace I x := ∑ p : Fin n, y p • e p with hu_def
  have hsfe_val : ∀ K Pf : Fin 1 → Fin n,
      fiberNormSqComponent (I := I) (M := M) g₀ x 1 1
          ((DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sharpFlatEndoCc (I := I) g₀ g₁).toSection x) n e K Pf =
        g₀.inner x (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo (I := I) g₀ g₁ x (e (K 0))) (e (Pf 0)) := by
    intro K Pf
    rw [k2_fiberNormSqComponent_sharpFlatEndoCc (I := I) (M := M) g₀ g₁ x e K Pf]
    rw [DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo_apply (I := I) g₀ g₁ x (e (K 0))]
  have hinner_sum : ∀ K : Fin 1 → Fin n,
      (∑ Pf : Fin 1 → Fin n,
        fiberNormSqComponent (I := I) (M := M) g₀ x 1 1
            ((DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sharpFlatEndoCc (I := I) g₀ g₁).toSection x) n e K Pf *
          fiberNormSqComponent (I := I) (M := M) g₀ x 1 c (D.toSection x) n e Pf J) =
      g₀.inner x u (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo (I := I) g₀ g₁ x (e (K 0))) := by
    intro K
    rw [k2_sum_fin1 (fun Pf : Fin 1 → Fin n =>
      fiberNormSqComponent (I := I) (M := M) g₀ x 1 1
          ((DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sharpFlatEndoCc (I := I) g₀ g₁).toSection x) n e K Pf *
        fiberNormSqComponent (I := I) (M := M) g₀ x 1 c (D.toSection x) n e Pf J)]
    rw [hu_def]
    rw [show g₀.inner x (∑ p : Fin n, y p • e p)
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo (I := I) g₀ g₁ x (e (K 0))) =
      ∑ p : Fin n, y p * g₀.inner x (e p)
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo (I := I) g₀ g₁ x (e (K 0))) from by
      rw [show g₀.inner x (∑ p : Fin n, y p • e p) =
          ∑ p : Fin n, y p • g₀.inner x (e p) from by
        rw [map_sum]; exact Finset.sum_congr rfl (fun p _ => by rw [map_smul])]
      rw [ContinuousLinearMap.sum_apply]
      exact Finset.sum_congr rfl (fun p _ => by
        rw [ContinuousLinearMap.smul_apply, smul_eq_mul])]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [hsfe_val K (fun _ => p)]
    rw [g₀.symm x (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo (I := I) g₀ g₁ x (e (K 0))) (e p)]
    rw [hy_def]
    ring
  rw [Finset.sum_congr rfl (fun K (_ : K ∈ Finset.univ) => by rw [hinner_sum K] :
    ∀ K ∈ Finset.univ, ((∑ Pf : Fin 1 → Fin n,
      fiberNormSqComponent (I := I) (M := M) g₀ x 1 1
          ((DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sharpFlatEndoCc (I := I) g₀ g₁).toSection x) n e K Pf *
        fiberNormSqComponent (I := I) (M := M) g₀ x 1 c (D.toSection x) n e Pf J) ^ 2) =
      (g₀.inner x u (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo (I := I) g₀ g₁ x (e (K 0)))) ^ 2)]
  rw [k2_sum_fin1 (fun K : Fin 1 → Fin n =>
    (g₀.inner x u (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo (I := I) g₀ g₁ x (e (K 0)))) ^ 2)]
  refine le_trans (gFrame_adjoint_parseval_le (I := I) (M := M) g₀ x
    (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo (I := I) g₀ g₁ x) ((1 / (1 - δ₀)) ^ 2) (by positivity)
    hWop e hpars u) ?_
  rw [hu_def, k2_gram_sum_sq (I := I) (M := M) g₀ x e y horth]
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (by positivity)
  rw [k2_sum_fin1 (fun K : Fin 1 → Fin n =>
    (fiberNormSqComponent (I := I) (M := M) g₀ x 1 c (D.toSection x) n e K J) ^ 2)]

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
private def k3_slotExtendIterFib (g : SmoothRiemannianMetric I M) (b c : ℕ) (x : M)
    (A : Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x) :
    ∀ w : ℕ, Tensor0SSpace (b + w) I x →L[ℝ] Tensor0SSpace (c + w) I x
  | 0 => A
  | (w + 1) => slotExtendFib (I := I) (M := M) g (b + w) (c + w) x
      (k3_slotExtendIterFib g b c x A w)

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
private lemma k3_appCcLeibnizPsi_succ_succ_eq (g : SmoothRiemannianMetric I M) (b c : ℕ)
    (Φ : SmoothCcTensor g b c) (i j : ℕ) :
    appCcLeibnizPsi (I := I) (M := M) g b c Φ (i + 1) (j + 1) =
      (if j + 1 < i + 1 then
          covGrad (I := I) (M := M) g (b + (j + 1)) (c + i)
            (appCcLeibnizPsi (I := I) (M := M) g b c Φ i (j + 1))
        else 0) +
        slotExtend (I := I) (M := M) g (b + j) (c + i)
          (appCcLeibnizPsi (I := I) (M := M) g b c Φ i j) := by
  rw [show appCcLeibnizPsi (I := I) (M := M) g b c Φ (i + 1) (j + 1) =
      (if j + 1 < i + 1 then
          covGrad (I := I) (M := M) g (b + (j + 1)) (c + i)
            (appCcLeibnizPsi (I := I) (M := M) g b c Φ i (j + 1))
        else 0) +
        castSrcCc g (c + (i + 1)) (by omega : (b + j) + 1 = b + (j + 1))
          (castRankCc_db g ((b + j) + 1) (by omega : (c + i) + 1 = c + (i + 1))
            (slotExtend (I := I) (M := M) g (b + j) (c + i)
              (appCcLeibnizPsi (I := I) (M := M) g b c Φ i j))) from rfl]
  rw [castRankCc_db, castSrcCc]

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
private lemma k3_appCcLeibnizPsi_diag_toSection (g : SmoothRiemannianMetric I M) (b c : ℕ)
    (Φ : SmoothCcTensor g b c) (i : ℕ) (x : M) :
    ((appCcLeibnizPsi (I := I) (M := M) g b c Φ i i).toSection x :
        Tensor0SSpace (b + i) I x →L[ℝ] Tensor0SSpace (c + i) I x) =
      k3_slotExtendIterFib (I := I) (M := M) g b c x
        (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x) i := by
  induction i with
  | zero => rfl
  | succ i ih =>
      have hdiag : appCcLeibnizPsi (I := I) (M := M) g b c Φ (i + 1) (i + 1) =
          slotExtend (I := I) (M := M) g (b + i) (c + i)
            (appCcLeibnizPsi (I := I) (M := M) g b c Φ i i) := by
        rw [k3_appCcLeibnizPsi_succ_succ_eq (I := I) (M := M) g b c Φ i i]
        rw [if_neg (by omega : ¬ (i + 1 < i + 1)), zero_add]
      rw [hdiag]
      rw [show (k3_slotExtendIterFib (I := I) (M := M) g b c x
            (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x) (i + 1)) =
          slotExtendFib (I := I) (M := M) g (b + i) (c + i) x
            (k3_slotExtendIterFib (I := I) (M := M) g b c x
              (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x) i)
          from rfl]
      rw [← ih]
      rfl

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
private lemma k3_fiberNormSqComponent_slotExtendFib_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (A : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (K' : Fin (r + 1) → Fin n) (J' : Fin (s + 1) → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g x (r + 1) (s + 1)
        (show TensorRSSpace (r + 1) (s + 1) I x from slotExtendFib (I := I) (M := M) g r s x A)
        n e K' J' =
      (if J' 0 = K' 0 then (1 : ℝ) else 0) *
        fiberNormSqComponent (I := I) (M := M) g x r s
          (show TensorRSSpace r s I x from A) n e
          (fun k => K' (Fin.succ k)) (fun k => J' (Fin.succ k)) := by
  classical
  have hcomp : fiberNormSqComponent (I := I) (M := M) g x (r + 1) (s + 1)
        (show TensorRSSpace (r + 1) (s + 1) I x from slotExtendFib (I := I) (M := M) g r s x A)
        n e K' J' =
      Tensor0SSpace.toModel
        (slotExtendFib (I := I) (M := M) g r s x A
          (coframeS (I := I) (M := M) g x (r + 1) e K'))
        (Fin.cons (show E from e (J' 0)) (fun k : Fin s => (show E from e (J' (Fin.succ k))))) := by
    rw [show fiberNormSqComponent (I := I) (M := M) g x (r + 1) (s + 1)
          (show TensorRSSpace (r + 1) (s + 1) I x from slotExtendFib (I := I) (M := M) g r s x A)
          n e K' J' =
        Tensor0SSpace.toModel
          (slotExtendFib (I := I) (M := M) g r s x A
            (coframeS (I := I) (M := M) g x (r + 1) e K'))
          (fun k => (show E from e (J' k))) from rfl]
    congr 1
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · rw [Fin.cons_zero]
    · rw [Fin.cons_succ]
  rw [hcomp]
  rw [slotExtendFib_apply_eval (I := I) (M := M) g r s x A
    (coframeS (I := I) (M := M) g x (r + 1) e K') (show E from e (J' 0))
    (fun k : Fin s => (show E from e (J' (Fin.succ k))))]
  have hcurry : (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x)
        (coframeS (I := I) (M := M) g x (r + 1) e K') (show E from e (J' 0)) =
      (if J' 0 = K' 0 then (1 : ℝ) else 0) •
        coframeS (I := I) (M := M) g x r e (fun k => K' (Fin.succ k)) := by
    apply Tensor0SSpace.toModel_injective
    refine ContinuousMultilinearMap.ext (fun u => ?_)
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := r)
      (coframeS (I := I) (M := M) g x (r + 1) e K') (show E from e (J' 0)) u]
    have hcf : Tensor0SSpace.toModel (coframeS (I := I) (M := M) g x (r + 1) e K')
          (Fin.cons (show E from e (J' 0)) u) =
        coframeS (I := I) (M := M) g x (r + 1) e K' (Fin.cons (show E from e (J' 0)) u) := rfl
    rw [hcf, coframeS_apply (I := I) (M := M) g x (r + 1) e K' (Fin.cons (show E from e (J' 0)) u)]
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [horth (K' 0) (J' 0)]
    rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    have hcf2 : Tensor0SSpace.toModel (coframeS (I := I) (M := M) g x r e
          (fun k => K' (Fin.succ k))) u =
        coframeS (I := I) (M := M) g x r e (fun k => K' (Fin.succ k)) u := rfl
    rw [hcf2, coframeS_apply (I := I) (M := M) g x r e (fun k => K' (Fin.succ k)) u]
    by_cases h : K' 0 = J' 0
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun hc => h hc.symm)]
  rw [hcurry, map_smul, Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
    smul_eq_mul]
  congr 1

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
private lemma k3_metricInner_injective (g₁ : SmoothRiemannianMetric I M) (x : M)
    {a b : TangentSpace I x}
    (hab : ∀ w : TangentSpace I x, g₁.inner x a w = g₁.inner x b w) : a = b := by
  by_contra hne
  have hsub : a - b ≠ 0 := sub_ne_zero.mpr hne
  have hpos := g₁.pos x (a - b) hsub
  have hzero : g₁.inner x (a - b) (a - b) = 0 := by
    have hsymm₁ : g₁.inner x (a - b) (a - b) =
        g₁.inner x (a - b) a - g₁.inner x (a - b) b := by rw [← map_sub]
    rw [hsymm₁, g₁.symm x (a - b) a, g₁.symm x (a - b) b]
    have e1 : g₁.inner x a (a - b) = g₁.inner x b (a - b) := hab (a - b)
    rw [e1]; ring
  exact absurd hzero (ne_of_gt hpos)

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
private lemma k3_cometric_sum_eq_invSharp (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (b : TangentSpace I x) :
    ∑ k : Fin (Module.finrank ℝ E),
        g₀.inner x b ((Module.finBasis ℝ E) k) •
          DeTurck.cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)) =
      inverseMetricSharpFib (I := I) g₁ x
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ x b) := by
  classical
  apply k3_metricInner_injective (I := I) g₁ x
  intro w
  have hcoord : ∀ k : Fin (Module.finrank ℝ E),
      (Module.finBasis ℝ E).cDualBasis k (w : E) =
        (Module.finBasis ℝ E).repr (w : E) k := by
    intro k
    rw [show ((Module.finBasis ℝ E).cDualBasis k) =
        LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord k) from by
      rw [Module.Basis.cDualBasis, Module.Basis.map_apply]
      congr 1
      exact congrFun (Module.Basis.coe_dualBasis (Module.finBasis ℝ E)) k]
    rw [LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
  rw [map_sum, ContinuousLinearMap.sum_apply]
  have hlhs : ∀ k : Fin (Module.finrank ℝ E),
      (g₁.inner x (g₀.inner x b ((Module.finBasis ℝ E) k) •
          DeTurck.cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))) w =
        g₀.inner x b ((Module.finBasis ℝ E) k) *
          (Module.finBasis ℝ E).repr (w : E) k := by
    intro k
    rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    congr 1
    have hinner : g₁.inner x (DeTurck.cometricLmodel (I := I) g₁ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k))) w =
        (Module.finBasis ℝ E).cDualBasis k (w : E) := by
      have h1 : DeTurck.cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)) =
          inverseMetricSharpFib (I := I) g₁ x
            ((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 1 x).symm
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))) := rfl
      rw [h1, inverseMetricSharpFib_inner (I := I) g₁ x _ w, cotangentToDualLinear_apply,
        cotangentToDual_apply]
      change (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k)) (fun _ : Fin 1 => (w : E)) = _
      rw [Tensor0SBundle.model_covectorOfCLM_apply]
    rw [hinner, hcoord k]
  rw [Finset.sum_congr rfl (fun k _ => hlhs k)]
  rw [inverseMetricSharpFib_inner, cotangentToDualLinear_apply,
    DifferentialGeometry.Analysis.Sobolev.TensorHilbert.cotangentToDual_g0FlatCLM]
  have hwexp : (w : TangentSpace I x) =
      ∑ k : Fin (Module.finrank ℝ E),
        (Module.finBasis ℝ E).repr (w : E) k • ((Module.finBasis ℝ E) k : TangentSpace I x) := by
    have h := (Module.finBasis ℝ E).sum_repr (w : E)
    exact h.symm
  conv_rhs => rw [hwexp, map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [ContinuousLinearMap.map_smul, smul_eq_mul, mul_comm]

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
private lemma k3_cometric_dualsum_inner_collapse (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (a c : TangentSpace I x) :
    (∑ k : Fin (Module.finrank ℝ E),
        g₀.inner x c ((Module.finBasis ℝ E) k) *
          g₀.inner x a (DeTurck.cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))) =
      g₀.inner x a (inverseMetricSharpFib (I := I) g₁ x
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ x c)) := by
  classical
  have hsumeq := k3_cometric_sum_eq_invSharp (I := I) (M := M) g₀ g₁ x c
  calc (∑ k : Fin (Module.finrank ℝ E),
        g₀.inner x c ((Module.finBasis ℝ E) k) *
          g₀.inner x a (DeTurck.cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k))))
      = ∑ k : Fin (Module.finrank ℝ E), g₀.inner x a
          (g₀.inner x c ((Module.finBasis ℝ E) k) •
            DeTurck.cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [ContinuousLinearMap.map_smul, smul_eq_mul]
    _ = g₀.inner x a
          (∑ k : Fin (Module.finrank ℝ E),
            g₀.inner x c ((Module.finBasis ℝ E) k) •
              DeTurck.cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))) := (map_sum (g₀.inner x a) _ _).symm
    _ = g₀.inner x a (inverseMetricSharpFib (I := I) g₁ x
          (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.g0FlatCLM (I := I) g₀ x c)) := by
        rw [hsumeq]

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
private lemma k3_slotPerm_coframeS (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (d : ℕ) (ρ : Equiv.Perm (Fin d))
    (Q : Fin d → Fin n) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM (I := I) ρ x
        (coframeS (I := I) (M := M) g x d e Q) =
      coframeS (I := I) (M := M) g x d e (fun k => Q (ρ.symm k)) := by
  classical
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun z => ?_)
  beta_reduce
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM_apply (I := I) ρ x
    (coframeS (I := I) (M := M) g x d e Q)]
  rw [Tensor0SSpace.toModel_ofModel]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  have h1 : Tensor0SSpace.toModel (coframeS (I := I) (M := M) g x d e Q)
        (fun i => z (ρ i)) =
      coframeS (I := I) (M := M) g x d e Q (fun i => z (ρ i)) := rfl
  have h2 : Tensor0SSpace.toModel
        (coframeS (I := I) (M := M) g x d e (fun k => Q (ρ.symm k))) z =
      coframeS (I := I) (M := M) g x d e (fun k => Q (ρ.symm k)) z := rfl
  rw [h1, h2, coframeS_apply (I := I) (M := M) g x d e Q (fun i => z (ρ i)),
    coframeS_apply (I := I) (M := M) g x d e (fun k => Q (ρ.symm k)) z]
  refine Fintype.prod_equiv ρ _ _ (fun a => ?_)
  rw [Equiv.symm_apply_apply]

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
private lemma k3_fnsc_comp_slotPerm (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (d s : ℕ)
    (A : Tensor0SSpace d I x →L[ℝ] Tensor0SSpace s I x) (ρ : Equiv.Perm (Fin d))
    (Q : Fin d → Fin n) (L : Fin s → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g x d s
        (show TensorRSSpace d s I x from
          A.comp (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM (I := I) ρ x))
        n e Q L =
      fiberNormSqComponent (I := I) (M := M) g x d s
        (show TensorRSSpace d s I x from A) n e (fun k => Q (ρ.symm k)) L := by
  have hread : fiberNormSqComponent (I := I) (M := M) g x d s
        (show TensorRSSpace d s I x from
          A.comp (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM (I := I) ρ x))
        n e Q L =
      Tensor0SSpace.toModel
        (A (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM (I := I) ρ x
          (coframeS (I := I) (M := M) g x d e Q)))
        (fun k => e (L k)) := by
    unfold fiberNormSqComponent coframeS
    rfl
  have hread2 : fiberNormSqComponent (I := I) (M := M) g x d s
        (show TensorRSSpace d s I x from A) n e (fun k => Q (ρ.symm k)) L =
      Tensor0SSpace.toModel
        (A (coframeS (I := I) (M := M) g x d e (fun k => Q (ρ.symm k))))
        (fun k => e (L k)) := by
    unfold fiberNormSqComponent coframeS
    rfl
  rw [hread, hread2, k3_slotPerm_coframeS (I := I) (M := M) g x e d ρ Q]

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
private lemma k3_doubleTrace_component_eq (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ a b : Fin n, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (Q : Fin 4 → Fin n) (L : Fin 2 → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
        (show TensorRSSpace 4 2 I x from DeTurck.cometricDoubleTraceFib (I := I) g₁ 2 x)
        n e Q L =
      (if Q 2 = L 0 then (1 : ℝ) else 0) * (if Q 3 = L 1 then (1 : ℝ) else 0) *
        g₀.inner x (e (Q 0))
          (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo
            (I := I) g₀ g₁ x (e (Q 1))) := by
  classical
  have hread : fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
        (show TensorRSSpace 4 2 I x from DeTurck.cometricDoubleTraceFib (I := I) g₁ 2 x)
        n e Q L =
      Tensor0SSpace.toModel
        ((DeTurck.cometricDoubleTraceFib (I := I) g₁ 2 x)
          (coframeS (I := I) (M := M) g₀ x 4 e Q))
        (fun k => e (L k)) := by
    unfold fiberNormSqComponent coframeS
    rfl
  rw [hread, DeTurck.cometricDoubleTraceFib_toModel]
  rw [DeTurck.modelDoubleTrace_apply (E := E) 2 (DeTurck.cometricLmodel (I := I) g₁ x) _
    (fun k => e (L k))]
  have hterm : ∀ k : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 4 e Q)
        (Fin.cons (DeTurck.cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          (Fin.cons ((Module.finBasis ℝ E) k) (fun l => e (L l)))) =
        (g₀.inner x (e (Q 2)) (e (L 0)) * g₀.inner x (e (Q 3)) (e (L 1))) *
          (g₀.inner x (e (Q 1)) ((Module.finBasis ℝ E) k) *
            g₀.inner x (e (Q 0)) (DeTurck.cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))) := by
    intro k
    set base : Fin 4 → E :=
      Fin.cons (DeTurck.cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        (Fin.cons ((Module.finBasis ℝ E) k) (fun l => e (L l))) with hbase
    have hcfeval : Tensor0SBundle.Tensor0SSpace.toModel
          (coframeS (I := I) (M := M) g₀ x 4 e Q) base =
        ∏ i : Fin 4, g₀.inner x (e (Q i)) (base i) :=
      coframeS_apply (I := I) (M := M) g₀ x 4 e Q base
    rw [hcfeval, Fin.prod_univ_four]
    have hb0 : base 0 = DeTurck.cometricLmodel (I := I) g₁ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k)) := by rw [hbase, Fin.cons_zero]
    have hb1 : base 1 = (Module.finBasis ℝ E) k := by
      rw [hbase, show (1 : Fin 4) = Fin.succ 0 from rfl, Fin.cons_succ, Fin.cons_zero]
    have hb2 : base 2 = e (L 0) := by
      rw [hbase, show (2 : Fin 4) = Fin.succ 1 from rfl, Fin.cons_succ,
        show (1 : Fin 3) = Fin.succ 0 from rfl, Fin.cons_succ]
    have hb3 : base 3 = e (L 1) := by
      rw [hbase, show (3 : Fin 4) = Fin.succ 2 from rfl, Fin.cons_succ,
        show (2 : Fin 3) = Fin.succ 1 from rfl, Fin.cons_succ]
    rw [hb0, hb1, hb2, hb3]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  rw [← Finset.mul_sum]
  rw [k3_cometric_dualsum_inner_collapse (I := I) (M := M) g₀ g₁ x (e (Q 0)) (e (Q 1))]
  rw [horth (Q 2) (L 0), horth (Q 3) (L 1)]
  rw [DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo_apply
    (I := I) g₀ g₁ x (e (Q 1))]

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
private lemma k3_pair_delta_sum_right {nn : ℕ} (a b : Fin nn) :
    (∑ L : Fin 2 → Fin nn,
      (if a = L 0 then (1 : ℝ) else 0) * (if b = L 1 then (1 : ℝ) else 0)) = 1 := by
  classical
  rw [← (finTwoArrowEquiv (Fin nn)).symm.sum_comp
    (fun L : Fin 2 → Fin nn =>
      (if a = L 0 then (1 : ℝ) else 0) * (if b = L 1 then (1 : ℝ) else 0))]
  rw [Fintype.sum_prod_type]
  simp only [finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hin : ∀ j0 : Fin nn,
      (∑ j1 : Fin nn, (if a = j0 then (1 : ℝ) else 0) * (if b = j1 then (1 : ℝ) else 0))
        = (if a = j0 then (1 : ℝ) else 0) := by
    intro j0
    rw [← Finset.mul_sum, Finset.sum_ite_eq Finset.univ b (fun _ => (1 : ℝ))]
    simp
  rw [Finset.sum_congr rfl (fun j0 _ => hin j0)]
  rw [Finset.sum_ite_eq Finset.univ a (fun _ => (1 : ℝ))]
  simp

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
private lemma k3_sum_fin4_split {nn : ℕ} (F : (Fin 4 → Fin nn) → ℝ) :
    ∑ Q : Fin 4 → Fin nn, F Q =
      ∑ q0 : Fin nn, ∑ q1 : Fin nn, ∑ Q2 : Fin 2 → Fin nn,
        F (Fin.cons q0 (Fin.cons q1 Q2)) := by
  classical
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin 4 => Fin nn))
    (fun pr : Fin nn × (Fin 3 → Fin nn) => F (Fin.cons pr.1 pr.2))
    (fun Q : Fin 4 → Fin nn => F Q)
    (fun pr => by simp [Fin.consEquiv])]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun q0 _ => ?_)
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin 3 => Fin nn))
    (fun pr : Fin nn × (Fin 2 → Fin nn) => F (Fin.cons q0 (Fin.cons pr.1 pr.2)))
    (fun Q' : Fin 3 → Fin nn => F (Fin.cons q0 Q'))
    (fun pr => by simp [Fin.consEquiv])]
  rw [Fintype.sum_prod_type]

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
private lemma k3_cons_indices {nn : ℕ} (q0 q1 : Fin nn) (Q2 : Fin 2 → Fin nn) :
    (Fin.cons q0 (Fin.cons q1 Q2) : Fin 4 → Fin nn) 0 = q0 ∧
    (Fin.cons q0 (Fin.cons q1 Q2) : Fin 4 → Fin nn) 1 = q1 ∧
    (Fin.cons q0 (Fin.cons q1 Q2) : Fin 4 → Fin nn) 2 = Q2 0 ∧
    (Fin.cons q0 (Fin.cons q1 Q2) : Fin 4 → Fin nn) 3 = Q2 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Fin.cons_zero]
  · rw [show (1 : Fin 4) = Fin.succ 0 from rfl, Fin.cons_succ, Fin.cons_zero]
  · rw [show (2 : Fin 4) = Fin.succ 1 from rfl, Fin.cons_succ,
      show (1 : Fin 3) = Fin.succ 0 from rfl, Fin.cons_succ]
  · rw [show (3 : Fin 4) = Fin.succ 2 from rfl, Fin.cons_succ,
      show (2 : Fin 3) = Fin.succ 1 from rfl, Fin.cons_succ]

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
private lemma k3_singleTrace_functional_sq_le (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ a b : Fin n, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (V : (Fin 4 → Fin n) → ℝ) :
    ∑ L : Fin 2 → Fin n,
        (∑ Q : Fin 4 → Fin n, V Q *
          fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
            (show TensorRSSpace 4 2 I x from DeTurck.cometricDoubleTraceFib (I := I) g₁ 2 x)
            n e Q L) ^ 2 ≤
      (∑ a : Fin n, ∑ b : Fin n,
          (g₀.inner x (e a)
            (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo
              (I := I) g₀ g₁ x (e b))) ^ 2) *
        ∑ Q : Fin 4 → Fin n, (V Q) ^ 2 := by
  classical
  set m : Fin n → Fin n → ℝ := fun a b =>
    g₀.inner x (e a)
      (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo
        (I := I) g₀ g₁ x (e b)) with hm_def
  set χ : (Fin 4 → Fin n) → (Fin 2 → Fin n) → ℝ := fun Q L =>
    (if Q 2 = L 0 then (1 : ℝ) else 0) * (if Q 3 = L 1 then (1 : ℝ) else 0) with hχ_def
  have hχ01 : ∀ Q L, χ Q L = 0 ∨ χ Q L = 1 := by
    intro Q L
    rw [hχ_def]
    by_cases h2 : Q 2 = L 0 <;> by_cases h3 : Q 3 = L 1 <;> simp [h2, h3]
  have hcomp : ∀ (Q : Fin 4 → Fin n) (L : Fin 2 → Fin n),
      fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
        (show TensorRSSpace 4 2 I x from DeTurck.cometricDoubleTraceFib (I := I) g₁ 2 x)
        n e Q L = χ Q L * m (Q 0) (Q 1) := fun Q L =>
    k3_doubleTrace_component_eq (I := I) (M := M) g₀ g₁ x e horth Q L
  have hCS : ∀ L : Fin 2 → Fin n,
      (∑ Q : Fin 4 → Fin n, V Q *
        fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
          (show TensorRSSpace 4 2 I x from DeTurck.cometricDoubleTraceFib (I := I) g₁ 2 x)
          n e Q L) ^ 2 ≤
      (∑ Q : Fin 4 → Fin n, (m (Q 0) (Q 1)) ^ 2 * χ Q L) *
        (∑ Q : Fin 4 → Fin n, (V Q) ^ 2 * χ Q L) := by
    intro L
    have hrw : (∑ Q : Fin 4 → Fin n, V Q *
        fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
          (show TensorRSSpace 4 2 I x from DeTurck.cometricDoubleTraceFib (I := I) g₁ 2 x)
          n e Q L) =
        ∑ Q : Fin 4 → Fin n, (m (Q 0) (Q 1) * χ Q L) * (V Q * χ Q L) := by
      refine Finset.sum_congr rfl (fun Q _ => ?_)
      rw [hcomp Q L]
      rcases hχ01 Q L with h | h <;> rw [h] <;> ring
    rw [hrw]
    refine le_trans (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun Q : Fin 4 → Fin n => m (Q 0) (Q 1) * χ Q L)
      (fun Q : Fin 4 → Fin n => V Q * χ Q L)) (le_of_eq ?_)
    congr 1
    · refine Finset.sum_congr rfl (fun Q _ => ?_)
      rcases hχ01 Q L with h | h <;> rw [h] <;> ring
    · refine Finset.sum_congr rfl (fun Q _ => ?_)
      rcases hχ01 Q L with h | h <;> rw [h] <;> ring
  have hmsum : ∀ L : Fin 2 → Fin n,
      (∑ Q : Fin 4 → Fin n, (m (Q 0) (Q 1)) ^ 2 * χ Q L) =
        ∑ a : Fin n, ∑ b : Fin n, (m a b) ^ 2 := by
    intro L
    rw [k3_sum_fin4_split (fun Q : Fin 4 → Fin n => (m (Q 0) (Q 1)) ^ 2 * χ Q L)]
    refine Finset.sum_congr rfl (fun q0 _ => Finset.sum_congr rfl (fun q1 _ => ?_))
    have hval : ∀ Q2 : Fin 2 → Fin n,
        (m ((Fin.cons q0 (Fin.cons q1 Q2) : Fin 4 → Fin n) 0)
            ((Fin.cons q0 (Fin.cons q1 Q2) : Fin 4 → Fin n) 1)) ^ 2 *
          χ (Fin.cons q0 (Fin.cons q1 Q2)) L =
        (m q0 q1) ^ 2 *
          ((if Q2 0 = L 0 then (1 : ℝ) else 0) * (if Q2 1 = L 1 then (1 : ℝ) else 0)) := by
      intro Q2
      obtain ⟨g0eq, g1eq, g2eq, g3eq⟩ := k3_cons_indices q0 q1 Q2
      rw [hχ_def]
      beta_reduce
      rw [g0eq, g1eq, g2eq, g3eq]
    rw [Finset.sum_congr rfl (fun Q2 _ => hval Q2)]
    rw [← Finset.mul_sum]
    have hδ : (∑ Q2 : Fin 2 → Fin n,
        (if Q2 0 = L 0 then (1 : ℝ) else 0) * (if Q2 1 = L 1 then (1 : ℝ) else 0)) = 1 := by
      rw [Finset.sum_congr rfl (fun Q2 _ => by
        rw [show (if Q2 0 = L 0 then (1 : ℝ) else 0) = (if L 0 = Q2 0 then (1 : ℝ) else 0) from by
          by_cases h : Q2 0 = L 0
          · rw [if_pos h, if_pos h.symm]
          · rw [if_neg h, if_neg (fun hc => h hc.symm)],
        show (if Q2 1 = L 1 then (1 : ℝ) else 0) = (if L 1 = Q2 1 then (1 : ℝ) else 0) from by
          by_cases h : Q2 1 = L 1
          · rw [if_pos h, if_pos h.symm]
          · rw [if_neg h, if_neg (fun hc => h hc.symm)]])]
      exact k3_pair_delta_sum_right (L 0) (L 1)
    rw [hδ, mul_one]
  have hVsum : (∑ L : Fin 2 → Fin n, ∑ Q : Fin 4 → Fin n, (V Q) ^ 2 * χ Q L) =
      ∑ Q : Fin 4 → Fin n, (V Q) ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun Q _ => ?_)
    rw [← Finset.mul_sum]
    rw [show (∑ L : Fin 2 → Fin n, χ Q L) = 1 from k3_pair_delta_sum_right (Q 2) (Q 3)]
    rw [mul_one]
  calc ∑ L : Fin 2 → Fin n,
        (∑ Q : Fin 4 → Fin n, V Q *
          fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
            (show TensorRSSpace 4 2 I x from DeTurck.cometricDoubleTraceFib (I := I) g₁ 2 x)
            n e Q L) ^ 2
      ≤ ∑ L : Fin 2 → Fin n,
          (∑ Q : Fin 4 → Fin n, (m (Q 0) (Q 1)) ^ 2 * χ Q L) *
            (∑ Q : Fin 4 → Fin n, (V Q) ^ 2 * χ Q L) :=
        Finset.sum_le_sum (fun L _ => hCS L)
    _ = (∑ a : Fin n, ∑ b : Fin n, (m a b) ^ 2) *
          ∑ L : Fin 2 → Fin n, ∑ Q : Fin 4 → Fin n, (V Q) ^ 2 * χ Q L := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun L _ => by rw [hmsum L])
    _ = (∑ a : Fin n, ∑ b : Fin n, (m a b) ^ 2) * ∑ Q : Fin 4 → Fin n, (V Q) ^ 2 := by
        rw [hVsum]

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
private def k3_permOfImages {n : ℕ} (f g : Fin n → Fin n)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) : Equiv.Perm (Fin n) :=
  ⟨f, g, h₁, h₂⟩

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
private def k3_perm4_0231 : Equiv.Perm (Fin 4) :=
  k3_permOfImages ![0, 2, 3, 1] ![0, 3, 1, 2] (by decide) (by decide)

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
private def k3_perm4_0321 : Equiv.Perm (Fin 4) :=
  k3_permOfImages ![0, 3, 2, 1] ![0, 3, 2, 1] (by decide) (by decide)

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
private def k3_perm4_2301 : Equiv.Perm (Fin 4) :=
  k3_permOfImages ![2, 3, 0, 1] ![2, 3, 0, 1] (by decide) (by decide)

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
private lemma k3_fourTraceCLM_eq (g₁ : SmoothRiemannianMetric I M) (x : M) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCLM
        (I := I) g₁ x =
      ((1 : ℝ) / 2) •
        ((DeTurck.cometricDoubleTraceFib (I := I) g₁ 2 x).comp
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM
              (I := I) k3_perm4_0231 x)
          + (DeTurck.cometricDoubleTraceFib (I := I) g₁ 2 x).comp
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM
              (I := I) k3_perm4_0321 x)
          - DeTurck.cometricDoubleTraceFib (I := I) g₁ 2 x
          - (DeTurck.cometricDoubleTraceFib (I := I) g₁ 2 x).comp
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM
              (I := I) k3_perm4_2301 x)) :=
  rfl

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
private lemma k3_fnsc_half_comb (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (A B C D : Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x)
    (Q : Fin 4 → Fin n) (L : Fin 2 → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g x 4 2
        (show TensorRSSpace 4 2 I x from ((1 : ℝ) / 2) • (A + B - C - D)) n e Q L =
      (1 / 2 : ℝ) *
        (fiberNormSqComponent (I := I) (M := M) g x 4 2
            (show TensorRSSpace 4 2 I x from A) n e Q L
          + fiberNormSqComponent (I := I) (M := M) g x 4 2
            (show TensorRSSpace 4 2 I x from B) n e Q L
          - fiberNormSqComponent (I := I) (M := M) g x 4 2
            (show TensorRSSpace 4 2 I x from C) n e Q L
          - fiberNormSqComponent (I := I) (M := M) g x 4 2
            (show TensorRSSpace 4 2 I x from D) n e Q L) := by
  unfold fiberNormSqComponent
  rw [show (((1 : ℝ) / 2) • (A + B - C - D))
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 4) ℝ).compContinuousLinearMap
          (fun k => g.inner x (e (Q k)))) =
      ((1 : ℝ) / 2) • (A ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 4) ℝ).compContinuousLinearMap
          (fun k => g.inner x (e (Q k))))
        + B ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 4) ℝ).compContinuousLinearMap
          (fun k => g.inner x (e (Q k))))
        - C ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 4) ℝ).compContinuousLinearMap
          (fun k => g.inner x (e (Q k))))
        - D ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 4) ℝ).compContinuousLinearMap
          (fun k => g.inner x (e (Q k))))) from by
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply]]
  rfl

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
private lemma k3_fourTrace_hA (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ a b : Fin n, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (V : (Fin 4 → Fin n) → ℝ) :
    ∑ L : Fin 2 → Fin n,
        (∑ Q : Fin 4 → Fin n, V Q *
          fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
            (show TensorRSSpace 4 2 I x from
              DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCLM
                (I := I) g₁ x)
            n e Q L) ^ 2 ≤
      (4 * ∑ a : Fin n, ∑ b : Fin n,
          (g₀.inner x (e a)
            (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo
              (I := I) g₀ g₁ x (e b))) ^ 2) *
        ∑ Q : Fin 4 → Fin n, (V Q) ^ 2 := by
  classical
  set T : Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x :=
    DeTurck.cometricDoubleTraceFib (I := I) g₁ 2 x with hT_def
  set HS : ℝ := ∑ a : Fin n, ∑ b : Fin n,
    (g₀.inner x (e a)
      (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo
        (I := I) g₀ g₁ x (e b))) ^ 2 with hHS_def
  set SV : ℝ := ∑ Q : Fin 4 → Fin n, (V Q) ^ 2 with hSV_def
  have hSV_nn : 0 ≤ SV := Finset.sum_nonneg (fun Q _ => sq_nonneg _)
  have hsingle : ∀ (ρ : Equiv.Perm (Fin 4)),
      ∑ L : Fin 2 → Fin n,
          (∑ Q : Fin 4 → Fin n, V Q *
            fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
              (show TensorRSSpace 4 2 I x from
                T.comp (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM
                  (I := I) ρ x))
              n e Q L) ^ 2 ≤ HS * SV := by
    intro ρ
    set ψ : (Fin 4 → Fin n) ≃ (Fin 4 → Fin n) :=
      Equiv.arrowCongr ρ (Equiv.refl (Fin n)) with hψ_def
    have hψ_apply : ∀ (Q : Fin 4 → Fin n) (k : Fin 4), ψ Q k = Q (ρ.symm k) := by
      intro Q k
      rfl
    have hreindex : ∀ L : Fin 2 → Fin n,
        (∑ Q : Fin 4 → Fin n, V Q *
          fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
            (show TensorRSSpace 4 2 I x from
              T.comp (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM
                (I := I) ρ x))
            n e Q L) =
        ∑ Q' : Fin 4 → Fin n, V (ψ.symm Q') *
          fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
            (show TensorRSSpace 4 2 I x from T) n e Q' L := by
      intro L
      refine Fintype.sum_equiv ψ _ _ (fun Q => ?_)
      rw [k3_fnsc_comp_slotPerm (I := I) (M := M) g₀ x e 4 2 T ρ Q L]
      rw [Equiv.symm_apply_apply]
      have hfun : (fun k => Q (ρ.symm k)) = ψ Q := by
        funext k
        rw [hψ_apply Q k]
      rw [hfun]
    have happ := k3_singleTrace_functional_sq_le (I := I) (M := M) g₀ g₁ x e horth
      (fun Q' => V (ψ.symm Q'))
    have hVsq : (∑ Q' : Fin 4 → Fin n, (V (ψ.symm Q')) ^ 2) = SV := by
      rw [hSV_def]
      exact Equiv.sum_comp ψ.symm (fun Q => (V Q) ^ 2)
    rw [Finset.sum_congr rfl (fun L _ => by rw [hreindex L])]
    rw [← hT_def] at happ
    rw [hVsq] at happ
    exact happ
  have hcomb : ∀ L : Fin 2 → Fin n,
      (∑ Q : Fin 4 → Fin n, V Q *
        fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
          (show TensorRSSpace 4 2 I x from
            DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCLM
              (I := I) g₁ x)
          n e Q L) =
      (1 / 2 : ℝ) *
        ((∑ Q : Fin 4 → Fin n, V Q *
            fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
              (show TensorRSSpace 4 2 I x from
                T.comp (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM
                  (I := I) k3_perm4_0231 x)) n e Q L)
          + (∑ Q : Fin 4 → Fin n, V Q *
            fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
              (show TensorRSSpace 4 2 I x from
                T.comp (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM
                  (I := I) k3_perm4_0321 x)) n e Q L)
          - (∑ Q : Fin 4 → Fin n, V Q *
            fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
              (show TensorRSSpace 4 2 I x from
                T.comp (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM
                  (I := I) k3_perm4_2301 x)) n e Q L)
          - (∑ Q : Fin 4 → Fin n, V Q *
            fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
              (show TensorRSSpace 4 2 I x from T) n e Q L)) := by
    intro L
    have hpt : ∀ Q : Fin 4 → Fin n,
        V Q * fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
          (show TensorRSSpace 4 2 I x from
            DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCLM
              (I := I) g₁ x)
          n e Q L =
        (1 / 2 : ℝ) *
          (V Q * fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
              (show TensorRSSpace 4 2 I x from
                T.comp (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM
                  (I := I) k3_perm4_0231 x)) n e Q L
            + V Q * fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
              (show TensorRSSpace 4 2 I x from
                T.comp (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM
                  (I := I) k3_perm4_0321 x)) n e Q L
            - V Q * fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
              (show TensorRSSpace 4 2 I x from
                T.comp (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM
                  (I := I) k3_perm4_2301 x)) n e Q L
            - V Q * fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
              (show TensorRSSpace 4 2 I x from T) n e Q L) := by
      intro Q
      rw [show fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
            (show TensorRSSpace 4 2 I x from
              DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCLM
                (I := I) g₁ x)
            n e Q L =
          fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
            (show TensorRSSpace 4 2 I x from ((1 : ℝ) / 2) •
              (T.comp (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM
                  (I := I) k3_perm4_0231 x)
                + T.comp (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM
                  (I := I) k3_perm4_0321 x)
                - T
                - T.comp (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM
                  (I := I) k3_perm4_2301 x)))
            n e Q L from by
        rw [hT_def]
        exact congrArg (fun (S : TensorRSSpace 4 2 I x) =>
          fiberNormSqComponent (I := I) (M := M) g₀ x 4 2 S n e Q L)
          (k3_fourTraceCLM_eq (I := I) (M := M) g₁ x)]
      rw [k3_fnsc_half_comb (I := I) (M := M) g₀ x e _ _ _ _ Q L]
      ring
    rw [Finset.sum_congr rfl (fun Q _ => hpt Q)]
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hquad : ∀ w1 w2 w3 w4 : ℝ,
      ((1 / 2 : ℝ) * (w1 + w2 - w3 - w4)) ^ 2 ≤ w1 ^ 2 + w2 ^ 2 + w3 ^ 2 + w4 ^ 2 := by
    intro w1 w2 w3 w4
    nlinarith [sq_nonneg (w1 - w2), sq_nonneg (w1 + w3), sq_nonneg (w1 + w4),
      sq_nonneg (w2 + w3), sq_nonneg (w2 + w4), sq_nonneg (w3 - w4)]
  calc ∑ L : Fin 2 → Fin n,
        (∑ Q : Fin 4 → Fin n, V Q *
          fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
            (show TensorRSSpace 4 2 I x from
              DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCLM
                (I := I) g₁ x)
            n e Q L) ^ 2
      ≤ ∑ L : Fin 2 → Fin n,
          ((∑ Q : Fin 4 → Fin n, V Q *
              fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
                (show TensorRSSpace 4 2 I x from
                  T.comp (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM
                    (I := I) k3_perm4_0231 x)) n e Q L) ^ 2
            + (∑ Q : Fin 4 → Fin n, V Q *
              fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
                (show TensorRSSpace 4 2 I x from
                  T.comp (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM
                    (I := I) k3_perm4_0321 x)) n e Q L) ^ 2
            + (∑ Q : Fin 4 → Fin n, V Q *
              fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
                (show TensorRSSpace 4 2 I x from
                  T.comp (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM
                    (I := I) k3_perm4_2301 x)) n e Q L) ^ 2
            + (∑ Q : Fin 4 → Fin n, V Q *
              fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
                (show TensorRSSpace 4 2 I x from T) n e Q L) ^ 2) := by
        refine Finset.sum_le_sum (fun L _ => ?_)
        rw [hcomb L]
        exact hquad _ _ _ _
    _ = (∑ L : Fin 2 → Fin n,
            (∑ Q : Fin 4 → Fin n, V Q *
              fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
                (show TensorRSSpace 4 2 I x from
                  T.comp (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM
                    (I := I) k3_perm4_0231 x)) n e Q L) ^ 2)
          + (∑ L : Fin 2 → Fin n,
            (∑ Q : Fin 4 → Fin n, V Q *
              fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
                (show TensorRSSpace 4 2 I x from
                  T.comp (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM
                    (I := I) k3_perm4_0321 x)) n e Q L) ^ 2)
          + (∑ L : Fin 2 → Fin n,
            (∑ Q : Fin 4 → Fin n, V Q *
              fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
                (show TensorRSSpace 4 2 I x from
                  T.comp (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM
                    (I := I) k3_perm4_2301 x)) n e Q L) ^ 2)
          + (∑ L : Fin 2 → Fin n,
            (∑ Q : Fin 4 → Fin n, V Q *
              fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
                (show TensorRSSpace 4 2 I x from T) n e Q L) ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ HS * SV + HS * SV + HS * SV + HS * SV := by
        have h1 := hsingle k3_perm4_0231
        have h2 := hsingle k3_perm4_0321
        have h3 := hsingle k3_perm4_2301
        have h4 : ∑ L : Fin 2 → Fin n,
            (∑ Q : Fin 4 → Fin n, V Q *
              fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
                (show TensorRSSpace 4 2 I x from T) n e Q L) ^ 2 ≤ HS * SV := by
          have happ := k3_singleTrace_functional_sq_le (I := I) (M := M) g₀ g₁ x e horth V
          rw [← hT_def] at happ
          exact happ
        exact add_le_add (add_le_add (add_le_add h1 h2) h3) h4
    _ = (4 * HS) * SV := by ring

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
private lemma k3_sum_sq_component_slotExtendIterFib_op_le (g : SmoothRiemannianMetric I M)
    (x : M) {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) :
    ∀ (w b c : ℕ) (A : Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x) (κ : ℝ)
      (hA : ∀ V : (Fin b → Fin n) → ℝ,
        ∑ L : Fin c → Fin n,
            (∑ Q : Fin b → Fin n, V Q *
              fiberNormSqComponent (I := I) (M := M) g x b c
                (show TensorRSSpace b c I x from A) n e Q L) ^ 2 ≤
          κ * ∑ Q : Fin b → Fin n, (V Q) ^ 2)
      (V : (Fin (b + w) → Fin n) → ℝ),
      ∑ J : Fin (c + w) → Fin n,
          (∑ P : Fin (b + w) → Fin n,
            V P * fiberNormSqComponent (I := I) (M := M) g x (b + w) (c + w)
              (show TensorRSSpace (b + w) (c + w) I x from
                k3_slotExtendIterFib (I := I) (M := M) g b c x A w) n e P J) ^ 2 ≤
        κ * ∑ P : Fin (b + w) → Fin n, (V P) ^ 2
  | 0 => fun b c A κ hA V => hA V
  | (w + 1) => by
      intro b c A κ hA V
      set cw : (Fin (b + w) → Fin n) → (Fin (c + w) → Fin n) → ℝ := fun P J =>
        fiberNormSqComponent (I := I) (M := M) g x (b + w) (c + w)
          (show TensorRSSpace (b + w) (c + w) I x from
            k3_slotExtendIterFib (I := I) (M := M) g b c x A w) n e P J with hcw_def
      have hpeel : ∀ (P : Fin (b + (w + 1)) → Fin n) (J : Fin (c + (w + 1)) → Fin n),
          fiberNormSqComponent (I := I) (M := M) g x (b + (w + 1)) (c + (w + 1))
              (show TensorRSSpace (b + (w + 1)) (c + (w + 1)) I x from
                k3_slotExtendIterFib (I := I) (M := M) g b c x A (w + 1)) n e P J =
            (if J 0 = P 0 then (1 : ℝ) else 0) *
              cw (fun k => P (Fin.succ k)) (fun k => J (Fin.succ k)) := fun P J =>
        k3_fiberNormSqComponent_slotExtendFib_eq (I := I) (M := M) g (b + w) (c + w) x
          (k3_slotExtendIterFib (I := I) (M := M) g b c x A w) e horth P J
      have hstep : ∀ J : Fin (c + (w + 1)) → Fin n,
          (∑ P : Fin (b + (w + 1)) → Fin n,
            V P * fiberNormSqComponent (I := I) (M := M) g x (b + (w + 1)) (c + (w + 1))
              (show TensorRSSpace (b + (w + 1)) (c + (w + 1)) I x from
                k3_slotExtendIterFib (I := I) (M := M) g b c x A (w + 1)) n e P J) =
          ∑ P' : Fin (b + w) → Fin n,
            V (Fin.cons (J 0) P') * cw P' (fun k => J (Fin.succ k)) := by
        intro J
        calc (∑ P : Fin (b + (w + 1)) → Fin n,
              V P * fiberNormSqComponent (I := I) (M := M) g x (b + (w + 1)) (c + (w + 1))
                (show TensorRSSpace (b + (w + 1)) (c + (w + 1)) I x from
                  k3_slotExtendIterFib (I := I) (M := M) g b c x A (w + 1)) n e P J)
            = ∑ P : Fin (b + (w + 1)) → Fin n,
                V P * ((if J 0 = P 0 then (1 : ℝ) else 0) *
                  cw (fun k => P (Fin.succ k)) (fun k => J (Fin.succ k))) :=
              Finset.sum_congr rfl (fun P _ => by rw [hpeel P J])
          _ = ∑ pr : Fin n × (Fin (b + w) → Fin n),
                V (Fin.cons pr.1 pr.2) * ((if J 0 = pr.1 then (1 : ℝ) else 0) *
                  cw pr.2 (fun k => J (Fin.succ k))) :=
              (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (b + w + 1) => Fin n))
                (fun pr : Fin n × (Fin (b + w) → Fin n) =>
                  V (Fin.cons pr.1 pr.2) * ((if J 0 = pr.1 then (1 : ℝ) else 0) *
                    cw pr.2 (fun k => J (Fin.succ k))))
                (fun P => V P * ((if J 0 = P 0 then (1 : ℝ) else 0) *
                  cw (fun k => P (Fin.succ k)) (fun k => J (Fin.succ k))))
                (fun pr => by simp [Fin.consEquiv])).symm
          _ = ∑ p₀ : Fin n, ∑ P' : Fin (b + w) → Fin n,
                V (Fin.cons p₀ P') * ((if J 0 = p₀ then (1 : ℝ) else 0) *
                  cw P' (fun k => J (Fin.succ k))) := Fintype.sum_prod_type _
          _ = ∑ P' : Fin (b + w) → Fin n, ∑ p₀ : Fin n,
                V (Fin.cons p₀ P') * ((if J 0 = p₀ then (1 : ℝ) else 0) *
                  cw P' (fun k => J (Fin.succ k))) := Finset.sum_comm
          _ = ∑ P' : Fin (b + w) → Fin n,
                V (Fin.cons (J 0) P') * cw P' (fun k => J (Fin.succ k)) := by
              refine Finset.sum_congr rfl (fun P' _ => ?_)
              simp only [mul_ite, ite_mul, one_mul, zero_mul, mul_zero]
              rw [Finset.sum_ite_eq Finset.univ (J 0) (fun p₀ =>
                V (Fin.cons p₀ P') * cw P' (fun k => J (Fin.succ k)))]
              rw [if_pos (Finset.mem_univ (J 0))]
      calc (∑ J : Fin (c + (w + 1)) → Fin n,
            (∑ P : Fin (b + (w + 1)) → Fin n,
              V P * fiberNormSqComponent (I := I) (M := M) g x (b + (w + 1)) (c + (w + 1))
                (show TensorRSSpace (b + (w + 1)) (c + (w + 1)) I x from
                  k3_slotExtendIterFib (I := I) (M := M) g b c x A (w + 1)) n e P J) ^ 2)
          = ∑ J : Fin (c + (w + 1)) → Fin n,
              (∑ P' : Fin (b + w) → Fin n,
                V (Fin.cons (J 0) P') * cw P' (fun k => J (Fin.succ k))) ^ 2 :=
            Finset.sum_congr rfl (fun J _ => by rw [hstep J])
        _ = ∑ pr : Fin n × (Fin (c + w) → Fin n),
              (∑ P' : Fin (b + w) → Fin n,
                V (Fin.cons pr.1 P') * cw P' pr.2) ^ 2 :=
            (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (c + w + 1) => Fin n))
              (fun pr : Fin n × (Fin (c + w) → Fin n) =>
                (∑ P' : Fin (b + w) → Fin n, V (Fin.cons pr.1 P') * cw P' pr.2) ^ 2)
              (fun J => (∑ P' : Fin (b + w) → Fin n,
                V (Fin.cons (J 0) P') * cw P' (fun k => J (Fin.succ k))) ^ 2)
              (fun pr => by simp [Fin.consEquiv])).symm
        _ = ∑ j₀ : Fin n, ∑ J' : Fin (c + w) → Fin n,
              (∑ P' : Fin (b + w) → Fin n,
                V (Fin.cons j₀ P') * cw P' J') ^ 2 := Fintype.sum_prod_type _
        _ ≤ ∑ j₀ : Fin n,
              (κ * ∑ P' : Fin (b + w) → Fin n, (V (Fin.cons j₀ P')) ^ 2) :=
            Finset.sum_le_sum (fun j₀ _ =>
              k3_sum_sq_component_slotExtendIterFib_op_le g x e horth w b c A κ hA
                (fun P' => V (Fin.cons j₀ P')))
        _ = κ * ∑ j₀ : Fin n, ∑ P' : Fin (b + w) → Fin n, (V (Fin.cons j₀ P')) ^ 2 := by
            rw [Finset.mul_sum]
        _ = κ * ∑ P : Fin (b + (w + 1)) → Fin n, (V P) ^ 2 := by
            refine congrArg (fun t : ℝ => κ * t) ?_
            exact Eq.trans (Fintype.sum_prod_type
                (fun pr : Fin n × (Fin (b + w) → Fin n) => (V (Fin.cons pr.1 pr.2)) ^ 2)).symm
              (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (b + w + 1) => Fin n))
                (fun pr : Fin n × (Fin (b + w) → Fin n) => (V (Fin.cons pr.1 pr.2)) ^ 2)
                (fun P => (V P) ^ 2)
                (fun pr => by simp [Fin.consEquiv]))

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
private theorem k3_rfns_comp_slotExtendIterFib_op_le (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (bse : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hn : n = Module.finrank ℝ E) (hbse : ∀ i : Fin n, bse i = e i)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (w p b c : ℕ) (A : Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x) (κ : ℝ) (hκ : 0 ≤ κ)
    (hA : ∀ V : (Fin b → Fin n) → ℝ,
      ∑ L : Fin c → Fin n,
          (∑ Q : Fin b → Fin n, V Q *
            fiberNormSqComponent (I := I) (M := M) g x b c
              (show TensorRSSpace b c I x from A) n e Q L) ^ 2 ≤
        κ * ∑ Q : Fin b → Fin n, (V Q) ^ 2)
    (U : Tensor0SSpace p I x →L[ℝ] Tensor0SSpace (b + w) I x) :
    riemannianFiberNormSq (I := I) (M := M) g p (c + w) x
        (show TensorRSSpace p (c + w) I x from
          (k3_slotExtendIterFib (I := I) (M := M) g b c x A w).comp U) ≤
      κ * riemannianFiberNormSq (I := I) (M := M) g p (b + w) x
        (show TensorRSSpace p (b + w) I x from U) := by
  classical
  rw [rfns_rs_eq_sum_componentSq_of_basis (I := I) (M := M) g p (c + w) x _ e bse hn hbse horth]
  rw [rfns_rs_eq_sum_componentSq_of_basis (I := I) (M := M) g p (b + w) x _ e bse hn hbse horth]
  have hcomp : ∀ (K : Fin p → Fin n) (J : Fin (c + w) → Fin n),
      fiberNormSqComponent (I := I) (M := M) g x p (c + w)
          (show TensorRSSpace p (c + w) I x from
            (k3_slotExtendIterFib (I := I) (M := M) g b c x A w).comp U) n e K J =
        ∑ P : Fin (b + w) → Fin n,
          fiberNormSqComponent (I := I) (M := M) g x p (b + w)
            (show TensorRSSpace p (b + w) I x from U) n e K P *
            fiberNormSqComponent (I := I) (M := M) g x (b + w) (c + w)
              (show TensorRSSpace (b + w) (c + w) I x from
                k3_slotExtendIterFib (I := I) (M := M) g b c x A w) n e P J :=
    fun K J => k2_fiberNormSqComponent_compRS_eq (I := I) (M := M) g p (b + w) (c + w) x
      (show TensorRSSpace (b + w) (c + w) I x from
        k3_slotExtendIterFib (I := I) (M := M) g b c x A w)
      (show TensorRSSpace p (b + w) I x from U) e bse hbse horth K J
  rw [Finset.sum_congr rfl (fun K (_ : K ∈ Finset.univ) =>
    Finset.sum_congr rfl (fun J (_ : J ∈ Finset.univ) => by rw [hcomp K J]))]
  refine le_trans (Finset.sum_le_sum (fun K (_ : K ∈ Finset.univ) =>
    k3_sum_sq_component_slotExtendIterFib_op_le (I := I) (M := M) g x e horth w b c A κ hA
      (fun P => fiberNormSqComponent (I := I) (M := M) g x p (b + w)
        (show TensorRSSpace p (b + w) I x from U) n e K P))) ?_
  rw [← Finset.mul_sum]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedVariables false in

theorem rfns_appCcRS_ricciCometricFourTraceCastG0_corner_op_le (g₀ g₁ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    {δ₀ δ : ℝ} (hδ₀ : δ₀ < 1) (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
    (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
    (i : ℕ) (U : SmoothCcTensor g₀ 2 (4 + i)) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((appCcRS (I := I) (M := M) g₀ 2 (4 + i) (2 + i)
          (appCcLeibnizPsi (I := I) (M := M) g₀ 4 2
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCastG0
              (I := I) g₀ g₁) i i) U).toSection x) ≤
      4 * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + i) x (U.toSection x) := by
  classical
  have h1δ : (0 : ℝ) < 1 - δ := by linarith
  have h1δ₀ : (0 : ℝ) < 1 - δ₀ := by linarith
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hexpand, hrepr02⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  have hWop : ∀ u : TangentSpace I x,
      g₀.inner x (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo (I := I) g₀ g₁ x u)
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo (I := I) g₀ g₁ x u) ≤
      (1 / (1 - δ₀)) ^ 2 * g₀.inner x u u := by
    intro u
    have hs := DifferentialGeometry.Analysis.Sobolev.TensorHilbert.sqrt_inner_gInvRaisedEndo_le (I := I) (M := M) g₀ g₁
      (fun y => ccTensorBilinSymm (I := I) g₀ P y) htie
      (show δ < 1 from by linarith) hδ0 hbound x u
    have h0T : 0 ≤ g₀.inner x (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo (I := I) g₀ g₁ x u)
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo (I := I) g₀ g₁ x u) :=
      DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg (I := I) (M := M) g₀ x _
    have h0u : 0 ≤ g₀.inner x u u := DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg (I := I) (M := M) g₀ x u
    have hinv : 1 / (1 - δ) ≤ 1 / (1 - δ₀) := by
      rw [div_le_div_iff₀ h1δ h1δ₀]
      linarith
    have hsq := Real.sq_sqrt h0T
    have hsqu := Real.sq_sqrt h0u
    have h1 : Real.sqrt (g₀.inner x
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo (I := I) g₀ g₁ x u)
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo (I := I) g₀ g₁ x u)) ≤
        (1 / (1 - δ₀)) * Real.sqrt (g₀.inner x u u) :=
      le_trans hs (mul_le_mul_of_nonneg_right hinv (Real.sqrt_nonneg _))
    calc g₀.inner x
          (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo (I := I) g₀ g₁ x u)
          (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo (I := I) g₀ g₁ x u)
        = Real.sqrt (g₀.inner x
            (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo (I := I) g₀ g₁ x u)
            (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo (I := I) g₀ g₁ x u)) ^ 2 :=
          hsq.symm
      _ ≤ ((1 / (1 - δ₀)) * Real.sqrt (g₀.inner x u u)) ^ 2 :=
          by nlinarith [h1, Real.sqrt_nonneg (g₀.inner x
            (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo (I := I) g₀ g₁ x u)
            (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo (I := I) g₀ g₁ x u))]
      _ = (1 / (1 - δ₀)) ^ 2 * g₀.inner x u u := by
          rw [mul_pow, hsqu]
  have hHS : (∑ a : Fin n, ∑ b : Fin n,
      (g₀.inner x (e a)
        (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo
          (I := I) g₀ g₁ x (e b))) ^ 2) ≤
      (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2 := by
    rw [Finset.sum_comm]
    have hcol : ∀ b : Fin n,
        (∑ a : Fin n, (g₀.inner x (e a)
          (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo
            (I := I) g₀ g₁ x (e b))) ^ 2) ≤ (1 / (1 - δ₀)) ^ 2 := by
      intro b
      have hp := hpars (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo
        (I := I) g₀ g₁ x (e b))
      rw [hp]
      refine le_trans (hWop (e b)) ?_
      rw [horth b b, if_pos rfl, mul_one]
    calc (∑ b : Fin n, ∑ a : Fin n, (g₀.inner x (e a)
          (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo
            (I := I) g₀ g₁ x (e b))) ^ 2)
        ≤ ∑ _b : Fin n, (1 / (1 - δ₀)) ^ 2 := Finset.sum_le_sum (fun b _ => hcol b)
      _ = (n : ℝ) * (1 / (1 - δ₀)) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2 := by rw [hnE]
  have hA : ∀ V : (Fin 4 → Fin n) → ℝ,
      ∑ L : Fin 2 → Fin n,
          (∑ Q : Fin 4 → Fin n, V Q *
            fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
              (show TensorRSSpace 4 2 I x from
                (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
                  (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCastG0
                    (I := I) g₀ g₁).toSection x)) n e Q L) ^ 2 ≤
        (4 * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2) *
          ∑ Q : Fin 4 → Fin n, (V Q) ^ 2 := by
    intro V
    have h := k3_fourTrace_hA (I := I) (M := M) g₀ g₁ x e horth V
    refine le_trans (le_of_eq ?_) (le_trans h ?_)
    · rfl
    · refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg (fun Q _ => sq_nonneg _))
      calc 4 * ∑ a : Fin n, ∑ b : Fin n,
            (g₀.inner x (e a)
              (DifferentialGeometry.Analysis.Sobolev.TensorHilbert.gInvRaisedEndo
                (I := I) g₀ g₁ x (e b))) ^ 2
          ≤ 4 * ((Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2) :=
            mul_le_mul_of_nonneg_left hHS (by norm_num)
        _ = 4 * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2 := by ring
  rw [appCcRS_toSection (I := I) (M := M) g₀ 2 (4 + i) (2 + i)
    (appCcLeibnizPsi (I := I) (M := M) g₀ 4 2
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCastG0
        (I := I) g₀ g₁) i i) U x]
  rw [show (show Tensor0SSpace (4 + i) I x →L[ℝ] Tensor0SSpace (2 + i) I x from
        (appCcLeibnizPsi (I := I) (M := M) g₀ 4 2
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCastG0
            (I := I) g₀ g₁) i i).toSection x) =
      k3_slotExtendIterFib (I := I) (M := M) g₀ 4 2 x
        (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCastG0
            (I := I) g₀ g₁).toSection x) i from
    k3_appCcLeibnizPsi_diag_toSection (I := I) (M := M) g₀ 4 2
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCastG0
        (I := I) g₀ g₁) i x]
  exact k3_rfns_comp_slotExtendIterFib_op_le (I := I) (M := M) g₀ x e bse hnE hbse horth
    i 2 4 2
    (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCastG0
        (I := I) g₀ g₁).toSection x)
    (4 * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2) (by positivity)
    hA
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace (4 + i) I x from U.toSection x)

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
private theorem b4_L0_topSeparated_proof (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ}
    (hδ₀ : δ₀ < 1) (hδ₀half : δ₀ ≤ 1 / 2) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
                (I := I) (M := M) g₀ g₁)).toSection x) ≤
          ((21 / 4 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2) ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)
            + K i * Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := by
  classical
  have h1δ : (0 : ℝ) < 1 - δ₀ := by linarith
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  set d : ℝ := 1 / (1 - δ₀) with hd_def
  have hd : 0 ≤ d := by positivity
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    exists_rfns_iteratedCovGrad_connDiffSection_tgrid (I := I) (M := M) g₀ hδ₀
  obtain ⟨Ktop0, hKtop0_nn, Kc, hKc_nn, hTS⟩ :=
    rfns_iteratedCovGrad_connDiffSection_topSeparated_le (I := I) (M := M) g₀ hδ₀
  obtain ⟨C4, hC4_nn, hC4⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.rfns_iteratedCovGrad_ricciCometricFourTraceCastG0_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨CK, hCK_nn, hCK⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.rfns_iteratedCovGrad_linearizedRicciConnDiffOrder0KernelField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  set Qq : ℕ → ℝ := fun i => appCcGdiag (E := E) i *
    ∑ n ∈ Finset.range (i + 1), ∑ m ∈ Finset.range (i + 1 - n),
      fr ^ 3 * CA n * CA m * Combinatorics.windowPairCellCount (n + 2) (m + 2) with hQq_def
  have hQq_nn : ∀ i, 0 ≤ Qq i := by
    intro i
    refine mul_nonneg (appCcGdiag_nonneg (E := E) i) ?_
    refine Finset.sum_nonneg (fun n _ => Finset.sum_nonneg (fun m _ => ?_))
    exact mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hfr 3) (hCA_nn n)) (hCA_nn m))
      (Combinatorics.windowPairCellCount_nonneg (n + 2) (m + 2))
  set Clow : ℕ → ℝ := fun i => (i : ℝ) * appCcGdiag (E := E) i *
    ∑ k ∈ Finset.range i,
      C4 (i - k) * CK k * Combinatorics.windowPairCellCount (i - k + 1) (k + 3) with hClow_def
  have hClow_nn : ∀ i, 0 ≤ Clow i := by
    intro i
    refine mul_nonneg (mul_nonneg (Nat.cast_nonneg i) (appCcGdiag_nonneg (E := E) i)) ?_
    refine Finset.sum_nonneg (fun k _ => ?_)
    exact mul_nonneg (mul_nonneg (hC4_nn (i - k)) (hCK_nn k))
      (Combinatorics.windowPairCellCount_nonneg (i - k + 1) (k + 3))
  set Kfun : ℕ → ℝ := fun i => 9 * (144 * fr * d ^ 2 * Qq i
    + 16 * fr ^ 2 * d ^ 2 * (Kc (i + 1) * ((i : ℝ) + 1)) + Clow i) with hKfun_def
  have hKfun_nn : ∀ i, 0 ≤ Kfun i := by
    intro i
    have h1 := hQq_nn i
    have h2 := hKc_nn (i + 1)
    have h3 := hClow_nn i
    have h4 : (0 : ℝ) ≤ (i : ℝ) + 1 := by positivity
    simp only [hKfun_def]
    positivity
  refine ⟨Kfun, hKfun_nn, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb_nn : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  set w : ℝ := Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) with hw_def
  have hw_nn : 0 ≤ w := Combinatorics.boundedFactorGridWindow_nonneg b hb_nn (i + 1) (i + 3)
  have hbtop_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
      ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + (i + 2)) x _
  have hAgrid : ∀ n : ℕ, n ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 2 n
          (connDiffSection (I := I) g₁ g₀)).toSection x) ≤
      CA n * Combinatorics.boundedFactorGridWindow b (i + 1) (n + 2) :=
    fun n hn => le_trans (hCA g₁ P htie hδ_le hδ0 hbound n x)
      (mul_le_mul_of_nonneg_left
        (le_of_eq (b4_sum_atg_eq_bfgWindow b (show n + 2 ≤ (i + 1) + 1 from by omega)))
        (hCA_nn n))
  have hcore : ∀ n, n ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + n) x
        ((iteratedCovGrad (I := I) g₀ 3 4 n
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁)).toSection x) ≤
      fr ^ 2 * CA n * Combinatorics.boundedFactorGridWindow b (i + 1) (n + 2) := by
    intro n hn
    refine le_trans (b4_cDCIF_le (I := I) (M := M) g₀ g₁ n x) ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hAgrid n (by omega)) (by positivity)
  have hWinner : ∀ m, m ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + m) x
        ((iteratedCovGrad (I := I) g₀ 2 3 m
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁)).toSection x) ≤
      fr * CA m * Combinatorics.boundedFactorGridWindow b (i + 1) (m + 2) := by
    intro m hm
    refine le_trans (b4_inner_le (I := I) (M := M) g₀ g₁ m x) ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hAgrid m (by omega)) hfr
  have hquad : ∀ W23 : SmoothCcTensor g₀ 2 3,
      (∀ m, m ≤ i → riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + m) x
        ((iteratedCovGrad (I := I) g₀ 2 3 m W23).toSection x) ≤
        fr * CA m * Combinatorics.boundedFactorGridWindow b (i + 1) (m + 2)) →
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 4 i
          (appCcRS (I := I) (M := M) g₀ 2 3 4
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) W23)).toSection x) ≤
      Qq i * w :=
    fun W23 hW => b4_quadArm_capped (I := I) (M := M) g₀ b hb_nn
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) W23 CA hCA_nn hfr
      (le_refl i) x hcore hW
  have hWa : ∀ m, m ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + m) x
        ((iteratedCovGrad (I := I) g₀ 2 3 m
          (appCcRS (I := I) (M := M) g₀ 2 3 3
            (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kMid0Perm102)
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁))).toSection x) ≤
      fr * CA m * Combinatorics.boundedFactorGridWindow b (i + 1) (m + 2) := by
    intro m hm
    rw [b3_armOuter23_rfns_eq (I := I) (M := M) g₀ b3_kMid0Perm102
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁) m x]
    exact hWinner m hm
  have hWb : ∀ m, m ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + m) x
        ((iteratedCovGrad (I := I) g₀ 2 3 m
          (appCcRS (I := I) (M := M) g₀ 2 3 3
            (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kMid0Perm120)
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁))).toSection x) ≤
      fr * CA m * Combinatorics.boundedFactorGridWindow b (i + 1) (m + 2) := by
    intro m hm
    rw [b3_armOuter23_rfns_eq (I := I) (M := M) g₀ b3_kMid0Perm120
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁) m x]
    exact hWinner m hm
  have hrkval : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (i + 1)) x
      ((iteratedCovGrad (I := I) g₀ 1 2 (i + 1)
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.raisedKoszul (I := I) g₀ g₁)).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x) := by
    rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.raisedKoszul_eq_cometricRaiseSlot0Field_koszulCovecCc
        (I := I) (M := M) g₀ g₁ P htie,
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.rfns_iteratedCovGrad_cometricRaiseSlot0Field_koszul_eq
        (I := I) (M := M) g₀ P (i + 1) x]
    refine le_trans (rfns_iteratedCovGrad_koszulCovecCc_symmS_le (I := I) (M := M) g₀ P (i + 1) x) ?_
    exact b1_rfns_icg_symmS_le (I := I) (M := M) g₀ P (i + 2) x
  have hres : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (i + 1)) x
      ((iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (connDiffSection (I := I) g₁ g₀) -
        appCcRS (I := I) (M := M) g₀ 1 1 (2 + (i + 1))
          (iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.raisedKoszul (I := I) g₀ g₁))
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
      (Kc (i + 1) * ((i : ℝ) + 1)) * w := by
    refine le_trans ((hTS g₁ P htie hδ_le hδ0 hbound (i + 1) x).2) ?_
    have hcell : ∀ k ∈ Finset.range (i + 1),
        b (i + 1 - k) * Combinatorics.antidiagonalTupleGrid b (k + 1) ≤ w := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [Combinatorics.antidiagonalTupleGrid_eq_boundedFactorGrid b
        (show k + 1 ≤ i + 1 from by omega)]
      refine le_trans (Combinatorics.single_factor_mul_boundedFactorGrid_le b hb_nn
        (K := i + 1) (k + 1) (i + 1 - k) (by omega) (by omega)) ?_
      rw [show (k + 1) + (i + 1 - k) = i + 2 from by omega, hw_def]
      exact Combinatorics.boundedFactorGrid_le_boundedFactorGridWindow b hb_nn (by omega)
    calc Kc (i + 1) * ∑ k ∈ Finset.range (i + 1),
            b (i + 1 - k) * Combinatorics.antidiagonalTupleGrid b (k + 1)
        ≤ Kc (i + 1) * ∑ k ∈ Finset.range (i + 1), w :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell) (hKc_nn (i + 1))
      _ = (Kc (i + 1) * ((i : ℝ) + 1)) * w := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  have hAsqrt : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (i + 1)) x
      ((iteratedCovGrad (I := I) g₀ 1 2 (i + 1)
        (connDiffSection (I := I) g₁ g₀)).toSection x)) ≤
      d * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x))
      + Real.sqrt ((Kc (i + 1) * ((i : ℝ) + 1)) * w) := by
    have hsplitA : (iteratedCovGrad (I := I) g₀ 1 2 (i + 1)
        (connDiffSection (I := I) g₁ g₀)).toSection x =
        (appCcRS (I := I) (M := M) g₀ 1 1 (2 + (i + 1))
          (iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.raisedKoszul (I := I) g₀ g₁))
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sharpFlatEndoCc (I := I) g₀ g₁)).toSection x +
        (iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (connDiffSection (I := I) g₁ g₀) -
          appCcRS (I := I) (M := M) g₀ 1 1 (2 + (i + 1))
            (iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.raisedKoszul (I := I) g₀ g₁))
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sharpFlatEndoCc (I := I) g₀ g₁)).toSection x := by
      rw [b1_toSection_sub (I := I) (M := M) g₀ 1 (2 + (i + 1))]
      abel
    rw [hsplitA]
    refine le_trans (b1_sqrt_rfns_add_le (I := I) (M := M) g₀ 1 (2 + (i + 1)) x _ _)
      (add_le_add ?_ (b1_sqrt_le_of_le hres))
    refine le_trans (b4_sqrt_le_coeff_mul (c := d)
      (rfns_appCcRS_sharpFlatEndoCc_contravariantSlot_op_le (I := I) (M := M) g₀ g₁ P htie hδ₀
        hδ_le hδ0 hbound (2 + (i + 1))
        (iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.raisedKoszul (I := I) g₀ g₁)) x) hd) ?_
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hrkval) hd
  have hgrad_sqrt : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 4 i
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffGradContrInsertionField (I := I) g₀ g₁)).toSection x)) ≤
      Real.sqrt fr * (d * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0
          (2 + (i + 2)) x ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x))
        + Real.sqrt ((Kc (i + 1) * ((i : ℝ) + 1)) * w)) := by
    have hval : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 4 i
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffGradContrInsertionField (I := I) g₀ g₁)).toSection x) ≤
        (Real.sqrt fr) ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (i + 1)) x
          ((iteratedCovGrad (I := I) g₀ 1 2 (i + 1)
            (connDiffSection (I := I) g₁ g₀)).toSection x) := by
      rw [Real.sq_sqrt hfr]
      exact b4_gradCore_le (I := I) (M := M) g₀ g₁ i x
    refine le_trans (b4_sqrt_le_coeff_mul hval (Real.sqrt_nonneg fr)) ?_
    exact mul_le_mul_of_nonneg_left hAsqrt (Real.sqrt_nonneg fr)
  have hjets : (iteratedCovGrad (I := I) g₀ 2 4 i
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0KernelField (I := I) g₀ g₁)).toSection x =
      (iteratedCovGrad (I := I) g₀ 2 4 i (appCcRS (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm3201) (appCcRS (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) (appCcRS (I := I) (M := M) g₀ 2 3 3 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kMid0Perm102) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁))))).toSection x
      + (iteratedCovGrad (I := I) g₀ 2 4 i (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoeffGen (I := I) (M := M) g₀ 2 4 (appCcRS (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm2301) (appCcRS (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) (appCcRS (I := I) (M := M) g₀ 2 3 3 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kMid0Perm102) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁)))) DifferentialGeometry.Analysis.Parabolic.TensorSpectral.innerCoreInPerm10)).toSection x
      + (iteratedCovGrad (I := I) g₀ 2 4 i (appCcRS (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm3102) (appCcRS (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) (appCcRS (I := I) (M := M) g₀ 2 3 3 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kMid0Perm120) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁))))).toSection x
      + (iteratedCovGrad (I := I) g₀ 2 4 i (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoeffGen (I := I) (M := M) g₀ 2 4 (appCcRS (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm1302) (appCcRS (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁))) DifferentialGeometry.Analysis.Parabolic.TensorSpectral.innerCoreInPerm10)).toSection x
      + (iteratedCovGrad (I := I) g₀ 2 4 i (appCcRS (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm1203) (appCcRS (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁)))).toSection x
      + (iteratedCovGrad (I := I) g₀ 2 4 i (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoeffGen (I := I) (M := M) g₀ 2 4 (appCcRS (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm2103) (appCcRS (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) (appCcRS (I := I) (M := M) g₀ 2 3 3 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kMid0Perm120) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁)))) DifferentialGeometry.Analysis.Parabolic.TensorSpectral.innerCoreInPerm10)).toSection x
      - (iteratedCovGrad (I := I) g₀ 2 4 i (appCcRS (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm3012) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffGradContrInsertionField (I := I) g₀ g₁))).toSection x
      - (iteratedCovGrad (I := I) g₀ 2 4 i (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoeffGen (I := I) (M := M) g₀ 2 4 (appCcRS (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm2013) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffGradContrInsertionField (I := I) g₀ g₁)) DifferentialGeometry.Analysis.Parabolic.TensorSpectral.innerCoreInPerm10)).toSection x := by
    rw [b3_order0KernelField_eq_arm_combination (I := I) (M := M) g₀ g₁]
    simp only [iteratedCovGrad_sub, iteratedCovGrad_add, b1_toSection_sub, b1_toSection_add]
  have hq1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 4 i (appCcRS (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm3201) (appCcRS (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) (appCcRS (I := I) (M := M) g₀ 2 3 3 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kMid0Perm102) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁))))).toSection x) ≤ Qq i * w := by
    rw [b3_armOuter24_rfns_eq (I := I) (M := M) g₀ b3_kOut0Perm3201
      (appCcRS (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) (appCcRS (I := I) (M := M) g₀ 2 3 3 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kMid0Perm102) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁))) i x]
    exact hquad _ hWa
  have hq2 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 4 i (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoeffGen (I := I) (M := M) g₀ 2 4 (appCcRS (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm2301) (appCcRS (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) (appCcRS (I := I) (M := M) g₀ 2 3 3 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kMid0Perm102) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁)))) DifferentialGeometry.Analysis.Parabolic.TensorSpectral.innerCoreInPerm10)).toSection x) ≤ Qq i * w := by
    rw [rfns_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 2 4
      (appCcRS (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm2301) (appCcRS (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) (appCcRS (I := I) (M := M) g₀ 2 3 3 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kMid0Perm102) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁)))) DifferentialGeometry.Analysis.Parabolic.TensorSpectral.innerCoreInPerm10 i x]
    rw [b3_armOuter24_rfns_eq (I := I) (M := M) g₀ b3_kOut0Perm2301
      (appCcRS (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) (appCcRS (I := I) (M := M) g₀ 2 3 3 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kMid0Perm102) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁))) i x]
    exact hquad _ hWa
  have hq3 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 4 i (appCcRS (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm3102) (appCcRS (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) (appCcRS (I := I) (M := M) g₀ 2 3 3 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kMid0Perm120) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁))))).toSection x) ≤ Qq i * w := by
    rw [b3_armOuter24_rfns_eq (I := I) (M := M) g₀ b3_kOut0Perm3102
      (appCcRS (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) (appCcRS (I := I) (M := M) g₀ 2 3 3 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kMid0Perm120) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁))) i x]
    exact hquad _ hWb
  have hq4 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 4 i (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoeffGen (I := I) (M := M) g₀ 2 4 (appCcRS (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm1302) (appCcRS (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁))) DifferentialGeometry.Analysis.Parabolic.TensorSpectral.innerCoreInPerm10)).toSection x) ≤ Qq i * w := by
    rw [rfns_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 2 4
      (appCcRS (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm1302) (appCcRS (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁))) DifferentialGeometry.Analysis.Parabolic.TensorSpectral.innerCoreInPerm10 i x]
    rw [b3_armOuter24_rfns_eq (I := I) (M := M) g₀ b3_kOut0Perm1302
      (appCcRS (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁)) i x]
    exact hquad _ hWinner
  have hq5 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 4 i (appCcRS (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm1203) (appCcRS (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁)))).toSection x) ≤ Qq i * w := by
    rw [b3_armOuter24_rfns_eq (I := I) (M := M) g₀ b3_kOut0Perm1203
      (appCcRS (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁)) i x]
    exact hquad _ hWinner
  have hq6 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 4 i (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoeffGen (I := I) (M := M) g₀ 2 4 (appCcRS (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm2103) (appCcRS (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) (appCcRS (I := I) (M := M) g₀ 2 3 3 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kMid0Perm120) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁)))) DifferentialGeometry.Analysis.Parabolic.TensorSpectral.innerCoreInPerm10)).toSection x) ≤ Qq i * w := by
    rw [rfns_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 2 4
      (appCcRS (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm2103) (appCcRS (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) (appCcRS (I := I) (M := M) g₀ 2 3 3 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kMid0Perm120) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁)))) DifferentialGeometry.Analysis.Parabolic.TensorSpectral.innerCoreInPerm10 i x]
    rw [b3_armOuter24_rfns_eq (I := I) (M := M) g₀ b3_kOut0Perm2103
      (appCcRS (I := I) (M := M) g₀ 2 3 4 (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionField (I := I) g₀ g₁) (appCcRS (I := I) (M := M) g₀ 2 3 3 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kMid0Perm120) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffContrInsertionInnerField (I := I) g₀ g₁))) i x]
    exact hquad _ hWb
  have hs7 : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 4 i (appCcRS (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm3012) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffGradContrInsertionField (I := I) g₀ g₁))).toSection x)) ≤
      Real.sqrt fr * (d * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x))
        + Real.sqrt ((Kc (i + 1) * ((i : ℝ) + 1)) * w)) := by
    rw [b3_armOuter24_rfns_eq (I := I) (M := M) g₀ b3_kOut0Perm3012
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffGradContrInsertionField (I := I) g₀ g₁) i x]
    exact hgrad_sqrt
  have hs8 : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 4 i (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoeffGen (I := I) (M := M) g₀ 2 4 (appCcRS (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm2013) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffGradContrInsertionField (I := I) g₀ g₁)) DifferentialGeometry.Analysis.Parabolic.TensorSpectral.innerCoreInPerm10)).toSection x)) ≤
      Real.sqrt fr * (d * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x))
        + Real.sqrt ((Kc (i + 1) * ((i : ℝ) + 1)) * w)) := by
    rw [rfns_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 2 4
      (appCcRS (I := I) (M := M) g₀ 2 4 4 (b3_slotPermCc0 (I := I) (M := M) g₀ b3_kOut0Perm2013) (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffGradContrInsertionField (I := I) g₀ g₁)) DifferentialGeometry.Analysis.Parabolic.TensorSpectral.innerCoreInPerm10 i x]
    rw [b3_armOuter24_rfns_eq (I := I) (M := M) g₀ b3_kOut0Perm2013
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connDiffGradContrInsertionField (I := I) g₀ g₁) i x]
    exact hgrad_sqrt
  have hWK_sqrt : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 4 i (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0KernelField (I := I) g₀ g₁)).toSection x)) ≤
      6 * Real.sqrt (Qq i * w)
      + 2 * (Real.sqrt fr * (d * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x))
        + Real.sqrt ((Kc (i + 1) * ((i : ℝ) + 1)) * w))) := by
    rw [hjets]
    refine le_trans (b4_sqrt_eightArm (I := I) (M := M) g₀ 2 (4 + i) x _ _ _ _ _ _ _ _) ?_
    have t1 := b1_sqrt_le_of_le hq1
    have t2 := b1_sqrt_le_of_le hq2
    have t3 := b1_sqrt_le_of_le hq3
    have t4 := b1_sqrt_le_of_le hq4
    have t5 := b1_sqrt_le_of_le hq5
    have t6 := b1_sqrt_le_of_le hq6
    linarith [t1, t2, t3, t4, t5, t6, hs7, hs8]
  have hcval : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((appCcRS (I := I) (M := M) g₀ 2 (4 + i) (2 + i)
        (appCcLeibnizPsi (I := I) (M := M) g₀ 4 2
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCastG0 (I := I) g₀ g₁) i i)
        (iteratedCovGrad (I := I) g₀ 2 4 i
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0KernelField (I := I) g₀ g₁))).toSection x) ≤
      (2 * Real.sqrt fr * d) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 4 i (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0KernelField (I := I) g₀ g₁)).toSection x) := by
    rw [show (2 * Real.sqrt fr * d) ^ 2 = 4 * fr * d ^ 2 from by
      rw [mul_pow, mul_pow, Real.sq_sqrt hfr]; norm_num]
    exact rfns_appCcRS_ricciCometricFourTraceCastG0_corner_op_le (I := I) (M := M) g₀ g₁ P htie hδ₀ hδ_le hδ0 hbound i
      (iteratedCovGrad (I := I) g₀ 2 4 i (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0KernelField (I := I) g₀ g₁)) x
  have hlow : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((∑ k ∈ Finset.range i,
        appCcRS (I := I) (M := M) g₀ 2 (4 + k) (2 + i)
          (appCcLeibnizPsi (I := I) (M := M) g₀ 4 2
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCastG0 (I := I) g₀ g₁) i k)
          (iteratedCovGrad (I := I) g₀ 2 4 k
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0KernelField (I := I) g₀ g₁))).toSection x) ≤ Clow i * w := by
    refine le_trans (rfns_appCcRS_argLower_le (I := I) (M := M) g₀ 2 4 2
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCastG0 (I := I) g₀ g₁)
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0KernelField (I := I) g₀ g₁) i x) ?_
    have hcell : ∀ k ∈ Finset.range i,
        riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + (i - k)) x
            ((iteratedCovGrad (I := I) g₀ 4 2 (i - k)
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCastG0 (I := I) g₀ g₁)).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + k) x
            ((iteratedCovGrad (I := I) g₀ 2 4 k
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0KernelField (I := I) g₀ g₁)).toSection x) ≤
        C4 (i - k) * CK k * Combinatorics.windowPairCellCount (i - k + 1) (k + 3) * w := by
      intro k hk
      rw [Finset.mem_range] at hk
      have h4 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + (i - k)) x
          ((iteratedCovGrad (I := I) g₀ 4 2 (i - k)
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCastG0 (I := I) g₀ g₁)).toSection x) ≤
          C4 (i - k) * Combinatorics.boundedFactorGridWindow b (i + 1) (i - k + 1) :=
        le_trans (hC4 g₁ P htie hδ_le hδ0 hbound (i - k) x)
          (mul_le_mul_of_nonneg_left
            (le_of_eq (b4_sum_atg_eq_bfgWindow b (show (i - k) + 1 ≤ (i + 1) + 1 from by omega)))
            (hC4_nn (i - k)))
      have hKk : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + k) x
          ((iteratedCovGrad (I := I) g₀ 2 4 k
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0KernelField (I := I) g₀ g₁)).toSection x) ≤
          CK k * Combinatorics.boundedFactorGridWindow b (i + 1) (k + 3) :=
        le_trans (hCK g₁ P htie hδ_le hδ0 hbound k x)
          (mul_le_mul_of_nonneg_left
            (le_of_eq (b4_sum_atg_eq_bfgWindow b (show k + 3 ≤ (i + 1) + 1 from by omega)))
            (hCK_nn k))
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + (i - k)) x
              ((iteratedCovGrad (I := I) g₀ 4 2 (i - k)
                (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCastG0 (I := I) g₀ g₁)).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + k) x
              ((iteratedCovGrad (I := I) g₀ 2 4 k
                (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0KernelField (I := I) g₀ g₁)).toSection x)
          ≤ (C4 (i - k) * Combinatorics.boundedFactorGridWindow b (i + 1) (i - k + 1)) *
              (CK k * Combinatorics.boundedFactorGridWindow b (i + 1) (k + 3)) :=
            mul_le_mul h4 hKk
              (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (4 + k) x _)
              (mul_nonneg (hC4_nn (i - k))
                (Combinatorics.boundedFactorGridWindow_nonneg b hb_nn (i + 1) (i - k + 1)))
        _ = (C4 (i - k) * CK k) *
              (Combinatorics.boundedFactorGridWindow b (i + 1) (i - k + 1) *
                Combinatorics.boundedFactorGridWindow b (i + 1) (k + 3)) := by ring
        _ ≤ (C4 (i - k) * CK k) *
              (Combinatorics.windowPairCellCount (i - k + 1) (k + 3) *
                Combinatorics.boundedFactorGridWindow b (i + 1) ((i - k + 1) + (k + 3) - 1)) :=
            mul_le_mul_of_nonneg_left
              (Combinatorics.boundedFactorGridWindow_mul_le b hb_nn (i + 1) (i - k + 1) (k + 3)
                (by omega) (by omega))
              (mul_nonneg (hC4_nn (i - k)) (hCK_nn k))
        _ = C4 (i - k) * CK k * Combinatorics.windowPairCellCount (i - k + 1) (k + 3) * w := by
            rw [show (i - k + 1) + (k + 3) - 1 = i + 3 from by omega, hw_def]
            ring
    calc (i : ℝ) * appCcGdiag (E := E) i *
            ∑ k ∈ Finset.range i,
              riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + (i - k)) x
                  ((iteratedCovGrad (I := I) g₀ 4 2 (i - k)
                    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCastG0 (I := I) g₀ g₁)).toSection x) *
                riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + k) x
                  ((iteratedCovGrad (I := I) g₀ 2 4 k
                    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0KernelField (I := I) g₀ g₁)).toSection x)
        ≤ (i : ℝ) * appCcGdiag (E := E) i *
            ∑ k ∈ Finset.range i,
              C4 (i - k) * CK k * Combinatorics.windowPairCellCount (i - k + 1) (k + 3) * w :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell)
            (mul_nonneg (Nat.cast_nonneg i) (appCcGdiag_nonneg (E := E) i))
      _ = Clow i * w := by
          simp only [hClow_def]
          rw [← Finset.sum_mul]
          ring
  have hsplitL0 : (iteratedCovGrad (I := I) g₀ 2 2 i
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
                (I := I) (M := M) g₀ g₁)).toSection x =
      (appCcRS (I := I) (M := M) g₀ 2 (4 + i) (2 + i)
          (appCcLeibnizPsi (I := I) (M := M) g₀ 4 2
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCastG0 (I := I) g₀ g₁) i i)
          (iteratedCovGrad (I := I) g₀ 2 4 i
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0KernelField (I := I) g₀ g₁))).toSection x +
      (∑ k ∈ Finset.range i,
          appCcRS (I := I) (M := M) g₀ 2 (4 + k) (2 + i)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 4 2
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCastG0 (I := I) g₀ g₁) i k)
            (iteratedCovGrad (I := I) g₀ 2 4 k
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0KernelField (I := I) g₀ g₁))).toSection x := by
    rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField_eq_appCcRS (I := I) (M := M) g₀ g₁,
      iteratedCovGrad_appCcRS_eq_argCorner_add_lower (I := I) (M := M) g₀ 2 4 2
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCastG0 (I := I) g₀ g₁)
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0KernelField (I := I) g₀ g₁) i,
      b1_toSection_add (I := I) (M := M) g₀ 2 (2 + i)]
  have hself : Real.sqrt fr * Real.sqrt fr = fr := Real.mul_self_sqrt hfr
  have hfold1 : (12 * Real.sqrt fr * d) * Real.sqrt (Qq i * w) =
      Real.sqrt ((144 * fr * d ^ 2 * Qq i) * w) := by
    rw [b4_coeff_into_sqrt (show (0 : ℝ) ≤ 12 * Real.sqrt fr * d from by positivity),
      show (12 * Real.sqrt fr * d) ^ 2 * Qq i = 144 * fr * d ^ 2 * Qq i from by
        rw [mul_pow, mul_pow, Real.sq_sqrt hfr]; ring]
  have hfold2 : (4 * fr * d) * Real.sqrt ((Kc (i + 1) * ((i : ℝ) + 1)) * w) =
      Real.sqrt ((16 * fr ^ 2 * d ^ 2 * (Kc (i + 1) * ((i : ℝ) + 1))) * w) := by
    rw [b4_coeff_into_sqrt (show (0 : ℝ) ≤ 4 * fr * d from by positivity),
      show (4 * fr * d) ^ 2 * (Kc (i + 1) * ((i : ℝ) + 1)) = 16 * fr ^ 2 * d ^ 2 * (Kc (i + 1) * ((i : ℝ) + 1)) from by ring]
  have htot : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
                (I := I) (M := M) g₀ g₁)).toSection x)) ≤
      (4 * fr * d ^ 2) * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x))
      + (Real.sqrt ((144 * fr * d ^ 2 * Qq i) * w) + Real.sqrt ((16 * fr ^ 2 * d ^ 2 * (Kc (i + 1) * ((i : ℝ) + 1))) * w) + Real.sqrt ((Clow i) * w)) := by
    rw [hsplitL0]
    refine le_trans (b1_sqrt_rfns_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
    have hcs : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((appCcRS (I := I) (M := M) g₀ 2 (4 + i) (2 + i)
          (appCcLeibnizPsi (I := I) (M := M) g₀ 4 2
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCastG0 (I := I) g₀ g₁) i i)
          (iteratedCovGrad (I := I) g₀ 2 4 i
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0KernelField (I := I) g₀ g₁))).toSection x)) ≤
        (2 * Real.sqrt fr * d) *
          (6 * Real.sqrt (Qq i * w)
            + 2 * (Real.sqrt fr * (d * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x))
              + Real.sqrt ((Kc (i + 1) * ((i : ℝ) + 1)) * w)))) :=
      le_trans (b4_sqrt_le_coeff_mul hcval (by positivity))
        (mul_le_mul_of_nonneg_left hWK_sqrt (by positivity))
    have hls : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((∑ k ∈ Finset.range i,
          appCcRS (I := I) (M := M) g₀ 2 (4 + k) (2 + i)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 4 2
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCastG0 (I := I) g₀ g₁) i k)
            (iteratedCovGrad (I := I) g₀ 2 4 k
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0KernelField (I := I) g₀ g₁))).toSection x)) ≤ Real.sqrt (Clow i * w) := b1_sqrt_le_of_le hlow
    refine le_trans (add_le_add hcs hls) (le_of_eq ?_)
    rw [← hfold1, ← hfold2]
    linear_combination (4 * d ^ 2 * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x))
      + 4 * d * Real.sqrt ((Kc (i + 1) * ((i : ℝ) + 1)) * w)) * hself
  have hfin := b4_young_head3
    (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + (i + 2)) x _) hw_nn
    (show (0 : ℝ) ≤ 4 * fr * d ^ 2 from by positivity)
    (show (0 : ℝ) ≤ 144 * fr * d ^ 2 * Qq i from by have h1 := hQq_nn i; positivity)
    (show (0 : ℝ) ≤ 16 * fr ^ 2 * d ^ 2 * (Kc (i + 1) * ((i : ℝ) + 1)) from by
      have h1 := hKc_nn (i + 1)
      have h2 : (0 : ℝ) ≤ (i : ℝ) + 1 := by positivity
      positivity)
    (show (0 : ℝ) ≤ Clow i from hClow_nn i)
    (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (2 + i) x _) htot
  refine le_trans hfin ?_
  have hcoef : (3 / 2 : ℝ) * (4 * fr * d ^ 2) ^ 2 ≤ ((21 / 4) * fr * d ^ 2) ^ 2 := by
    nlinarith [sq_nonneg (fr * d ^ 2)]
  have hKeq : Kfun i = 9 * (144 * fr * d ^ 2 * Qq i + 16 * fr ^ 2 * d ^ 2 * (Kc (i + 1) * ((i : ℝ) + 1)) + Clow i) := by
    simp only [hKfun_def]
  rw [hKeq]
  exact add_le_add (mul_le_mul_of_nonneg_right hcoef hbtop_nn) (le_refl _)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private lemma b4_young_head1 {T e btop c K w : ℝ}
    (hbtop : 0 ≤ btop) (hw : 0 ≤ w) (he : 0 ≤ e) (hc : 0 ≤ c) (hK : 0 ≤ K) (hT0 : 0 ≤ T)
    (hT : Real.sqrt T ≤ e * Real.sqrt btop + c * Real.sqrt (K * w)) :
    T ≤ (5 / 4) * e ^ 2 * btop + 5 * c ^ 2 * K * w := by
  set u : ℝ := e * Real.sqrt btop with hu_def
  set v : ℝ := c * Real.sqrt (K * w) with hv_def
  have hu0 : 0 ≤ u := mul_nonneg he (Real.sqrt_nonneg _)
  have hv0 : 0 ≤ v := mul_nonneg hc (Real.sqrt_nonneg _)
  have hTuv : T ≤ (u + v) ^ 2 := by
    have hsq : Real.sqrt T ^ 2 ≤ (u + v) ^ 2 := by
      nlinarith [hT, Real.sqrt_nonneg T]
    rw [Real.sq_sqrt hT0] at hsq
    exact hsq
  have hyoung := rfns_tl_young_sq u v (1 / 4) (by norm_num)
  have hu2 : u ^ 2 = e ^ 2 * btop := by
    rw [hu_def, mul_pow, Real.sq_sqrt hbtop]
  have hv2 : v ^ 2 = c ^ 2 * (K * w) := by
    rw [hv_def, mul_pow, Real.sq_sqrt (by positivity)]
  have hinv : ((1 : ℝ) / 4)⁻¹ = 4 := by norm_num
  rw [hinv] at hyoung
  calc T ≤ (u + v) ^ 2 := hTuv
    _ ≤ (1 + 1 / 4) * u ^ 2 + (1 + 4) * v ^ 2 := hyoung
    _ = (5 / 4) * e ^ 2 * btop + 5 * c ^ 2 * K * w := by
        rw [hu2, hv2]
        ring

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedVariables false in

theorem rfns_iteratedCovGrad_refoldKernelContractionMonomialField_topSeparated_and_lowerWindow_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (σ : Equiv.Perm (Fin 4)) (i : ℕ) (x : M),
        (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((appCcRS (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
              (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2
                (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mvPairTraceOp (I := I) (M := M) g₀ g₁) i i)
              (iteratedCovGrad (I := I) g₀ 2 6 i
                (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6
                  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sigmaE
                  (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                    (domDomCongrSection (I := I) g₀
                      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
                      (iteratedCovGrad (I := I) g₀ 0 2 2
                        (symmS (I := I) (M := M) g₀ P))))))).toSection x) ≤
          ((1 / (1 - δ₀)) ^ 2) ^ 2 *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x))
        ∧
        (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
                (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P))
                σ)).toSection x
            - (appCcRS (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
              (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2
                (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mvPairTraceOp (I := I) (M := M) g₀ g₁) i i)
              (iteratedCovGrad (I := I) g₀ 2 6 i
                (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6
                  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sigmaE
                  (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                    (domDomCongrSection (I := I) g₀
                      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
                      (iteratedCovGrad (I := I) g₀ 0 2 2
                        (symmS (I := I) (M := M) g₀ P))))))).toSection x) ≤
          K i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3)) := by
  obtain ⟨K, hK_nn, hres⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_rfns_icg_refoldKernelContractionMonomialField_leibnizResidual_window
      (I := I) (M := M) g₀ hδ₀
  refine ⟨K, hK_nn, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound σ i x
  exact ⟨DifferentialGeometry.Analysis.Parabolic.TensorSpectral.rfns_appCcRS_mvPairTraceOp_leibnizCorner_refoldArgument_le
      (I := I) (M := M) g₀ g₁ P htie hδ₀ hδ_le hδ0 hbound σ i x,
    hres g₁ P htie hδ_le hδ0 hbound σ i x⟩

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedVariables false in

theorem refoldKernelContractionMonomialField_eq_of_finrank_one (h1 : Module.finrank ℝ E = 1)
    (g₀ g₁ : SmoothRiemannianMetric I M) (G : SmoothCcTensor g₀ 0 4)
    (σ σ' : Equiv.Perm (Fin 4)) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁ G σ =
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁ G σ' := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField_toSection (I := I) (M := M) g₀ g₁ G σ x,
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField_toSection (I := I) (M := M) g₀ g₁ G σ' x]
  refine congrArg (fun (T : Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ]
      Tensor0SBundle.Tensor0SSpace 2 I x) =>
    (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM T)) ?_
  rw [show DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialBiContrFib (I := I) (M := M) g₁
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ccTensorFourUnitValueSection (I := I) (M := M) g₀ G) σ x =
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialFibFixedFrame (I := I) (M := M)
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ccTensorFourUnitValueSection (I := I) (M := M) g₀ G) σ
        (smoothOrthoFrame (I := I) g₁ x) x from rfl,
    show DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialBiContrFib (I := I) (M := M) g₁
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ccTensorFourUnitValueSection (I := I) (M := M) g₀ G) σ' x =
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialFibFixedFrame (I := I) (M := M)
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ccTensorFourUnitValueSection (I := I) (M := M) g₀ G) σ'
        (smoothOrthoFrame (I := I) g₁ x) x from rfl]
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective (𝕜 := ℝ)
  apply ContinuousMultilinearMap.ext
  intro v
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialFibFixedFrame_toModel,
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialFibFixedFrame_toModel]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  refine congrArg _ ?_
  have hperm : ∀ (ρ : Equiv.Perm (Fin 4)) (W : Fin 4 → E),
      Tensor0SBundle.Tensor0SSpace.toModel (𝕜 := ℝ)
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ccTensorFourUnitValueSection (I := I) (M := M) g₀ G x)
          (fun i => W (ρ i)) =
        Tensor0SBundle.Tensor0SSpace.toModel (𝕜 := ℝ)
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ccTensorFourUnitValueSection (I := I) (M := M) g₀ G x) W := by
    intro ρ W
    rw [← ContinuousMultilinearMap.domDomCongr_apply,
      dim1_domDomCongr_eq (E := E) h1
        (Tensor0SBundle.Tensor0SSpace.toModel (𝕜 := ℝ)
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ccTensorFourUnitValueSection (I := I) (M := M) g₀ G x)) ρ]
  rw [hperm σ, hperm σ']

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
private theorem b4_refold_topSeparated_proof (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ}
    (hδ₀ : δ₀ < 1) (hδ₀half : δ₀ ≤ 1 / 2) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionField
                (I := I) (M := M) g₀ g₁
                (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P))
                (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
                (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1)).toSection x) ≤
          ((23 / 20 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2) ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)
            + K i * Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := by
  classical
  by_cases hn1 : Module.finrank ℝ E = 1
  · refine ⟨fun _ => 0, fun _ => le_refl 0, ?_⟩
    intro g₁ P htie δ hδ_le hδ0 hbound i x
    have hzero : DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionField
        (I := I) (M := M) g₀ g₁
        (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P))
        (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
        (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1 = 0 := by
      rw [show DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionField
          (I := I) (M := M) g₀ g₁
          (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P))
          (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1 =
          (1 / 2 : ℝ) •
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
                (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P)) (Equiv.swap (0 : Fin 4) 2)
              + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
                (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P)) (Equiv.swap (1 : Fin 4) 3)
              - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
                (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P)) (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3)
              - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
                (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P)) 1) from rfl]
      rw [refoldKernelContractionMonomialField_eq_of_finrank_one (I := I) (M := M) hn1 g₀ g₁
          (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P)) (Equiv.swap (1 : Fin 4) 3) (Equiv.swap (0 : Fin 4) 2),
        refoldKernelContractionMonomialField_eq_of_finrank_one (I := I) (M := M) hn1 g₀ g₁
          (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P)) (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) (Equiv.swap (0 : Fin 4) 2),
        refoldKernelContractionMonomialField_eq_of_finrank_one (I := I) (M := M) hn1 g₀ g₁
          (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P)) 1 (Equiv.swap (0 : Fin 4) 2)]
      rw [show DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
            (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P)) (Equiv.swap (0 : Fin 4) 2)
          + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
            (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P)) (Equiv.swap (0 : Fin 4) 2)
          - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
            (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P)) (Equiv.swap (0 : Fin 4) 2)
          - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
            (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P)) (Equiv.swap (0 : Fin 4) 2) = 0 from by abel]
      rw [smul_zero]
    rw [hzero, rfns_tl_icg_zero (I := I) g₀ 2 2 i,
      rfns_tl_toSection_zero (I := I) g₀ 2 (2 + i) x,
      riemannianFiberNormSq_zero (I := I) (M := M) g₀ 2 (2 + i) x]
    simp only [zero_mul, add_zero]
    exact mul_nonneg (sq_nonneg _)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + (i + 2)) x _)
  · have hn2 : 2 ≤ Module.finrank ℝ E := by
      have h1 : Module.finrank ℝ E ≠ 0 := NeZero.ne _
      omega
    obtain ⟨KM, hKM_nn, hKM⟩ := rfns_iteratedCovGrad_refoldKernelContractionMonomialField_topSeparated_and_lowerWindow_le (I := I) (M := M) g₀ hδ₀
    refine ⟨fun i => 5 * 2 ^ 2 * KM i,
      fun i => by have := hKM_nn i; positivity, ?_⟩
    intro g₁ P htie δ hδ_le hδ0 hbound i x
    have hb_nn : ∀ l, (0 : ℝ) ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) :=
      fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
    have hw_nn : (0 : ℝ) ≤ Combinatorics.boundedFactorGridWindow
        (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) :=
      Combinatorics.boundedFactorGridWindow_nonneg _ hb_nn (i + 1) (i + 3)
    have hsm : ∀ σ : Equiv.Perm (Fin 4),
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
              (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P)) σ)).toSection x)) ≤
        (1 / (1 - δ₀)) ^ 2 * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0
            (2 + (i + 2)) x ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x))
          + Real.sqrt (KM i * Combinatorics.boundedFactorGridWindow
              (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3)) := by
      intro σ
      have hconj := hKM g₁ P htie hδ_le hδ0 hbound σ i x
      have h1 := b1_sqrt_le_of_le hconj.1
      have h2 := b1_sqrt_le_of_le hconj.2
      have hd2 : Real.sqrt (((1 / (1 - δ₀)) ^ 2) ^ 2 *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) =
          (1 / (1 - δ₀)) ^ 2 *
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) := by
        rw [Real.sqrt_mul (by positivity) _, Real.sqrt_sq (by positivity)]
      calc Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            (((iteratedCovGrad (I := I) g₀ 2 2 i
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
              (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P))
              σ)).toSection x)))
          = Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              ((((iteratedCovGrad (I := I) g₀ 2 2 i
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
              (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P))
              σ)).toSection x)
                - (appCcRS (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
              (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2
                (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mvPairTraceOp (I := I) (M := M) g₀ g₁) i i)
              (iteratedCovGrad (I := I) g₀ 2 6 i
                (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6
                  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sigmaE
                  (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                    (domDomCongrSection (I := I) g₀
                      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
                      (iteratedCovGrad (I := I) g₀ 0 2 2
                        (symmS (I := I) (M := M) g₀ P))))))).toSection x)
                + (appCcRS (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
              (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2
                (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mvPairTraceOp (I := I) (M := M) g₀ g₁) i i)
              (iteratedCovGrad (I := I) g₀ 2 6 i
                (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6
                  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sigmaE
                  (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                    (domDomCongrSection (I := I) g₀
                      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
                      (iteratedCovGrad (I := I) g₀ 0 2 2
                        (symmS (I := I) (M := M) g₀ P))))))).toSection x)) := by
            rw [sub_add_cancel]
        _ ≤ Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              (((iteratedCovGrad (I := I) g₀ 2 2 i
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
              (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P))
              σ)).toSection x)
                - (appCcRS (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
              (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2
                (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mvPairTraceOp (I := I) (M := M) g₀ g₁) i i)
              (iteratedCovGrad (I := I) g₀ 2 6 i
                (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6
                  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sigmaE
                  (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                    (domDomCongrSection (I := I) g₀
                      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
                      (iteratedCovGrad (I := I) g₀ 0 2 2
                        (symmS (I := I) (M := M) g₀ P))))))).toSection x))
            + Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
                ((appCcRS (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
              (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2
                (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mvPairTraceOp (I := I) (M := M) g₀ g₁) i i)
              (iteratedCovGrad (I := I) g₀ 2 6 i
                (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6
                  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sigmaE
                  (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                    (domDomCongrSection (I := I) g₀
                      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ)
                      (iteratedCovGrad (I := I) g₀ 0 2 2
                        (symmS (I := I) (M := M) g₀ P))))))).toSection x)) :=
            b1_sqrt_rfns_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _
        _ ≤ Real.sqrt (KM i * Combinatorics.boundedFactorGridWindow
              (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3))
            + Real.sqrt (((1 / (1 - δ₀)) ^ 2) ^ 2 *
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) :=
            add_le_add h2 h1
        _ = (1 / (1 - δ₀)) ^ 2 *
              Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x))
            + Real.sqrt (KM i * Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3)) := by
            rw [hd2]
            ring
    have hsplit : (iteratedCovGrad (I := I) g₀ 2 2 i
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionField
          (I := I) (M := M) g₀ g₁
          (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P))
          (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1)).toSection x =
        (1 / 2 : ℝ) •
          ((iteratedCovGrad (I := I) g₀ 2 2 i
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
              (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P)) (Equiv.swap (0 : Fin 4) 2))).toSection x
          + (iteratedCovGrad (I := I) g₀ 2 2 i
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
              (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P)) (Equiv.swap (1 : Fin 4) 3))).toSection x
          - (iteratedCovGrad (I := I) g₀ 2 2 i
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
              (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P)) (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))).toSection x
          - (iteratedCovGrad (I := I) g₀ 2 2 i
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
              (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P)) 1)).toSection x) := by
      rw [show DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionField
          (I := I) (M := M) g₀ g₁
          (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P))
          (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1 =
          (1 / 2 : ℝ) •
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
                (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P)) (Equiv.swap (0 : Fin 4) 2)
              + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
                (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P)) (Equiv.swap (1 : Fin 4) 3)
              - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
                (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P)) (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3)
              - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
                (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P)) 1) from rfl]
      rw [b1_iteratedCovGrad_smul (I := I) (M := M) g₀ 2 2 i]
      rw [iteratedCovGrad_sub (I := I) g₀ 2 2 i, iteratedCovGrad_sub (I := I) g₀ 2 2 i,
        iteratedCovGrad_add (I := I) g₀ 2 2 i]
      rw [b1_toSection_smul (I := I) (M := M) g₀ 2 (2 + i)]
      rw [b1_toSection_sub (I := I) (M := M) g₀ 2 (2 + i),
        b1_toSection_sub (I := I) (M := M) g₀ 2 (2 + i),
        b1_toSection_add (I := I) (M := M) g₀ 2 (2 + i)]
    have htot : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionField
            (I := I) (M := M) g₀ g₁
            (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P))
            (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
            (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1)).toSection x)) ≤
        (2 * (1 / (1 - δ₀)) ^ 2) * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 0
            (2 + (i + 2)) x ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x))
          + 2 * Real.sqrt (KM i * Combinatorics.boundedFactorGridWindow
              (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3)) := by
      rw [hsplit]
      refine le_trans (b4_sqrt_le_coeff_mul (c := 1 / 2)
        (le_of_eq (b1_rfns_smul_value (I := I) (M := M) g₀ 2 (2 + i) x (1 / 2) _))
        (by norm_num)) ?_
      have hsub2 := b1_sqrt_rfns_sub_le (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
            (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P)) (Equiv.swap (0 : Fin 4) 2))).toSection x
        + (iteratedCovGrad (I := I) g₀ 2 2 i
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
            (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P)) (Equiv.swap (1 : Fin 4) 3))).toSection x
        - (iteratedCovGrad (I := I) g₀ 2 2 i
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
            (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P)) (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))).toSection x)
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
            (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P)) 1)).toSection x)
      have hsub1 := b1_sqrt_rfns_sub_le (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
            (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P)) (Equiv.swap (0 : Fin 4) 2))).toSection x
        + (iteratedCovGrad (I := I) g₀ 2 2 i
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
            (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P)) (Equiv.swap (1 : Fin 4) 3))).toSection x)
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
            (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P)) (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3))).toSection x)
      have hadd1 := b1_sqrt_rfns_add_le (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
            (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P)) (Equiv.swap (0 : Fin 4) 2))).toSection x)
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionMonomialField (I := I) (M := M) g₀ g₁
            (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P)) (Equiv.swap (1 : Fin 4) 3))).toSection x)
      have h1 := hsm (Equiv.swap (0 : Fin 4) 2)
      have h2 := hsm (Equiv.swap (1 : Fin 4) 3)
      have h3 := hsm (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3)
      have h4 := hsm 1
      linarith [hsub2, hsub1, hadd1, h1, h2, h3, h4]
    have hfin := b4_young_head1 (hb_nn (i + 2)) hw_nn
      (show (0 : ℝ) ≤ 2 * (1 / (1 - δ₀)) ^ 2 from by positivity)
      (show (0 : ℝ) ≤ (2 : ℝ) from by norm_num) (hKM_nn i)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (2 + i) x _) htot
    refine le_trans hfin (add_le_add ?_ (le_refl _))
    refine mul_le_mul_of_nonneg_right ?_ (hb_nn (i + 2))
    have hfr2 : (2 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by exact_mod_cast hn2
    have hd4 : (0 : ℝ) ≤ ((1 / (1 - δ₀)) ^ 2) ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right
      (mul_le_mul hfr2 hfr2 (by norm_num) (by linarith)) hd4]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in

theorem rfns_iteratedCovGrad_refoldKernelContractionField_symmSSecondGradient_topAmplitude_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ}
    (hδ₀ : δ₀ < 1) (hδ₀half : δ₀ ≤ 1 / 2) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionField
                (I := I) (M := M) g₀ g₁
                (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P))
                (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
                (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1)).toSection x) ≤
          ((23 / 20 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2) ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)
            + K i * Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) :=
  b4_refold_topSeparated_proof (I := I) (M := M) g₀ hδ₀ hδ₀half

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in

theorem rfns_iteratedCovGrad_linearizedRicciConnDiffOrder0CoeffField_topAmplitude_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ}
    (hδ₀ : δ₀ < 1) (hδ₀half : δ₀ ≤ 1 / 2) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
                (I := I) (M := M) g₀ g₁)).toSection x) ≤
          ((21 / 4 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2) ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)
            + K i * Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) :=
  b4_L0_topSeparated_proof (I := I) (M := M) g₀ hδ₀ hδ₀half

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in

private theorem rfns_iteratedCovGrad_linearizedRicciConnDiffOrder0RiemannHalfCombination_topSeparated_budgetDualCap_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (hδ₀half : δ₀ ≤ 1 / 2) :
    ∃ ε : ℝ, 0 ≤ ε ∧
      27 * Real.sqrt (Module.finrank ℝ E) * (1 - δ₀) * ε ≤
        2 * (32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
          28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2) ∧
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
                  (I := I) (M := M) g₀ g₁
                + (1 / 2 : ℝ) •
                  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
                    (I := I) (M := M) g₀ g₁)).toSection x) ≤
          ε ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)
            + C i * Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := by
  by_cases hn1 : Module.finrank ℝ E = 1
  · refine ⟨0, le_refl 0, ?_, fun _ => 0, fun _ => le_refl 0, ?_⟩
    · rw [mul_zero]
      rw [rfns_tl_fibreConst_one hn1]
      norm_num
    · intro g₁ P htie δ hδ_le hδ0 hbound i x
      have hS : DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
            (I := I) (M := M) g₀ g₁
          + (1 / 2 : ℝ) •
            DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
              (I := I) (M := M) g₀ g₁ = (0 : SmoothCcTensor g₀ 2 2) := by
        rw [dim1_linearizedRicciConnDiffOrder0CoeffField_eq_zero hn1 g₀ g₁,
          dim1_ricciArmOrder0RiemannCoeff_eq_zero hn1 g₀ g₁]
        rw [smul_zero, add_zero]
      rw [hS]
      rw [rfns_tl_icg_zero (I := I) g₀ 2 2 i]
      rw [rfns_tl_toSection_zero (I := I) g₀ 2 (2 + i) x]
      rw [riemannianFiberNormSq_zero (I := I) (M := M) g₀ 2 (2 + i) x]
      rw [show ((0 : ℝ)) ^ 2 = 0 from by norm_num, zero_mul, zero_mul, add_zero]
  · have hn2 : 2 ≤ Module.finrank ℝ E := by
      have h1 : Module.finrank ℝ E ≠ 0 := NeZero.ne _
      omega
    obtain ⟨KC, hKC_nn, hKC⟩ := rfns_iteratedCovGrad_linearizedRicciConnDiffOrder0CoeffField_topAmplitude_le (I := I) (M := M) g₀ hδ₀ hδ₀half
    obtain ⟨KR, hKR_nn, hKR⟩ := rfns_iteratedCovGrad_refoldKernelContractionField_symmSSecondGradient_topAmplitude_le (I := I) (M := M) g₀ hδ₀ hδ₀half
    obtain ⟨KA, hKA_nn, hKA⟩ :=
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_rfns_icg_ricciArmOrder0AACommCoeffField_window
        (I := I) (M := M) g₀ hδ₀
    obtain ⟨KB, hKB_nn, hKB⟩ := b1_bgRDiff_window (I := I) (M := M) g₀ hδ₀
    obtain ⟨KM, hKM_nn, hKM⟩ := b1_fixedField_jet_bound (I := I) (M := M) g₀ 2 2
      ((1 / 2 : ℝ) •
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
          (I := I) (M := M) g₀ g₀)
    refine ⟨(804 / 125 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2,
      by positivity,
      rfns_tl_budgetDualCap (Module.finrank ℝ E) hn2 hδ₀ hδ₀half
        (by norm_num) (by norm_num),
      fun i => 505 * (KC i + KR i + KA i + KB i + KM i),
      fun i => by
        have h1 := hKC_nn i
        have h2 := hKR_nn i
        have h3 := hKA_nn i
        have h4 := hKB_nn i
        have h5 := hKM_nn i
        positivity, ?_⟩
    intro g₁ P htie δ hδ_le hδ0 hbound i x
    have hQsymm : ∀ (y : M) (v w : TangentSpace I y),
        ccTensorBilin (I := I) g₀ (symmS (I := I) (M := M) g₀ P) y v w =
        ccTensorBilin (I := I) g₀ (symmS (I := I) (M := M) g₀ P) y w v := by
      intro y v w
      rw [ccTensorBilin_symmS (I := I) (M := M) g₀ P y v w,
        ccTensorBilin_symmS (I := I) (M := M) g₀ P y w v,
        ccTensorBilinSymm_apply, ccTensorBilinSymm_apply]
      ring
    have htie' : ∀ (y : M) (v w : TangentSpace I y),
        g₁.inner y v w = g₀.inner y v w +
          ccTensorBilinSymm (I := I) g₀ (symmS (I := I) (M := M) g₀ P) y v w := by
      intro y v w
      rw [show ccTensorBilinSymm (I := I) g₀ (symmS (I := I) (M := M) g₀ P) y v w =
          (1 / 2 : ℝ) * (ccTensorBilin (I := I) g₀ (symmS (I := I) (M := M) g₀ P) y v w
            + ccTensorBilin (I := I) g₀ (symmS (I := I) (M := M) g₀ P) y w v) from by
        rw [ccTensorBilinSymm_apply]]
      rw [ccTensorBilin_symmS (I := I) (M := M) g₀ P y v w,
        ccTensorBilin_symmS (I := I) (M := M) g₀ P y w v,
        ccTensorBilinSymm_apply, ccTensorBilinSymm_apply, htie y v w,
        ccTensorBilinSymm_apply]
      ring
    have hhalf := b1_halfRiemannBackgroundDifference_eq_residualFieldSum_add_kernelContraction
      (I := I) (M := M) g₀ g₁ (symmS (I := I) (M := M) g₀ P) htie' hQsymm
    have hdec : DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
          (I := I) (M := M) g₀ g₁
        + (1 / 2 : ℝ) •
          DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
            (I := I) (M := M) g₀ g₁ =
        (((DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
            (I := I) (M := M) g₀ g₁
          + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0AACommCoeffField
              (I := I) (M := M) g₀ g₁)
          + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.bgRDiffRefoldRemainderField
              (I := I) (M := M) g₀ g₁)
          + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionField
              (I := I) (M := M) g₀ g₁
              (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P))
              (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
              (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1)
          + (1 / 2 : ℝ) •
            DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
              (I := I) (M := M) g₀ g₀ := by
      have hgoal : DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0AACommCoeffField
            (I := I) (M := M) g₀ g₁
          + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.bgRDiffRefoldRemainderField
              (I := I) (M := M) g₀ g₁
          + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionField
              (I := I) (M := M) g₀ g₁
              (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P))
              (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
              (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1 =
          (1 / 2 : ℝ) •
            DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
              (I := I) (M := M) g₀ g₁
          - (1 / 2 : ℝ) •
            DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
              (I := I) (M := M) g₀ g₀ := by
        rw [← hhalf]
        rw [smul_sub]
      have hstep : (((DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
            (I := I) (M := M) g₀ g₁
          + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0AACommCoeffField
              (I := I) (M := M) g₀ g₁)
          + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.bgRDiffRefoldRemainderField
              (I := I) (M := M) g₀ g₁)
          + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionField
              (I := I) (M := M) g₀ g₁
              (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P))
              (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
              (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1)
          =
          DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
            (I := I) (M := M) g₀ g₁
          + ((1 / 2 : ℝ) •
              DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
                (I := I) (M := M) g₀ g₁
            - (1 / 2 : ℝ) •
              DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
                (I := I) (M := M) g₀ g₀) := by
        rw [show (((DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
            (I := I) (M := M) g₀ g₁
          + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0AACommCoeffField
              (I := I) (M := M) g₀ g₁)
          + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.bgRDiffRefoldRemainderField
              (I := I) (M := M) g₀ g₁)
          + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionField
              (I := I) (M := M) g₀ g₁
              (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P))
              (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
              (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1)
          =
          DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
            (I := I) (M := M) g₀ g₁
          + (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0AACommCoeffField
              (I := I) (M := M) g₀ g₁
            + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.bgRDiffRefoldRemainderField
              (I := I) (M := M) g₀ g₁
            + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionField
              (I := I) (M := M) g₀ g₁
              (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P))
              (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
              (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1) from by abel]
        rw [hgoal]
      rw [hstep]
      abel
    rw [hdec]
    rw [iteratedCovGrad_add (I := I) g₀ 2 2 i, iteratedCovGrad_add (I := I) g₀ 2 2 i,
      iteratedCovGrad_add (I := I) g₀ 2 2 i, iteratedCovGrad_add (I := I) g₀ 2 2 i]
    rw [b1_toSection_add (I := I) (M := M) g₀ 2 (2 + i), b1_toSection_add (I := I) (M := M) g₀ 2 (2 + i),
      b1_toSection_add (I := I) (M := M) g₀ 2 (2 + i), b1_toSection_add (I := I) (M := M) g₀ 2 (2 + i)]
    have hb_nn : ∀ l, (0 : ℝ) ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) :=
      fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
    have hw_nn : (0 : ℝ) ≤ Combinatorics.boundedFactorGridWindow
        (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) :=
      Combinatorics.boundedFactorGridWindow_nonneg _ hb_nn (i + 1) (i + 3)
    have hw_one : (1 : ℝ) ≤ Combinatorics.boundedFactorGridWindow
        (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) :=
      Combinatorics.one_le_boundedFactorGridWindow _ hb_nn (by omega)
    have hL0b := hKC g₁ P htie hδ_le hδ0 hbound i x
    have hRb := hKR g₁ P htie hδ_le hδ0 hbound i x
    have hAb := hKA g₁ P htie hδ_le hδ0 hbound i x
    have hBb := hKB g₁ P htie hδ_le hδ0 hbound i x
    have hMb : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          ((1 / 2 : ℝ) •
            DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
              (I := I) (M := M) g₀ g₀)).toSection x) ≤
        KM i * Combinatorics.boundedFactorGridWindow
          (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := by
      refine le_trans (hKM i x) ?_
      nlinarith [hw_one, hKM_nn i]
    set T1 : TensorRSSpace 2 (2 + i) I x := (iteratedCovGrad (I := I) g₀ 2 2 i
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
        (I := I) (M := M) g₀ g₁)).toSection x with hT1_def
    set T2 : TensorRSSpace 2 (2 + i) I x := (iteratedCovGrad (I := I) g₀ 2 2 i
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0AACommCoeffField
        (I := I) (M := M) g₀ g₁)).toSection x with hT2_def
    set T3 : TensorRSSpace 2 (2 + i) I x := (iteratedCovGrad (I := I) g₀ 2 2 i
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.bgRDiffRefoldRemainderField
        (I := I) (M := M) g₀ g₁)).toSection x with hT3_def
    set T4 : TensorRSSpace 2 (2 + i) I x := (iteratedCovGrad (I := I) g₀ 2 2 i
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.refoldKernelContractionField
        (I := I) (M := M) g₀ g₁
        (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ P))
        (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
        (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1)).toSection x with hT4_def
    set T5 : TensorRSSpace 2 (2 + i) I x := (iteratedCovGrad (I := I) g₀ 2 2 i
      ((1 / 2 : ℝ) •
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
          (I := I) (M := M) g₀ g₀)).toSection x with hT5_def
    set btop : ℝ := riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
      ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x) with hbtop_def
    set w : ℝ := Combinatorics.boundedFactorGridWindow
      (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) with hw_def
    have hsq_chain : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((((T1 + T2) + T3) + T4) + T5)) ≤
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x T1)
        + Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x T2)
        + Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x T3)
        + Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x T4)
        + Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x T5) := by
      have h4 := b1_sqrt_rfns_add_le (I := I) (M := M) g₀ 2 (2 + i) x
        (((T1 + T2) + T3) + T4) T5
      have h3 := b1_sqrt_rfns_add_le (I := I) (M := M) g₀ 2 (2 + i) x
        ((T1 + T2) + T3) T4
      have h2 := b1_sqrt_rfns_add_le (I := I) (M := M) g₀ 2 (2 + i) x (T1 + T2) T3
      have h1 := b1_sqrt_rfns_add_le (I := I) (M := M) g₀ 2 (2 + i) x T1 T2
      linarith [h1, h2, h3, h4]
    have hsp1 : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x T1) ≤
        ((21 / 4 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2) * Real.sqrt btop
        + Real.sqrt (KC i * w) :=
      b1_sqrt_head_split (by positivity) (hb_nn (i + 2)) (hKC_nn i) hw_nn hL0b
    have hsp4 : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x T4) ≤
        ((23 / 20 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2) * Real.sqrt btop
        + Real.sqrt (KR i * w) :=
      b1_sqrt_head_split (by positivity) (hb_nn (i + 2)) (hKR_nn i) hw_nn hRb
    have hsp2 : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x T2) ≤
        Real.sqrt (KA i * w) := b1_sqrt_le_of_le hAb
    have hsp3 : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x T3) ≤
        Real.sqrt (KB i * w) := b1_sqrt_le_of_le hBb
    have hsp5 : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x T5) ≤
        Real.sqrt (KM i * w) := b1_sqrt_le_of_le hMb
    have hTsum : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((((T1 + T2) + T3) + T4) + T5)) ≤
        (((23 / 20 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2)
          + ((21 / 4 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2)) * Real.sqrt btop
        + (Real.sqrt (KC i * w) + Real.sqrt (KR i * w) + Real.sqrt (KA i * w)
          + Real.sqrt (KB i * w) + Real.sqrt (KM i * w)) := by
      have hexp : (((23 / 20 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2)
          + ((21 / 4 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2)) * Real.sqrt btop =
          ((23 / 20 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2) * Real.sqrt btop
          + ((21 / 4 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2) * Real.sqrt btop := by
        ring
      rw [hexp]
      linarith [hsq_chain, hsp1, hsp2, hsp3, hsp4, hsp5]
    have hfin := b1_young_assembly (hb_nn (i + 2)) hw_nn
      (by positivity : (0 : ℝ) ≤ (23 / 20 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2)
      (by positivity : (0 : ℝ) ≤ (21 / 4 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2)
      (hKC_nn i) (hKR_nn i) (hKA_nn i) (hKB_nn i) (hKM_nn i)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (2 + i) x
        ((((T1 + T2) + T3) + T4) + T5)) hTsum
    have hEamp : (((201 : ℝ) / 200) *
        (((23 / 20 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2)
          + ((21 / 4 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2))) ^ 2 =
        ((804 / 125 : ℝ) * (Module.finrank ℝ E : ℝ) * (1 / (1 - δ₀)) ^ 2) ^ 2 := by
      ring
    rw [hEamp] at hfin
    exact hfin

namespace DeTurckRemainderTameLipschitz

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in

theorem linearizedRicciConnDiffOrder0RiemannHalfCombination_perOrder_l2_topArm_tameEnvelope_generic_highOrder
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (hδ₀half : δ₀ ≤ 1 / 2) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
    ∃ ε : ℝ, 0 ≤ ε ∧
      27 * Real.sqrt (Module.finrank ℝ E) * (1 - δ₀) * ε ≤
        2 * (32 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 3 -
          28 * deTurckArmFibreConst (Module.finrank ℝ E) ^ 2) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), a < i →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
                  (I := I) (M := M) g₀ g₁
                + (1 / 2 : ℝ) •
                  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
                    (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) +
              ε ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 := by
  classical
  obtain ⟨ε, hε_nn, hε_cap, C, hC_nn, hC⟩ :=
    rfns_iteratedCovGrad_linearizedRicciConnDiffOrder0RiemannHalfCombination_topSeparated_budgetDualCap_le
      (I := I) (M := M) g₀ hδ₀ hδ₀half
  obtain ⟨Kflat, hKflat_nn, hKflat⟩ :=
    boundedFactorGridWindow_integral_ballUniform_flat_allOrders
      (I := I) (M := M) g₀ a ha_super hR
  refine ⟨fun i => C i * Kflat i, fun i => mul_nonneg (hC_nn i) (hKflat_nn i),
    ε, hε_nn, hε_cap, ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i hi
  by_cases hM : Nonempty M
  · obtain ⟨x₀⟩ := hM
    have hδ0 : 0 ≤ δ := by
      obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x₀, v ≠ 0 := by
        haveI : Nontrivial (TangentSpace I x₀) := by
          have hfr : 0 < Module.finrank ℝ (TangentSpace I x₀) := by
            have heq : Module.finrank ℝ (TangentSpace I x₀) = Module.finrank ℝ E := rfl
            rw [heq]; exact Nat.pos_of_ne_zero (NeZero.ne _)
          exact Module.nontrivial_of_finrank_pos hfr
        exact exists_ne 0
      have hpos : 0 < g₀.inner x₀ v v := g₀.pos x₀ v hv
      have hbound := hδ x₀ v v
      have hsqrt_pos : 0 < Real.sqrt (g₀.inner x₀ v v) := Real.sqrt_pos.mpr hpos
      have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀ P x₀ v v| := abs_nonneg _
      by_contra hδc
      have hδc' : δ < 0 := lt_of_not_ge hδc
      have hrhs_neg : δ * Real.sqrt (g₀.inner x₀ v v) * Real.sqrt (g₀.inner x₀ v v) < 0 := by
        have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 := mul_neg_of_neg_of_pos hδc' hsqrt_pos
        exact mul_neg_of_neg_of_pos h1 hsqrt_pos
      linarith [le_trans habs_nn hbound]
    obtain ⟨hWint, hWbound⟩ := hKflat P hPball i
    have hbint : MeasureTheory.Integrable
        (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
      DifferentialGeometry.Integral.Connection.integrable_riemannianFiberNormSq_toSection
        (I := I) (M := M) g₀ 0 (2 + (i + 2)) (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P)
    have hF_int : MeasureTheory.Integrable
        (fun x => ε ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)
          + C i * Combinatorics.boundedFactorGridWindow
              (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
      MeasureTheory.Integrable.add (hbint.const_mul (ε ^ 2)) (hWint.const_mul (C i))
    have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (2 + i)
      (iteratedCovGrad (I := I) g₀ 2 2 i
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
            (I := I) (M := M) g₀ g₁
          + (1 / 2 : ℝ) •
            DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
              (I := I) (M := M) g₀ g₁))
      (fun x => ε ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)
        + C i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3))
      hF_int
      (fun x => hC g₁ P htie hδ_le hδ0 hδ i x)
    refine le_trans key ?_
    rw [MeasureTheory.integral_add (hbint.const_mul (ε ^ 2)) (hWint.const_mul (C i)),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    have hPtop : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
        ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 := by
      rw [SmoothCcTensor.norm_def (I := I) (M := M) (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P),
        tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 0
          (2 + (i + 2)) (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P)]
    rw [hPtop]
    have h2 : C i * (∫ x, Combinatorics.boundedFactorGridWindow
        (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        (C i * Kflat i) * (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
      calc C i * (∫ x, Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀))
          ≤ C i * (Kflat i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left hWbound (hC_nn i)
        _ = (C i * Kflat i) * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by ring
    linarith
  · haveI hM' : IsEmpty M := not_nonempty_iff.mp hM
    have hz : ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnDiffOrder0CoeffField
            (I := I) (M := M) g₀ g₁
          + (1 / 2 : ℝ) •
            DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciArmOrder0RiemannCoeff
              (I := I) (M := M) g₀ g₁)‖ = 0 := by
      rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
        MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
    rw [hz]
    have hwin_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hK_nn : (0 : ℝ) ≤ C i * Kflat i := mul_nonneg (hC_nn i) (hKflat_nn i)
    have h1 : (0 : ℝ) ≤ (C i * Kflat i) * (1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) :=
      mul_nonneg hK_nn (by linarith)
    have h2 : (0 : ℝ) ≤ ε ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 :=
      mul_nonneg (sq_nonneg ε) (sq_nonneg _)
    nlinarith

end DeTurckRemainderTameLipschitz

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
