import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegCoeffJets
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderLowBaseC1Lip

/-!
# Fixed-background order-one coefficient pairs

This module isolates the two-state correction caused by replacing the frozen
metric in the DeTurck background slot by a fixed background metric.  The Ricci
order-one coefficient cancels from this correction.  The remaining Lie-arm
passenger is factored before its fixed-order Sobolev estimate.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option linter.unusedVariables false in
private theorem dom_sub
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (A B : SmoothCcTensor g 0 s) :
    domDomCongrSection (I := I) g σ (A - B) =
      domDomCongrSection (I := I) g σ A -
        domDomCongrSection (I := I) g σ B := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  have hsub : ∀ (P Q : SmoothCcTensor g 0 s),
      unitModel (I := I) (M := M) g s (P - Q) x =
        unitModel (I := I) (M := M) g s P x -
          unitModel (I := I) (M := M) g s Q x := by
    intro P Q
    simp only [unitModel]
    rw [SmoothCcTensor.toSection_sub]
    rfl
  rw [domDomCongrSection_unitModel, hsub A B]
  rw [hsub
    (domDomCongrSection (I := I) g σ A)
    (domDomCongrSection (I := I) g σ B)]
  rw [domDomCongrSection_unitModel, domDomCongrSection_unitModel]
  apply ContinuousMultilinearMap.ext
  intro v
  simp only [ContinuousMultilinearMap.sub_apply,
    ContinuousMultilinearMap.domDomCongr_apply]

set_option linter.unusedVariables false in
private theorem raise_sub
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : SmoothCcTensor g 0 (s + 2)) :
    cometricRaiseSlot0Field (I := I) (M := M) g s (A - B) =
      cometricRaiseSlot0Field (I := I) (M := M) g s A -
        cometricRaiseSlot0Field (I := I) (M := M) g s B := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show
      (cometricRaiseSlot0Field (I := I) (M := M) g s A -
        cometricRaiseSlot0Field (I := I) (M := M) g s B).toSection x =
      (cometricRaiseSlot0Field (I := I) (M := M) g s A).toSection x -
        (cometricRaiseSlot0Field (I := I) (M := M) g s B).toSection x from by
    rw [SmoothCcTensor.toSection_sub]
    rfl]
  rw [cometricRaiseSlot0Field_toSection,
    cometricRaiseSlot0Field_toSection,
    cometricRaiseSlot0Field_toSection]
  rw [show
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from
        (A - B).toSection x) (unitTensor (I := I) (M := M) x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from
        A.toSection x) (unitTensor (I := I) (M := M) x) -
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from
        B.toSection x) (unitTensor (I := I) (M := M) x) from by
    rw [SmoothCcTensor.toSection_sub]
    rfl]
  exact ContinuousLinearMap.map_sub _ _ _

private theorem lieKappa_eq
    (g gT gB : SmoothRiemannianMetric I M) :
    lieArm1LoweredBgKappa (I := I) (M := M) g gT gB =
      -lc0Kappa (I := I) (M := M) g gT gB := by
  have h := metricConnDiffLoweredCc_eq_neg_kappa
    (I := I) (M := M) g gT gB
  change lc0Kappa (I := I) (M := M) g gT gB =
    -lieArm1LoweredBgKappa (I := I) (M := M) g gT gB at h
  have hneg := congrArg Neg.neg h
  simp only [neg_neg] at hneg
  exact hneg.symm

private theorem lieKappa_bg
    (g gT gB : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g T x u v) :
    lieArm1LoweredBgKappa (I := I) (M := M) g gT gB -
        lieArm1LoweredBgKappa (I := I) (M := M) g gT g =
      -lc0Kappa (I := I) (M := M) g g gB -
        lc0PbLow (I := I) (M := M) g T g gB := by
  rw [lieKappa_eq (I := I) (M := M) g gT gB,
    lieKappa_eq (I := I) (M := M) g gT g,
    kappa_bg (I := I) (M := M) g gT gB T htie]
  module

private noncomputable def psiBgLeft
    (g gT gB : SmoothRiemannianMetric I M) : SmoothCcTensor g 1 2 :=
  cometricRaiseSlot0Field (I := I) (M := M) g 1
    (domDomCongrSection (I := I) g lieArm1RhoSlot0
      (lieArm1LoweredBgKappa (I := I) (M := M) g gT gB))

private theorem psiBgLeft_corr
    (g gT gB : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g T x u v) :
    psiBgLeft (I := I) (M := M) g gT gB -
        psiBgLeft (I := I) (M := M) g gT g =
      cometricRaiseSlot0Field (I := I) (M := M) g 1
        (domDomCongrSection (I := I) g lieArm1RhoSlot0
          (-lc0Kappa (I := I) (M := M) g g gB -
            lc0PbLow (I := I) (M := M) g T g gB)) := by
  simp only [psiBgLeft]
  rw [← raise_sub, ← dom_sub,
    lieKappa_bg (I := I) (M := M) g gT gB T htie]

private noncomputable def psiBgCorr
    (g gT gB : SmoothRiemannianMetric I M) : SmoothCcTensor g 1 2 :=
  lieArm1PsiB (I := I) (M := M) g gT gB -
    lieArm1PsiB (I := I) (M := M) g gT g

private theorem psiBgCorr_eq
    (g gT gB : SmoothRiemannianMetric I M) :
    psiBgCorr (I := I) (M := M) g gT gB =
      appCcRS (I := I) (M := M) g 1 1 2
        (psiBgLeft (I := I) (M := M) g gT gB -
          psiBgLeft (I := I) (M := M) g gT g)
        (sharpFlatEndoCc (I := I) g gT) := by
  simp only [psiBgCorr, psiBgLeft, lieArm1PsiB, lieArm1RhoSlot0]
  rw [appCcRS_sub_left]

private theorem psiBgLeft_pair
    (g gT gU gB : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    (hTtie : ∀ (x : M) (u v : TangentSpace I x),
      gT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
    (hUtie : ∀ (x : M) (u v : TangentSpace I x),
      gU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g U x u v) :
    (psiBgLeft (I := I) (M := M) g gT gB -
        psiBgLeft (I := I) (M := M) g gT g) -
      (psiBgLeft (I := I) (M := M) g gU gB -
        psiBgLeft (I := I) (M := M) g gU g) =
      cometricRaiseSlot0Field (I := I) (M := M) g 1
        (domDomCongrSection (I := I) g lieArm1RhoSlot0
          (-lc0PbLow (I := I) (M := M) g (T - U) g gB)) := by
  rw [psiBgLeft_corr (I := I) (M := M) g gT gB T hTtie,
    psiBgLeft_corr (I := I) (M := M) g gU gB U hUtie]
  rw [← raise_sub, ← dom_sub]
  congr 2
  rw [pbLow_sub (I := I) (M := M) g T U g gB]
  module

private theorem psiBgCorr_pair
    (g gT gU gB : SmoothRiemannianMetric I M) :
    psiBgCorr (I := I) (M := M) g gT gB -
        psiBgCorr (I := I) (M := M) g gU gB =
      appCcRS (I := I) (M := M) g 1 1 2
          (psiBgLeft (I := I) (M := M) g gT gB -
            psiBgLeft (I := I) (M := M) g gT g)
          (sharpFlatEndoCc (I := I) g gT -
            sharpFlatEndoCc (I := I) g gU) +
        appCcRS (I := I) (M := M) g 1 1 2
          ((psiBgLeft (I := I) (M := M) g gT gB -
              psiBgLeft (I := I) (M := M) g gT g) -
            (psiBgLeft (I := I) (M := M) g gU gB -
              psiBgLeft (I := I) (M := M) g gU g))
          (sharpFlatEndoCc (I := I) g gU) := by
  let AT : SmoothCcTensor g 1 2 :=
    psiBgLeft (I := I) (M := M) g gT gB -
      psiBgLeft (I := I) (M := M) g gT g
  let AU : SmoothCcTensor g 1 2 :=
    psiBgLeft (I := I) (M := M) g gU gB -
      psiBgLeft (I := I) (M := M) g gU g
  let ST : SmoothCcTensor g 1 1 := sharpFlatEndoCc (I := I) g gT
  let SU : SmoothCcTensor g 1 1 := sharpFlatEndoCc (I := I) g gU
  rw [psiBgCorr_eq (I := I) (M := M) g gT gB,
    psiBgCorr_eq (I := I) (M := M) g gU gB]
  change appCcRS (I := I) (M := M) g 1 1 2 AT ST -
      appCcRS (I := I) (M := M) g 1 1 2 AU SU =
    appCcRS (I := I) (M := M) g 1 1 2 AT (ST - SU) +
      appCcRS (I := I) (M := M) g 1 1 2 (AT - AU) SU
  have hR : appCcRS (I := I) (M := M) g 1 1 2 AT (ST - SU) =
      appCcRS (I := I) (M := M) g 1 1 2 AT ST -
        appCcRS (I := I) (M := M) g 1 1 2 AT SU := by
    rw [appCcRS_sub_right]
  have hL : appCcRS (I := I) (M := M) g 1 1 2 (AT - AU) SU =
      appCcRS (I := I) (M := M) g 1 1 2 AT SU -
        appCcRS (I := I) (M := M) g 1 1 2 AU SU := by
    rw [appCcRS_sub_left]
  rw [hR, hL]
  module

private theorem jet_add1
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (m : ℕ)
    (S V : SmoothCcTensor g r s) :
    lowJetSq (I := I) (M := M) g m (S + V) ≤
      2 * (lowJetSq (I := I) (M := M) g m S +
        lowJetSq (I := I) (M := M) g m V) := by
  unfold lowJetSq
  calc
    ∑ q ∈ Finset.range (m + 1),
        ‖iteratedCovGrad (I := I) g r s q (S + V)‖ ^ 2 ≤
      ∑ q ∈ Finset.range (m + 1),
        2 * (‖iteratedCovGrad (I := I) g r s q S‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g r s q V‖ ^ 2) := by
      refine Finset.sum_le_sum fun q _ => ?_
      rw [iteratedCovGrad_add]
      have htri := norm_add_le
        (iteratedCovGrad (I := I) g r s q S)
        (iteratedCovGrad (I := I) g r s q V)
      calc
        ‖iteratedCovGrad (I := I) g r s q S +
            iteratedCovGrad (I := I) g r s q V‖ ^ 2 ≤
          (‖iteratedCovGrad (I := I) g r s q S‖ +
            ‖iteratedCovGrad (I := I) g r s q V‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) htri 2
        _ ≤ 2 * (‖iteratedCovGrad (I := I) g r s q S‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g r s q V‖ ^ 2) := by
          nlinarith [sq_nonneg
            (‖iteratedCovGrad (I := I) g r s q S‖ -
              ‖iteratedCovGrad (I := I) g r s q V‖)]
    _ = 2 * ((∑ q ∈ Finset.range (m + 1),
          ‖iteratedCovGrad (I := I) g r s q S‖ ^ 2) +
        ∑ q ∈ Finset.range (m + 1),
          ‖iteratedCovGrad (I := I) g r s q V‖ ^ 2) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]

private theorem jet_smul1
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (m : ℕ)
    (c : ℝ) (S : SmoothCcTensor g r s) :
    lowJetSq (I := I) (M := M) g m (c • S) =
      c ^ 2 * lowJetSq (I := I) (M := M) g m S := by
  unfold lowJetSq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [iteratedCovGrad_smul, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]

private theorem jet_neg1
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (m : ℕ)
    (S : SmoothCcTensor g r s) :
    lowJetSq (I := I) (M := M) g m (-S) =
      lowJetSq (I := I) (M := M) g m S := by
  simpa only [neg_one_smul, neg_one_sq, one_mul] using
    jet_smul1 (I := I) (M := M) g m (-1 : ℝ) S

private theorem dom_h2
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g 0 s) :
    lowJetSq (I := I) (M := M) g 2
        (domDomCongrSection (I := I) g σ S) =
      lowJetSq (I := I) (M := M) g 2 S := by
  unfold lowJetSq
  apply Finset.sum_congr rfl
  intro q _
  rw [SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun x =>
    riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
      (I := I) (M := M) g σ S q x

private theorem raiseDom_h2
    (g : SmoothRiemannianMetric I M)
    (ρ : Equiv.Perm (Fin 3)) (S : SmoothCcTensor g 0 3) :
    lowJetSq (I := I) (M := M) g 2
        (cometricRaiseSlot0Field (I := I) (M := M) g 1
          (domDomCongrSection (I := I) g ρ S)) =
      lowJetSq (I := I) (M := M) g 2 S := by
  calc
    lowJetSq (I := I) (M := M) g 2
        (cometricRaiseSlot0Field (I := I) (M := M) g 1
          (domDomCongrSection (I := I) g ρ S)) =
      lowJetSq (I := I) (M := M) g 2
        (domDomCongrSection (I := I) g ρ S) := by
          unfold lowJetSq
          apply Finset.sum_congr rfl
          intro q _
          rw [norm_iCG_cometricRaiseSlot0Field_eq
            (I := I) (M := M) g 1
            (domDomCongrSection (I := I) g ρ S) q]
    _ = lowJetSq (I := I) (M := M) g 2 S :=
      dom_h2 (I := I) (M := M) g ρ S

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 2400000 in
/-- On a sufficiently small spectral `H²` metric ball, the fixed-background
correction to the `PsiB` Lie passenger is `H²`-Lipschitz in the state. -/
theorem psiBg_pair_h2
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ ρ P B : ℝ,
      0 < ρ ∧ 0 ≤ P ∧ 0 ≤ B ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δT δU : ℝ}
        (_hδT_le : δT ≤ δ₀) (_hδT0 : 0 ≤ δT)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δT)
        (_hδU_le : δU ≤ δ₀) (_hδU0 : 0 ≤ δU)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δU),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
      let N := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
      lowJetSq (I := I) (M := M) g 2
          (lieArm1PsiB (I := I) (M := M) g gT gB -
            lieArm1PsiB (I := I) (M := M) g gT g) ≤ P ^ 2 ∧
        lowJetSq (I := I) (M := M) g 2
          ((lieArm1PsiB (I := I) (M := M) g gT gB -
              lieArm1PsiB (I := I) (M := M) g gT g) -
            (lieArm1PsiB (I := I) (M := M) g gU gB -
              lieArm1PsiB (I := I) (M := M) g gU g)) ≤
          (B * N) ^ 2 := by
  obtain ⟨ρs, Cs, hρs, hCs, hsharpPair⟩ :=
    sharp_pair_h2 (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Ks, hKs, hsharpBdd⟩ :=
    sharp_h2_low (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨Kp, hKp, hpb⟩ :=
    pbLow_h2_mul (I := I) (M := M) hDim g gB
  obtain ⟨Ch, hCh, hhs⟩ :=
    hs2_low2 (I := I) (M := M) g 2
  obtain ⟨Ca, hCa, happ⟩ :=
    appRS_h2_h2_h2 (I := I) (M := M) hDim g 1 1 2
  let ρ : ℝ := min ρs 1
  let S0 : ℝ := Ks * (1 + Ch ^ 2)
  let Bs : ℝ := Real.sqrt S0
  let F : SmoothCcTensor g 0 3 :=
    -lc0Kappa (I := I) (M := M) g g gB
  let F0 : ℝ := Real.sqrt (lowJetSq (I := I) (M := M) g 2 F)
  let Pb0 : ℝ := Kp * Ch
  let L0 : ℝ := 2 * (F0 + Pb0)
  let P : ℝ := Ca * L0 * Bs
  let B : ℝ := 2 * (Ca * L0 * Cs + Ca * Kp * Ch * Bs)
  have hρ : 0 < ρ := lt_min hρs (by norm_num)
  have hS0 : 0 ≤ S0 :=
    mul_nonneg hKs (add_nonneg (by norm_num) (sq_nonneg Ch))
  have hBs : 0 ≤ Bs := Real.sqrt_nonneg _
  have hBssq : Bs ^ 2 = S0 := by
    simpa only [Bs] using Real.sq_sqrt hS0
  have hF0 : 0 ≤ F0 := Real.sqrt_nonneg _
  have hF0sq : F0 ^ 2 = lowJetSq (I := I) (M := M) g 2 F := by
    simpa only [F0] using Real.sq_sqrt
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hPb0 : 0 ≤ Pb0 := mul_nonneg hKp hCh
  have hL0 : 0 ≤ L0 :=
    mul_nonneg (by norm_num) (add_nonneg hF0 hPb0)
  have hP : 0 ≤ P := mul_nonneg (mul_nonneg hCa hL0) hBs
  have hB : 0 ≤ B :=
    mul_nonneg (by norm_num)
      (add_nonneg
        (mul_nonneg (mul_nonneg hCa hL0) hCs)
        (mul_nonneg (mul_nonneg (mul_nonneg hCa hKp) hCh) hBs))
  refine ⟨ρ, P, B, hρ, hP, hB, ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU hTHs hUHs
  dsimp only
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  let LT : SmoothCcTensor g 1 2 :=
    psiBgLeft (I := I) (M := M) g gT gB -
      psiBgLeft (I := I) (M := M) g gT g
  let LU : SmoothCcTensor g 1 2 :=
    psiBgLeft (I := I) (M := M) g gU gB -
      psiBgLeft (I := I) (M := M) g gU g
  let ST : SmoothCcTensor g 1 1 := sharpFlatEndoCc (I := I) g gT
  let SU : SmoothCcTensor g 1 1 := sharpFlatEndoCc (I := I) g gU
  let PbT : SmoothCcTensor g 0 3 :=
    lc0PbLow (I := I) (M := M) g T g gB
  have hN : 0 ≤ N := norm_nonneg _
  have hTHss : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρs := hTHs.trans (min_le_left _ _)
  have hUHss : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) U‖ ≤ ρs := hUHs.trans (min_le_left _ _)
  have hTHs1 : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ 1 := hTHs.trans (min_le_right _ _)
  have hUHs1 : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) U‖ ≤ 1 := hUHs.trans (min_le_right _ _)
  have hT2 : lowJetSq (I := I) (M := M) g 2 T ≤ Ch ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 2 T ≤
          (Ch * ‖ccTensorToHs (I := I) (M := M) g 2
            (2 : ℝ) T‖) ^ 2 := by
        simpa only [lowJetSq, Nat.reduceAdd] using hhs T
      _ ≤ (Ch * 1) ^ 2 :=
        pow_le_pow_left₀
          (mul_nonneg hCh (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hTHs1 hCh) 2
      _ = Ch ^ 2 := by rw [mul_one]
  have hU2 : lowJetSq (I := I) (M := M) g 2 U ≤ Ch ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 2 U ≤
          (Ch * ‖ccTensorToHs (I := I) (M := M) g 2
            (2 : ℝ) U‖) ^ 2 := by
        simpa only [lowJetSq, Nat.reduceAdd] using hhs U
      _ ≤ (Ch * 1) ^ 2 :=
        pow_le_pow_left₀
          (mul_nonneg hCh (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hUHs1 hCh) 2
      _ = Ch ^ 2 := by rw [mul_one]
  have hST : lowJetSq (I := I) (M := M) g 2 ST ≤ Bs ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 2 ST ≤
          Ks * (1 + lowJetSq (I := I) (M := M) g 2 T) := by
        simpa only [ST] using
          hsharpBdd gT T hT hTtie hδT_le hδT0 hδT
      _ ≤ S0 := by
        dsimp only [S0]
        exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hT2) hKs
      _ = Bs ^ 2 := hBssq.symm
  have hSU : lowJetSq (I := I) (M := M) g 2 SU ≤ Bs ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 2 SU ≤
          Ks * (1 + lowJetSq (I := I) (M := M) g 2 U) := by
        simpa only [SU] using
          hsharpBdd gU U hU hUtie hδU_le hδU0 hδU
      _ ≤ S0 := by
        dsimp only [S0]
        exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hU2) hKs
      _ = Bs ^ 2 := hBssq.symm
  have hSD : lowJetSq (I := I) (M := M) g 2 (ST - SU) ≤
      (Cs * N) ^ 2 := by
    simpa only [ST, SU, N] using
      hsharpPair gT gU T U hT hU hTtie hUtie
        hδT_le hδT0 hδT hδU_le hδU0 hδU hTHss hUHss
  have hTU2 : lowJetSq (I := I) (M := M) g 2 (T - U) ≤
      (Ch * N) ^ 2 := by
    simpa only [lowJetSq, Nat.reduceAdd, N] using hhs (T - U)
  have hPbT : lowJetSq (I := I) (M := M) g 2 PbT ≤ Pb0 ^ 2 := by
    simpa only [PbT, Pb0] using hpb T Ch hCh hT2
  have hLT : lowJetSq (I := I) (M := M) g 2 LT ≤ L0 ^ 2 := by
    rw [show LT =
        cometricRaiseSlot0Field (I := I) (M := M) g 1
          (domDomCongrSection (I := I) g lieArm1RhoSlot0 (F - PbT)) by
      simpa only [LT, F, PbT] using
        psiBgLeft_corr (I := I) (M := M) g gT gB T hTtie]
    rw [raiseDom_h2 (I := I) (M := M) g lieArm1RhoSlot0 (F - PbT)]
    calc
      lowJetSq (I := I) (M := M) g 2 (F - PbT) =
          lowJetSq (I := I) (M := M) g 2 (F + -PbT) := by
        rw [sub_eq_add_neg]
      _ ≤ 2 * (lowJetSq (I := I) (M := M) g 2 F +
          lowJetSq (I := I) (M := M) g 2 (-PbT)) :=
        jet_add1 (I := I) (M := M) g 2 F (-PbT)
      _ = 2 * (F0 ^ 2 + lowJetSq (I := I) (M := M) g 2 PbT) := by
        rw [jet_neg1 (I := I) (M := M) g 2 PbT, hF0sq]
      _ ≤ 2 * (F0 ^ 2 + Pb0 ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hPbT) (by norm_num)
      _ ≤ L0 ^ 2 := by
        simp only [L0]
        nlinarith [mul_nonneg hF0 hPb0]
  have hPbD : lowJetSq (I := I) (M := M) g 2
      (lc0PbLow (I := I) (M := M) g (T - U) g gB) ≤
      (Kp * (Ch * N)) ^ 2 :=
    hpb (T - U) (Ch * N) (mul_nonneg hCh hN) hTU2
  have hLD : lowJetSq (I := I) (M := M) g 2 (LT - LU) ≤
      (Kp * (Ch * N)) ^ 2 := by
    rw [show LT - LU =
        cometricRaiseSlot0Field (I := I) (M := M) g 1
          (domDomCongrSection (I := I) g lieArm1RhoSlot0
            (-lc0PbLow (I := I) (M := M) g (T - U) g gB)) by
      simpa only [LT, LU] using
        psiBgLeft_pair (I := I) (M := M) g gT gU gB T U hTtie hUtie]
    rw [raiseDom_h2 (I := I) (M := M) g lieArm1RhoSlot0,
      jet_neg1 (I := I) (M := M) g 2]
    exact hPbD
  let V1 : SmoothCcTensor g 1 2 :=
    appCcRS (I := I) (M := M) g 1 1 2 LT (ST - SU)
  let V2 : SmoothCcTensor g 1 2 :=
    appCcRS (I := I) (M := M) g 1 1 2 (LT - LU) SU
  let Z1 : ℝ := Ca * L0 * (Cs * N)
  let Z2 : ℝ := Ca * (Kp * (Ch * N)) * Bs
  have hZ1 : 0 ≤ Z1 :=
    mul_nonneg (mul_nonneg hCa hL0) (mul_nonneg hCs hN)
  have hZ2 : 0 ≤ Z2 :=
    mul_nonneg
      (mul_nonneg hCa (mul_nonneg hKp (mul_nonneg hCh hN))) hBs
  have hPsiT : lowJetSq (I := I) (M := M) g 2
      (lieArm1PsiB (I := I) (M := M) g gT gB -
        lieArm1PsiB (I := I) (M := M) g gT g) ≤ P ^ 2 := by
    change lowJetSq (I := I) (M := M) g 2
      (psiBgCorr (I := I) (M := M) g gT gB) ≤ P ^ 2
    rw [psiBgCorr_eq (I := I) (M := M) g gT gB]
    simpa only [LT, ST, P] using
      happ LT ST L0 Bs hL0 hBs hLT hST
  have hV1 : lowJetSq (I := I) (M := M) g 2 V1 ≤ Z1 ^ 2 := by
    simpa only [V1, Z1] using
      happ LT (ST - SU) L0 (Cs * N) hL0
        (mul_nonneg hCs hN) hLT hSD
  have hV2 : lowJetSq (I := I) (M := M) g 2 V2 ≤ Z2 ^ 2 := by
    simpa only [V2, Z2] using
      happ (LT - LU) SU (Kp * (Ch * N)) Bs
        (mul_nonneg hKp (mul_nonneg hCh hN)) hBs hLD hSU
  refine ⟨hPsiT, ?_⟩
  change lowJetSq (I := I) (M := M) g 2
    (psiBgCorr (I := I) (M := M) g gT gB -
      psiBgCorr (I := I) (M := M) g gU gB) ≤ (B * N) ^ 2
  rw [psiBgCorr_pair (I := I) (M := M) g gT gU gB]
  change lowJetSq (I := I) (M := M) g 2 (V1 + V2) ≤ (B * N) ^ 2
  calc
    lowJetSq (I := I) (M := M) g 2 (V1 + V2) ≤
        2 * (lowJetSq (I := I) (M := M) g 2 V1 +
          lowJetSq (I := I) (M := M) g 2 V2) :=
      jet_add1 (I := I) (M := M) g 2 V1 V2
    _ ≤ 2 * (Z1 ^ 2 + Z2 ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hV1 hV2) (by norm_num)
    _ ≤ (2 * (Z1 + Z2)) ^ 2 := by
      nlinarith [sq_nonneg Z1, sq_nonneg Z2, mul_nonneg hZ1 hZ2]
    _ = (B * N) ^ 2 := by
      simp only [Z1, Z2, B]
      ring

private theorem slotExt_add
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (P Q : SmoothCcTensor g r s) :
    slotExtend (I := I) (M := M) g r s (P + Q) =
      slotExtend (I := I) (M := M) g r s P +
        slotExtend (I := I) (M := M) g r s Q := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rfl

private theorem reidx_add
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (P Q : SmoothCcTensor g r s) (σ : Equiv.Perm (Fin r)) :
    reindexCoeffGen (I := I) (M := M) g r s (P + Q) σ =
      reindexCoeffGen (I := I) (M := M) g r s P σ +
        reindexCoeffGen (I := I) (M := M) g r s Q σ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rfl

private theorem reidx_sub
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (P Q : SmoothCcTensor g r s) (σ : Equiv.Perm (Fin r)) :
    reindexCoeffGen (I := I) (M := M) g r s (P - Q) σ =
      reindexCoeffGen (I := I) (M := M) g r s P σ -
        reindexCoeffGen (I := I) (M := M) g r s Q σ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rfl

private theorem liePiece_add
    (g gm : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3))
    (P Q : SmoothCcTensor g 1 2) :
    lieArm1Piece (I := I) (M := M) g gm σ ρ (P + Q) =
      lieArm1Piece (I := I) (M := M) g gm σ ρ P +
        lieArm1Piece (I := I) (M := M) g gm σ ρ Q := by
  unfold lieArm1Piece
  rw [slotExt_add (I := I) (M := M), slotExt_add (I := I) (M := M),
    appCcRS_add_right, reidx_add (I := I) (M := M)]

private theorem liePiece_sub
    (g gm : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3))
    (P Q : SmoothCcTensor g 1 2) :
    lieArm1Piece (I := I) (M := M) g gm σ ρ (P - Q) =
      lieArm1Piece (I := I) (M := M) g gm σ ρ P -
        lieArm1Piece (I := I) (M := M) g gm σ ρ Q := by
  unfold lieArm1Piece
  rw [slotExtend_sub, slotExtend_sub, appCcRS_sub_right,
    reidx_sub (I := I) (M := M)]

private theorem connBg_self
    (g gm : SmoothRiemannianMetric I M) :
    lieArm1ConnDiffBgCc (I := I) (M := M) g gm g =
      connDiffSection (I := I) gm g := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rfl

private theorem lieBgCorr_eq
    (g gm gB : SmoothRiemannianMetric I M) :
    deTurckLieArm1Coeff (I := I) (M := M) g gm gB -
        deTurckLieArm1Coeff (I := I) (M := M) g gm g =
      lieArm1Piece (I := I) (M := M) g gm lieArm1SigmaC
          lieArm1RhoSlot0 (lieArm1FixCd (I := I) (M := M) g gB) +
        lieArm1Piece (I := I) (M := M) g gm lieArm1SigmaA
          (Equiv.refl (Fin 3)) (psiBgCorr (I := I) (M := M) g gm gB) +
        lieArm1Piece (I := I) (M := M) g gm lieArm1SigmaASwap
          (Equiv.refl (Fin 3)) (psiBgCorr (I := I) (M := M) g gm gB) := by
  rw [deTurckLieArm1Coeff_eq_lieArm1Piece_sum
      (I := I) (M := M) g gm gB,
    deTurckLieArm1Coeff_eq_lieArm1Piece_sum
      (I := I) (M := M) g gm g,
    lieArm1_connDiffBg_decomp (I := I) (M := M) g gm gB,
    connBg_self (I := I) (M := M) g gm,
    liePiece_add (I := I) (M := M)]
  unfold psiBgCorr
  rw [liePiece_sub (I := I) (M := M),
    liePiece_sub (I := I) (M := M)]
  module

private theorem reidx_h2
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (S : SmoothCcTensor g r s) (ρ : Equiv.Perm (Fin r)) :
    lowJetSq (I := I) (M := M) g 2
        (reindexCoeffGen (I := I) (M := M) g r s S ρ) =
      lowJetSq (I := I) (M := M) g 2 S := by
  unfold lowJetSq
  apply Finset.sum_congr rfl
  intro q _
  rw [iteratedCovGrad_reindexCoeffGen (I := I) (M := M),
    norm_reindexCoeffGen_eq (I := I) (M := M)]

private theorem lieTrace_eq1
    (g gm : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) :
    deTurckLieTraceCoeff (I := I) (M := M) g gm σ =
      reindexCoeffGen (I := I) (M := M) g 4 2
        (pureTrace (I := I) (M := M) g gm 2) σ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [deTurckLieTraceCoeff_toSection, reindexCoeffGen_toSection,
    pureTrace_toSection]
  apply ContinuousLinearMap.ext
  intro D
  rw [reindexCoeffFibGen_apply, deTurckLieTraceFib,
    ContinuousLinearMap.comp_apply, domDomCongrFibPerm_apply]

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 2400000 in
private theorem lieBg_pair_h2
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ ρ B : ℝ, 0 < ρ ∧ 0 ≤ B ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δT δU : ℝ}
        (_hδT_le : δT ≤ δ₀) (_hδT0 : 0 ≤ δT)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δT)
        (_hδU_le : δU ≤ δ₀) (_hδU0 : 0 ≤ δU)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δU),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
      let N := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
      lowJetSq (I := I) (M := M) g 2
          ((deTurckLieArm1Coeff (I := I) (M := M) g gT gB -
              deTurckLieArm1Coeff (I := I) (M := M) g gT g) -
            (deTurckLieArm1Coeff (I := I) (M := M) g gU gB -
              deTurckLieArm1Coeff (I := I) (M := M) g gU g)) ≤
        (B * N) ^ 2 := by
  obtain ⟨ρt, Ct, hρt, hCt, htracePair⟩ :=
    LowBaseInternal.trace2_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρb, Tb, hρb, hTb, htraceBdd⟩ :=
    LowBaseInternal.trace2_h2_bdd (I := I) (M := M) hDim g
  obtain ⟨ρp, Pp, Bp, hρp, hPp, hBp, hpsi⟩ :=
    psiBg_pair_h2 (I := I) (M := M) hDim g gB hδ₀0 hδ₀
  obtain ⟨Cp, hCp, hpiece⟩ :=
    liePiece_pair (I := I) (M := M) hDim g
  let F : SmoothCcTensor g 1 2 :=
    lieArm1FixCd (I := I) (M := M) g gB
  let F0 : ℝ := Real.sqrt (lowJetSq (I := I) (M := M) g 2 F)
  let B : ℝ :=
    2 * (Cp * Ct * F0 + 2 * (Cp * (Tb * Bp + Ct * Pp)))
  let ρ : ℝ := min ρt (min ρb ρp)
  have hF0 : 0 ≤ F0 := Real.sqrt_nonneg _
  have hF0sq : F0 ^ 2 = lowJetSq (I := I) (M := M) g 2 F := by
    simpa only [F0] using Real.sq_sqrt
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  have hρ : 0 < ρ := lt_min hρt (lt_min hρb hρp)
  refine ⟨ρ, B, hρ, hB, ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU hTHs hUHs
  dsimp only
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  have hN : 0 ≤ N := norm_nonneg _
  have hTHst : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρt := hTHs.trans (min_le_left _ _)
  have hUHst : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) U‖ ≤ ρt := hUHs.trans (min_le_left _ _)
  have hTHsb : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρb :=
    hTHs.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hUHsb : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) U‖ ≤ ρb :=
    hUHs.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hTHsp : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρp :=
    hTHs.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hUHsp : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) U‖ ≤ ρp :=
    hUHs.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hTrU : ∀ σ : Equiv.Perm (Fin 4),
      lowJetSq (I := I) (M := M) g 2
          (deTurckLieTraceCoeff (I := I) (M := M) g gU σ) ≤
        Tb ^ 2 := by
    intro σ
    rw [lieTrace_eq1 (I := I) (M := M) g gU σ,
      reidx_h2 (I := I) (M := M)]
    exact htraceBdd U gU hUtie hUHsb
  have hTrD : ∀ σ : Equiv.Perm (Fin 4),
      lowJetSq (I := I) (M := M) g 2
          (deTurckLieTraceCoeff (I := I) (M := M) g gT σ -
            deTurckLieTraceCoeff (I := I) (M := M) g gU σ) ≤
        (Ct * N) ^ 2 := by
    intro σ
    have heq :
        deTurckLieTraceCoeff (I := I) (M := M) g gT σ -
            deTurckLieTraceCoeff (I := I) (M := M) g gU σ =
          reindexCoeffGen (I := I) (M := M) g 4 2
            (pureTrace (I := I) (M := M) g gT 2 -
              pureTrace (I := I) (M := M) g gU 2) σ := by
      rw [lieTrace_eq1 (I := I) (M := M) g gT σ,
        lieTrace_eq1 (I := I) (M := M) g gU σ,
        reidx_sub (I := I) (M := M)]
    rw [heq, reidx_h2 (I := I) (M := M)]
    simpa only [N] using
      htracePair T U gT gU hTtie hUtie hTHst hUHst
  have hPsiRaw := hpsi gT gU T U hT hU hTtie hUtie
    hδT_le hδT0 hδT hδU_le hδU0 hδU hTHsp hUHsp
  let PT : SmoothCcTensor g 1 2 :=
    psiBgCorr (I := I) (M := M) g gT gB
  let PU : SmoothCcTensor g 1 2 :=
    psiBgCorr (I := I) (M := M) g gU gB
  have hPT : lowJetSq (I := I) (M := M) g 2 PT ≤ Pp ^ 2 := by
    simpa only [PT, psiBgCorr] using hPsiRaw.1
  have hPD : lowJetSq (I := I) (M := M) g 2 (PT - PU) ≤
      (Bp * N) ^ 2 := by
    simpa only [PT, PU, psiBgCorr, N] using hPsiRaw.2
  have hFF : lowJetSq (I := I) (M := M) g 2 (F - F) ≤
      (0 : ℝ) ^ 2 := by
    rw [sub_self]
    unfold lowJetSq
    have hz (q : ℕ) : iteratedCovGrad (I := I) g 1 2 q
        (0 : SmoothCcTensor g 1 2) = 0 := by
      have h := iteratedCovGrad_smul_real (I := I) (M := M) g 1 2 q
        (0 : ℝ) (0 : SmoothCcTensor g 1 2)
      simpa only [zero_smul] using h
    simp only [hz, norm_zero]
    norm_num
  have hFs : lowJetSq (I := I) (M := M) g 2 F ≤ F0 ^ 2 :=
    hF0sq.symm.le
  let V0 : SmoothCcTensor g 3 2 :=
    lieArm1Piece (I := I) (M := M) g gT lieArm1SigmaC
        lieArm1RhoSlot0 F -
      lieArm1Piece (I := I) (M := M) g gU lieArm1SigmaC
        lieArm1RhoSlot0 F
  let V1 : SmoothCcTensor g 3 2 :=
    lieArm1Piece (I := I) (M := M) g gT lieArm1SigmaA
        (Equiv.refl (Fin 3)) PT -
      lieArm1Piece (I := I) (M := M) g gU lieArm1SigmaA
        (Equiv.refl (Fin 3)) PU
  let V2 : SmoothCcTensor g 3 2 :=
    lieArm1Piece (I := I) (M := M) g gT lieArm1SigmaASwap
        (Equiv.refl (Fin 3)) PT -
      lieArm1Piece (I := I) (M := M) g gU lieArm1SigmaASwap
        (Equiv.refl (Fin 3)) PU
  let Z0 : ℝ := Cp * (Tb * 0 + (Ct * N) * F0)
  let Z1 : ℝ := Cp * (Tb * (Bp * N) + (Ct * N) * Pp)
  have hZ0 : 0 ≤ Z0 := by
    dsimp only [Z0]
    positivity
  have hZ1 : 0 ≤ Z1 := by
    dsimp only [Z1]
    positivity
  have hV0 : lowJetSq (I := I) (M := M) g 2 V0 ≤ Z0 ^ 2 := by
    simpa only [V0, Z0] using
      hpiece gT gU lieArm1SigmaC lieArm1RhoSlot0 F F
        Tb (Ct * N) F0 0 hTb (mul_nonneg hCt hN) hF0
        (by norm_num) (hTrU lieArm1SigmaC) (hTrD lieArm1SigmaC)
        hFs hFF
  have hV1 : lowJetSq (I := I) (M := M) g 2 V1 ≤ Z1 ^ 2 := by
    simpa only [V1, Z1] using
      hpiece gT gU lieArm1SigmaA (Equiv.refl (Fin 3)) PT PU
        Tb (Ct * N) Pp (Bp * N) hTb (mul_nonneg hCt hN) hPp
        (mul_nonneg hBp hN) (hTrU lieArm1SigmaA)
        (hTrD lieArm1SigmaA) hPT hPD
  have hV2 : lowJetSq (I := I) (M := M) g 2 V2 ≤ Z1 ^ 2 := by
    simpa only [V2, Z1] using
      hpiece gT gU lieArm1SigmaASwap (Equiv.refl (Fin 3)) PT PU
        Tb (Ct * N) Pp (Bp * N) hTb (mul_nonneg hCt hN) hPp
        (mul_nonneg hBp hN) (hTrU lieArm1SigmaASwap)
        (hTrD lieArm1SigmaASwap) hPT hPD
  have hcorr :
      (deTurckLieArm1Coeff (I := I) (M := M) g gT gB -
          deTurckLieArm1Coeff (I := I) (M := M) g gT g) -
        (deTurckLieArm1Coeff (I := I) (M := M) g gU gB -
          deTurckLieArm1Coeff (I := I) (M := M) g gU g) =
      V0 + V1 + V2 := by
    rw [lieBgCorr_eq (I := I) (M := M) g gT gB,
      lieBgCorr_eq (I := I) (M := M) g gU gB]
    dsimp only [V0, V1, V2, PT, PU, F]
    module
  rw [hcorr]
  change lowJetSq (I := I) (M := M) g 2 (V0 + V1 + V2) ≤
    (B * N) ^ 2
  calc
    lowJetSq (I := I) (M := M) g 2 (V0 + V1 + V2) ≤
        2 * (lowJetSq (I := I) (M := M) g 2 (V0 + V1) +
          lowJetSq (I := I) (M := M) g 2 V2) :=
      jet_add1 (I := I) (M := M) g 2 (V0 + V1) V2
    _ ≤ 2 * (2 * (lowJetSq (I := I) (M := M) g 2 V0 +
          lowJetSq (I := I) (M := M) g 2 V1) +
        lowJetSq (I := I) (M := M) g 2 V2) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add (jet_add1 (I := I) (M := M) g 2 V0 V1) le_rfl)
        (by norm_num)
    _ ≤ 2 * (2 * (Z0 ^ 2 + Z1 ^ 2) + Z1 ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add
          (mul_le_mul_of_nonneg_left (add_le_add hV0 hV1) (by norm_num))
          hV2) (by norm_num)
    _ ≤ 4 * (Z0 ^ 2 + Z1 ^ 2 + Z1 ^ 2) := by
      nlinarith [sq_nonneg Z1]
    _ ≤ (2 * (Z0 + Z1 + Z1)) ^ 2 := by
      nlinarith [sq_nonneg Z0, sq_nonneg Z1, mul_nonneg hZ0 hZ1]
    _ = (B * N) ^ 2 := by
      simp only [Z0, Z1, B]
      ring

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 2400000 in
/-- On a sufficiently small spectral `H²` metric ball, the complete order-one
DeTurck Lie coefficient is Lipschitz for an arbitrary fixed background, with
the same critical `H³/H²` two-arm modulus as the diagonal-background case. -/
theorem lie1_bg_pair_h2
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M) :
    ∃ ρ B0 B1 : ℝ,
      0 < ρ ∧ 0 ≤ B0 ∧ 0 ≤ B1 ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δ : ℝ} (_hδ_le : δ ≤ (1 : ℝ) / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ (A D3 : ℝ), 0 ≤ A → 0 ≤ D3 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      let D2 :=
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
      lowJetSq (I := I) (M := M) g 2
          (deTurckLieArm1Coeff (I := I) (M := M) g gT gB -
            deTurckLieArm1Coeff (I := I) (M := M) g gU gB) ≤
        (B0 * D3 + B1 * D2 + B1 * A * D2) ^ 2 := by
  obtain ⟨ρs, L0, L1, hρs, hL0, hL1, hsame⟩ :=
    lie1_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρc, C, hρc, hC, hcorr⟩ :=
    lieBg_pair_h2 (I := I) (M := M) hDim g gB
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  let ρ : ℝ := min ρs ρc
  let B0 : ℝ := 2 * L0
  let B1 : ℝ := 2 * (L1 + C)
  have hρ : 0 < ρ := lt_min hρs hρc
  have hB0 : 0 ≤ B0 := mul_nonneg (by norm_num) hL0
  have hB1 : 0 ≤ B1 :=
    mul_nonneg (by norm_num) (add_nonneg hL1 hC)
  refine ⟨ρ, B0, B1, hρ, hB0, hB1, ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δ hδ_le hδ0 hδT hδU hTHs hUHs A D3 hA hD3 hT3 hTU3
  dsimp only
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  let S : ℝ := L0 * D3 + L1 * N + L1 * A * N
  let X : SmoothCcTensor g 3 2 :=
    deTurckLieArm1Coeff (I := I) (M := M) g gT g -
      deTurckLieArm1Coeff (I := I) (M := M) g gU g
  let Y : SmoothCcTensor g 3 2 :=
    (deTurckLieArm1Coeff (I := I) (M := M) g gT gB -
        deTurckLieArm1Coeff (I := I) (M := M) g gT g) -
      (deTurckLieArm1Coeff (I := I) (M := M) g gU gB -
        deTurckLieArm1Coeff (I := I) (M := M) g gU g)
  have hN : 0 ≤ N := norm_nonneg _
  have hS : 0 ≤ S := by
    dsimp only [S]
    positivity
  have hTHss : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρs := hTHs.trans (min_le_left _ _)
  have hUHss : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) U‖ ≤ ρs := hUHs.trans (min_le_left _ _)
  have hTHsc : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρc := hTHs.trans (min_le_right _ _)
  have hUHsc : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) U‖ ≤ ρc := hUHs.trans (min_le_right _ _)
  have hX : lowJetSq (I := I) (M := M) g 2 X ≤ S ^ 2 := by
    simpa only [X, S, N] using
      hsame gT gU T U hT hU hTtie hUtie hδ_le hδ0 hδT hδU
        hTHss hUHss A D3 hA hD3 hT3 hTU3
  have hY : lowJetSq (I := I) (M := M) g 2 Y ≤ (C * N) ^ 2 := by
    simpa only [Y, N] using
      hcorr gT gU T U hT hU hTtie hUtie
        hδ_le hδ0 hδT hδ_le hδ0 hδU hTHsc hUHsc
  have hsplit :
      deTurckLieArm1Coeff (I := I) (M := M) g gT gB -
          deTurckLieArm1Coeff (I := I) (M := M) g gU gB =
        X + Y := by
    dsimp only [X, Y]
    module
  have hlin : 2 * (S + C * N) ≤
      B0 * D3 + B1 * N + B1 * A * N := by
    dsimp only [S, B0, B1]
    nlinarith [mul_nonneg hC hN,
      mul_nonneg hC (mul_nonneg hA hN)]
  rw [hsplit]
  calc
    lowJetSq (I := I) (M := M) g 2 (X + Y) ≤
        2 * (lowJetSq (I := I) (M := M) g 2 X +
          lowJetSq (I := I) (M := M) g 2 Y) :=
      jet_add1 (I := I) (M := M) g 2 X Y
    _ ≤ 2 * (S ^ 2 + (C * N) ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hX hY) (by norm_num)
    _ ≤ (2 * (S + C * N)) ^ 2 := by
      nlinarith [sq_nonneg S, sq_nonneg (C * N),
        mul_nonneg hS (mul_nonneg hC hN)]
    _ ≤ (B0 * D3 + B1 * N + B1 * A * N) ^ 2 :=
      pow_le_pow_left₀
        (mul_nonneg (by norm_num) (add_nonneg hS (mul_nonneg hC hN)))
        hlin 2

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
