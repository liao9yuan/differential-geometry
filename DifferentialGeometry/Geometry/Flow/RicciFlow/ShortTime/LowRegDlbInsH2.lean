import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.LowRegTraceH3Pair
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegBgC0Zero

/-!
# Cancellation-preserving `H²` pair bound for `DLb + Insert`

The two arbitrary-background corrections must be added before estimation.  In
that sum, their moving-connection contributions combine into the derivative of
one moving-trace difference.  The trace is controlled in `H³`, so the final
coefficient is controlled in `H²` without requesting fourth metric jets.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open LieCorr0Core

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-! ### The exact cancellation package -/

private noncomputable def endoPairH2
    (g : SmoothRiemannianMetric I M)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    SmoothCcTensor g 2 2 :=
  let X := slotInsertEndoCc (I := I) (M := M) g 1 Λ
  X + reindexCoeffGen (I := I) (M := M) g 2 2
    (rsDomDomCongrSection (I := I) (M := M) g 2 2
      (Equiv.swap (0 : Fin 2) 1) X)
    (Equiv.swap (0 : Fin 2) 1)

private theorem endoPairH2_jet
    (g : SmoothRiemannianMetric I M)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    lowJetSq (I := I) (M := M) g 2
        (endoPairH2 (I := I) (M := M) g Λ) ≤
      4 * (Module.finrank ℝ E : ℝ) *
        lowJetSq (I := I) (M := M) g 2
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ) := by
  let X : SmoothCcTensor g 2 2 :=
    slotInsertEndoCc (I := I) (M := M) g 1 Λ
  let Y : SmoothCcTensor g 2 2 :=
    reindexCoeffGen (I := I) (M := M) g 2 2
      (rsDomDomCongrSection (I := I) (M := M) g 2 2
        (Equiv.swap (0 : Fin 2) 1) X)
      (Equiv.swap (0 : Fin 2) 1)
  have hY : lowJetSq (I := I) (M := M) g 2 Y =
      lowJetSq (I := I) (M := M) g 2 X := by
    dsimp only [Y]
    rw [reindexJet, rspermH2]
  have hX : lowJetSq (I := I) (M := M) g 2 X ≤
      (Module.finrank ℝ E : ℝ) *
        lowJetSq (I := I) (M := M) g 2
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ) := by
    simpa only [X, pow_one] using
      LowRegBgC0Core.endoIns_jet (I := I) (M := M) g 1 2 Λ
  change lowJetSq (I := I) (M := M) g 2 (X + Y) ≤ _
  calc
    lowJetSq (I := I) (M := M) g 2 (X + Y) ≤
        2 * (lowJetSq (I := I) (M := M) g 2 X +
          lowJetSq (I := I) (M := M) g 2 Y) :=
      jetAdd (I := I) (M := M) g 2 X Y
    _ = 4 * lowJetSq (I := I) (M := M) g 2 X := by
      rw [hY]
      ring
    _ ≤ 4 * ((Module.finrank ℝ E : ℝ) *
        lowJetSq (I := I) (M := M) g 2
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ)) :=
      mul_le_mul_of_nonneg_left hX (by norm_num)
    _ = 4 * (Module.finrank ℝ E : ℝ) *
        lowJetSq (I := I) (M := M) g 2
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ) := by ring

private theorem endoPairH2_sub
    (g : SmoothRiemannianMetric I M)
    (Λ Γ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    endoPairH2 (I := I) (M := M) g (Λ - Γ) =
      endoPairH2 (I := I) (M := M) g Λ -
        endoPairH2 (I := I) (M := M) g Γ := by
  unfold endoPairH2
  dsimp only
  rw [slotInsertEndoCc_sub, rspermSub, reindexSub]
  module

private noncomputable def insEndoH2
    (g gm g_bg : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) :=
  (deTurckLieWEndoSection (I := I) (M := M) gm g_bg -
      deTurckLieWEndoSection (I := I) (M := M) gm g) +
    endoDiffSection (I := I) (M := M) g gm g_bg

private lemma insEndoH2_apply
    (g gm g_bg : SmoothRiemannianMetric I M) (x : M) :
    insEndoH2 (I := I) (M := M) g gm g_bg x =
      (deTurckLieWEndo (I := I) gm g_bg x -
        deTurckLieWEndo (I := I) gm g x) +
      (lieCorr0NEndo (I := I) g gm g_bg x -
        lieCorr0NEndo (I := I) g gm g x) := by
  rw [insEndoH2]
  change (_ - _) + endoDiffSection (I := I) (M := M) g gm g_bg x = _
  have hdiff : endoDiffSection (I := I) (M := M) g gm g_bg x =
      lieCorr0NEndo (I := I) g gm g_bg x -
        lieCorr0NEndo (I := I) g gm g x := by
    simpa only [endoDiffSection, connDiffDVFSection,
      ContMDiffSection.coe_sub, Pi.sub_apply] using
      (nEndo_diff (I := I) (M := M) g gm g_bg x).symm
  rw [hdiff]
  simp only [deTurckLieWEndoSection_apply]

private theorem dlbIns_eq_pair_h2
    (g gm g_bg : SmoothRiemannianMetric I M) :
    (deTurckLieDLbCoeffField (I := I) (M := M) g gm g_bg -
        deTurckLieDLbCoeffField (I := I) (M := M) g gm g) +
      (lc0Insert (I := I) (M := M) g gm g_bg -
        lc0Insert (I := I) (M := M) g gm g) =
      endoPairH2 (I := I) (M := M) g
        (insEndoH2 (I := I) (M := M) g gm g_bg) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  let Λ := insEndoH2 (I := I) (M := M) g gm g_bg
  let X := slotInsertEndoCc (I := I) (M := M) g 1 Λ
  let Y := reindexCoeffGen (I := I) (M := M) g 2 2
    (rsDomDomCongrSection (I := I) (M := M) g 2 2
      (Equiv.swap (0 : Fin 2) 1) X)
    (Equiv.swap (0 : Fin 2) 1)
  have hsum :
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (X + Y).toSection x) D =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        X.toSection x) D +
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        Y.toSection x) D := rfl
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        ((deTurckLieDLbCoeffField (I := I) (M := M) g gm g_bg -
            deTurckLieDLbCoeffField (I := I) (M := M) g gm g) +
          (lc0Insert (I := I) (M := M) g gm g_bg -
            lc0Insert (I := I) (M := M) g gm g)).toSection x) D) m =
    Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (X + Y).toSection x) D) m
  rw [hsum, Tensor0SSpace.toModel_add,
    ContinuousMultilinearMap.add_apply]
  rw [show
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        ((deTurckLieDLbCoeffField (I := I) (M := M) g gm g_bg -
            deTurckLieDLbCoeffField (I := I) (M := M) g gm g) +
          (lc0Insert (I := I) (M := M) g gm g_bg -
            lc0Insert (I := I) (M := M) g gm g)).toSection x) D =
        (deTurckLieDLbFib (I := I) gm g_bg x D -
          deTurckLieDLbFib (I := I) gm g x D) +
        (lieCorr0InsertFib (I := I) g gm g_bg x D -
          lieCorr0InsertFib (I := I) g gm g x D) from rfl]
  rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply,
    Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply,
    Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]
  rw [deTurckLieDLbFib_toModel (I := I) gm g_bg x D m,
    deTurckLieDLbFib_toModel (I := I) gm g x D m,
    lieCorr0InsertFib_toModel (I := I) g gm g_bg x D m,
    lieCorr0InsertFib_toModel (I := I) g gm g x D m]
  have hX :
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        X.toSection x) D =
      slotInsertEndoFib (I := I) (M := M) 2 0 x (Λ x) D := rfl
  rw [hX, slotInsertEndoFib_apply_eval]
  have hY :
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        Y.toSection x) D =
      reindexCoeffFibGen (I := I) 2 2 (Equiv.swap (0 : Fin 2) 1) x
        (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (rsDomDomCongrSection (I := I) (M := M) g 2 2
            (Equiv.swap (0 : Fin 2) 1) X).toSection x) D := rfl
  rw [hY, reindexCoeffFibGen_apply]
  rw [show
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (rsDomDomCongrSection (I := I) (M := M) g 2 2
          (Equiv.swap (0 : Fin 2) 1) X).toSection x) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        rsDomDomCongr (I := I) (M := M) (Equiv.swap (0 : Fin 2) 1)
          (X.toSection x)) from by
        rw [rsDomDomCongrSection_toSection]]
  rw [toModel_rsDomDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply]
  have hX' :
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        X.toSection x)
        (Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr
            (Equiv.swap (0 : Fin 2) 1) (Tensor0SSpace.toModel D))) =
      slotInsertEndoFib (I := I) (M := M) 2 0 x (Λ x)
        (Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr
            (Equiv.swap (0 : Fin 2) 1) (Tensor0SSpace.toModel D))) := rfl
  rw [hX', slotInsertEndoFib_apply_eval,
    Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  have harg :
      (fun k => Function.update
        (fun i => m ((Equiv.swap (0 : Fin 2) 1) i)) 0
        (Λ x ((fun i => m ((Equiv.swap (0 : Fin 2) 1) i)) 0))
        ((Equiv.swap (0 : Fin 2) 1) k)) =
      Function.update m 1 (Λ x (m 1)) := by
    funext k
    have hswap0 : (Equiv.swap (0 : Fin 2) 1) 0 = 1 :=
      Equiv.swap_apply_left 0 1
    have hswap1 : (Equiv.swap (0 : Fin 2) 1) 1 = 0 :=
      Equiv.swap_apply_right 0 1
    simp only [Function.update_apply]
    rw [hswap0, Equiv.swap_apply_self]
    have hcond : ((Equiv.swap (0 : Fin 2) 1) k = 0) = (k = 1) := by
      apply propext
      constructor
      · intro h
        have h2 := congrArg (Equiv.swap (0 : Fin 2) 1) h
        rwa [Equiv.swap_apply_self, hswap0] at h2
      · intro h
        rw [h, hswap1]
    simp only [hcond]
  rw [harg]
  have hΛ := insEndoH2_apply (I := I) (M := M) g gm g_bg x
  dsimp only [Λ] at hΛ ⊢
  rw [hΛ]
  simp only [ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply,
    ContinuousMultilinearMap.map_update_add,
    ContinuousMultilinearMap.map_update_sub]
  simp only [sub_eq_add_neg, neg_add_rev]
  ac_rfl

private theorem raise_sub0_h2
    (g : SmoothRiemannianMetric I M)
    (W W' : SmoothCcTensor g 0 2) :
    cometricRaiseSlot0Field (I := I) (M := M) g 0 (W - W') =
      cometricRaiseSlot0Field (I := I) (M := M) g 0 W -
        cometricRaiseSlot0Field (I := I) (M := M) g 0 W' := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  simp only [SmoothCcTensor.toSection_sub,
    cometricRaiseSlot0Field_toSection]
  rfl

private theorem raise_add0_h2
    (g : SmoothRiemannianMetric I M)
    (W W' : SmoothCcTensor g 0 2) :
    cometricRaiseSlot0Field (I := I) (M := M) g 0 (W + W') =
      cometricRaiseSlot0Field (I := I) (M := M) g 0 W +
        cometricRaiseSlot0Field (I := I) (M := M) g 0 W' := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  simp only [SmoothCcTensor.toSection_add,
    cometricRaiseSlot0Field_toSection]
  rfl

private theorem insEndoH2_one
    (g gm g_bg : SmoothRiemannianMetric I M) :
    slotInsertEndoCc (I := I) (M := M) g 0
        (insEndoH2 (I := I) (M := M) g gm g_bg) =
      cometricRaiseSlot0Field (I := I) (M := M) g 0
        (wAlphaA (I := I) (M := M) g gm g_bg -
          wAlphaA (I := I) (M := M) g gm g) := by
  rw [insEndoH2, slotInsertEndoCc_add, slotInsertEndoCc_sub]
  change (deTurckLieWEndoInsert (I := I) (M := M) g gm g_bg -
      deTurckLieWEndoInsert (I := I) (M := M) g gm g) +
    slotInsertEndoCc (I := I) (M := M) g 0
      (endoDiffSection (I := I) (M := M) g gm g_bg) = _
  rw [endoDiffSection, slotInsertEndoCc_sub,
    deTurckLieWEndoInsert_eq_cometricRaise_wAlpha,
    deTurckLieWEndoInsert_eq_cometricRaise_wAlpha,
    connDiffDVFInsert_eq_cometricRaise,
    connDiffDVFInsert_eq_cometricRaise]
  rw [wAlpha, wAlpha, raise_add0_h2, raise_add0_h2, raise_sub0_h2]
  module

private theorem omega_bg_sub_h2
    (g g_bg gT gU : SmoothRiemannianMetric I M) :
    (wOmega (I := I) (M := M) g gT g_bg -
        wOmega (I := I) (M := M) g gT g) -
      (wOmega (I := I) (M := M) g gU g_bg -
        wOmega (I := I) (M := M) g gU g) =
      appCcRS (I := I) (M := M) g 0 3 1
        (lc0TraceRF (I := I) (M := M) g gT 1 (Equiv.refl _) -
          lc0TraceRF (I := I) (M := M) g gU 1 (Equiv.refl _))
        (connDiffLoweredCc (I := I) g g -
          connDiffLoweredCc (I := I) g g_bg) := by
  rw [wOmega_sub_refold (I := I) (M := M) g gT g_bg g,
    wOmega_sub_refold (I := I) (M := M) g gU g_bg g,
    appCcRS_sub_left]

set_option linter.unusedVariables false in
private theorem omega_pair_h3
    (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δT δU : ℝ}
        (hδT_le : δT ≤ (1 / 3 : ℝ)) (hδT0 : 0 ≤ δT)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δT)
        (hδU_le : δU ≤ (1 / 3 : ℝ)) (hδU0 : 0 ≤ δU)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δU)
        (R A D2 D3 : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        lowJetSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      lowJetSq (I := I) (M := M) g 3
          ((wOmega (I := I) (M := M) g gT g_bg -
              wOmega (I := I) (M := M) g gT g) -
            (wOmega (I := I) (M := M) g gU g_bg -
              wOmega (I := I) (M := M) g gU g)) ≤
        (B R * (D3 + D2 + A * D2)) ^ 2 := by
  obtain ⟨Bt, hBt, htrace⟩ :=
    LowBaseInternal.trace1_pair_h3 (I := I) (M := M) hDim g
      (by norm_num : 0 ≤ (1 / 3 : ℝ)) (by norm_num : (1 / 3 : ℝ) < 1)
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h3_tame (I := I) (M := M) hDim g 0 3 1
  let P : SmoothCcTensor g 0 3 :=
    connDiffLoweredCc (I := I) g g -
      connDiffLoweredCc (I := I) g g_bg
  let JP2 : ℝ := lowJetSq (I := I) (M := M) g 2 P
  let JP3 : ℝ := lowJetSq (I := I) (M := M) g 3 P
  let Z : ℝ := Ca * (JP2 + JP3)
  let C : ℝ := Real.sqrt Z
  let B : ℝ → ℝ := fun R => C * Bt R
  have hJP2 : 0 ≤ JP2 := jetNn (I := I) (M := M) (m := 2) g P
  have hJP3 : 0 ≤ JP3 := jetNn (I := I) (M := M) (m := 3) g P
  have hZ : 0 ≤ Z := mul_nonneg hCa (add_nonneg hJP2 hJP3)
  have hCsq : C ^ 2 = Z := by
    simpa only [C] using Real.sq_sqrt hZ
  refine ⟨B, ?_, ?_⟩
  · intro R hR
    exact mul_nonneg (Real.sqrt_nonneg _) (hBt R hR)
  · intro gT gU T U hT hU hTtie hUtie
      δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
      R A D2 D3 hR hA hD2 hD3 hT2 hU2 hT3 hU3 hTU2 hTU3
    let Q : ℝ := D3 + D2 + A * D2
    let Φ : SmoothCcTensor g 3 1 :=
      lc0TraceRF (I := I) (M := M) g gT 1 (Equiv.refl _) -
        lc0TraceRF (I := I) (M := M) g gU 1 (Equiv.refl _)
    have hΦ3 : lowJetSq (I := I) (M := M) g 3 Φ ≤
        (Bt R * Q) ^ 2 := by
      dsimp only [Φ, Q]
      rw [trSub, reindexJet]
      exact htrace gT gU T U hT hU hTtie hUtie
        hδT_le hδT0 hδT hδU_le hδU0 hδU
        R A D2 D3 hR hA hD2 hD3 hT2 hU2 hT3 hU3 hTU2 hTU3
    have hΦ2 : lowJetSq (I := I) (M := M) g 2 Φ ≤
        (Bt R * Q) ^ 2 :=
      (jetMono (I := I) (M := M) g (by omega : 2 ≤ 3) Φ).trans hΦ3
    rw [omega_bg_sub_h2 (I := I) (M := M) g g_bg gT gU]
    change lowJetSq (I := I) (M := M) g 3
        (appCcRS (I := I) (M := M) g 0 3 1 Φ P) ≤
      (B R * Q) ^ 2
    calc
      lowJetSq (I := I) (M := M) g 3
          (appCcRS (I := I) (M := M) g 0 3 1 Φ P) ≤
        Ca * (lowJetSq (I := I) (M := M) g 3 Φ * JP2 +
          lowJetSq (I := I) (M := M) g 2 Φ * JP3) := by
            simpa only [JP2, JP3] using happ Φ P
      _ ≤ Ca * ((Bt R * Q) ^ 2 * JP2 + (Bt R * Q) ^ 2 * JP3) := by
        apply mul_le_mul_of_nonneg_left _ hCa
        exact add_le_add
          (mul_le_mul_of_nonneg_right hΦ3 hJP2)
          (mul_le_mul_of_nonneg_right hΦ2 hJP3)
      _ = Z * (Bt R * Q) ^ 2 := by
        dsimp only [Z]
        ring
      _ = (B R * Q) ^ 2 := by
        dsimp only [B]
        calc
          Z * (Bt R * Q) ^ 2 = C ^ 2 * (Bt R * Q) ^ 2 := by rw [hCsq]
          _ = (C * Bt R * Q) ^ 2 := by ring
      _ = (B R * (D3 + D2 + A * D2)) ^ 2 := by
        simp only [Q]

private theorem alpha_bg_eq_h2
    (g g_bg gm : SmoothRiemannianMetric I M) :
    wAlphaA (I := I) (M := M) g gm g_bg -
        wAlphaA (I := I) (M := M) g gm g =
      domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
        (covGrad (I := I) (M := M) g 0 1
          (wOmega (I := I) (M := M) g gm g_bg -
            wOmega (I := I) (M := M) g gm g)) := by
  unfold wAlphaA
  rw [← domSub, ← covGrad_sub]

private theorem alpha_bg_sub_h2
    (g g_bg gT gU : SmoothRiemannianMetric I M) :
    (wAlphaA (I := I) (M := M) g gT g_bg -
        wAlphaA (I := I) (M := M) g gT g) -
      (wAlphaA (I := I) (M := M) g gU g_bg -
        wAlphaA (I := I) (M := M) g gU g) =
      domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
        (covGrad (I := I) (M := M) g 0 1
          ((wOmega (I := I) (M := M) g gT g_bg -
              wOmega (I := I) (M := M) g gT g) -
            (wOmega (I := I) (M := M) g gU g_bg -
              wOmega (I := I) (M := M) g gU g))) := by
  rw [alpha_bg_eq_h2 (I := I) (M := M) g g_bg gT,
    alpha_bg_eq_h2 (I := I) (M := M) g g_bg gU,
    ← domSub, ← covGrad_sub]

private theorem grad_h2_local
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (S : SmoothCcTensor g r s) :
    lowJetSq (I := I) (M := M) g 2
        (covGrad (I := I) (M := M) g r s S) ≤
      lowJetSq (I := I) (M := M) g 3 S := by
  have grad_sq_local : ∀ i : ℕ,
      ‖iteratedCovGrad (I := I) g r (s + 1) i
          (covGrad (I := I) (M := M) g r s S)‖ ^ 2 =
        ‖iteratedCovGrad (I := I) g r s (i + 1) S‖ ^ 2 := by
    intro i
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
      SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
    refine MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun x => ?_)
    exact rfns_iteratedCovGrad_covGrad_comm_rs
      (I := I) (M := M) g r s i S x
  have h0 := grad_sq_local 0
  have h1 := grad_sq_local 1
  have h2 := grad_sq_local 2
  unfold lowJetSq
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.reduceAdd] at h0 h1 h2 ⊢
  rw [h0, h1, h2]
  nlinarith [sq_nonneg ‖S‖]

set_option linter.unusedVariables false in
private theorem alpha_pair_h2
    (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δT δU : ℝ}
        (hδT_le : δT ≤ (1 / 3 : ℝ)) (hδT0 : 0 ≤ δT)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δT)
        (hδU_le : δU ≤ (1 / 3 : ℝ)) (hδU0 : 0 ≤ δU)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δU)
        (R A D2 D3 : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        lowJetSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      lowJetSq (I := I) (M := M) g 2
          ((wAlphaA (I := I) (M := M) g gT g_bg -
              wAlphaA (I := I) (M := M) g gT g) -
            (wAlphaA (I := I) (M := M) g gU g_bg -
              wAlphaA (I := I) (M := M) g gU g)) ≤
        (B R * (D3 + D2 + A * D2)) ^ 2 := by
  obtain ⟨B, hB, hω⟩ := omega_pair_h3 (I := I) (M := M) hDim g g_bg
  refine ⟨B, hB, ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
    R A D2 D3 hR hA hD2 hD3 hT2 hU2 hT3 hU3 hTU2 hTU3
  rw [alpha_bg_sub_h2 (I := I) (M := M) g g_bg gT gU, domH2]
  exact (grad_h2_local (I := I) (M := M) g
    ((wOmega (I := I) (M := M) g gT g_bg -
        wOmega (I := I) (M := M) g gT g) -
      (wOmega (I := I) (M := M) g gU g_bg -
        wOmega (I := I) (M := M) g gU g))).trans
    (hω gT gU T U hT hU hTtie hUtie
      hδT_le hδT0 hδT hδU_le hδU0 hδU
      R A D2 D3 hR hA hD2 hD3 hT2 hU2 hT3 hU3 hTU2 hTU3)

private theorem raise_h2
    (g : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    lowJetSq (I := I) (M := M) g 2
        (cometricRaiseSlot0Field (I := I) (M := M) g 0 W) =
      lowJetSq (I := I) (M := M) g 2 W := by
  unfold lowJetSq
  apply Finset.sum_congr rfl
  intro q _
  rw [norm_iCG_cometricRaiseSlot0Field_eq]

set_option linter.unusedVariables false in
/-- The arbitrary-background `DLb` correction and endomorphism insertion,
combined before estimation, form an `H²`-Lipschitz pair on the fixed fibre-small
metric ball.  Both endpoints carry an `H³` cap, and the bound uses only the
adjacent-scale currency `D3 + D2 + A * D2`. -/
theorem dlbIns_pair_h2
    (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δT δU : ℝ}
        (hδT_le : δT ≤ (1 / 3 : ℝ)) (hδT0 : 0 ≤ δT)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δT)
        (hδU_le : δU ≤ (1 / 3 : ℝ)) (hδU0 : 0 ≤ δU)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δU)
        (R A D2 D3 : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        lowJetSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      lowJetSq (I := I) (M := M) g 2
          (((deTurckLieDLbCoeffField (I := I) (M := M) g gT g_bg -
                deTurckLieDLbCoeffField (I := I) (M := M) g gT g) +
              (lc0Insert (I := I) (M := M) g gT g_bg -
                lc0Insert (I := I) (M := M) g gT g)) -
            ((deTurckLieDLbCoeffField (I := I) (M := M) g gU g_bg -
                deTurckLieDLbCoeffField (I := I) (M := M) g gU g) +
              (lc0Insert (I := I) (M := M) g gU g_bg -
                lc0Insert (I := I) (M := M) g gU g))) ≤
        (B R * (D3 + D2 + A * D2)) ^ 2 := by
  obtain ⟨Ba, hBa, hα⟩ := alpha_pair_h2 (I := I) (M := M) hDim g g_bg
  let fr : ℝ := Module.finrank ℝ E
  let Z : ℝ := 4 * fr
  let C : ℝ := Real.sqrt Z
  let B : ℝ → ℝ := fun R => C * Ba R
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hZ : 0 ≤ Z := mul_nonneg (by norm_num) hfr
  have hCsq : C ^ 2 = Z := by
    simpa only [C] using Real.sq_sqrt hZ
  refine ⟨B, ?_, ?_⟩
  · intro R hR
    exact mul_nonneg (Real.sqrt_nonneg _) (hBa R hR)
  · intro gT gU T U hT hU hTtie hUtie
      δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
      R A D2 D3 hR hA hD2 hD3 hT2 hU2 hT3 hU3 hTU2 hTU3
    let Q : ℝ := D3 + D2 + A * D2
    let ΛT := insEndoH2 (I := I) (M := M) g gT g_bg
    let ΛU := insEndoH2 (I := I) (M := M) g gU g_bg
    let AT : SmoothCcTensor g 0 2 :=
      wAlphaA (I := I) (M := M) g gT g_bg -
        wAlphaA (I := I) (M := M) g gT g
    let AU : SmoothCcTensor g 0 2 :=
      wAlphaA (I := I) (M := M) g gU g_bg -
        wAlphaA (I := I) (M := M) g gU g
    let FT : SmoothCcTensor g 2 2 :=
      (deTurckLieDLbCoeffField (I := I) (M := M) g gT g_bg -
          deTurckLieDLbCoeffField (I := I) (M := M) g gT g) +
        (lc0Insert (I := I) (M := M) g gT g_bg -
          lc0Insert (I := I) (M := M) g gT g)
    let FU : SmoothCcTensor g 2 2 :=
      (deTurckLieDLbCoeffField (I := I) (M := M) g gU g_bg -
          deTurckLieDLbCoeffField (I := I) (M := M) g gU g) +
        (lc0Insert (I := I) (M := M) g gU g_bg -
          lc0Insert (I := I) (M := M) g gU g)
    have hFT : FT = endoPairH2 (I := I) (M := M) g ΛT := by
      simpa only [FT, ΛT] using
        dlbIns_eq_pair_h2 (I := I) (M := M) g gT g_bg
    have hFU : FU = endoPairH2 (I := I) (M := M) g ΛU := by
      simpa only [FU, ΛU] using
        dlbIns_eq_pair_h2 (I := I) (M := M) g gU g_bg
    have hFsub : FT - FU =
        endoPairH2 (I := I) (M := M) g (ΛT - ΛU) := by
      rw [hFT, hFU, endoPairH2_sub]
    have hslot :
        slotInsertEndoCc (I := I) (M := M) g 0 (ΛT - ΛU) =
          cometricRaiseSlot0Field (I := I) (M := M) g 0 (AT - AU) := by
      dsimp only [ΛT, ΛU, AT, AU]
      rw [slotInsertEndoCc_sub,
        insEndoH2_one (I := I) (M := M) g gT g_bg,
        insEndoH2_one (I := I) (M := M) g gU g_bg,
        ← raise_sub0_h2]
    have hslotJet : lowJetSq (I := I) (M := M) g 2
        (slotInsertEndoCc (I := I) (M := M) g 0 (ΛT - ΛU)) =
          lowJetSq (I := I) (M := M) g 2 (AT - AU) := by
      rw [hslot, raise_h2]
    have hA : lowJetSq (I := I) (M := M) g 2 (AT - AU) ≤
        (Ba R * Q) ^ 2 := by
      simpa only [AT, AU, Q] using
        hα gT gU T U hT hU hTtie hUtie
          hδT_le hδT0 hδT hδU_le hδU0 hδU
          R A D2 D3 hR hA hD2 hD3 hT2 hU2 hT3 hU3 hTU2 hTU3
    change lowJetSq (I := I) (M := M) g 2 (FT - FU) ≤
      (B R * Q) ^ 2
    rw [hFsub]
    calc
      lowJetSq (I := I) (M := M) g 2
          (endoPairH2 (I := I) (M := M) g (ΛT - ΛU)) ≤
        4 * fr * lowJetSq (I := I) (M := M) g 2
          (slotInsertEndoCc (I := I) (M := M) g 0 (ΛT - ΛU)) := by
            simpa only [fr] using
              endoPairH2_jet (I := I) (M := M) g (ΛT - ΛU)
      _ = 4 * fr * lowJetSq (I := I) (M := M) g 2 (AT - AU) := by
        rw [hslotJet]
      _ ≤ 4 * fr * (Ba R * Q) ^ 2 :=
        mul_le_mul_of_nonneg_left hA (mul_nonneg (by norm_num) hfr)
      _ = (B R * Q) ^ 2 := by
        dsimp only [B, Z] at hCsq ⊢
        calc
          4 * fr * (Ba R * Q) ^ 2 = C ^ 2 * (Ba R * Q) ^ 2 := by
            rw [hCsq]
          _ = (C * Ba R * Q) ^ 2 := by ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
