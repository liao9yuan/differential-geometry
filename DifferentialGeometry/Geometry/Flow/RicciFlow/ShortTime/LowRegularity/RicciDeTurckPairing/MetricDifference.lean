import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.C1Lipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.H3CoefficientPairing
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.JetApplication

noncomputable section

open Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Spectral (appCcRS appCcRS_sub_left appCcRS_sub_right covGrad_sub
  fullRaisedEndoField fullRaisedEndoField_apply gInvDiffSlotCoeff permCoeff
  symmS_eq_self_of_ccTensorBilin_symm)
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private theorem app_left_h3
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (p r c : ℕ)
    (Φ : SmoothCcTensor g r c) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ W : SmoothCcTensor g p r,
        lowJetSq (I := I) (M := M) g 3
            (appCcRS (I := I) (M := M) g p r c Φ W) ≤
          C * lowJetSq (I := I) (M := M) g 3 W := by
  obtain ⟨C₀, hC₀, happ⟩ :=
    app_h3_tame (I := I) (M := M) hDim g p r c
  let C : ℝ := C₀ *
    (lowJetSq (I := I) (M := M) g 3 Φ +
      lowJetSq (I := I) (M := M) g 2 Φ)
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg hC₀
      (add_nonneg
        (jetNn (I := I) (M := M) (m := 3) g Φ)
        (jetNn (I := I) (M := M) (m := 2) g Φ))
  refine ⟨C, hC, ?_⟩
  intro W
  have hW23 :
      lowJetSq (I := I) (M := M) g 2 W ≤
        lowJetSq (I := I) (M := M) g 3 W :=
    jetMono (I := I) (M := M) g (by omega : 2 ≤ 3) W
  calc
    lowJetSq (I := I) (M := M) g 3
        (appCcRS (I := I) (M := M) g p r c Φ W) ≤
      C₀ * (lowJetSq (I := I) (M := M) g 3 Φ *
          lowJetSq (I := I) (M := M) g 2 W +
        lowJetSq (I := I) (M := M) g 2 Φ *
          lowJetSq (I := I) (M := M) g 3 W) :=
      happ Φ W
    _ ≤ C₀ * (lowJetSq (I := I) (M := M) g 3 Φ *
          lowJetSq (I := I) (M := M) g 3 W +
        lowJetSq (I := I) (M := M) g 2 Φ *
          lowJetSq (I := I) (M := M) g 3 W) := by
      apply mul_le_mul_of_nonneg_left _ hC₀
      exact add_le_add
        (mul_le_mul_of_nonneg_left hW23
          (jetNn (I := I) (M := M) (m := 3) g Φ))
        le_rfl
    _ = C * lowJetSq (I := I) (M := M) g 3 W := by
      simp only [C]
      ring

private theorem app_right_h3
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (p r c : ℕ)
    (W : SmoothCcTensor g p r) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ Φ : SmoothCcTensor g r c,
        lowJetSq (I := I) (M := M) g 3
            (appCcRS (I := I) (M := M) g p r c Φ W) ≤
          C * lowJetSq (I := I) (M := M) g 3 Φ := by
  obtain ⟨C₀, hC₀, happ⟩ :=
    app_h3_tame (I := I) (M := M) hDim g p r c
  let C : ℝ := C₀ *
    (lowJetSq (I := I) (M := M) g 2 W +
      lowJetSq (I := I) (M := M) g 3 W)
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg hC₀
      (add_nonneg
        (jetNn (I := I) (M := M) (m := 2) g W)
        (jetNn (I := I) (M := M) (m := 3) g W))
  refine ⟨C, hC, ?_⟩
  intro Φ
  have hΦ23 :
      lowJetSq (I := I) (M := M) g 2 Φ ≤
        lowJetSq (I := I) (M := M) g 3 Φ :=
    jetMono (I := I) (M := M) g (by omega : 2 ≤ 3) Φ
  calc
    lowJetSq (I := I) (M := M) g 3
        (appCcRS (I := I) (M := M) g p r c Φ W) ≤
      C₀ * (lowJetSq (I := I) (M := M) g 3 Φ *
          lowJetSq (I := I) (M := M) g 2 W +
        lowJetSq (I := I) (M := M) g 2 Φ *
          lowJetSq (I := I) (M := M) g 3 W) :=
      happ Φ W
    _ ≤ C₀ * (lowJetSq (I := I) (M := M) g 3 Φ *
          lowJetSq (I := I) (M := M) g 2 W +
        lowJetSq (I := I) (M := M) g 3 Φ *
          lowJetSq (I := I) (M := M) g 3 W) := by
      apply mul_le_mul_of_nonneg_left _ hC₀
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_right hΦ23
          (jetNn (I := I) (M := M) (m := 3) g W))
    _ = C * lowJetSq (I := I) (M := M) g 3 Φ := by
      simp only [C]
      ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M]
    [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem full_raised_endo_sub_eq_inv_diff_raised_endo
    (g gT gU : SmoothRiemannianMetric I M) :
    fullRaisedEndoField (I := I) (M := M) g gT -
        fullRaisedEndoField (I := I) (M := M) g gU =
      gInvDiffRaisedEndoField (I := I) g gT -
        gInvDiffRaisedEndoField (I := I) g gU := by
  apply ContMDiffSection.ext
  intro x
  rw [ContMDiffSection.coe_sub, Pi.sub_apply,
    ContMDiffSection.coe_sub, Pi.sub_apply]
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
    fullRaisedEndoField_apply, fullRaisedEndoField_apply,
    show gInvDiffRaisedEndoField (I := I) g gT x =
      gInvDiffRaisedEndo (I := I) g gT x from rfl,
    show gInvDiffRaisedEndoField (I := I) g gU x =
      gInvDiffRaisedEndo (I := I) g gU x from rfl,
    gInvRaisedEndo_eq_diff_add_id (I := I) g gT x v,
    gInvRaisedEndo_eq_diff_add_id (I := I) g gU x v]
  abel

theorem full_raised_endo_field_pair_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
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
          (ccTensorBilinSymm (I := I) g U) δU)
        (R D2 : ℝ),
        0 ≤ R → 0 ≤ D2 →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
      lowJetSq (I := I) (M := M) g 2
          (slotInsertEndoCc (I := I) (M := M) g 1
              (fullRaisedEndoField (I := I) (M := M) g gT) -
            slotInsertEndoCc (I := I) (M := M) g 1
              (fullRaisedEndoField (I := I) (M := M) g gU)) ≤
        (B R * D2) ^ 2 := by
  obtain ⟨Bh, hBh, hbdd⟩ :=
    LowBaseInternal.fullSlot_bdd_h2
      (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨C, hC, happ⟩ :=
    appH2 (I := I) (M := M) hDim g 2 2 2
  let fr : ℝ := Module.finrank ℝ E
  let Z : ℝ → ℝ := fun R => C ^ 2 * fr * (Bh R) ^ 4
  let B : ℝ → ℝ := fun R => Real.sqrt (Z R)
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hZ : ∀ R : ℝ, 0 ≤ Z R := by
    intro R
    dsimp only [Z]
    positivity
  refine ⟨B, fun R _ => Real.sqrt_nonneg _, ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
    R D2 hR hD2 hT2 hU2 hTU2
  let LT : SmoothCcTensor g 2 2 :=
    slotInsertEndoCc (I := I) (M := M) g 1
      (fullRaisedEndoField (I := I) (M := M) g gT)
  let LU : SmoothCcTensor g 2 2 :=
    slotInsertEndoCc (I := I) (M := M) g 1
      (fullRaisedEndoField (I := I) (M := M) g gU)
  let P : SmoothCcTensor g 2 2 :=
    slotInsertEndoCc (I := I) (M := M) g 1
      (symmRaiseEndo (I := I) (M := M) g (T - U))
  let X : SmoothCcTensor g 2 2 :=
    appCcRS (I := I) (M := M) g 2 2 2 P LT
  let Y : SmoothCcTensor g 2 2 :=
    appCcRS (I := I) (M := M) g 2 2 2 LU X
  have hsymm : symmS (I := I) (M := M) g (T - U) = T - U := by
    have hTs := symmS_eq_self_of_ccTensorBilin_symm
      (I := I) (M := M) g T hT
    have hUs := symmS_eq_self_of_ccTensorBilin_symm
      (I := I) (M := M) g U hU
    change ccTensor02Symm (I := I) (M := M) g T = T at hTs
    change ccTensor02Symm (I := I) (M := M) g U = U at hUs
    change ccTensor02Symm (I := I) (M := M) g (T - U) = T - U
    rw [symmS_sub, hTs, hUs]
  have hLT2 :
      lowJetSq (I := I) (M := M) g 2 LT ≤ (Bh R) ^ 2 := by
    simpa only [LT] using
      hbdd gT T hT hTtie hδT_le hδT0 hδT R hR hT2
  have hLU2 :
      lowJetSq (I := I) (M := M) g 2 LU ≤ (Bh R) ^ 2 := by
    simpa only [LU] using
      hbdd gU U hU hUtie hδU_le hδU0 hδU R hR hU2
  have hP2 :
      lowJetSq (I := I) (M := M) g 2 P ≤ fr * D2 ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 2 P ≤
          fr * lowJetSq (I := I) (M := M) g 2 (T - U) := by
        simpa only [P, fr] using
          symm_raise_endo_jet_le (I := I) (M := M) g 2 (T - U) hsymm
      _ ≤ fr * D2 ^ 2 :=
        mul_le_mul_of_nonneg_left hTU2 hfr
  have hX2 :
      lowJetSq (I := I) (M := M) g 2 X ≤
        C * (fr * D2 ^ 2) * (Bh R) ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 2 X ≤
          C * lowJetSq (I := I) (M := M) g 2 P *
            lowJetSq (I := I) (M := M) g 2 LT := by
        simpa only [X] using happ P LT
      _ ≤ C * (fr * D2 ^ 2) *
            lowJetSq (I := I) (M := M) g 2 LT := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hP2 hC)
          (jetNn (I := I) (M := M) (m := 2) g LT)
      _ ≤ C * (fr * D2 ^ 2) * (Bh R) ^ 2 := by
        exact mul_le_mul_of_nonneg_left hLT2
          (mul_nonneg hC (mul_nonneg hfr (sq_nonneg D2)))
  have hY2 :
      lowJetSq (I := I) (M := M) g 2 Y ≤
        Z R * D2 ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 2 Y ≤
          C * lowJetSq (I := I) (M := M) g 2 LU *
            lowJetSq (I := I) (M := M) g 2 X := by
        simpa only [Y] using happ LU X
      _ ≤ C * (Bh R) ^ 2 *
            lowJetSq (I := I) (M := M) g 2 X := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hLU2 hC)
          (jetNn (I := I) (M := M) (m := 2) g X)
      _ ≤ C * (Bh R) ^ 2 *
            (C * (fr * D2 ^ 2) * (Bh R) ^ 2) := by
        exact mul_le_mul_of_nonneg_left hX2
          (mul_nonneg hC (sq_nonneg (Bh R)))
      _ = Z R * D2 ^ 2 := by
        simp only [Z]
        ring
  have hslot :
      LT - LU =
        gInvDiffSlotCoeff (I := I) g gT -
          gInvDiffSlotCoeff (I := I) g gU := by
    simp only [LT, LU]
    rw [gInvDiffSlotCoeff_eq_slotInsertEndoCc (I := I) g gT,
      gInvDiffSlotCoeff_eq_slotInsertEndoCc (I := I) g gU,
      ← slotInsertEndoCc_sub, ← slotInsertEndoCc_sub,
      full_raised_endo_sub_eq_inv_diff_raised_endo (I := I) (M := M) g gT gU]
  rw [show
      slotInsertEndoCc (I := I) (M := M) g 1
            (fullRaisedEndoField (I := I) (M := M) g gT) -
          slotInsertEndoCc (I := I) (M := M) g 1
            (fullRaisedEndoField (I := I) (M := M) g gU) =
        LT - LU from rfl,
    hslot,
    invSlot_sub_factor (I := I) (M := M) g gT gU T U hTtie hUtie,
    jetNeg (I := I) (M := M) g 2]
  calc
    lowJetSq (I := I) (M := M) g 2
        (appCcRS (I := I) (M := M) g 2 2 2
          (slotInsertEndoCc (I := I) (M := M) g 1
            (fullRaisedEndoField (I := I) (M := M) g gU))
          (appCcRS (I := I) (M := M) g 2 2 2
            (slotInsertEndoCc (I := I) (M := M) g 1
              (symmRaiseEndo (I := I) (M := M) g (T - U)))
            (slotInsertEndoCc (I := I) (M := M) g 1
              (fullRaisedEndoField (I := I) (M := M) g gT)))) =
      lowJetSq (I := I) (M := M) g 2 Y := rfl
    _ ≤ Z R * D2 ^ 2 := hY2
    _ = (B R * D2) ^ 2 := by
      rw [mul_pow, show (B R) ^ 2 = Z R by
        simpa only [B] using Real.sq_sqrt (hZ R)]

private def koszulH2
    (g : SmoothRiemannianMetric I M) : SmoothCcTensor g 3 3 :=
  (1 / 2 : ℝ) •
    (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 2) +
      permCoeff (I := I) (M := M) g (finRotate 3) -
      permCoeff (I := I) (M := M) g (Equiv.swap (1 : Fin 3) 2))

private theorem connection_pair_h3
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
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
          (LowBaseInternal.connLowOp (I := I) (M := M) g gT -
            LowBaseInternal.connLowOp (I := I) (M := M) g gU) ≤
        (B R * (D3 + D2 + A * D2)) ^ 2 := by
  obtain ⟨BF, hBF, hfull⟩ :=
    inv_slot_pair_h3 (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨CK, hCK, hright⟩ :=
    app_right_h3 (I := I) (M := M) hDim g 3 3 3
      (koszulH2 (I := I) (M := M) g)
  obtain ⟨CP, hCP, hleft⟩ :=
    app_left_h3 (I := I) (M := M) hDim g 3 3 3
      (permCoeff (I := I) (M := M) g LowBaseInternal.lowPerm)
  let Z : ℝ := CP * CK
  let C : ℝ := Real.sqrt Z
  let B : ℝ → ℝ := fun R => C * (3 * BF R)
  have hZ : 0 ≤ Z := mul_nonneg hCP hCK
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hCsq : C ^ 2 = Z := by
    simpa only [C] using Real.sq_sqrt hZ
  refine ⟨B, fun R hR => mul_nonneg hC
    (mul_nonneg (by norm_num) (hBF R hR)), ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
    R A D2 D3 hR hA hD2 hD3 hT2 hU2 hT3 hU3 hTU2 hTU3
  let Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) :=
    fullRaisedEndoField (I := I) (M := M) g gT -
      fullRaisedEndoField (I := I) (M := M) g gU
  let D : SmoothCcTensor g 3 3 :=
    slotInsertEndoCc (I := I) (M := M) g 2 Λ
  let K : SmoothCcTensor g 3 3 :=
    koszulH2 (I := I) (M := M) g
  let P : SmoothCcTensor g 3 3 :=
    permCoeff (I := I) (M := M) g LowBaseInternal.lowPerm
  let Mid : SmoothCcTensor g 3 3 :=
    appCcRS (I := I) (M := M) g 3 3 3 D K
  let Q : ℝ := D3 + D2 + A * D2
  have hQ : 0 ≤ Q :=
    add_nonneg (add_nonneg hD3 hD2) (mul_nonneg hA hD2)
  have hslot1 :
      lowJetSq (I := I) (M := M) g 3
          (slotInsertEndoCc (I := I) (M := M) g 1 Λ) ≤
        (BF R * Q) ^ 2 := by
    change lowJetSq (I := I) (M := M) g 3
        (slotInsertEndoCc (I := I) (M := M) g 1
          (fullRaisedEndoField (I := I) (M := M) g gT -
            fullRaisedEndoField (I := I) (M := M) g gU)) ≤ _
    rw [full_raised_endo_sub_eq_inv_diff_raised_endo
      (I := I) (M := M) g gT gU, slotInsertEndoCc_sub]
    have hTslot :
        slotInsertEndoCc (I := I) (M := M) g 1
            (gInvDiffRaisedEndoField (I := I) g gT) =
          gInvDiffSlotCoeff (I := I) g gT :=
      (gInvDiffSlotCoeff_eq_slotInsertEndoCc (I := I) g gT).symm
    have hUslot :
        slotInsertEndoCc (I := I) (M := M) g 1
            (gInvDiffRaisedEndoField (I := I) g gU) =
          gInvDiffSlotCoeff (I := I) g gU :=
      (gInvDiffSlotCoeff_eq_slotInsertEndoCc (I := I) g gU).symm
    rw [hTslot, hUslot]
    exact hfull gT gU T U hT hU hTtie hUtie
      hδT_le hδT0 hδT hδU_le hδU0 hδU
      R A D2 D3 hR hA hD2 hD3 hT2 hU2 hT3 hU3 hTU2 hTU3
  have hslot2 :
      lowJetSq (I := I) (M := M) g 3 D ≤
        (3 * BF R * Q) ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 3 D ≤
          (Module.finrank ℝ E : ℝ) *
            lowJetSq (I := I) (M := M) g 3
              (slotInsertEndoCc (I := I) (M := M) g 1 Λ) := by
        simpa only [D, Nat.reduceAdd] using
          slot_insert_endo_succ_jet_le (I := I) (M := M) g 1 3 Λ
      _ = 3 * lowJetSq (I := I) (M := M) g 3
            (slotInsertEndoCc (I := I) (M := M) g 1 Λ) := by
        rw [hDim]
        norm_num
      _ ≤ 3 * (BF R * Q) ^ 2 :=
        mul_le_mul_of_nonneg_left hslot1 (by norm_num)
      _ ≤ (3 * BF R * Q) ^ 2 := by
        nlinarith only [sq_nonneg (BF R * Q)]
  have hMid :
      lowJetSq (I := I) (M := M) g 3 Mid ≤
        CK * (3 * BF R * Q) ^ 2 :=
    (hright D).trans
      (mul_le_mul_of_nonneg_left hslot2 hCK)
  have heq :
      LowBaseInternal.connLowOp (I := I) (M := M) g gT -
          LowBaseInternal.connLowOp (I := I) (M := M) g gU =
        appCcRS (I := I) (M := M) g 3 3 3 P Mid := by
    change
      appCcRS (I := I) (M := M) g 3 3 3 P
            (appCcRS (I := I) (M := M) g 3 3 3
              (slotInsertEndoCc (I := I) (M := M) g 2
                (fullRaisedEndoField (I := I) (M := M) g gT)) K) -
          appCcRS (I := I) (M := M) g 3 3 3 P
            (appCcRS (I := I) (M := M) g 3 3 3
              (slotInsertEndoCc (I := I) (M := M) g 2
                (fullRaisedEndoField (I := I) (M := M) g gU)) K) =
        appCcRS (I := I) (M := M) g 3 3 3 P Mid
    rw [← appCcRS_sub_right, ← appCcRS_sub_left]
    simp only [Mid, D, Λ, slotInsertEndoCc_sub]
  rw [heq]
  calc
    lowJetSq (I := I) (M := M) g 3
        (appCcRS (I := I) (M := M) g 3 3 3 P Mid) ≤
      CP * lowJetSq (I := I) (M := M) g 3 Mid :=
        hleft Mid
    _ ≤ CP * (CK * (3 * BF R * Q) ^ 2) :=
      mul_le_mul_of_nonneg_left hMid hCP
    _ = (B R * Q) ^ 2 := by
      change C ^ 2 = CP * CK at hCsq
      dsimp only [B]
      rw [show CP * (CK * (3 * BF R * Q) ^ 2) =
          (CP * CK) * (3 * BF R * Q) ^ 2 by ring, ← hCsq]
      ring

theorem dag_low_op_pair_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
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
          (LowBaseInternal.dagLowOp (I := I) (M := M) g gT -
            LowBaseInternal.dagLowOp (I := I) (M := M) g gU) ≤
        (B R * (D3 + D2 + A * D2)) ^ 2 := by
  obtain ⟨BC, hBC, hconn⟩ :=
    connection_pair_h3 (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Ca, hCa, happ⟩ :=
    appH2 (I := I) (M := M) hDim g 3 4 4
  let P : SmoothCcTensor g 4 4 :=
    permCoeff (I := I) (M := M) g LowBaseInternal.daPermA
  let L : ℝ := Ca * lowJetSq (I := I) (M := M) g 2 P
  let C : ℝ := Real.sqrt L
  let B : ℝ → ℝ := fun R => C * BC R
  have hL : 0 ≤ L :=
    mul_nonneg hCa (jetNn (I := I) (M := M) (m := 2) g P)
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hCsq : C ^ 2 = L := by
    simpa only [C] using Real.sq_sqrt hL
  refine ⟨B, fun R hR => mul_nonneg hC (hBC R hR), ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
    R A D2 D3 hR hA hD2 hD3 hT2 hU2 hT3 hU3 hTU2 hTU3
  let D : SmoothCcTensor g 3 3 :=
    LowBaseInternal.connLowOp (I := I) (M := M) g gT -
      LowBaseInternal.connLowOp (I := I) (M := M) g gU
  let G : SmoothCcTensor g 3 4 :=
    covGrad (I := I) (M := M) g 3 3 D
  let Q : ℝ := D3 + D2 + A * D2
  have hconn' :
      lowJetSq (I := I) (M := M) g 3 D ≤
        (BC R * Q) ^ 2 := by
    simpa only [D, Q] using
      hconn gT gU T U hT hU hTtie hUtie
        hδT_le hδT0 hδT hδU_le hδU0 hδU
        R A D2 D3 hR hA hD2 hD3 hT2 hU2 hT3 hU3 hTU2 hTU3
  have hG :
      lowJetSq (I := I) (M := M) g 2 G ≤
        (BC R * Q) ^ 2 :=
    (low_jet_sq_cov_grad_two_le_three (I := I) (M := M) g D).trans hconn'
  have heq :
      LowBaseInternal.dagLowOp (I := I) (M := M) g gT -
          LowBaseInternal.dagLowOp (I := I) (M := M) g gU =
        appCcRS (I := I) (M := M) g 3 4 4 P G := by
    change
      appCcRS (I := I) (M := M) g 3 4 4 P
          (covGrad (I := I) (M := M) g 3 3
            (LowBaseInternal.connLowOp (I := I) (M := M) g gT)) -
        appCcRS (I := I) (M := M) g 3 4 4 P
          (covGrad (I := I) (M := M) g 3 3
            (LowBaseInternal.connLowOp (I := I) (M := M) g gU)) =
        appCcRS (I := I) (M := M) g 3 4 4 P G
    rw [← appCcRS_sub_right, ← covGrad_sub]
  rw [heq]
  calc
    lowJetSq (I := I) (M := M) g 2
        (appCcRS (I := I) (M := M) g 3 4 4 P G) ≤
      Ca * lowJetSq (I := I) (M := M) g 2 P *
        lowJetSq (I := I) (M := M) g 2 G :=
      happ P G
    _ ≤ L * (BC R * Q) ^ 2 := by
      simpa only [L] using
        mul_le_mul_of_nonneg_left hG
          (mul_nonneg hCa
            (jetNn (I := I) (M := M) (m := 2) g P))
    _ = (B R * Q) ^ 2 := by
      simp only [B]
      rw [mul_pow, ← hCsq]
      ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
