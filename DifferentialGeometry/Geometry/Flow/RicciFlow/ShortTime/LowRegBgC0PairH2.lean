import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegBgC0One
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegCoeffJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegDlbInsH2
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegInsertH1

/-!
# Fixed-background order-zero coefficient pairs in H2

This module upgrades the three-dimensional fixed-background order-zero
correction from the existing `H1` pair estimate to the `H3 → H2` currency used
by the one-sided smooth bootstrap.  The mixed arm is treated first because all
of its factor estimates already exist at `H2`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open LieCorr0Core
open LowRegBgC0Core

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- The part of the lowered connection difference caused by changing the
DeTurck background while keeping the moving metric fixed. -/
private noncomputable def bgKappa
    (g gm gB : SmoothRiemannianMetric I M) : SmoothCcTensor g 0 3 :=
  lc0Kappa (I := I) (M := M) g gm gB -
    lc0Kappa (I := I) (M := M) g gm g

private theorem bgKappa_pair
    (g gT gU gB : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    (hTtie : ∀ (x : M) (u v : TangentSpace I x),
      gT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
    (hUtie : ∀ (x : M) (u v : TangentSpace I x),
      gU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g U x u v) :
    bgKappa (I := I) (M := M) g gT gB -
        bgKappa (I := I) (M := M) g gU gB =
      lc0PbLow (I := I) (M := M) g (T - U) g gB := by
  unfold bgKappa
  rw [kappa_bg (I := I) (M := M) g gT gB T hTtie,
    kappa_bg (I := I) (M := M) g gU gB U hUtie,
    pbLow_sub (I := I) (M := M) g T U g gB]
  module

/-- One refolded half of the mixed order-zero background correction. -/
private noncomputable def bgAmixHalf
    (g gm gB : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) : SmoothCcTensor g 2 2 :=
  appCcRS (I := I) (M := M) g 2 4 2
    (lc0TraceRF (I := I) (M := M) g gm 2 σ)
    (appCcRS (I := I) (M := M) g 2 6 4
      (lc0TraceRF (I := I) (M := M) g gm 4 lieCorr0AMixPerm1)
      (appCcRS (I := I) (M := M) g 2 3 6
        (slotExtendIter (I := I) (M := M) g 0 3 3
          (bgKappa (I := I) (M := M) g gm gB))
        (appCcRS (I := I) (M := M) g 2 5 3
          (lc0TraceRF (I := I) (M := M) g gm 3 lieCorr0AMixPermQ)
          (slotExtendIter (I := I) (M := M) g 0 3 2
            (lc0Kappa (I := I) (M := M) g gm g)))))

private theorem slotIter_sub
    (g : SmoothRiemannianMetric I M) (r s w : ℕ)
    (A B : SmoothCcTensor g r s) :
    slotExtendIter (I := I) (M := M) g r s w (A - B) =
      slotExtendIter (I := I) (M := M) g r s w A -
        slotExtendIter (I := I) (M := M) g r s w B := by
  induction w with
  | zero => simp only [slotExtendIter]
  | succ w ih =>
      change slotExtend (I := I) (M := M) g (r + w) (s + w)
          (slotExtendIter (I := I) (M := M) g r s w (A - B)) = _
      rw [ih, slotExtend_sub]
      rfl

private theorem amixHalf_bg
    (g gm gB : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) :
    lc0AMixHalfRF (I := I) (M := M) g gm gB σ -
        lc0AMixHalfRF (I := I) (M := M) g gm g σ =
      bgAmixHalf (I := I) (M := M) g gm gB σ := by
  unfold lc0AMixHalfRF bgAmixHalf bgKappa lc0Kappa
  rw [← appCcRS_sub_right, ← appCcRS_sub_right,
    ← appCcRS_sub_left, ← slotIter_sub]

private theorem bgAmix_eq
    (g gm gB : SmoothRiemannianMetric I M) :
    lc0AMix (I := I) (M := M) g gm gB -
        lc0AMix (I := I) (M := M) g gm g =
      (2 : ℝ) •
        (bgAmixHalf (I := I) (M := M) g gm gB lieCorr0AMixPerm2 +
          bgAmixHalf (I := I) (M := M) g gm gB
            (lc0SwapPermRF * lieCorr0AMixPerm2)) := by
  rw [amix_refold_rf (I := I) (M := M) g gm gB,
    amix_refold_rf (I := I) (M := M) g gm g]
  have h0 := amixHalf_bg (I := I) (M := M) g gm gB lieCorr0AMixPerm2
  have h1 := amixHalf_bg (I := I) (M := M) g gm gB
    (lc0SwapPermRF * lieCorr0AMixPerm2)
  simp only [lc0AMixFormRF]
  rw [show
      (2 : ℝ) •
          (lc0AMixHalfRF (I := I) (M := M) g gm gB lieCorr0AMixPerm2 +
            lc0AMixHalfRF (I := I) (M := M) g gm gB
              (lc0SwapPermRF * lieCorr0AMixPerm2)) -
        (2 : ℝ) •
          (lc0AMixHalfRF (I := I) (M := M) g gm g lieCorr0AMixPerm2 +
            lc0AMixHalfRF (I := I) (M := M) g gm g
              (lc0SwapPermRF * lieCorr0AMixPerm2)) =
        (2 : ℝ) •
          ((lc0AMixHalfRF (I := I) (M := M) g gm gB lieCorr0AMixPerm2 -
              lc0AMixHalfRF (I := I) (M := M) g gm g lieCorr0AMixPerm2) +
            (lc0AMixHalfRF (I := I) (M := M) g gm gB
                (lc0SwapPermRF * lieCorr0AMixPerm2) -
              lc0AMixHalfRF (I := I) (M := M) g gm g
                (lc0SwapPermRF * lieCorr0AMixPerm2))) by module,
    h0, h1]

/-- The background-change part of the lowered connection has an `H2` bound
and a linear two-state `H2` modulus. -/
private theorem bgKappaH2
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ, ∃ C : ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧ 0 ≤ C ∧
      (∀ (gT : SmoothRiemannianMetric I M)
        (T : SmoothCcTensor g 0 2)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (R : ℝ), 0 ≤ R →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2
            (bgKappa (I := I) (M := M) g gT gB) ≤ (B R) ^ 2) ∧
      (∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        (D : ℝ), 0 ≤ D →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D ^ 2 →
        lowJetSq (I := I) (M := M) g 2
            (bgKappa (I := I) (M := M) g gT gB -
              bgKappa (I := I) (M := M) g gU gB) ≤ (C * D) ^ 2) := by
  obtain ⟨B, hB, hone⟩ := kappaDiff_h2 (I := I) (M := M) hDim g gB
  obtain ⟨C, hC, hpair⟩ := pbLow_h2_mul (I := I) (M := M) hDim g gB
  refine ⟨B, C, hB, hC, ?_, ?_⟩
  · intro gT T hTtie R hR hT
    have hraw := hone gT T hTtie R hR (by
      simpa only [lowJetSq, Nat.reduceAdd] using hT)
    have heq :
        bgKappa (I := I) (M := M) g gT gB =
          -(lc0Kappa (I := I) (M := M) g gT g -
            lc0Kappa (I := I) (M := M) g gT gB) := by
      unfold bgKappa
      module
    rw [heq, show -(lc0Kappa (I := I) (M := M) g gT g -
        lc0Kappa (I := I) (M := M) g gT gB) =
          (-1 : ℝ) • (lc0Kappa (I := I) (M := M) g gT g -
            lc0Kappa (I := I) (M := M) g gT gB) by simp,
      jetSmul]
    norm_num
    simpa only [lowJetSq, Nat.reduceAdd] using hraw
  · intro gT gU T U hTtie hUtie D hD hTU
    rw [bgKappa_pair (I := I) (M := M) g gT gU gB T U hTtie hUtie]
    exact hpair (T - U) D hD (by
      simpa only [lowJetSq, Nat.reduceAdd] using hTU)

set_option maxHeartbeats 6400000 in
/-- A refolded mixed half is `H2`-Lipschitz in the critical `H3/H2`
two-state currency. -/
private theorem amixHalfH2
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M) :
    ∃ ρ B0 B1 : ℝ,
      0 < ρ ∧ 0 ≤ B0 ∧ 0 ≤ B1 ∧
      ∀ (σ : Equiv.Perm (Fin 4))
        (T U : SmoothCcTensor g 0 2)
        (gT gU : SmoothRiemannianMetric I M),
        (∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v) →
        (∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ (A D3 : ℝ), 0 ≤ A → 0 ≤ D3 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        lowJetSq (I := I) (M := M) g 2
            (bgAmixHalf (I := I) (M := M) g gT gB σ -
              bgAmixHalf (I := I) (M := M) g gU gB σ) ≤
          (B0 * D3 + B1 * A *
            ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖) ^ 2 := by
  obtain ⟨ρ2p, Ct2, hρ2p, hCt2, hp2⟩ :=
    LowBaseInternal.trace2_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρ2b, Bt2, hρ2b, hBt2, hb2⟩ :=
    LowBaseInternal.trace2_h2_bdd (I := I) (M := M) hDim g
  obtain ⟨ρ3p, Ct3, hρ3p, hCt3, hp3⟩ :=
    LowBaseInternal.trace3_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρ3b, Bt3, hρ3b, hBt3, hb3⟩ :=
    LowBaseInternal.trace3_h2_bdd (I := I) (M := M) hDim g
  obtain ⟨ρ4p, Ct4, hρ4p, hCt4, hp4⟩ :=
    LowBaseInternal.trace4_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρ4b, Bt4, hρ4b, hBt4, hb4⟩ :=
    LowBaseInternal.trace4_h2_bdd (I := I) (M := M) hDim g
  obtain ⟨Kb, Cb, hKb, hCb, hkOne, hkPair⟩ :=
    bgKappaH2 (I := I) (M := M) hDim g gB
  obtain ⟨Ch, hCh, hhs⟩ := hs2_low2 (I := I) (M := M) g 2
  obtain ⟨O2, hO2, hone2⟩ := appRoot_h2 (I := I) (M := M) hDim g 2 4 2
  obtain ⟨P2, hP2, hpair2⟩ := appPairH2 (I := I) (M := M) hDim g 2 4 2
  obtain ⟨O4, hO4, hone4⟩ := appRoot_h2 (I := I) (M := M) hDim g 2 6 4
  obtain ⟨P4, hP4, hpair4⟩ := appPairH2 (I := I) (M := M) hDim g 2 6 4
  obtain ⟨Ok, hOk, honek⟩ := appRoot_h2 (I := I) (M := M) hDim g 2 3 6
  obtain ⟨Pk, hPk, hpairk⟩ := appPairH2 (I := I) (M := M) hDim g 2 3 6
  obtain ⟨O3, hO3, hone3⟩ := appRoot_h2 (I := I) (M := M) hDim g 2 5 3
  obtain ⟨P3, hP3, hpair3⟩ := appPairH2 (I := I) (M := M) hDim g 2 5 3
  let sf2 : ℝ := Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 2)
  let sf3 : ℝ := Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 3)
  let BK : ℝ := Kb Ch
  let CK : ℝ := Cb * Ch
  let A5 : ℝ := sf2 * 4
  let D5 : ℝ := sf2 * 4
  let A4 : ℝ := O3 * Bt3 * A5
  let D40 : ℝ := P3 * Bt3 * D5
  let D41 : ℝ := P3 * Ct3 * A5
  let AK : ℝ := sf3 * BK
  let DK : ℝ := sf3 * CK
  let A3 : ℝ := Ok * AK * A4
  let D30 : ℝ := Pk * AK * D40
  let D31 : ℝ := Pk * (DK * A4 + AK * D41)
  let A2 : ℝ := O4 * Bt4 * A3
  let D20 : ℝ := P4 * Bt4 * D30
  let D21 : ℝ := P4 * (Ct4 * A3 + Bt4 * D31)
  let B0 : ℝ := P2 * Bt2 * D20
  let B1 : ℝ := P2 * (Ct2 * A2 + Bt2 * D21)
  let ρ : ℝ := min 1
    (min ρ2p (min ρ2b (min ρ3p (min ρ3b (min ρ4p ρ4b)))))
  have hρ : 0 < ρ := by
    dsimp only [ρ]
    exact lt_min (by norm_num)
      (lt_min hρ2p (lt_min hρ2b
        (lt_min hρ3p (lt_min hρ3b (lt_min hρ4p hρ4b)))))
  have hBK : 0 ≤ BK := hKb Ch hCh
  have hCK : 0 ≤ CK := mul_nonneg hCb hCh
  have hsf2 : 0 ≤ sf2 := Real.sqrt_nonneg _
  have hsf3 : 0 ≤ sf3 := Real.sqrt_nonneg _
  have hA5 : 0 ≤ A5 := by dsimp only [A5]; positivity
  have hD5 : 0 ≤ D5 := by dsimp only [D5]; positivity
  have hA4 : 0 ≤ A4 := by dsimp only [A4]; positivity
  have hD40 : 0 ≤ D40 := by dsimp only [D40]; positivity
  have hD41 : 0 ≤ D41 := by dsimp only [D41]; positivity
  have hAK : 0 ≤ AK := by dsimp only [AK]; positivity
  have hDK : 0 ≤ DK := by dsimp only [DK]; positivity
  have hA3 : 0 ≤ A3 := by dsimp only [A3]; positivity
  have hD30 : 0 ≤ D30 := by dsimp only [D30]; positivity
  have hD31 : 0 ≤ D31 := by dsimp only [D31]; positivity
  have hA2 : 0 ≤ A2 := by dsimp only [A2]; positivity
  have hD20 : 0 ≤ D20 := by dsimp only [D20]; positivity
  have hD21 : 0 ≤ D21 := by dsimp only [D21]; positivity
  have hB0 : 0 ≤ B0 := by dsimp only [B0]; positivity
  have hB1 : 0 ≤ B1 := by dsimp only [B1]; positivity
  refine ⟨ρ, B0, B1, hρ, hB0, hB1, ?_⟩
  intro σ T U gT gU hTtie hUtie hTHs hUHs A D3 hA hD3 hT3 hTU3
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  have hN : 0 ≤ N := norm_nonneg _
  have hρ1 : ρ ≤ 1 := by
    dsimp only [ρ]
    exact min_le_left _ _
  have hρ2p' : ρ ≤ ρ2p := by
    dsimp only [ρ]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hρ2b' : ρ ≤ ρ2b := by
    dsimp only [ρ]
    calc
      _ ≤ min ρ2p (min ρ2b (min ρ3p (min ρ3b (min ρ4p ρ4b)))) :=
        min_le_right _ _
      _ ≤ min ρ2b (min ρ3p (min ρ3b (min ρ4p ρ4b))) := min_le_right _ _
      _ ≤ ρ2b := min_le_left _ _
  have hρ3p' : ρ ≤ ρ3p := by
    dsimp only [ρ]
    calc
      _ ≤ min ρ2p (min ρ2b (min ρ3p (min ρ3b (min ρ4p ρ4b)))) :=
        min_le_right _ _
      _ ≤ min ρ2b (min ρ3p (min ρ3b (min ρ4p ρ4b))) := min_le_right _ _
      _ ≤ min ρ3p (min ρ3b (min ρ4p ρ4b)) := min_le_right _ _
      _ ≤ ρ3p := min_le_left _ _
  have hρ3b' : ρ ≤ ρ3b := by
    dsimp only [ρ]
    calc
      _ ≤ min ρ2p (min ρ2b (min ρ3p (min ρ3b (min ρ4p ρ4b)))) :=
        min_le_right _ _
      _ ≤ min ρ2b (min ρ3p (min ρ3b (min ρ4p ρ4b))) := min_le_right _ _
      _ ≤ min ρ3p (min ρ3b (min ρ4p ρ4b)) := min_le_right _ _
      _ ≤ min ρ3b (min ρ4p ρ4b) := min_le_right _ _
      _ ≤ ρ3b := min_le_left _ _
  have hρ4p' : ρ ≤ ρ4p := by
    dsimp only [ρ]
    calc
      _ ≤ min ρ2p (min ρ2b (min ρ3p (min ρ3b (min ρ4p ρ4b)))) :=
        min_le_right _ _
      _ ≤ min ρ2b (min ρ3p (min ρ3b (min ρ4p ρ4b))) := min_le_right _ _
      _ ≤ min ρ3p (min ρ3b (min ρ4p ρ4b)) := min_le_right _ _
      _ ≤ min ρ3b (min ρ4p ρ4b) := min_le_right _ _
      _ ≤ min ρ4p ρ4b := min_le_right _ _
      _ ≤ ρ4p := min_le_left _ _
  have hρ4b' : ρ ≤ ρ4b := by
    dsimp only [ρ]
    calc
      _ ≤ min ρ2p (min ρ2b (min ρ3p (min ρ3b (min ρ4p ρ4b)))) :=
        min_le_right _ _
      _ ≤ min ρ2b (min ρ3p (min ρ3b (min ρ4p ρ4b))) := min_le_right _ _
      _ ≤ min ρ3p (min ρ3b (min ρ4p ρ4b)) := min_le_right _ _
      _ ≤ min ρ3b (min ρ4p ρ4b) := min_le_right _ _
      _ ≤ min ρ4p ρ4b := min_le_right _ _
      _ ≤ ρ4b := min_le_right _ _
  have hTHs1 : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ 1 :=
    hTHs.trans hρ1
  have hUHs1 : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ 1 :=
    hUHs.trans hρ1
  have hT2 : lowJetSq (I := I) (M := M) g 2 T ≤ Ch ^ 2 := by
    calc
      _ ≤ (Ch * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖) ^ 2 := by
        simpa only [lowJetSq, Nat.reduceAdd] using hhs T
      _ ≤ (Ch * 1) ^ 2 := pow_le_pow_left₀
        (mul_nonneg hCh (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hTHs1 hCh) 2
      _ = Ch ^ 2 := by rw [mul_one]
  have hU2 : lowJetSq (I := I) (M := M) g 2 U ≤ Ch ^ 2 := by
    calc
      _ ≤ (Ch * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖) ^ 2 := by
        simpa only [lowJetSq, Nat.reduceAdd] using hhs U
      _ ≤ (Ch * 1) ^ 2 := pow_le_pow_left₀
        (mul_nonneg hCh (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hUHs1 hCh) 2
      _ = Ch ^ 2 := by rw [mul_one]
  have hTU2 : lowJetSq (I := I) (M := M) g 2 (T - U) ≤ (Ch * N) ^ 2 := by
    simpa only [lowJetSq, Nat.reduceAdd, N] using hhs (T - U)
  have hTHs2p := hTHs.trans hρ2p'
  have hUHs2p := hUHs.trans hρ2p'
  have hTHs2b := hTHs.trans hρ2b'
  have hUHs2b := hUHs.trans hρ2b'
  have hTHs3p := hTHs.trans hρ3p'
  have hUHs3p := hUHs.trans hρ3p'
  have hTHs3b := hTHs.trans hρ3b'
  have hUHs3b := hUHs.trans hρ3b'
  have hTHs4p := hTHs.trans hρ4p'
  have hUHs4p := hUHs.trans hρ4p'
  have hTHs4b := hTHs.trans hρ4b'
  have hUHs4b := hUHs.trans hρ4b'
  let Tr2T : SmoothCcTensor g 4 2 := lc0TraceRF (I := I) (M := M) g gT 2 σ
  let Tr2U : SmoothCcTensor g 4 2 := lc0TraceRF (I := I) (M := M) g gU 2 σ
  let Tr3T : SmoothCcTensor g 5 3 :=
    lc0TraceRF (I := I) (M := M) g gT 3 lieCorr0AMixPermQ
  let Tr3U : SmoothCcTensor g 5 3 :=
    lc0TraceRF (I := I) (M := M) g gU 3 lieCorr0AMixPermQ
  let Tr4T : SmoothCcTensor g 6 4 :=
    lc0TraceRF (I := I) (M := M) g gT 4 lieCorr0AMixPerm1
  let Tr4U : SmoothCcTensor g 6 4 :=
    lc0TraceRF (I := I) (M := M) g gU 4 lieCorr0AMixPerm1
  let K0T : SmoothCcTensor g 0 3 := lc0Kappa (I := I) (M := M) g gT g
  let K0U : SmoothCcTensor g 0 3 := lc0Kappa (I := I) (M := M) g gU g
  let KbT : SmoothCcTensor g 0 3 := bgKappa (I := I) (M := M) g gT gB
  let KbU : SmoothCcTensor g 0 3 := bgKappa (I := I) (M := M) g gU gB
  let S5T : SmoothCcTensor g 2 5 :=
    slotExtendIter (I := I) (M := M) g 0 3 2 K0T
  let S5U : SmoothCcTensor g 2 5 :=
    slotExtendIter (I := I) (M := M) g 0 3 2 K0U
  let E3T : SmoothCcTensor g 3 6 :=
    slotExtendIter (I := I) (M := M) g 0 3 3 KbT
  let E3U : SmoothCcTensor g 3 6 :=
    slotExtendIter (I := I) (M := M) g 0 3 3 KbU
  let S4T : SmoothCcTensor g 2 3 :=
    appCcRS (I := I) (M := M) g 2 5 3 Tr3T S5T
  let S4U : SmoothCcTensor g 2 3 :=
    appCcRS (I := I) (M := M) g 2 5 3 Tr3U S5U
  let S3T : SmoothCcTensor g 2 6 :=
    appCcRS (I := I) (M := M) g 2 3 6 E3T S4T
  let S3U : SmoothCcTensor g 2 6 :=
    appCcRS (I := I) (M := M) g 2 3 6 E3U S4U
  let S2T : SmoothCcTensor g 2 4 :=
    appCcRS (I := I) (M := M) g 2 6 4 Tr4T S3T
  let S2U : SmoothCcTensor g 2 4 :=
    appCcRS (I := I) (M := M) g 2 6 4 Tr4U S3U
  have hTr2U : lowJetSq (I := I) (M := M) g 2 Tr2U ≤ Bt2 ^ 2 := by
    rw [show Tr2U = lc0TraceRF (I := I) (M := M) g gU 2 σ by rfl, trJet]
    exact hb2 U gU hUtie hUHs2b
  have hTr2D : lowJetSq (I := I) (M := M) g 2 (Tr2T - Tr2U) ≤
      (Ct2 * N) ^ 2 := by
    rw [show Tr2T - Tr2U = lc0TraceRF (I := I) (M := M) g gT 2 σ -
        lc0TraceRF (I := I) (M := M) g gU 2 σ by rfl, trSub, reindexJet]
    simpa only [N] using hp2 T U gT gU hTtie hUtie hTHs2p hUHs2p
  have hTr3T : lowJetSq (I := I) (M := M) g 2 Tr3T ≤ Bt3 ^ 2 := by
    rw [show Tr3T = lc0TraceRF (I := I) (M := M) g gT 3
        lieCorr0AMixPermQ by rfl, trJet]
    exact hb3 T gT hTtie hTHs3b
  have hTr3U : lowJetSq (I := I) (M := M) g 2 Tr3U ≤ Bt3 ^ 2 := by
    rw [show Tr3U = lc0TraceRF (I := I) (M := M) g gU 3
        lieCorr0AMixPermQ by rfl, trJet]
    exact hb3 U gU hUtie hUHs3b
  have hTr3D : lowJetSq (I := I) (M := M) g 2 (Tr3T - Tr3U) ≤
      (Ct3 * N) ^ 2 := by
    rw [show Tr3T - Tr3U = lc0TraceRF (I := I) (M := M) g gT 3
        lieCorr0AMixPermQ - lc0TraceRF (I := I) (M := M) g gU 3
          lieCorr0AMixPermQ by rfl, trSub, reindexJet]
    simpa only [N] using hp3 T U gT gU hTtie hUtie hTHs3p hUHs3p
  have hTr4T : lowJetSq (I := I) (M := M) g 2 Tr4T ≤ Bt4 ^ 2 := by
    rw [show Tr4T = lc0TraceRF (I := I) (M := M) g gT 4
        lieCorr0AMixPerm1 by rfl, trJet]
    exact hb4 T gT hTtie hTHs4b
  have hTr4U : lowJetSq (I := I) (M := M) g 2 Tr4U ≤ Bt4 ^ 2 := by
    rw [show Tr4U = lc0TraceRF (I := I) (M := M) g gU 4
        lieCorr0AMixPerm1 by rfl, trJet]
    exact hb4 U gU hUtie hUHs4b
  have hTr4D : lowJetSq (I := I) (M := M) g 2 (Tr4T - Tr4U) ≤
      (Ct4 * N) ^ 2 := by
    rw [show Tr4T - Tr4U = lc0TraceRF (I := I) (M := M) g gT 4
        lieCorr0AMixPerm1 - lc0TraceRF (I := I) (M := M) g gU 4
          lieCorr0AMixPerm1 by rfl, trSub, reindexJet]
    simpa only [N] using hp4 T U gT gU hTtie hUtie hTHs4p hUHs4p
  have hK0T : lowJetSq (I := I) (M := M) g 2 K0T ≤ (4 * A) ^ 2 := by
    simpa only [K0T, lowJetSq, Nat.reduceAdd] using
      kappaSelf_h2 (I := I) (M := M) g gT T hTtie A hA
        (by simpa only [lowJetSq, Nat.reduceAdd] using hT3)
  have hK0D : lowJetSq (I := I) (M := M) g 2 (K0T - K0U) ≤
      (4 * D3) ^ 2 := by
    have hk := kappa_self_pair_h2 (I := I) (M := M) g gT gU T U hTtie hUtie
    have hk' : lowJetSq (I := I) (M := M) g 2 (K0T - K0U) ≤
        10 * lowJetSq (I := I) (M := M) g 3 (T - U) := by
      simpa only [K0T, K0U, lowJetSq, Nat.reduceAdd] using hk
    calc
      _ ≤ 10 * lowJetSq (I := I) (M := M) g 3 (T - U) := hk'
      _ ≤ 10 * D3 ^ 2 := mul_le_mul_of_nonneg_left hTU3 (by norm_num)
      _ ≤ (4 * D3) ^ 2 := by nlinarith [sq_nonneg D3]
  have hKbT : lowJetSq (I := I) (M := M) g 2 KbT ≤ BK ^ 2 := by
    simpa only [KbT, BK] using hkOne gT T hTtie Ch hCh hT2
  have hKbU : lowJetSq (I := I) (M := M) g 2 KbU ≤ BK ^ 2 := by
    simpa only [KbU, BK] using hkOne gU U hUtie Ch hCh hU2
  have hKbD : lowJetSq (I := I) (M := M) g 2 (KbT - KbU) ≤
      (CK * N) ^ 2 := by
    have hk := hkPair gT gU T U hTtie hUtie (Ch * N)
      (mul_nonneg hCh hN) hTU2
    simpa only [KbT, KbU, CK, mul_assoc] using hk
  have hS5T : lowJetSq (I := I) (M := M) g 2 S5T ≤ (A5 * A) ^ 2 := by
    have hs := slotIter_h2b (I := I) (M := M) g 0 3 2 K0T (4 * A)
      (by simpa only [lowJetSq, Nat.reduceAdd] using hK0T)
    simpa only [S5T, lowJetSq, Nat.reduceAdd, A5, sf2, mul_assoc] using hs
  have hS5D : lowJetSq (I := I) (M := M) g 2 (S5T - S5U) ≤
      (D5 * D3) ^ 2 := by
    rw [show S5T - S5U =
        slotExtendIter (I := I) (M := M) g 0 3 2 (K0T - K0U) by
      dsimp only [S5T, S5U]
      rw [slotIter_sub]]
    have hs := slotIter_h2b (I := I) (M := M) g 0 3 2
      (K0T - K0U) (4 * D3)
      (by simpa only [lowJetSq, Nat.reduceAdd] using hK0D)
    simpa only [lowJetSq, Nat.reduceAdd, D5, sf2, mul_assoc] using hs
  have hE3T : lowJetSq (I := I) (M := M) g 2 E3T ≤ AK ^ 2 := by
    simpa only [E3T, AK, sf3, lowJetSq, Nat.reduceAdd] using
      slotIter_h2b (I := I) (M := M) g 0 3 3 KbT BK
        (by simpa only [lowJetSq, Nat.reduceAdd] using hKbT)
  have hE3U : lowJetSq (I := I) (M := M) g 2 E3U ≤ AK ^ 2 := by
    simpa only [E3U, AK, sf3, lowJetSq, Nat.reduceAdd] using
      slotIter_h2b (I := I) (M := M) g 0 3 3 KbU BK
        (by simpa only [lowJetSq, Nat.reduceAdd] using hKbU)
  have hE3D : lowJetSq (I := I) (M := M) g 2 (E3T - E3U) ≤
      (DK * N) ^ 2 := by
    rw [show E3T - E3U =
        slotExtendIter (I := I) (M := M) g 0 3 3 (KbT - KbU) by
      dsimp only [E3T, E3U]
      rw [slotIter_sub]]
    have hs := slotIter_h2b (I := I) (M := M) g 0 3 3
      (KbT - KbU) (CK * N)
      (by simpa only [lowJetSq, Nat.reduceAdd] using hKbD)
    simpa only [lowJetSq, Nat.reduceAdd, DK, sf3, mul_assoc] using hs
  have hS4T : lowJetSq (I := I) (M := M) g 2 S4T ≤ (A4 * A) ^ 2 := by
    have hs := hone3 Tr3T S5T Bt3 (A5 * A) hBt3
      (mul_nonneg hA5 hA) hTr3T hS5T
    calc
      _ ≤ (O3 * Bt3 * (A5 * A)) ^ 2 := by simpa only [S4T] using hs
      _ = (A4 * A) ^ 2 := by dsimp only [A4]; ring
  have hS4D : lowJetSq (I := I) (M := M) g 2 (S4T - S4U) ≤
      (D40 * D3 + D41 * A * N) ^ 2 := by
    have hp := hpair3 Tr3T Tr3U S5T S5U (Ct3 * N) Bt3
      (A5 * A) (D5 * D3) (mul_nonneg hCt3 hN) hBt3
      (mul_nonneg hA5 hA) (mul_nonneg hD5 hD3)
      hTr3D hTr3U hS5T hS5D
    calc
      _ ≤ (P3 * ((Ct3 * N) * (A5 * A) + Bt3 * (D5 * D3))) ^ 2 := by
        simpa only [S4T, S4U] using hp
      _ = (D40 * D3 + D41 * A * N) ^ 2 := by
        dsimp only [D40, D41]
        ring
  have hS3T : lowJetSq (I := I) (M := M) g 2 S3T ≤ (A3 * A) ^ 2 := by
    have hs := honek E3T S4T AK (A4 * A) hAK
      (mul_nonneg hA4 hA) hE3T hS4T
    calc
      _ ≤ (Ok * AK * (A4 * A)) ^ 2 := by simpa only [S3T] using hs
      _ = (A3 * A) ^ 2 := by dsimp only [A3]; ring
  have hS3D : lowJetSq (I := I) (M := M) g 2 (S3T - S3U) ≤
      (D30 * D3 + D31 * A * N) ^ 2 := by
    have hp := hpairk E3T E3U S4T S4U (DK * N) AK
      (A4 * A) (D40 * D3 + D41 * A * N)
      (mul_nonneg hDK hN) hAK (mul_nonneg hA4 hA)
      (add_nonneg (mul_nonneg hD40 hD3)
        (mul_nonneg (mul_nonneg hD41 hA) hN))
      hE3D hE3U hS4T hS4D
    calc
      _ ≤ (Pk * ((DK * N) * (A4 * A) +
          AK * (D40 * D3 + D41 * A * N))) ^ 2 := by
        simpa only [S3T, S3U] using hp
      _ = (D30 * D3 + D31 * A * N) ^ 2 := by
        dsimp only [D30, D31]
        ring
  have hS2T : lowJetSq (I := I) (M := M) g 2 S2T ≤ (A2 * A) ^ 2 := by
    have hs := hone4 Tr4T S3T Bt4 (A3 * A) hBt4
      (mul_nonneg hA3 hA) hTr4T hS3T
    calc
      _ ≤ (O4 * Bt4 * (A3 * A)) ^ 2 := by simpa only [S2T] using hs
      _ = (A2 * A) ^ 2 := by dsimp only [A2]; ring
  have hS2D : lowJetSq (I := I) (M := M) g 2 (S2T - S2U) ≤
      (D20 * D3 + D21 * A * N) ^ 2 := by
    have hp := hpair4 Tr4T Tr4U S3T S3U (Ct4 * N) Bt4
      (A3 * A) (D30 * D3 + D31 * A * N)
      (mul_nonneg hCt4 hN) hBt4 (mul_nonneg hA3 hA)
      (add_nonneg (mul_nonneg hD30 hD3)
        (mul_nonneg (mul_nonneg hD31 hA) hN))
      hTr4D hTr4U hS3T hS3D
    calc
      _ ≤ (P4 * ((Ct4 * N) * (A3 * A) +
          Bt4 * (D30 * D3 + D31 * A * N))) ^ 2 := by
        simpa only [S2T, S2U] using hp
      _ = (D20 * D3 + D21 * A * N) ^ 2 := by
        dsimp only [D20, D21]
        ring
  have hp := hpair2 Tr2T Tr2U S2T S2U (Ct2 * N) Bt2
    (A2 * A) (D20 * D3 + D21 * A * N)
    (mul_nonneg hCt2 hN) hBt2 (mul_nonneg hA2 hA)
    (add_nonneg (mul_nonneg hD20 hD3)
      (mul_nonneg (mul_nonneg hD21 hA) hN))
    hTr2D hTr2U hS2T hS2D
  have hhalfT : bgAmixHalf (I := I) (M := M) g gT gB σ =
      appCcRS (I := I) (M := M) g 2 4 2 Tr2T S2T := by rfl
  have hhalfU : bgAmixHalf (I := I) (M := M) g gU gB σ =
      appCcRS (I := I) (M := M) g 2 4 2 Tr2U S2U := by rfl
  rw [hhalfT, hhalfU]
  calc
    _ ≤ (P2 * ((Ct2 * N) * (A2 * A) +
        Bt2 * (D20 * D3 + D21 * A * N))) ^ 2 := hp
    _ = (B0 * D3 + B1 * A * N) ^ 2 := by
      dsimp only [B0, B1]
      ring

set_option maxHeartbeats 2400000 in
/-- The arbitrary-background mixed order-zero correction is `H2`-Lipschitz on
a common spectral `H2` ball, in the critical `H3/H2` two-state currency. -/
theorem amixBg_pair_h2
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M) :
    ∃ ρ B0 B1 : ℝ,
      0 < ρ ∧ 0 ≤ B0 ∧ 0 ≤ B1 ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2),
        (∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v) →
        (∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ (A D3 : ℝ), 0 ≤ A → 0 ≤ D3 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        lowJetSq (I := I) (M := M) g 2
            ((lc0AMix (I := I) (M := M) g gT gB -
                lc0AMix (I := I) (M := M) g gT g) -
              (lc0AMix (I := I) (M := M) g gU gB -
                lc0AMix (I := I) (M := M) g gU g)) ≤
          (B0 * D3 +
            B1 * ‖ccTensorToHs (I := I) (M := M)
              g 2 (2 : ℝ) (T - U)‖ +
            B1 * A * ‖ccTensorToHs (I := I) (M := M)
              g 2 (2 : ℝ) (T - U)‖) ^ 2 := by
  obtain ⟨ρ, C0, C1, hρ, hC0, hC1, hhalf⟩ :=
    amixHalfH2 (I := I) (M := M) hDim g gB
  let B0 : ℝ := 4 * C0
  let B1 : ℝ := 4 * C1
  have hB0 : 0 ≤ B0 := mul_nonneg (by norm_num) hC0
  have hB1 : 0 ≤ B1 := mul_nonneg (by norm_num) hC1
  refine ⟨ρ, B0, B1, hρ, hB0, hB1, ?_⟩
  intro gT gU T U hTtie hUtie hTHs hUHs A D3 hA hD3 hT3 hTU3
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  let Q : ℝ := C0 * D3 + C1 * A * N
  let Q' : ℝ := C0 * D3 + C1 * N + C1 * A * N
  have hN : 0 ≤ N := norm_nonneg _
  have hQ : 0 ≤ Q :=
    add_nonneg (mul_nonneg hC0 hD3) (mul_nonneg (mul_nonneg hC1 hA) hN)
  have hQ' : 0 ≤ Q' :=
    add_nonneg (add_nonneg (mul_nonneg hC0 hD3) (mul_nonneg hC1 hN))
      (mul_nonneg (mul_nonneg hC1 hA) hN)
  have hQQ' : Q ≤ Q' := by
    dsimp only [Q, Q']
    nlinarith [mul_nonneg hC1 hN]
  let D0 : SmoothCcTensor g 2 2 :=
    bgAmixHalf (I := I) (M := M) g gT gB lieCorr0AMixPerm2 -
      bgAmixHalf (I := I) (M := M) g gU gB lieCorr0AMixPerm2
  let D1 : SmoothCcTensor g 2 2 :=
    bgAmixHalf (I := I) (M := M) g gT gB
        (lc0SwapPermRF * lieCorr0AMixPerm2) -
      bgAmixHalf (I := I) (M := M) g gU gB
        (lc0SwapPermRF * lieCorr0AMixPerm2)
  have hD0 : lowJetSq (I := I) (M := M) g 2 D0 ≤ Q ^ 2 := by
    simpa only [D0, Q, N] using hhalf lieCorr0AMixPerm2 T U gT gU
      hTtie hUtie hTHs hUHs A D3 hA hD3 hT3 hTU3
  have hD1 : lowJetSq (I := I) (M := M) g 2 D1 ≤ Q ^ 2 := by
    simpa only [D1, Q, N] using
      hhalf (lc0SwapPermRF * lieCorr0AMixPerm2) T U gT gU
        hTtie hUtie hTHs hUHs A D3 hA hD3 hT3 hTU3
  have hsum : lowJetSq (I := I) (M := M) g 2 (D0 + D1) ≤
      (2 * Q) ^ 2 := by
    calc
      _ ≤ 2 * (lowJetSq (I := I) (M := M) g 2 D0 +
          lowJetSq (I := I) (M := M) g 2 D1) :=
        jetAdd (I := I) (M := M) g 2 D0 D1
      _ ≤ 2 * (Q ^ 2 + Q ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hD0 hD1) (by norm_num)
      _ = (2 * Q) ^ 2 := by ring
  have heq :
      (lc0AMix (I := I) (M := M) g gT gB -
          lc0AMix (I := I) (M := M) g gT g) -
        (lc0AMix (I := I) (M := M) g gU gB -
          lc0AMix (I := I) (M := M) g gU g) =
      (2 : ℝ) • (D0 + D1) := by
    rw [bgAmix_eq (I := I) (M := M) g gT gB,
      bgAmix_eq (I := I) (M := M) g gU gB]
    dsimp only [D0, D1]
    module
  rw [heq, jetSmul]
  norm_num
  calc
    4 * lowJetSq (I := I) (M := M) g 2 (D0 + D1) ≤
        4 * (2 * Q) ^ 2 := mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = (4 * Q) ^ 2 := by ring
    _ ≤ (4 * Q') ^ 2 := pow_le_pow_left₀
      (mul_nonneg (by norm_num) hQ)
      (mul_le_mul_of_nonneg_left hQQ' (by norm_num)) 2
    _ = (B0 * D3 + B1 * N + B1 * A * N) ^ 2 := by
      dsimp only [B0, B1, Q', N]
      ring

set_option maxHeartbeats 3200000 in
/-- The three-term Palatini telescope for `lieBgLow` preserves prescribed
`H2` root bounds for its two moving factors. -/
private theorem lieBgLow_raw_h2
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M) :
    ∃ P Q : ℝ, 0 ≤ P ∧ 0 ≤ Q ∧
      ∀ (gT gU : SmoothRiemannianMetric I M) (X Y : ℝ),
        0 ≤ X → 0 ≤ Y →
        lowJetSq (I := I) (M := M) g 2
            (connDiffLoweredCc (I := I) g gT -
              connDiffLoweredCc (I := I) g gU) ≤ X ^ 2 →
        lowJetSq (I := I) (M := M) g 2
            (lieCovArm2 (I := I) (M := M) g gT -
              lieCovArm2 (I := I) (M := M) g gU) ≤ Y ^ 2 →
        lowJetSq (I := I) (M := M) g 2
            (lieBgLow (I := I) (M := M) g gT gB -
              lieBgLow (I := I) (M := M) g gU gB) ≤
          (P * X + Q * Y) ^ 2 := by
  obtain ⟨Ca, hCa, happ⟩ :=
    appRoot_h2 (I := I) (M := M) hDim g 0 3 4
  let JA : ℝ := lowJetSq (I := I) (M := M) g 2
    (lieCovArm2 (I := I) (M := M) g gB)
  let JC : ℝ := lowJetSq (I := I) (M := M) g 2
    (connDiffLoweredCc (I := I) g gB)
  let KA : ℝ := Real.sqrt JA
  let KC : ℝ := Real.sqrt JC
  let P : ℝ := 2 * Ca * KA
  let Q : ℝ := 3 * Ca * KC
  have hJA : 0 ≤ JA := jetNn (I := I) (M := M) (m := 2) g _
  have hJC : 0 ≤ JC := jetNn (I := I) (M := M) (m := 2) g _
  have hKA : 0 ≤ KA := Real.sqrt_nonneg _
  have hKC : 0 ≤ KC := Real.sqrt_nonneg _
  have hKAsq : KA ^ 2 = JA := by
    simpa only [KA] using Real.sq_sqrt hJA
  have hKCsq : KC ^ 2 = JC := by
    simpa only [KC] using Real.sq_sqrt hJC
  have hP : 0 ≤ P := mul_nonneg (mul_nonneg (by norm_num) hCa) hKA
  have hQ : 0 ≤ Q := mul_nonneg (mul_nonneg (by norm_num) hCa) hKC
  refine ⟨P, Q, hP, hQ, ?_⟩
  intro gT gU X Y hX hY hconn harm
  let X1 : SmoothCcTensor g 0 4 :=
    domDomCongrSection (I := I) g (lieBgPerm 0)
      (appCcRS (I := I) (M := M) g 0 3 4
        (lieCovArm2 (I := I) (M := M) g gB)
        (connDiffLoweredCc (I := I) g gT -
          connDiffLoweredCc (I := I) g gU))
  let X2 : SmoothCcTensor g 0 4 :=
    domDomCongrSection (I := I) g (lieBgPerm 1)
      (appCcRS (I := I) (M := M) g 0 3 4
        (lieCovArm2 (I := I) (M := M) g gT -
          lieCovArm2 (I := I) (M := M) g gU)
        (connDiffLoweredCc (I := I) g gB))
  let X3 : SmoothCcTensor g 0 4 :=
    domDomCongrSection (I := I) g (lieBgPerm 2)
      (appCcRS (I := I) (M := M) g 0 3 4
        (lieCovArm2 (I := I) (M := M) g gT -
          lieCovArm2 (I := I) (M := M) g gU)
        (connDiffLoweredCc (I := I) g gB))
  let a : ℝ := Ca * KA * X
  let b : ℝ := Ca * Y * KC
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hX1 : lowJetSq (I := I) (M := M) g 2 X1 ≤ a ^ 2 := by
    dsimp only [X1]
    rw [domH2]
    exact happ _ _ KA X hKA hX (le_of_eq hKAsq.symm) hconn
  have hX2 : lowJetSq (I := I) (M := M) g 2 X2 ≤ b ^ 2 := by
    dsimp only [X2]
    rw [domH2]
    exact happ _ _ Y KC hY hKC harm (le_of_eq hKCsq.symm)
  have hX3 : lowJetSq (I := I) (M := M) g 2 X3 ≤ b ^ 2 := by
    dsimp only [X3]
    rw [domH2]
    exact happ _ _ Y KC hY hKC harm (le_of_eq hKCsq.symm)
  have h12sum := jetAdd (I := I) (M := M) g 2 ((-1 : ℝ) • X1) X2
  have h123sum := jetAdd (I := I) (M := M) g 2
    ((-1 : ℝ) • X1 + X2) X3
  have hneg : lowJetSq (I := I) (M := M) g 2 ((-1 : ℝ) • X1) =
      lowJetSq (I := I) (M := M) g 2 X1 := by
    rw [jetSmul]
    norm_num
  have hsum : lowJetSq (I := I) (M := M) g 2
      (((-1 : ℝ) • X1 + X2) + X3) ≤
        4 * lowJetSq (I := I) (M := M) g 2 X1 +
          4 * lowJetSq (I := I) (M := M) g 2 X2 +
          2 * lowJetSq (I := I) (M := M) g 2 X3 := by
    rw [hneg] at h12sum
    nlinarith
  rw [lieBgLow_sub (I := I) (M := M) g gT gU gB]
  change lowJetSq (I := I) (M := M) g 2
    (((-1 : ℝ) • X1 + X2) + X3) ≤ _
  calc
    _ ≤ 4 * a ^ 2 + 6 * b ^ 2 := by
      nlinarith [hsum, hX1, hX2, hX3]
    _ ≤ (2 * a + 3 * b) ^ 2 := by
      nlinarith [mul_nonneg ha hb, sq_nonneg b]
    _ = (P * X + Q * Y) ^ 2 := by
      dsimp only [a, b, P, Q]
      ring

set_option maxHeartbeats 3200000 in
set_option linter.unusedVariables false in
/-- The fixed-background low `DLa` coefficient is `H2`-Lipschitz in the
critical `H3/H2` two-state currency.  The background is arbitrary but fixed;
all spectral smallness is imposed only on the two moving metrics. -/
private theorem lieBgLow_pair_h2
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
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
        {δ : ℝ} (hδ_le : δ ≤ (1 : ℝ) / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (R A D2 D3 : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        lowJetSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      lowJetSq (I := I) (M := M) g 2
          (lieBgLow (I := I) (M := M) g gT gB -
            lieBgLow (I := I) (M := M) g gU gB) ≤
        (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 := by
  obtain ⟨P, Q, hP, hQ, hraw⟩ :=
    lieBgLow_raw_h2 (I := I) (M := M) hDim g gB
  obtain ⟨W0, W1, hW0, hW1, hw⟩ :=
    wXi_sub_tame (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨S0, S1, hS0, hS1, hs⟩ :=
    armPairH2 (I := I) (M := M) hDim g
  let fr : ℝ := Module.finrank ℝ E
  let B0 : ℝ → ℝ := fun R => P * W0 R + Q * (fr * S0 R)
  let B1 : ℝ → ℝ := fun R => P * W1 R + Q * (fr * S1 R)
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨B0, B1, ?_, ?_, ?_⟩
  · intro R hR
    exact add_nonneg (mul_nonneg hP (hW0 R hR))
      (mul_nonneg hQ (mul_nonneg hfr (hS0 R hR)))
  · intro R hR
    exact add_nonneg (mul_nonneg hP (hW1 R hR))
      (mul_nonneg hQ (mul_nonneg hfr (hS1 R hR)))
  · intro gT gU T U hT hU hTtie hUtie δ hδ_le hδ0 hδT hδU
      R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
    let X : ℝ := W0 R * D3 + W1 R * D2 + W1 R * A * D2
    let Y : ℝ := fr * S0 R * D3 + fr * S1 R * D2 +
      fr * S1 R * A * D2
    have hX : 0 ≤ X :=
      add_nonneg
        (add_nonneg (mul_nonneg (hW0 R hR) hD3)
          (mul_nonneg (hW1 R hR) hD2))
        (mul_nonneg (mul_nonneg (hW1 R hR) hA) hD2)
    have hY : 0 ≤ Y :=
      add_nonneg
        (add_nonneg (mul_nonneg (mul_nonneg hfr (hS0 R hR)) hD3)
          (mul_nonneg (mul_nonneg hfr (hS1 R hR)) hD2))
        (mul_nonneg (mul_nonneg (mul_nonneg hfr (hS1 R hR)) hA) hD2)
    have hconnEq :
        wXi (I := I) (M := M) g gT g -
            wXi (I := I) (M := M) g gU g =
          connDiffLoweredCc (I := I) g gT -
            connDiffLoweredCc (I := I) g gU := by
      simp only [wXi]
      module
    have hconn : lowJetSq (I := I) (M := M) g 2
        (connDiffLoweredCc (I := I) g gT -
          connDiffLoweredCc (I := I) g gU) ≤ X ^ 2 := by
      rw [← hconnEq]
      dsimp only [X]
      exact hw gT gU g T U hT hU hTtie hUtie
        hδ_le hδ0 hδT hδ_le hδ0 hδU
        R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
    have harm : lowJetSq (I := I) (M := M) g 2
        (lieCovArm2 (I := I) (M := M) g gT -
          lieCovArm2 (I := I) (M := M) g gU) ≤ Y ^ 2 := by
      rw [lieCovArm2, lieCovArm2]
      dsimp only [Y, fr]
      exact hs gT gU T U hT hU hTtie hUtie hδ_le hδ0 hδT hδU
        R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
    calc
      _ ≤ (P * X + Q * Y) ^ 2 := hraw gT gU X Y hX hY hconn harm
      _ = (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 := by
        dsimp only [B0, B1, X, Y]
        ring

set_option maxHeartbeats 2400000 in
set_option linter.unusedVariables false in
/-- The fixed-background low `DLa` coefficient has an `H2` single-state
bound obtained from its two-state estimate against the zero perturbation. -/
private theorem lieBgLow_bdd_h2
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M) :
    ∃ C0 C1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ C0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ C1 R) ∧
      ∀ (gT : SmoothRiemannianMetric I M)
        (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δ : ℝ} (hδ_le : δ ≤ (1 : ℝ) / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      lowJetSq (I := I) (M := M) g 2
          (lieBgLow (I := I) (M := M) g gT gB) ≤
        (C0 R + C1 R * A) ^ 2 := by
  obtain ⟨B0, B1, hB0, hB1, hpair⟩ :=
    lieBgLow_pair_h2 (I := I) (M := M) hDim g gB
  let J0 : ℝ := lowJetSq (I := I) (M := M) g 2
    (lieBgLow (I := I) (M := M) g g gB)
  let K : ℝ := Real.sqrt J0
  let C0 : ℝ → ℝ := fun R => 2 * (K + B1 0 * R)
  let C1 : ℝ → ℝ := fun R => 2 * (B0 0 + B1 0 * R)
  have hJ0 : 0 ≤ J0 := jetNn (I := I) (M := M) (m := 2) g _
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  have hKsq : K ^ 2 = J0 := by
    simpa only [K] using Real.sq_sqrt hJ0
  refine ⟨C0, C1, ?_, ?_, ?_⟩
  · intro R hR
    exact mul_nonneg (by norm_num)
      (add_nonneg hK (mul_nonneg (hB1 0 (by norm_num)) hR))
  · intro R hR
    exact mul_nonneg (by norm_num)
      (add_nonneg (hB0 0 (by norm_num))
        (mul_nonneg (hB1 0 (by norm_num)) hR))
  · intro gT T hT hTtie δ hδ_le hδ0 hδT R A hR hA hT2 hT3
    have hzero : ∀ (x : M) (u v : TangentSpace I x),
        ccTensorBilin (I := I) g (0 : SmoothCcTensor g 0 2) x u v =
          ccTensorBilin (I := I) g (0 : SmoothCcTensor g 0 2) x v u := by
      intro x u v
      rw [ccTensorBilin_zero_weight, ccTensorBilin_zero_weight]
    have hzeroTie : ∀ (x : M) (u v : TangentSpace I x),
        g.inner x u v = g.inner x u v +
          ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2) x u v := by
      intro x u v
      rw [ccTensorBilinSymm_apply, ccTensorBilin_zero_weight,
        ccTensorBilin_zero_weight]
      ring
    have hzeroOp : gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g
          (0 : SmoothCcTensor g 0 2)) δ := by
      intro x v w
      rw [ccTensorBilinSymm_apply, ccTensorBilin_zero_weight,
        ccTensorBilin_zero_weight]
      simpa only [zero_add, mul_zero, abs_zero] using
        (mul_nonneg (mul_nonneg hδ0 (Real.sqrt_nonneg (g.inner x v v)))
          (Real.sqrt_nonneg (g.inner x w w)))
    have hz2 : lowJetSq (I := I) (M := M) g 2
        (0 : SmoothCcTensor g 0 2) ≤ (0 : ℝ) ^ 2 := by
      rw [jetZero]
      norm_num
    have hTU2 : lowJetSq (I := I) (M := M) g 2
        (T - (0 : SmoothCcTensor g 0 2)) ≤ R ^ 2 := by
      simpa only [sub_zero] using hT2
    have hTU3 : lowJetSq (I := I) (M := M) g 3
        (T - (0 : SmoothCcTensor g 0 2)) ≤ A ^ 2 := by
      simpa only [sub_zero] using hT3
    have hpair0 : lowJetSq (I := I) (M := M) g 2
        (lieBgLow (I := I) (M := M) g gT gB -
          lieBgLow (I := I) (M := M) g g gB) ≤
        (B0 0 * A + B1 0 * R + B1 0 * A * R) ^ 2 :=
      hpair gT g T (0 : SmoothCcTensor g 0 2)
        hT hzero hTtie hzeroTie hδ_le hδ0 hδT hzeroOp
        0 A R A (by norm_num) hA hR hA hz2 hT3 hTU2 hTU3
    have hdecomp : lieBgLow (I := I) (M := M) g gT gB =
        (lieBgLow (I := I) (M := M) g gT gB -
          lieBgLow (I := I) (M := M) g g gB) +
        lieBgLow (I := I) (M := M) g g gB := by
      module
    let L : ℝ := B0 0 * A + B1 0 * R + B1 0 * A * R
    have hL : 0 ≤ L := by
      dsimp only [L]
      exact add_nonneg
        (add_nonneg (mul_nonneg (hB0 0 (by norm_num)) hA)
          (mul_nonneg (hB1 0 (by norm_num)) hR))
        (mul_nonneg (mul_nonneg (hB1 0 (by norm_num)) hA) hR)
    have hmain : lowJetSq (I := I) (M := M) g 2
        (lieBgLow (I := I) (M := M) g gT gB) ≤
          2 * (L ^ 2 + J0) := by
      rw [hdecomp]
      exact (jetAdd (I := I) (M := M) g 2 _ _).trans
        (mul_le_mul_of_nonneg_left
          (add_le_add (by simpa only [L] using hpair0) le_rfl) (by norm_num))
    calc
      lowJetSq (I := I) (M := M) g 2
          (lieBgLow (I := I) (M := M) g gT gB) ≤
        2 * (L ^ 2 + J0) := hmain
      _ = 2 * (L ^ 2 + K ^ 2) := by rw [hKsq]
      _ ≤ (2 * (K + L)) ^ 2 := by
        nlinarith [mul_nonneg hK hL]
      _ = (C0 R + C1 R * A) ^ 2 := by
        dsimp only [C0, C1, L]
        ring

/-- The raised slot-three factor is Lipschitz in the metric perturbation at
the `H²` jet level. -/
private theorem rev3_pair_h2
    (g gT gU : SmoothRiemannianMetric I M)
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
        g.inner x u v + ccTensorBilinSymm (I := I) g U x u v) :
    lowJetSq (I := I) (M := M) g 2
        (slotInsertEndoCc (I := I) (M := M) g 3
            (fullRaisedEndoField (I := I) (M := M) gT g) -
          slotInsertEndoCc (I := I) (M := M) g 3
            (fullRaisedEndoField (I := I) (M := M) gU g)) ≤
      (Module.finrank ℝ E : ℝ) ^ 3 *
        lowJetSq (I := I) (M := M) g 2 (T - U) := by
  have hsymm : symmS (I := I) (M := M) g (T - U) = T - U := by
    rw [symmS_sub,
      symmS_eq_self_of_ccTensorBilin_symm (I := I) (M := M) g T hT,
      symmS_eq_self_of_ccTensorBilin_symm (I := I) (M := M) g U hU]
  rw [← slotInsertEndoCc_sub,
    LowBaseInternal.fullRev_sub (I := I) (M := M)
      g gT gU T U hTtie hUtie]
  exact perturb_jet (I := I) (M := M) g 3 2 (T - U) hsymm

set_option linter.unusedVariables false in
/-- A background-dependent `H²` bound for the raised slot-three factor,
with all state dependence recorded by the prescribed radius. -/
private theorem rev3_bdd_h2
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ B R) ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        (R : ℝ),
        lowJetSq (I := I) (M := M) g 2 P ≤ R ^ 2 →
      lowJetSq (I := I) (M := M) g 2
          (slotInsertEndoCc (I := I) (M := M) g 3
            (fullRaisedEndoField (I := I) (M := M) gm g)) ≤
        (B R) ^ 2 := by
  let A0 : SmoothCcTensor g 4 4 :=
    slotInsertEndoCc (I := I) (M := M) g 3
      (fullRaisedEndoField (I := I) (M := M) g g)
  let J0 : ℝ := lowJetSq (I := I) (M := M) g 2 A0
  let fr : ℝ := Module.finrank ℝ E
  let L : ℝ → ℝ := fun R => 2 * (fr ^ 3 * R ^ 2 + J0)
  let B : ℝ → ℝ := fun R => Real.sqrt (L R)
  have hJ0 : 0 ≤ J0 := jetNn (I := I) (M := M) (m := 2) g A0
  refine ⟨B, fun R => Real.sqrt_nonneg _, ?_⟩
  intro gm P hP htie R hP2
  have hzero : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g (0 : SmoothCcTensor g 0 2) x u v =
        ccTensorBilin (I := I) g (0 : SmoothCcTensor g 0 2) x v u := by
    intro x u v
    rw [ccTensorBilin_zero_weight, ccTensorBilin_zero_weight]
  have hzeroTie : ∀ (x : M) (u v : TangentSpace I x),
      g.inner x u v = g.inner x u v +
        ccTensorBilinSymm (I := I) g
          (0 : SmoothCcTensor g 0 2) x u v := by
    intro x u v
    rw [ccTensorBilinSymm_apply, ccTensorBilin_zero_weight,
      ccTensorBilin_zero_weight]
    ring
  let A : SmoothCcTensor g 4 4 :=
    slotInsertEndoCc (I := I) (M := M) g 3
      (fullRaisedEndoField (I := I) (M := M) gm g)
  have hpair : lowJetSq (I := I) (M := M) g 2 (A - A0) ≤
      fr ^ 3 * lowJetSq (I := I) (M := M) g 2 P := by
    simpa only [A, A0, fr, sub_zero] using
      rev3_pair_h2 (I := I) (M := M) g gm g P
        (0 : SmoothCcTensor g 0 2) hP hzero htie hzeroTie
  have hpairR : lowJetSq (I := I) (M := M) g 2 (A - A0) ≤
      fr ^ 3 * R ^ 2 :=
    hpair.trans (mul_le_mul_of_nonneg_left hP2 (by positivity))
  have hL : 0 ≤ L R := by
    dsimp only [L]
    exact mul_nonneg (by norm_num)
      (add_nonneg (mul_nonneg (by positivity) (sq_nonneg R)) hJ0)
  have hBsq : (B R) ^ 2 = L R := by
    simpa only [B] using Real.sq_sqrt hL
  have hAeq : A = (A - A0) + A0 := by module
  change lowJetSq (I := I) (M := M) g 2 A ≤ (B R) ^ 2
  rw [hAeq]
  calc
    lowJetSq (I := I) (M := M) g 2 ((A - A0) + A0) ≤
        2 * (lowJetSq (I := I) (M := M) g 2 (A - A0) +
          lowJetSq (I := I) (M := M) g 2 A0) :=
      jetAdd (I := I) (M := M) g 2 (A - A0) A0
    _ ≤ 2 * (fr ^ 3 * R ^ 2 + J0) :=
      mul_le_mul_of_nonneg_left
        (add_le_add hpairR le_rfl) (by norm_num)
    _ = L R := by rfl
    _ = (B R) ^ 2 := hBsq.symm

set_option maxHeartbeats 3200000 in
set_option linter.unusedVariables false in
/-- The full fixed-background `DLa` core is `H²`-Lipschitz in the critical
`H³/H²` two-state currency. -/
private theorem lieBgCore_pair_h2
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
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
        {δ : ℝ} (hδ_le : δ ≤ (1 : ℝ) / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (R A D2 D3 : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        lowJetSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      lowJetSq (I := I) (M := M) g 2
          (lieBgCore (I := I) (M := M) g gT gB -
            lieBgCore (I := I) (M := M) g gU gB) ≤
        (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 := by
  obtain ⟨Br, hBr, hrev⟩ := rev3_bdd_h2 (I := I) (M := M) g
  obtain ⟨C, hC, happ⟩ := appPairH2 (I := I) (M := M) hDim g 0 4 4
  obtain ⟨P0, P1, hP0, hP1, hlowPair⟩ :=
    lieBgLow_pair_h2 (I := I) (M := M) hDim g gB
  obtain ⟨D0, D1, hD0, hD1, hlowBdd⟩ :=
    lieBgLow_bdd_h2 (I := I) (M := M) hDim g gB
  let fr : ℝ := Module.finrank ℝ E
  let sf : ℝ := Real.sqrt (fr ^ 3)
  let B0 : ℝ → ℝ := fun R => 2 * C * (Br R * P0 R)
  let B1 : ℝ → ℝ := fun R =>
    2 * C * (sf * (D0 R + D1 R) + Br R * P1 R)
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hsf : 0 ≤ sf := Real.sqrt_nonneg _
  have hsfSq : sf ^ 2 = fr ^ 3 := by
    simpa only [sf] using Real.sq_sqrt (pow_nonneg hfr 3)
  refine ⟨B0, B1, ?_, ?_, ?_⟩
  · intro R hR
    exact mul_nonneg (mul_nonneg (by norm_num) hC)
      (mul_nonneg (hBr R) (hP0 R hR))
  · intro R hR
    exact mul_nonneg (mul_nonneg (by norm_num) hC)
      (add_nonneg
        (mul_nonneg hsf (add_nonneg (hD0 R hR) (hD1 R hR)))
        (mul_nonneg (hBr R) (hP1 R hR)))
  · intro gT gU T U hT hU hTtie hUtie δ hδ_le hδ0 hδT hδU
      R A D2 D3 hR hA hD2 hD3 hT2 hU2 hT3 hTU2 hTU3
    let ST : SmoothCcTensor g 4 4 :=
      slotInsertEndoCc (I := I) (M := M) g 3
        (fullRaisedEndoField (I := I) (M := M) gT g)
    let SU : SmoothCcTensor g 4 4 :=
      slotInsertEndoCc (I := I) (M := M) g 3
        (fullRaisedEndoField (I := I) (M := M) gU g)
    let LT : SmoothCcTensor g 0 4 :=
      lieBgLow (I := I) (M := M) g gT gB
    let LU : SmoothCcTensor g 0 4 :=
      lieBgLow (I := I) (M := M) g gU gB
    let HT : SmoothCcTensor g 0 4 :=
      appCcRS (I := I) (M := M) g 0 4 4 ST LT
    let HU : SmoothCcTensor g 0 4 :=
      appCcRS (I := I) (M := M) g 0 4 4 SU LU
    let FD : ℝ := sf * D2
    let FB : ℝ := Br R
    let WB : ℝ := D0 R + D1 R * A
    let WD : ℝ := P0 R * D3 + P1 R * D2 + P1 R * A * D2
    have hFD : 0 ≤ FD := mul_nonneg hsf hD2
    have hFB : 0 ≤ FB := hBr R
    have hWB : 0 ≤ WB :=
      add_nonneg (hD0 R hR) (mul_nonneg (hD1 R hR) hA)
    have hWD : 0 ≤ WD :=
      add_nonneg
        (add_nonneg (mul_nonneg (hP0 R hR) hD3)
          (mul_nonneg (hP1 R hR) hD2))
        (mul_nonneg (mul_nonneg (hP1 R hR) hA) hD2)
    have hSD : lowJetSq (I := I) (M := M) g 2 (ST - SU) ≤ FD ^ 2 := by
      refine (rev3_pair_h2 (I := I) (M := M) g gT gU T U
        hT hU hTtie hUtie).trans ?_
      calc
        fr ^ 3 * lowJetSq (I := I) (M := M) g 2 (T - U) ≤
            fr ^ 3 * D2 ^ 2 :=
          mul_le_mul_of_nonneg_left hTU2 (pow_nonneg hfr 3)
        _ = FD ^ 2 := by
          simp only [FD, mul_pow, hsfSq]
    have hSU : lowJetSq (I := I) (M := M) g 2 SU ≤ FB ^ 2 := by
      simpa only [SU, FB] using hrev gU U hU hUtie R hU2
    have hLT : lowJetSq (I := I) (M := M) g 2 LT ≤ WB ^ 2 := by
      simpa only [LT, WB] using
        hlowBdd gT T hT hTtie hδ_le hδ0 hδT R A hR hA hT2 hT3
    have hLD : lowJetSq (I := I) (M := M) g 2 (LT - LU) ≤ WD ^ 2 := by
      simpa only [LT, LU, WD] using
        hlowPair gT gU T U hT hU hTtie hUtie hδ_le hδ0 hδT hδU
          R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
    have hhalf : lowJetSq (I := I) (M := M) g 2 (HT - HU) ≤
        (C * (FD * WB + FB * WD)) ^ 2 := by
      simpa only [HT, HU] using
        happ ST SU LT LU FD FB WB WD hFD hFB hWB hWD hSD hSU hLT hLD
    have hcore : lieBgCore (I := I) (M := M) g gT gB -
        lieBgCore (I := I) (M := M) g gU gB =
        domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1) (HT - HU) +
          (HT - HU) := by
      rw [lieBgCore, lieBgCore]
      change (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1) HT + HT) -
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1) HU + HU) = _
      rw [domSub]
      module
    have hcoreJet : lowJetSq (I := I) (M := M) g 2
        (lieBgCore (I := I) (M := M) g gT gB -
          lieBgCore (I := I) (M := M) g gU gB) ≤
        4 * lowJetSq (I := I) (M := M) g 2 (HT - HU) := by
      rw [hcore]
      calc
        lowJetSq (I := I) (M := M) g 2
            (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1) (HT - HU) +
              (HT - HU)) ≤
          2 * (lowJetSq (I := I) (M := M) g 2
              (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1) (HT - HU)) +
            lowJetSq (I := I) (M := M) g 2 (HT - HU)) :=
          jetAdd (I := I) (M := M) g 2 _ _
        _ = 4 * lowJetSq (I := I) (M := M) g 2 (HT - HU) := by
          rw [domH2]
          ring
    let Z : ℝ := 2 * C * (FD * WB + FB * WD)
    let Qout : ℝ := B0 R * D3 + B1 R * D2 + B1 R * A * D2
    have hZ : 0 ≤ Z :=
      mul_nonneg (mul_nonneg (by norm_num) hC)
        (add_nonneg (mul_nonneg hFD hWB) (mul_nonneg hFB hWD))
    have hmain : lowJetSq (I := I) (M := M) g 2
        (lieBgCore (I := I) (M := M) g gT gB -
          lieBgCore (I := I) (M := M) g gU gB) ≤ Z ^ 2 :=
      hcoreJet.trans <| calc
        4 * lowJetSq (I := I) (M := M) g 2 (HT - HU) ≤
            4 * (C * (FD * WB + FB * WD)) ^ 2 :=
          mul_le_mul_of_nonneg_left hhalf (by norm_num)
        _ = Z ^ 2 := by
          dsimp only [Z]
          ring
    have he0 : 0 ≤ 2 * C * sf * D1 R * D2 :=
      mul_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC) hsf)
          (hD1 R hR)) hD2
    have he1 : 0 ≤ 2 * C * sf * D0 R * A * D2 :=
      mul_nonneg
        (mul_nonneg
          (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC) hsf)
            (hD0 R hR)) hA) hD2
    have hQeq : Qout = Z +
        (2 * C * sf * D1 R * D2 + 2 * C * sf * D0 R * A * D2) := by
      dsimp only [Qout, Z, B0, B1, FD, FB, WB, WD]
      ring
    have hZQ : Z ≤ Qout := by
      rw [hQeq]
      exact le_add_of_nonneg_right (add_nonneg he0 he1)
    calc
      lowJetSq (I := I) (M := M) g 2
          (lieBgCore (I := I) (M := M) g gT gB -
            lieBgCore (I := I) (M := M) g gU gB) ≤ Z ^ 2 := hmain
      _ ≤ Qout ^ 2 := pow_le_pow_left₀ hZ hZQ 2
      _ = (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 := by
        rfl

set_option maxHeartbeats 2400000 in
set_option linter.unusedVariables false in
/-- The full fixed-background `DLa` core has an `H²` single-state bound whose
dependence on the `H³` size remains affine. -/
private theorem lieBgCore_bdd_h2
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M) :
    ∃ C0 C1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ C0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ C1 R) ∧
      ∀ (gT : SmoothRiemannianMetric I M)
        (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δ : ℝ} (hδ_le : δ ≤ (1 : ℝ) / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      lowJetSq (I := I) (M := M) g 2
          (lieBgCore (I := I) (M := M) g gT gB) ≤
        (C0 R + C1 R * A) ^ 2 := by
  obtain ⟨B0, B1, hB0, hB1, hpair⟩ :=
    lieBgCore_pair_h2 (I := I) (M := M) hDim g gB
  let J0 : ℝ := lowJetSq (I := I) (M := M) g 2
    (lieBgCore (I := I) (M := M) g g gB)
  let K : ℝ := Real.sqrt J0
  let C0 : ℝ → ℝ := fun R => 2 * (K + B1 R * R)
  let C1 : ℝ → ℝ := fun R => 2 * (B0 R + B1 R * R)
  have hJ0 : 0 ≤ J0 := jetNn (I := I) (M := M) (m := 2) g _
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  have hKsq : K ^ 2 = J0 := by
    simpa only [K] using Real.sq_sqrt hJ0
  refine ⟨C0, C1, ?_, ?_, ?_⟩
  · intro R hR
    exact mul_nonneg (by norm_num)
      (add_nonneg hK (mul_nonneg (hB1 R hR) hR))
  · intro R hR
    exact mul_nonneg (by norm_num)
      (add_nonneg (hB0 R hR) (mul_nonneg (hB1 R hR) hR))
  · intro gT T hT hTtie δ hδ_le hδ0 hδT R A hR hA hT2 hT3
    have hzero : ∀ (x : M) (u v : TangentSpace I x),
        ccTensorBilin (I := I) g (0 : SmoothCcTensor g 0 2) x u v =
          ccTensorBilin (I := I) g (0 : SmoothCcTensor g 0 2) x v u := by
      intro x u v
      rw [ccTensorBilin_zero_weight, ccTensorBilin_zero_weight]
    have hzeroTie : ∀ (x : M) (u v : TangentSpace I x),
        g.inner x u v = g.inner x u v +
          ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2) x u v := by
      intro x u v
      rw [ccTensorBilinSymm_apply, ccTensorBilin_zero_weight,
        ccTensorBilin_zero_weight]
      ring
    have hzeroOp : gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g
          (0 : SmoothCcTensor g 0 2)) δ := by
      intro x v w
      rw [ccTensorBilinSymm_apply, ccTensorBilin_zero_weight,
        ccTensorBilin_zero_weight]
      simpa only [zero_add, mul_zero, abs_zero] using
        (mul_nonneg (mul_nonneg hδ0 (Real.sqrt_nonneg (g.inner x v v)))
          (Real.sqrt_nonneg (g.inner x w w)))
    have hz2 : lowJetSq (I := I) (M := M) g 2
        (0 : SmoothCcTensor g 0 2) ≤ R ^ 2 := by
      rw [jetZero]
      exact sq_nonneg R
    have hTU2 : lowJetSq (I := I) (M := M) g 2
        (T - (0 : SmoothCcTensor g 0 2)) ≤ R ^ 2 := by
      simpa only [sub_zero] using hT2
    have hTU3 : lowJetSq (I := I) (M := M) g 3
        (T - (0 : SmoothCcTensor g 0 2)) ≤ A ^ 2 := by
      simpa only [sub_zero] using hT3
    have hpair0 : lowJetSq (I := I) (M := M) g 2
        (lieBgCore (I := I) (M := M) g gT gB -
          lieBgCore (I := I) (M := M) g g gB) ≤
        (B0 R * A + B1 R * R + B1 R * A * R) ^ 2 :=
      hpair gT g T (0 : SmoothCcTensor g 0 2)
        hT hzero hTtie hzeroTie hδ_le hδ0 hδT hzeroOp
        R A R A hR hA hR hA hT2 hz2 hT3 hTU2 hTU3
    have hdecomp : lieBgCore (I := I) (M := M) g gT gB =
        (lieBgCore (I := I) (M := M) g gT gB -
          lieBgCore (I := I) (M := M) g g gB) +
        lieBgCore (I := I) (M := M) g g gB := by
      module
    let L : ℝ := B0 R * A + B1 R * R + B1 R * A * R
    have hL : 0 ≤ L := by
      dsimp only [L]
      exact add_nonneg
        (add_nonneg (mul_nonneg (hB0 R hR) hA)
          (mul_nonneg (hB1 R hR) hR))
        (mul_nonneg (mul_nonneg (hB1 R hR) hA) hR)
    have hmain : lowJetSq (I := I) (M := M) g 2
        (lieBgCore (I := I) (M := M) g gT gB) ≤
          2 * (L ^ 2 + J0) := by
      rw [hdecomp]
      exact (jetAdd (I := I) (M := M) g 2 _ _).trans
        (mul_le_mul_of_nonneg_left
          (add_le_add (by simpa only [L] using hpair0) le_rfl) (by norm_num))
    calc
      lowJetSq (I := I) (M := M) g 2
          (lieBgCore (I := I) (M := M) g gT gB) ≤
        2 * (L ^ 2 + J0) := hmain
      _ = 2 * (L ^ 2 + K ^ 2) := by rw [hKsq]
      _ ≤ (2 * (K + L)) ^ 2 := by
        nlinarith [mul_nonneg hK hL]
      _ = (C0 R + C1 R * A) ^ 2 := by
        dsimp only [C0, C1, L]
        ring

/-- The slot-extension and permutation package occurring in the fixed-background
`DLa` refold. -/
private noncomputable def dLaBgPass
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 4) :
    SmoothCcTensor g 2 6 :=
  rsDomDomCongrSection (I := I) (M := M) g 2 6 lieCovSigma
    (slotExtendIter (I := I) (M := M) g 0 4 2 S)

/-- The fixed-background `DLa` pass package preserves subtraction. -/
private theorem dLaBgPass_sub
    (g : SmoothRiemannianMetric I M) (A B : SmoothCcTensor g 0 4) :
    dLaBgPass (I := I) (M := M) g (A - B) =
      dLaBgPass (I := I) (M := M) g A -
        dLaBgPass (I := I) (M := M) g B := by
  unfold dLaBgPass
  rw [slotIter_sub, rspermSub]

/-- The fixed-background `DLa` pass package preserves `H²` jets up to the
two inserted finite-dimensional slots. -/
private theorem dLaBgPass_h2
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 4) :
    lowJetSq (I := I) (M := M) g 2
        (dLaBgPass (I := I) (M := M) g S) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        lowJetSq (I := I) (M := M) g 2 S := by
  unfold dLaBgPass
  rw [rspermH2]
  simpa only [lowJetSq] using
    slotIter_h2 (I := I) (M := M) g 0 4 2 S

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 3200000 in
set_option linter.unusedVariables false in
/-- On a sufficiently small spectral `H²` metric ball, changing the fixed
DeTurck background in the `DLa` coefficient is `H²`-Lipschitz in the critical
`H³/H²` two-state currency. -/
theorem dlaBg_pair_h2
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B0 B1 : ℝ → ℝ,
      0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
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
        {δ : ℝ} (hδ_le : δ ≤ (1 : ℝ) / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ (R A D2 D3 : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        lowJetSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      let N := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
      lowJetSq (I := I) (M := M) g 2
          ((deTurckLieDLaCoeffField (I := I) (M := M) g gT gB -
              deTurckLieDLaCoeffField (I := I) (M := M) g gT g) -
            (deTurckLieDLaCoeffField (I := I) (M := M) g gU gB -
              deTurckLieDLaCoeffField (I := I) (M := M) g gU g)) ≤
        (B0 R * D3 + B1 R * D2 + B1 R * A * D2 +
          B1 R * N + B1 R * A * N) ^ 2 := by
  obtain ⟨C, hC, happ⟩ := appPairH2 (I := I) (M := M) hDim g 2 6 2
  obtain ⟨Bc0, Bc1, hBc0, hBc1, hcore⟩ :=
    lieBgCore_pair_h2 (I := I) (M := M) hDim g gB
  obtain ⟨Bt0, Bt1, hBt0, hBt1, hcoreBdd⟩ :=
    lieBgCore_bdd_h2 (I := I) (M := M) hDim g gB
  obtain ⟨ρp, Cp, hρp, hCp, htracePair⟩ :=
    LowBaseInternal.pairTrace_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρb, Pb, hρb, hPb, htraceBdd⟩ :=
    LowBaseInternal.pairTrace_bdd_h2 (I := I) (M := M) hDim g
  let fr : ℝ := Module.finrank ℝ E
  let a : ℝ := C * fr
  let ρ : ℝ := min ρp ρb
  let S : ℝ → ℝ := fun R =>
    Pb * Bc1 R + Cp * Bt0 R + Cp * Bt1 R
  let B0 : ℝ → ℝ := fun R => a * (Pb * Bc0 R)
  let B1 : ℝ → ℝ := fun R => a * S R
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have ha : 0 ≤ a := mul_nonneg hC hfr
  have hρ : 0 < ρ := lt_min hρp hρb
  refine ⟨ρ, B0, B1, hρ, ?_, ?_, ?_⟩
  · intro R hR
    exact mul_nonneg ha (mul_nonneg hPb (hBc0 R hR))
  · intro R hR
    exact mul_nonneg ha
      (add_nonneg
        (add_nonneg (mul_nonneg hPb (hBc1 R hR))
          (mul_nonneg hCp (hBt0 R hR)))
        (mul_nonneg hCp (hBt1 R hR)))
  · intro gT gU T U hT hU hTtie hUtie δ hδ_le hδ0 hδT hδU
      hTHs hUHs R A D2 D3 hR hA hD2 hD3 hT2 hU2 hT3 hTU2 hTU3
    dsimp only
    let N : ℝ :=
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
    let PT : SmoothCcTensor g 6 2 :=
      lieCovPair (I := I) (M := M) g gT
    let PU : SmoothCcTensor g 6 2 :=
      lieCovPair (I := I) (M := M) g gU
    let XT : SmoothCcTensor g 2 6 :=
      dLaBgPass (I := I) (M := M) g
        (lieBgCore (I := I) (M := M) g gT gB)
    let XU : SmoothCcTensor g 2 6 :=
      dLaBgPass (I := I) (M := M) g
        (lieBgCore (I := I) (M := M) g gU gB)
    let YT : SmoothCcTensor g 2 2 :=
      appCcRS (I := I) (M := M) g 2 6 2 PT XT
    let YU : SmoothCcTensor g 2 2 :=
      appCcRS (I := I) (M := M) g 2 6 2 PU XU
    let FT : SmoothCcTensor g 2 2 :=
      deTurckLieDLaCoeffField (I := I) (M := M) g gT gB -
        deTurckLieDLaCoeffField (I := I) (M := M) g gT g
    let FU : SmoothCcTensor g 2 2 :=
      deTurckLieDLaCoeffField (I := I) (M := M) g gU gB -
        deTurckLieDLaCoeffField (I := I) (M := M) g gU g
    let X : ℝ := Bc0 R * D3 + Bc1 R * D2 + Bc1 R * A * D2
    let Y : ℝ := Bt0 R + Bt1 R * A
    have hN : 0 ≤ N := norm_nonneg _
    have hX : 0 ≤ X :=
      add_nonneg
        (add_nonneg (mul_nonneg (hBc0 R hR) hD3)
          (mul_nonneg (hBc1 R hR) hD2))
        (mul_nonneg (mul_nonneg (hBc1 R hR) hA) hD2)
    have hY : 0 ≤ Y :=
      add_nonneg (hBt0 R hR) (mul_nonneg (hBt1 R hR) hA)
    have hFT : FT = (-1 : ℝ) • YT := by
      dsimp only [FT, YT, PT, XT]
      simpa only [dLaBgPass] using
        (dlaBg_eq (I := I) (M := M) g gB gT)
    have hFU : FU = (-1 : ℝ) • YU := by
      dsimp only [FU, YU, PU, XU]
      simpa only [dLaBgPass] using
        (dlaBg_eq (I := I) (M := M) g gB gU)
    have hFsub : FT - FU = (-1 : ℝ) • (YT - YU) := by
      rw [hFT, hFU]
      module
    have hXsub : XT - XU =
        dLaBgPass (I := I) (M := M) g
          (lieBgCore (I := I) (M := M) g gT gB -
            lieBgCore (I := I) (M := M) g gU gB) := by
      simpa only [XT, XU] using
        (dLaBgPass_sub (I := I) (M := M) g
          (lieBgCore (I := I) (M := M) g gT gB)
          (lieBgCore (I := I) (M := M) g gU gB)).symm
    have hTHsp : ‖ccTensorToHs (I := I) (M := M) g 2
        (2 : ℝ) T‖ ≤ ρp := hTHs.trans (min_le_left _ _)
    have hUHsp : ‖ccTensorToHs (I := I) (M := M) g 2
        (2 : ℝ) U‖ ≤ ρp := hUHs.trans (min_le_left _ _)
    have hUHsb : ‖ccTensorToHs (I := I) (M := M) g 2
        (2 : ℝ) U‖ ≤ ρb := hUHs.trans (min_le_right _ _)
    have hPU : lowJetSq (I := I) (M := M) g 2 PU ≤ Pb ^ 2 := by
      simpa only [PU] using htraceBdd U gU hUtie hUHsb
    have hPD : lowJetSq (I := I) (M := M) g 2 (PT - PU) ≤
        (Cp * N) ^ 2 := by
      simpa only [PT, PU, N] using
        htracePair T U gT gU hTtie hUtie hTHsp hUHsp
    have hcoreD : lowJetSq (I := I) (M := M) g 2
        (lieBgCore (I := I) (M := M) g gT gB -
          lieBgCore (I := I) (M := M) g gU gB) ≤ X ^ 2 := by
      simpa only [X] using
        hcore gT gU T U hT hU hTtie hUtie hδ_le hδ0 hδT hδU
          R A D2 D3 hR hA hD2 hD3 hT2 hU2 hT3 hTU2 hTU3
    have hcoreT : lowJetSq (I := I) (M := M) g 2
        (lieBgCore (I := I) (M := M) g gT gB) ≤ Y ^ 2 := by
      simpa only [Y] using
        hcoreBdd gT T hT hTtie hδ_le hδ0 hδT R A hR hA hT2 hT3
    have hXD : lowJetSq (I := I) (M := M) g 2 (XT - XU) ≤
        (fr * X) ^ 2 := by
      rw [hXsub]
      calc
        lowJetSq (I := I) (M := M) g 2
            (dLaBgPass (I := I) (M := M) g
              (lieBgCore (I := I) (M := M) g gT gB -
                lieBgCore (I := I) (M := M) g gU gB)) ≤
          fr ^ 2 * lowJetSq (I := I) (M := M) g 2
            (lieBgCore (I := I) (M := M) g gT gB -
              lieBgCore (I := I) (M := M) g gU gB) :=
          dLaBgPass_h2 (I := I) (M := M) g _
        _ ≤ fr ^ 2 * X ^ 2 :=
          mul_le_mul_of_nonneg_left hcoreD (pow_nonneg hfr 2)
        _ = (fr * X) ^ 2 := by ring
    have hXT : lowJetSq (I := I) (M := M) g 2 XT ≤
        (fr * Y) ^ 2 := by
      dsimp only [XT]
      calc
        lowJetSq (I := I) (M := M) g 2
            (dLaBgPass (I := I) (M := M) g
              (lieBgCore (I := I) (M := M) g gT gB)) ≤
          fr ^ 2 * lowJetSq (I := I) (M := M) g 2
            (lieBgCore (I := I) (M := M) g gT gB) :=
          dLaBgPass_h2 (I := I) (M := M) g _
        _ ≤ fr ^ 2 * Y ^ 2 :=
          mul_le_mul_of_nonneg_left hcoreT (pow_nonneg hfr 2)
        _ = (fr * Y) ^ 2 := by ring
    have hpairY : lowJetSq (I := I) (M := M) g 2 (YT - YU) ≤
        (C * ((Cp * N) * (fr * Y) + Pb * (fr * X))) ^ 2 := by
      simpa only [YT, YU] using
        happ PT PU XT XU (Cp * N) Pb (fr * Y) (fr * X)
          (mul_nonneg hCp hN) hPb (mul_nonneg hfr hY)
          (mul_nonneg hfr hX) hPD hPU hXT hXD
    have hFjet : lowJetSq (I := I) (M := M) g 2 (FT - FU) =
        lowJetSq (I := I) (M := M) g 2 (YT - YU) := by
      rw [hFsub]
      simpa only [neg_one_sq, one_mul] using
        (jetSmul (I := I) (M := M) g 2 (-1 : ℝ) (YT - YU))
    let V : ℝ :=
      Pb * Bc0 R * D3 + Pb * Bc1 R * D2 + Pb * Bc1 R * A * D2 +
        Cp * Bt0 R * N + Cp * Bt1 R * A * N
    let W : ℝ :=
      Pb * Bc0 R * D3 + S R * D2 + S R * A * D2 + S R * N + S R * A * N
    have hPbBc : Pb * Bc1 R ≤ S R := by
      dsimp only [S]
      exact (le_add_of_nonneg_right (mul_nonneg hCp (hBt0 R hR))).trans
        (le_add_of_nonneg_right (mul_nonneg hCp (hBt1 R hR)))
    have hCpBt0 : Cp * Bt0 R ≤ S R := by
      dsimp only [S]
      exact (le_add_of_nonneg_left (mul_nonneg hPb (hBc1 R hR))).trans
        (le_add_of_nonneg_right (mul_nonneg hCp (hBt1 R hR)))
    have hCpBt1 : Cp * Bt1 R ≤ S R := by
      dsimp only [S]
      exact le_add_of_nonneg_left
        (add_nonneg (mul_nonneg hPb (hBc1 R hR))
          (mul_nonneg hCp (hBt0 R hR)))
    have hVleW : V ≤ W := by
      dsimp only [V, W]
      exact add_le_add
        (add_le_add
          (add_le_add
            (add_le_add le_rfl
              (mul_le_mul_of_nonneg_right hPbBc hD2))
            (by
              simpa only [mul_assoc] using
                mul_le_mul_of_nonneg_right hPbBc (mul_nonneg hA hD2)))
          (mul_le_mul_of_nonneg_right hCpBt0 hN))
        (by
          simpa only [mul_assoc] using
            mul_le_mul_of_nonneg_right hCpBt1 (mul_nonneg hA hN))
    have hrootEq :
        C * ((Cp * N) * (fr * Y) + Pb * (fr * X)) = a * V := by
      dsimp only [a, V, X, Y]
      ring
    have htargetEq :
        B0 R * D3 + B1 R * D2 + B1 R * A * D2 +
            B1 R * N + B1 R * A * N = a * W := by
      dsimp only [B0, B1, W]
      ring
    have hroot0 : 0 ≤ C * ((Cp * N) * (fr * Y) + Pb * (fr * X)) :=
      mul_nonneg hC
        (add_nonneg
          (mul_nonneg (mul_nonneg hCp hN) (mul_nonneg hfr hY))
          (mul_nonneg hPb (mul_nonneg hfr hX)))
    have hrootLe : C * ((Cp * N) * (fr * Y) + Pb * (fr * X)) ≤
        B0 R * D3 + B1 R * D2 + B1 R * A * D2 +
          B1 R * N + B1 R * A * N := by
      rw [hrootEq, htargetEq]
      exact mul_le_mul_of_nonneg_left hVleW ha
    change lowJetSq (I := I) (M := M) g 2 (FT - FU) ≤
      (B0 R * D3 + B1 R * D2 + B1 R * A * D2 +
        B1 R * N + B1 R * A * N) ^ 2
    rw [hFjet]
    exact hpairY.trans (pow_le_pow_left₀ hroot0 hrootLe 2)

private theorem lie0_bg_split_h2
    (g gT gU gB : SmoothRiemannianMetric I M) :
    ((deTurckLieCoeffField (I := I) (M := M) g gT gB +
          lieCorr0Field (I := I) (M := M) g gT gB) -
        (deTurckLieCoeffField (I := I) (M := M) g gT g +
          lieCorr0Field (I := I) (M := M) g gT g)) -
      ((deTurckLieCoeffField (I := I) (M := M) g gU gB +
          lieCorr0Field (I := I) (M := M) g gU gB) -
        (deTurckLieCoeffField (I := I) (M := M) g gU g +
          lieCorr0Field (I := I) (M := M) g gU g)) =
      (((deTurckLieDLaCoeffField (I := I) (M := M) g gT gB -
            deTurckLieDLaCoeffField (I := I) (M := M) g gT g) -
          (deTurckLieDLaCoeffField (I := I) (M := M) g gU gB -
            deTurckLieDLaCoeffField (I := I) (M := M) g gU g)) +
        (((deTurckLieDLbCoeffField (I := I) (M := M) g gT gB -
              deTurckLieDLbCoeffField (I := I) (M := M) g gT g) +
            (lc0Insert (I := I) (M := M) g gT gB -
              lc0Insert (I := I) (M := M) g gT g)) -
          ((deTurckLieDLbCoeffField (I := I) (M := M) g gU gB -
              deTurckLieDLbCoeffField (I := I) (M := M) g gU g) +
            (lc0Insert (I := I) (M := M) g gU gB -
              lc0Insert (I := I) (M := M) g gU g)))) +
      ((lc0AMix (I := I) (M := M) g gT gB -
          lc0AMix (I := I) (M := M) g gT g) -
        (lc0AMix (I := I) (M := M) g gU gB -
          lc0AMix (I := I) (M := M) g gU g)) := by
  rw [← deTurckLieDLaCoeffField_add_deTurckLieDLbCoeffField
      (I := I) (M := M) g gT gB,
    ← deTurckLieDLaCoeffField_add_deTurckLieDLbCoeffField
      (I := I) (M := M) g gT g,
    ← deTurckLieDLaCoeffField_add_deTurckLieDLbCoeffField
      (I := I) (M := M) g gU gB,
    ← deTurckLieDLaCoeffField_add_deTurckLieDLbCoeffField
      (I := I) (M := M) g gU g,
    lc0_decomp (I := I) (M := M) g gT gB,
    lc0_decomp (I := I) (M := M) g gT g,
    lc0_decomp (I := I) (M := M) g gU gB,
    lc0_decomp (I := I) (M := M) g gU g]
  module

set_option linter.unusedVariables false in
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 3200000 in
/-- On a common spectral `H2` ball, the complete arbitrary-background
order-zero DeTurck correction is `H2`-Lipschitz in the five adjacent-scale
currencies `D3`, `D2`, `A * D2`, `N`, and `A * N`. -/
theorem lie0_bg_pair_h2
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B0 B1 : ℝ → ℝ,
      0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
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
        {δ : ℝ} (hδ_le : δ ≤ (1 : ℝ) / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ (R A D2 D3 : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        lowJetSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      let N := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
      lowJetSq (I := I) (M := M) g 2
          (((deTurckLieCoeffField (I := I) (M := M) g gT gB +
                lieCorr0Field (I := I) (M := M) g gT gB) -
              (deTurckLieCoeffField (I := I) (M := M) g gT g +
                lieCorr0Field (I := I) (M := M) g gT g)) -
            ((deTurckLieCoeffField (I := I) (M := M) g gU gB +
                lieCorr0Field (I := I) (M := M) g gU gB) -
              (deTurckLieCoeffField (I := I) (M := M) g gU g +
                lieCorr0Field (I := I) (M := M) g gU g))) ≤
        (B0 R * D3 + B1 R * D2 + B1 R * A * D2 +
          B1 R * N + B1 R * A * N) ^ 2 := by
  obtain ⟨ρa, Ba0, Ba1, hρa, hBa0, hBa1, hDLa⟩ :=
    dlaBg_pair_h2 (I := I) (M := M) hDim g gB
  obtain ⟨Bb, hBb, hDLb⟩ :=
    dlbIns_pair_h2 (I := I) (M := M) hDim g gB
  obtain ⟨ρm, Bm0, Bm1, hρm, hBm0, hBm1, hAMix⟩ :=
    amixBg_pair_h2 (I := I) (M := M) hDim g gB
  let ρ : ℝ := min ρa ρm
  let B0 : ℝ → ℝ := fun R => 2 * (Ba0 R + Bb R + Bm0)
  let B1 : ℝ → ℝ := fun R => 2 * (Ba1 R + Bb R + Bm1)
  have hρ : 0 < ρ := lt_min hρa hρm
  refine ⟨ρ, B0, B1, hρ, ?_, ?_, ?_⟩
  · intro R hR
    exact mul_nonneg (by norm_num)
      (add_nonneg (add_nonneg (hBa0 R hR) (hBb R hR)) hBm0)
  · intro R hR
    exact mul_nonneg (by norm_num)
      (add_nonneg (add_nonneg (hBa1 R hR) (hBb R hR)) hBm1)
  · intro gT gU T U hT hU hTtie hUtie δ hδ_le hδ0 hδT hδU
      hTHs hUHs R A D2 D3 hR hA hD2 hD3 hT2 hU2 hT3 hU3 hTU2 hTU3
    dsimp only
    let N : ℝ :=
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
    let X : SmoothCcTensor g 2 2 :=
      (deTurckLieDLaCoeffField (I := I) (M := M) g gT gB -
          deTurckLieDLaCoeffField (I := I) (M := M) g gT g) -
        (deTurckLieDLaCoeffField (I := I) (M := M) g gU gB -
          deTurckLieDLaCoeffField (I := I) (M := M) g gU g)
    let Y : SmoothCcTensor g 2 2 :=
      ((deTurckLieDLbCoeffField (I := I) (M := M) g gT gB -
            deTurckLieDLbCoeffField (I := I) (M := M) g gT g) +
          (lc0Insert (I := I) (M := M) g gT gB -
            lc0Insert (I := I) (M := M) g gT g)) -
        ((deTurckLieDLbCoeffField (I := I) (M := M) g gU gB -
            deTurckLieDLbCoeffField (I := I) (M := M) g gU g) +
          (lc0Insert (I := I) (M := M) g gU gB -
            lc0Insert (I := I) (M := M) g gU g))
    let Z : SmoothCcTensor g 2 2 :=
      (lc0AMix (I := I) (M := M) g gT gB -
          lc0AMix (I := I) (M := M) g gT g) -
        (lc0AMix (I := I) (M := M) g gU gB -
          lc0AMix (I := I) (M := M) g gU g)
    let SX : ℝ :=
      Ba0 R * D3 + Ba1 R * D2 + Ba1 R * A * D2 +
        Ba1 R * N + Ba1 R * A * N
    let SY : ℝ := Bb R * (D3 + D2 + A * D2)
    let SZ : ℝ := Bm0 * D3 + Bm1 * N + Bm1 * A * N
    have hN : 0 ≤ N := norm_nonneg _
    have hBa0R : 0 ≤ Ba0 R := hBa0 R hR
    have hBa1R : 0 ≤ Ba1 R := hBa1 R hR
    have hBbR : 0 ≤ Bb R := hBb R hR
    have hSX : 0 ≤ SX := by
      dsimp only [SX]
      exact add_nonneg
        (add_nonneg
          (add_nonneg
            (add_nonneg (mul_nonneg hBa0R hD3) (mul_nonneg hBa1R hD2))
            (mul_nonneg (mul_nonneg hBa1R hA) hD2))
          (mul_nonneg hBa1R hN))
        (mul_nonneg (mul_nonneg hBa1R hA) hN)
    have hSY : 0 ≤ SY := by
      dsimp only [SY]
      exact mul_nonneg hBbR
        (add_nonneg (add_nonneg hD3 hD2) (mul_nonneg hA hD2))
    have hSZ : 0 ≤ SZ := by
      dsimp only [SZ]
      exact add_nonneg
        (add_nonneg (mul_nonneg hBm0 hD3) (mul_nonneg hBm1 hN))
        (mul_nonneg (mul_nonneg hBm1 hA) hN)
    have hTHsa : ‖ccTensorToHs (I := I) (M := M) g 2
        (2 : ℝ) T‖ ≤ ρa := hTHs.trans (min_le_left _ _)
    have hUHsa : ‖ccTensorToHs (I := I) (M := M) g 2
        (2 : ℝ) U‖ ≤ ρa := hUHs.trans (min_le_left _ _)
    have hTHsm : ‖ccTensorToHs (I := I) (M := M) g 2
        (2 : ℝ) T‖ ≤ ρm := hTHs.trans (min_le_right _ _)
    have hUHsm : ‖ccTensorToHs (I := I) (M := M) g 2
        (2 : ℝ) U‖ ≤ ρm := hUHs.trans (min_le_right _ _)
    have hX : lowJetSq (I := I) (M := M) g 2 X ≤ SX ^ 2 := by
      simpa only [X, SX, N] using
        hDLa gT gU T U hT hU hTtie hUtie hδ_le hδ0 hδT hδU
          hTHsa hUHsa R A D2 D3 hR hA hD2 hD3 hT2 hU2 hT3
          hTU2 hTU3
    have hY : lowJetSq (I := I) (M := M) g 2 Y ≤ SY ^ 2 := by
      simpa only [Y, SY] using
        hDLb gT gU T U hT hU hTtie hUtie
          hδ_le hδ0 hδT hδ_le hδ0 hδU
          R A D2 D3 hR hA hD2 hD3 hT2 hU2 hT3 hU3 hTU2 hTU3
    have hZ : lowJetSq (I := I) (M := M) g 2 Z ≤ SZ ^ 2 := by
      simpa only [Z, SZ, N] using
        hAMix gT gU T U hTtie hUtie hTHsm hUHsm
          A D3 hA hD3 hT3 hTU3
    have hsplit :
        ((deTurckLieCoeffField (I := I) (M := M) g gT gB +
              lieCorr0Field (I := I) (M := M) g gT gB) -
            (deTurckLieCoeffField (I := I) (M := M) g gT g +
              lieCorr0Field (I := I) (M := M) g gT g)) -
          ((deTurckLieCoeffField (I := I) (M := M) g gU gB +
              lieCorr0Field (I := I) (M := M) g gU gB) -
            (deTurckLieCoeffField (I := I) (M := M) g gU g +
              lieCorr0Field (I := I) (M := M) g gU g)) =
        (X + Y) + Z := by
      simpa only [X, Y, Z] using
        lie0_bg_split_h2 (I := I) (M := M) g gT gU gB
    have hsum : lowJetSq (I := I) (M := M) g 2 ((X + Y) + Z) ≤
        4 * SX ^ 2 + 4 * SY ^ 2 + 2 * SZ ^ 2 := by
      calc
        lowJetSq (I := I) (M := M) g 2 ((X + Y) + Z) ≤
            2 * (lowJetSq (I := I) (M := M) g 2 (X + Y) +
              lowJetSq (I := I) (M := M) g 2 Z) :=
          jetAdd (I := I) (M := M) g 2 (X + Y) Z
        _ ≤ 2 * (2 * (lowJetSq (I := I) (M := M) g 2 X +
                lowJetSq (I := I) (M := M) g 2 Y) +
              lowJetSq (I := I) (M := M) g 2 Z) := by
          exact mul_le_mul_of_nonneg_left
            (add_le_add (jetAdd (I := I) (M := M) g 2 X Y) le_rfl)
            (by norm_num)
        _ ≤ 2 * (2 * (SX ^ 2 + SY ^ 2) + SZ ^ 2) := by
          exact mul_le_mul_of_nonneg_left
            (add_le_add
              (mul_le_mul_of_nonneg_left (add_le_add hX hY) (by norm_num)) hZ)
            (by norm_num)
        _ = 4 * SX ^ 2 + 4 * SY ^ 2 + 2 * SZ ^ 2 := by ring
    have hsq : 4 * SX ^ 2 + 4 * SY ^ 2 + 2 * SZ ^ 2 ≤
        (2 * (SX + SY + SZ)) ^ 2 := by
      nlinarith [mul_nonneg hSX hSY, mul_nonneg hSX hSZ,
        mul_nonneg hSY hSZ, sq_nonneg SZ]
    let Extra : ℝ :=
      Bm1 * D2 + Bm1 * A * D2 + Bb R * N + Bb R * A * N
    have hExtra : 0 ≤ Extra := by
      dsimp only [Extra]
      exact add_nonneg
        (add_nonneg
          (add_nonneg (mul_nonneg hBm1 hD2)
            (mul_nonneg (mul_nonneg hBm1 hA) hD2))
          (mul_nonneg hBbR hN))
        (mul_nonneg (mul_nonneg hBbR hA) hN)
    have hlin :
        B0 R * D3 + B1 R * D2 + B1 R * A * D2 +
            B1 R * N + B1 R * A * N =
          2 * (SX + SY + SZ) + 2 * Extra := by
      dsimp only [B0, B1, SX, SY, SZ]
      dsimp only [Extra]
      ring
    have hroot0 : 0 ≤ 2 * (SX + SY + SZ) := by positivity
    have hrootLe : 2 * (SX + SY + SZ) ≤
        B0 R * D3 + B1 R * D2 + B1 R * A * D2 +
          B1 R * N + B1 R * A * N := by
      rw [hlin]
      exact le_add_of_nonneg_right (mul_nonneg (by norm_num) hExtra)
    rw [hsplit]
    calc
      lowJetSq (I := I) (M := M) g 2 ((X + Y) + Z) ≤
          4 * SX ^ 2 + 4 * SY ^ 2 + 2 * SZ ^ 2 := hsum
      _ ≤ (2 * (SX + SY + SZ)) ^ 2 := hsq
      _ ≤ (B0 R * D3 + B1 R * D2 + B1 R * A * D2 +
          B1 R * N + B1 R * A * N) ^ 2 :=
        pow_le_pow_left₀ hroot0 hrootLe 2

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
