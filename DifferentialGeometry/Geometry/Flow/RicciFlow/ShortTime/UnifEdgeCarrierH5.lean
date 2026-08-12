import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.H1Jet
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.LowRegC01JetTower
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.UnifMorreyRS
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifAppH3
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifConvexJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifEdgeCenterH5

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Bundle Manifold Set Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators RealInnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private theorem iter_three_one_pair_abs_le_h5_h3
    (g : SmoothRiemannianMetric I M)
    (T Y : SmoothCcTensor g 0 2) :
    |tensorL2Inner (I := I) (M := M) g 0 2
        (oneMinusConnLapSmooth (I := I) g 0 2
          (oneMinusConnLapSmooth (I := I) g 0 2
            (oneMinusConnLapSmooth (I := I) g 0 2 T))).toFun
        (oneMinusConnLapSmooth (I := I) g 0 2 Y).toFun| ≤
      ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) T‖ *
        ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) Y‖ := by
  classical
  let LT := oneMinusConnLapSmooth (I := I) g 0 2 T
  let L2T := oneMinusConnLapSmooth (I := I) g 0 2 LT
  let L3T := oneMinusConnLapSmooth (I := I) g 0 2 L2T
  let LY := oneMinusConnLapSmooth (I := I) g 0 2 Y
  have hL2iter : L2T = oneMinusConnLapSmoothIter (I := I) g 0 2 2 T := by
    simp only [L2T, LT, oneMinusConnLapSmoothIter]
  have hL3iter : L3T = oneMinusConnLapSmoothIter (I := I) g 0 2 3 T := by
    simp only [L3T, L2T, LT, oneMinusConnLapSmoothIter]
  have hLYiter : LY = oneMinusConnLapSmoothIter (I := I) g 0 2 1 Y := by
    simp only [LY, oneMinusConnLapSmoothIter]
  have hinner :
      tensorL2Inner (I := I) (M := M) g 0 2 L3T.toFun LY.toFun =
        (inner ℝ
          (smoothCcToTensorHs (I := I) (M := M) g ((1 : ℕ) : ℝ) L2T)
          (smoothCcToTensorHs (I := I) (M := M) g ((1 : ℕ) : ℝ) LY) : ℝ) := by
    rw [tensorL2Inner_eq_tsum_l2Coeff_cross_arm
      (I := I) (M := M) g L3T LY,
      tensorHs.inner_def]
    refine tsum_congr (fun i => ?_)
    rw [smoothCcToTensorHs_coeff, smoothCcToTensorHs_coeff,
      hL2iter, hLYiter, hL3iter,
      tensorL2Coeff_ofCompact_oneMinusConnLapSmoothIter
        (I := I) (M := M) g
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) T i 2,
      tensorL2Coeff_ofCompact_oneMinusConnLapSmoothIter
        (I := I) (M := M) g
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) Y i 1,
      tensorL2Coeff_ofCompact_oneMinusConnLapSmoothIter
        (I := I) (M := M) g
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) T i 3]
    unfold tensorSobolevWeight
    rw [Real.rpow_natCast]
    ring
  have hTnorm :
      ‖smoothCcToTensorHs (I := I) (M := M) g ((1 : ℕ) : ℝ) L2T‖ =
        ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) T‖ := by
    rw [norm_ccHs_eq_smoothHs]
    have h5 := smoothCcToTensorHs_add_two_norm_eq_oneMinusConnLap
      (I := I) (M := M) g 3 T
    have h3 := smoothCcToTensorHs_add_two_norm_eq_oneMinusConnLap
      (I := I) (M := M) g 1 LT
    have h5' :
        ‖smoothCcToTensorHs (I := I) (M := M) g (5 : ℝ) T‖ =
          ‖smoothCcToTensorHs (I := I) (M := M) g (3 : ℝ) LT‖ := by
      simpa only [Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one] using h5
    have h3' :
        ‖smoothCcToTensorHs (I := I) (M := M) g (3 : ℝ) LT‖ =
          ‖smoothCcToTensorHs (I := I) (M := M) g ((1 : ℕ) : ℝ) L2T‖ := by
      simpa only [L2T, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one] using h3
    exact (h5'.trans h3').symm
  have hYnorm :
      ‖smoothCcToTensorHs (I := I) (M := M) g ((1 : ℕ) : ℝ) LY‖ =
        ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) Y‖ := by
    rw [norm_ccHs_eq_smoothHs]
    have h3 := smoothCcToTensorHs_add_two_norm_eq_oneMinusConnLap
      (I := I) (M := M) g 1 Y
    have h3' :
        ‖smoothCcToTensorHs (I := I) (M := M) g (3 : ℝ) Y‖ =
          ‖smoothCcToTensorHs (I := I) (M := M) g ((1 : ℕ) : ℝ) LY‖ := by
      simpa only [LY, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one] using h3
    exact h3'.symm
  change |tensorL2Inner (I := I) (M := M) g 0 2 L3T.toFun LY.toFun| ≤ _
  rw [hinner, ← hTnorm, ← hYnorm]
  exact abs_real_inner_le_norm _ _

theorem edge_carrier_h3_of_h4_cap
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Lambda Qcap : ℝ}
    (hLambda : 1 ≤ Lambda) (hQcap : 0 ≤ Qcap) :
    ∀ g : SmoothRiemannianMetric I M,
      MetricUniformEquivalentOn (I := I) Set.univ gBase g Lambda →
      (∀ a : ℕ, a ≤ 3 →
        MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Lambda) →
      ∃ D : ℝ, 0 ≤ D ∧
        ∀ (T : SmoothCcTensor g 0 2)
          (_hTsymm : ∀ (x : M) (u v : TangentSpace I x),
            ccTensorBilin (I := I) g T x u v =
              ccTensorBilin (I := I) g T x v u)
          {delta : ℝ}, delta ≤ 1 / 3 → 0 ≤ delta →
          ∀ (hdelta : gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g T) delta)
            (hdeltaZ : gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g
                (0 : SmoothCcTensor g 0 2)) delta)
            {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
          ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ≤ Qcap →
          let A := LowBaseInternal.rhsSelfLow
              (I := I) (M := M) g gBase T hdelta hdeltaZ s +
            phiMetCurvCoeff (I := I) g gBase g
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ)
              (appCc (I := I) (M := M) g 2 2 A T)‖ ≤
            D * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ := by
  obtain ⟨Ca, hCa, happ⟩ :=
    appRS_h3_sup_unif (I := I) (M := M) gBase Lambda 0 2 2
  obtain ⟨Cm0, hCm0, hmor0⟩ :=
    morreyRS_unif (I := I) (M := M) hDim gBase hLambda 0 2
  obtain ⟨Cm2, hCm2, hmor2⟩ :=
    morreyRS_unif (I := I) (M := M) hDim gBase hLambda 2 2
  obtain ⟨Kcurv, hKcurv⟩ :=
    exists_curv_actions (I := I) (M := M) gBase hLambda
  let Ct : ℝ := hs2FibreActionC Cm0 Kcurv.rankTwo
  let Cj : ℝ := h3CovsumC Kcurv.rankTwo Kcurv.rankThree
  have hCt : 0 ≤ Ct := by
    dsimp only [Ct]
    exact hs2FibreAct_nonneg hCm0 _
  have hCj : 0 ≤ Cj := by
    dsimp only [Cj]
    exact h3CovsumC_nonneg _ _
  intro g hEq hjet
  obtain ⟨hact2, hact3⟩ := hKcurv.bounds g hEq hjet
  obtain ⟨K0, K2, hK0, hK2, hself⟩ :=
    selfLowJetQBg (I := I) (M := M) hDim g gBase
  obtain ⟨C4, hC4, hjet4⟩ := hsJet_le (I := I) (M := M) g 2 4
  obtain ⟨Ch, hCh, hhs⟩ := hs_le_jet (I := I) (M := M) g 2 3
  let W : ℝ := C4 * Qcap
  let Bself : ℝ := (K0 3 + K2 3 * W ^ 2) * (1 + W ^ 2)
  let Jc : ℝ := lowJetSq (I := I) (M := M) g 3
    (phiMetCurvCoeff (I := I) g gBase g)
  let B2 : ℝ := 2 * (Bself + Jc)
  let B : ℝ := Real.sqrt B2
  let K : ℝ := Ca *
    (Ct ^ 2 * B ^ 2 + (Cm2 * B) ^ 2 * Cj ^ 2)
  let D : ℝ := 2 * Ch * Real.sqrt K
  have hW : 0 ≤ W := mul_nonneg hC4 hQcap
  have hBself : 0 ≤ Bself := by
    dsimp only [Bself]
    exact mul_nonneg
      (add_nonneg (hK0 3) (mul_nonneg (hK2 3) (sq_nonneg W)))
      (add_nonneg (by norm_num) (sq_nonneg W))
  have hJc : 0 ≤ Jc := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hB2 : 0 ≤ B2 := mul_nonneg (by norm_num) (add_nonneg hBself hJc)
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hBsq : B ^ 2 = B2 := by
    simpa only [B] using Real.sq_sqrt hB2
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg hCa
      (add_nonneg (mul_nonneg (sq_nonneg Ct) (sq_nonneg B))
        (mul_nonneg (sq_nonneg (Cm2 * B)) (sq_nonneg Cj)))
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact mul_nonneg (mul_nonneg (by norm_num) hCh) (Real.sqrt_nonneg _)
  refine ⟨D, hD, ?_⟩
  intro T hTsymm delta hdelta_le hdelta0 hdelta hdeltaZ s hs hT4
  let x : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖
  let y : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
  let q : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖
  let S : SmoothCcTensor g 2 2 := LowBaseInternal.rhsSelfLow
    (I := I) (M := M) g gBase T hdelta hdeltaZ s
  let C : SmoothCcTensor g 2 2 := phiMetCurvCoeff (I := I) g gBase g
  let A : SmoothCcTensor g 2 2 := S + C
  let Y : SmoothCcTensor g 0 2 := appCc (I := I) (M := M) g 2 2 A T
  have hx : 0 ≤ x := norm_nonneg _
  have hy : 0 ≤ y := norm_nonneg _
  have hq : 0 ≤ q := norm_nonneg _
  have hxy : x ≤ y := by
    dsimp only [x, y]
    exact ccToHs_norm_mono (I := I) (M := M) g 2 (by norm_num) T
  have hqcap : q ≤ Qcap := by simpa only [q] using hT4
  have hsum5 :
      ∑ j ∈ Finset.range 5,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ≤ W := by
    calc
      _ ≤ C4 * q := by simpa only [q, Nat.reduceAdd] using hjet4 T
      _ ≤ C4 * Qcap := mul_le_mul_of_nonneg_left hqcap hC4
      _ = W := rfl
  have hsq5 :
      ∑ j ∈ Finset.range 5,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 ≤ W ^ 2 := by
    calc
      _ ≤ (∑ j ∈ Finset.range 5,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg fun j _ => norm_nonneg _
      _ ≤ W ^ 2 := pow_le_pow_left₀
        (Finset.sum_nonneg fun j _ => norm_nonneg _) hsum5 2
  have hshift :
      ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 (1 + j) T‖ ^ 2 ≤ W ^ 2 := by
    refine (show
      ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 (1 + j) T‖ ^ 2 ≤
        ∑ j ∈ Finset.range 5,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero,
        zero_add, Nat.reduceAdd]
      nlinarith [sq_nonneg ‖iteratedCovGrad (I := I) g 0 2 0 T‖,
        sq_nonneg ‖iteratedCovGrad (I := I) g 0 2 4 T‖]).trans hsq5
  have hS : lowJetSq (I := I) (M := M) g 3 S ≤ Bself := by
    have hraw := hself T hTsymm hdelta0 hdelta_le hdelta hdeltaZ 3 s hs
    let U : ℝ := ∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 0 2 (1 + j) T‖ ^ 2
    let V : ℝ := ∑ j ∈ Finset.range 5,
      ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2
    have hU : U ≤ W ^ 2 := by simpa only [U] using hshift
    have hV : V ≤ W ^ 2 := by simpa only [V] using hsq5
    have hU0 : 0 ≤ U := Finset.sum_nonneg fun j _ => sq_nonneg _
    have hV0 : 0 ≤ V := Finset.sum_nonneg fun j _ => sq_nonneg _
    have hfirst : K0 3 + K2 3 * U ≤ K0 3 + K2 3 * W ^ 2 :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hU (hK2 3))
    have hsecond : 1 + V ≤ 1 + W ^ 2 := add_le_add le_rfl hV
    calc
      lowJetSq (I := I) (M := M) g 3 S ≤
          (K0 3 + K2 3 * U) * (1 + V) := by
        simpa only [S, U, V, Nat.reduceAdd] using hraw
      _ ≤ (K0 3 + K2 3 * W ^ 2) * (1 + W ^ 2) :=
        mul_le_mul hfirst hsecond (add_nonneg (by norm_num) hV0)
          (add_nonneg (hK0 3) (mul_nonneg (hK2 3) (sq_nonneg W)))
      _ = Bself := rfl
  have hAjet : lowJetSq (I := I) (M := M) g 3 A ≤ B ^ 2 := by
    rw [hBsq]
    exact (jetAdd (I := I) (M := M) g 3 S C).trans
      (mul_le_mul_of_nonneg_left (add_le_add hS le_rfl) (by norm_num))
  have hApt : ∀ z : M,
      riemannianFiberNormSq (I := I) (M := M) g 2 2 z (A.toSection z) ≤
        (Cm2 * B) ^ 2 := by
    intro z
    have hm := hmor2 g hEq (hjet 1 (by norm_num)) (hjet 2 (by norm_num)) A z
    calc
      _ ≤ Cm2 ^ 2 * ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 2 2 j A‖ ^ 2 := hm
      _ ≤ Cm2 ^ 2 * lowJetSq (I := I) (M := M) g 3 A := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg Cm2)
        simp only [lowJetSq, Nat.reduceAdd, Finset.sum_range_succ]
        exact le_add_of_nonneg_right (sq_nonneg _)
      _ ≤ Cm2 ^ 2 * B ^ 2 :=
        mul_le_mul_of_nonneg_left hAjet (sq_nonneg Cm2)
      _ = (Cm2 * B) ^ 2 := by ring
  have hmor0' : ∀ (U : SmoothCcTensor g 0 2) (z : M),
      riemannianFiberNormSq (I := I) (M := M) g 0 2 z (U.toSection z) ≤
        Cm0 ^ 2 * ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
          ‖iteratedCovGrad (I := I) g 0 2 j U‖ ^ 2 := by
    intro U z
    rw [hDim]
    norm_num
    exact hmor0 g hEq (hjet 1 (by norm_num)) (hjet 2 (by norm_num)) U z
  have hTpt : ∀ z : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 z (T.toSection z) ≤
        (Ct * y) ^ 2 := by
    intro z
    calc
      _ ≤ Ct ^ 2 * x ^ 2 := by
        simpa only [Ct, x] using
          hs2_fiber_sq_action (I := I) (M := M) hDim g hact2 hmor0' T z
      _ ≤ Ct ^ 2 * y ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxy 2) (sq_nonneg Ct)
      _ = (Ct * y) ^ 2 := by ring
  have hTjet :
      ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 ≤ (Cj * y) ^ 2 := by
    calc
      _ ≤ (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg fun j _ => norm_nonneg _
      _ ≤ (Cj * y) ^ 2 := pow_le_pow_left₀
        (Finset.sum_nonneg fun j _ => norm_nonneg _)
        (by simpa only [Cj, y] using
          covsum_hs_three (I := I) (M := M) g 2 hact2 hact3 T) 2
  have hYjet : lowJetSq (I := I) (M := M) g 3 Y ≤ K * y ^ 2 := by
    have happRaw := happ g hEq A T (Cm2 * B) (Ct * y)
      (mul_nonneg hCm2 hB) (mul_nonneg hCt hy) hApt hTpt
    change (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 0 2 j Y‖ ^ 2) ≤ _
    refine happRaw.trans ?_
    calc
      Ca * ((Ct * y) ^ 2 * ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 2 2 j A‖ ^ 2 +
          (Cm2 * B) ^ 2 * ∑ j ∈ Finset.range 4,
            ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) ≤
          Ca * ((Ct * y) ^ 2 * B ^ 2 +
            (Cm2 * B) ^ 2 * (Cj * y) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hCa
        exact add_le_add
          (mul_le_mul_of_nonneg_left hAjet (sq_nonneg (Ct * y)))
          (mul_le_mul_of_nonneg_left hTjet (sq_nonneg (Cm2 * B)))
      _ = K * y ^ 2 := by
        dsimp only [K]
        ring
  have hKy : 0 ≤ Real.sqrt K * y := mul_nonneg (Real.sqrt_nonneg _) hy
  have hYjet' : lowJetSq (I := I) (M := M) g 3 Y ≤
      (Real.sqrt K * y) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hK]
    exact hYjet
  let JY : ℝ := ∑ j ∈ Finset.range 4,
    ‖iteratedCovGrad (I := I) g 0 2 j Y‖
  have hJY0 : 0 ≤ JY := Finset.sum_nonneg fun j _ => norm_nonneg _
  have hJYsq : JY ^ 2 ≤ 4 * lowJetSq (I := I) (M := M) g 3 Y := by
    have h := sq_sum_le_card_mul_sum_sq
      (s := Finset.range 4)
      (f := fun j => ‖iteratedCovGrad (I := I) g 0 2 j Y‖)
    simpa only [JY, Finset.card_range, Nat.cast_ofNat, lowJetSq,
      Nat.reduceAdd] using h
  have hJY : JY ≤ 2 * (Real.sqrt K * y) := by
    nlinarith [hJYsq.trans
      (mul_le_mul_of_nonneg_left hYjet' (by norm_num))]
  change ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) Y‖ ≤ D * y
  calc
    _ ≤ Ch * JY := by simpa only [JY, Nat.reduceAdd] using hhs Y
    _ ≤ Ch * (2 * (Real.sqrt K * y)) :=
      mul_le_mul_of_nonneg_left hJY hCh
    _ = D * y := by
      dsimp only [D]
      ring

theorem carrier_pair_abs_h5_of_h3
    (g : SmoothRiemannianMetric I M)
    (T Y : SmoothCcTensor g 0 2) {eta D : ℝ}
    (heta : 0 < eta)
    (hY : ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) Y‖ ≤
      D * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖) :
    2 * |tensorL2Inner (I := I) (M := M) g 0 2
        (oneMinusConnLapSmooth (I := I) g 0 2
          (oneMinusConnLapSmooth (I := I) g 0 2
            (oneMinusConnLapSmooth (I := I) g 0 2 T))).toFun
        (oneMinusConnLapSmooth (I := I) g 0 2 Y).toFun| ≤
      eta * ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) T‖ ^ 2 +
        eta⁻¹ * D ^ 2 *
          ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 := by
  let y : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
  let q : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖
  let z : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) T‖
  have hy : 0 ≤ y := norm_nonneg _
  have hz : 0 ≤ z := norm_nonneg _
  have hyq : y ≤ q := by
    dsimp only [y, q]
    exact ccToHs_norm_mono (I := I) (M := M) g 2 (by norm_num) T
  have hpair := iter_three_one_pair_abs_le_h5_h3
    (I := I) (M := M) g T Y
  have hraw :
      2 * |tensorL2Inner (I := I) (M := M) g 0 2
          (oneMinusConnLapSmooth (I := I) g 0 2
            (oneMinusConnLapSmooth (I := I) g 0 2
              (oneMinusConnLapSmooth (I := I) g 0 2 T))).toFun
          (oneMinusConnLapSmooth (I := I) g 0 2 Y).toFun| ≤
        2 * z * (D * y) := by
    calc
      _ ≤ 2 * (z *
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) Y‖) :=
        mul_le_mul_of_nonneg_left (by simpa only [z] using hpair) (by norm_num)
      _ ≤ 2 * (z * (D * y)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (by simpa only [y] using hY) hz)
          (by norm_num)
      _ = 2 * z * (D * y) := by ring
  have hinv : 0 ≤ eta⁻¹ := inv_nonneg.mpr heta.le
  have hyq2 : (D * y) ^ 2 ≤ D ^ 2 * q ^ 2 := by
    calc
      (D * y) ^ 2 = D ^ 2 * y ^ 2 := by ring
      _ ≤ D ^ 2 * q ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy hyq 2) (sq_nonneg D)
  have hyoung : 2 * z * (D * y) ≤
      eta * z ^ 2 + eta⁻¹ * (D * y) ^ 2 := by
    have hs := mul_nonneg hinv (sq_nonneg (eta * z - D * y))
    have hexpand : eta⁻¹ * (eta * z - D * y) ^ 2 =
        eta * z ^ 2 - 2 * z * (D * y) + eta⁻¹ * (D * y) ^ 2 := by
      field_simp [ne_of_gt heta]
      ring
    rw [hexpand] at hs
    linarith
  calc
    _ ≤ 2 * z * (D * y) := hraw
    _ ≤ eta * z ^ 2 + eta⁻¹ * (D * y) ^ 2 := hyoung
    _ ≤ eta * z ^ 2 + eta⁻¹ * (D ^ 2 * q ^ 2) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hyq2 hinv)
    _ = eta * ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) T‖ ^ 2 +
        eta⁻¹ * D ^ 2 *
          ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 := by
      dsimp only [z, q]
      ring

theorem edge_center_h5_unif
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Lambda Qcap : ℝ}
    (hLambda : 1 ≤ Lambda) (hQcap : 0 ≤ Qcap) :
    ∀ {eta : ℝ}, 0 < eta →
      ∃ delta2 R2 : ℝ,
        0 < delta2 ∧ delta2 ≤ 1 / 3 ∧ 0 < R2 ∧ R2 ≤ 1 ∧
        ∀ g : SmoothRiemannianMetric I M,
          MetricUniformEquivalentOn (I := I) Set.univ gBase g Lambda →
          (∀ a : ℕ, a ≤ 3 →
            MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Lambda) →
          ∃ G : ℝ, 0 ≤ G ∧
            ∀ (T : SmoothCcTensor g 0 2)
              (_hTsymm : ∀ (x : M) (u v : TangentSpace I x),
                ccTensorBilin (I := I) g T x u v =
                  ccTensorBilin (I := I) g T x v u)
              {delta : ℝ}, delta ≤ delta2 → 0 ≤ delta →
              ∀ (hdelta : gFibreOpBound (I := I) (M := M) g
                  (ccTensorBilinSymm (I := I) g T) delta)
                (hdeltaZ : gFibreOpBound (I := I) (M := M) g
                  (ccTensorBilinSymm (I := I) g
                    (0 : SmoothCcTensor g 0 2)) delta)
                {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
              ∀ {R : ℝ}, 0 ≤ R → R ≤ R2 →
              ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
              ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ≤ Qcap →
              let gs := realizedFam (I := I) g T 0 hdelta hdeltaZ s
              let R0 := rhsRefold0 (I := I) (M := M) g gBase T
                hdelta hdeltaZ s
              let K0 := phiMetCurvCoeff (I := I) g gBase g
              let LT := oneMinusConnLapSmooth (I := I) g 0 2 T
              let HT := iteratedCovGrad (I := I) g 0 2 2 T
              let HLT := iteratedCovGrad (I := I) g 0 2 2 LT
              let Q : SmoothCcTensor g 0 2 → SmoothCcTensor g 2 2 := fun U =>
                edgeTopPairBi (I := I) (M := M) g T U hdelta hdeltaZ
                  ricciRefoldQA ricciRefoldQB lieRefoldQ lieRefoldEps s
              let Z := appCc (I := I) (M := M) g 2 2 (Q T) T
              let Cross :=
                appCc (I := I) (M := M) g 2 2 (Q LT) T +
                  appCc (I := I) (M := M) g 2 2 (Q T) LT
              let PairComm :=
                oneMinusConnLapSmooth (I := I) g 0 2 Z -
                  appCc (I := I) (M := M) g 2 2 (Q LT) T -
                  appCc (I := I) (M := M) g 2 2 (Q T) LT + Z
              let C : SmoothCcTensor g 4 2 :=
                deTurckPhiMetTotal (I := I) (M := M) g gBase gs -
                  deTurckPhiMetTotal (I := I) (M := M) g gBase g
              let J :=
                oneMinusConnLapSmooth (I := I) g 0 2
                    (appCc (I := I) (M := M) g 2 2 (R0 + K0) T) +
                  PairComm +
                  (oneMinusConnLapSmooth (I := I) g 0 2
                      (appCc (I := I) (M := M) g 4 2 C HT) -
                    appCc (I := I) (M := M) g 4 2 C HLT) - Z
              let V := oneMinusConnLapSmooth (I := I) g 0 2
                (oneMinusConnLapSmooth (I := I) g 0 2 LT)
              2 * |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun
                    (J + Cross).toFun| ≤
                eta * ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) T‖ ^ 2 +
                  G *
                    (‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
                      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 2 *
                        ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
                      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 4) := by
  intro eta heta
  obtain ⟨delta2, R2, hdelta2, hdelta2third, hR2, hR2one, hcenter⟩ :=
    edge_center_pair_abs_h5_of_carrier (I := I) (M := M)
      hDim gBase hLambda heta
  refine ⟨delta2, R2, hdelta2, hdelta2third, hR2, hR2one, ?_⟩
  intro g hEq hjet
  obtain ⟨Gd, hGd, hcenterG⟩ := hcenter g hEq hjet
  obtain ⟨D, hD, hcarrier⟩ :=
    edge_carrier_h3_of_h4_cap (I := I) (M := M)
      hDim gBase hLambda hQcap g hEq hjet
  let e : ℝ := eta / 5
  let Gc : ℝ := e⁻¹ * D ^ 2
  let G : ℝ := Gc + Gd
  have he : 0 < e := by dsimp only [e]; positivity
  have hGc : 0 ≤ Gc := by
    dsimp only [Gc]
    exact mul_nonneg (inv_nonneg.mpr he.le) (sq_nonneg D)
  have hG : 0 ≤ G := add_nonneg hGc hGd
  refine ⟨G, hG, ?_⟩
  intro T hTsymm delta hdelta_le hdelta0 hdelta hdeltaZ s hs
    R hR hRle hT2 hT4
  let A : SmoothCcTensor g 2 2 :=
    LowBaseInternal.rhsSelfLow (I := I) (M := M)
        g gBase T hdelta hdeltaZ s +
      phiMetCurvCoeff (I := I) g gBase g
  let Y : SmoothCcTensor g 0 2 :=
    appCc (I := I) (M := M) g 2 2 A T
  let y : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
  let q : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖
  have hdelta_third : delta ≤ 1 / 3 := hdelta_le.trans hdelta2third
  have hY := hcarrier T hTsymm hdelta_third hdelta0
    hdelta hdeltaZ hs hT4
  have hpair := carrier_pair_abs_h5_of_h3
    (I := I) (M := M) g T Y (eta := e) he (by
      simpa only [A, Y] using hY)
  have hpair' :
      2 * |tensorL2Inner (I := I) (M := M) g 0 2
          (oneMinusConnLapSmooth (I := I) g 0 2
            (oneMinusConnLapSmooth (I := I) g 0 2
              (oneMinusConnLapSmooth (I := I) g 0 2 T))).toFun
          (oneMinusConnLapSmooth (I := I) g 0 2 Y).toFun| ≤
        (eta / 5) *
            ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) T‖ ^ 2 +
          Gc * q ^ 2 := by
    simpa only [e, Gc, q] using hpair
  have hassembled := hcenterG T hTsymm hdelta_le hdelta0
    hdelta hdeltaZ hs hR hRle hT2 (Lc := Gc * q ^ 2) (by
      simpa only [Y, A, q] using hpair')
  dsimp only at hassembled ⊢
  have hq2 : 0 ≤ q ^ 2 := sq_nonneg _
  have hyq2 : 0 ≤ y ^ 2 * q ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hy4 : 0 ≤ y ^ 4 := by positivity
  calc
    _ ≤ eta * ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) T‖ ^ 2 +
        Gc * q ^ 2 + Gd * (q ^ 2 + y ^ 2 * q ^ 2 + y ^ 4) := by
      simpa only [q, y] using hassembled
    _ ≤ eta * ‖ccTensorToHs (I := I) (M := M) g 2 (5 : ℝ) T‖ ^ 2 +
        G * (q ^ 2 + y ^ 2 * q ^ 2 + y ^ 4) := by
      dsimp only [G]
      nlinarith [mul_nonneg hGc hyq2, mul_nonneg hGc hy4]


end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
