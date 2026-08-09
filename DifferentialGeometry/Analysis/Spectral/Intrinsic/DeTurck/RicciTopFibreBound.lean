import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderLowBaseAction
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.Lowered
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradFibreNormPermutationInvariance

/-!
# Uniform fibre bound for the transparent Ricci top coefficient

The top Palatini coefficient is controlled pointwise by the fibre-smallness
radius, with its constant chosen before the background metric varies.  The
proof uses only the inverse-metric bound and the fact that the Koszul slot
permutations are fibre isometries.
-/

noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Tensor0SBundle
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.LowBaseInternal

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open CurvatureCoefficientDifferenceJetTower

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private theorem perm_re
    (g : SmoothRiemannianMetric I M) {d : ℕ}
    (Φ : SmoothCcTensor g d d) (ρ : Equiv.Perm (Fin d)) :
    appCcRS (I := I) (M := M) g d d d Φ
        (permCoeff (I := I) (M := M) g ρ) =
      reindexCoeffGen (I := I) (M := M) g d d Φ ρ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [appCcRS_toSection, ContinuousLinearMap.comp_apply,
    reindexCoeffGen_toSection, reindexCoeffFibGen_apply]
  change (show Tensor0SSpace d I x →L[ℝ] Tensor0SSpace d I x from
      Φ.toSection x) (slotPermCLM (I := I) ρ x D) = _
  rw [slotPermCLM_apply]

private theorem perm_left_rfns
    (g : SmoothRiemannianMetric I M) {d : ℕ}
    (ρ : Equiv.Perm (Fin d)) (S : SmoothCcTensor g d d) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g d d x
        ((appCcRS (I := I) (M := M) g d d d
          (permCoeff (I := I) (M := M) g ρ) S).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g d d x
        (S.toSection x) := by
  have h := rfns_iteratedCovGrad_rs_eq_of_section_domDomCongr
    (I := I) (M := M) g d d ρ S
    (appCcRS (I := I) (M := M) g d d d
      (permCoeff (I := I) (M := M) g ρ) S)
    (fun y D => by
      rw [appCcRS_toSection, ContinuousLinearMap.comp_apply]
      change Tensor0SSpace.toModel
          (slotPermCLM (I := I) ρ y
            ((show Tensor0SSpace d I y →L[ℝ] Tensor0SSpace d I y from
              S.toSection y) D)) = _
      rw [slotPermCLM_apply, Tensor0SSpace.toModel_ofModel]) 0 x
  simpa only [iteratedCovGrad_zero, Nat.add_zero] using h

private theorem conn_nf
    (g gm : SmoothRiemannianMetric I M) :
    connLowOp (I := I) (M := M) g gm =
      appCcRS (I := I) (M := M) g 3 3 3
        (permCoeff (I := I) (M := M) g lowPerm)
        (appCcRS (I := I) (M := M) g 3 3 3
          (slotInsertEndoCc (I := I) (M := M) g 2
            (fullRaisedEndoField (I := I) (M := M) g gm))
          ((1 / 2 : ℝ) •
            (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 2) +
              permCoeff (I := I) (M := M) g (finRotate 3) -
              permCoeff (I := I) (M := M) g
                (Equiv.swap (1 : Fin 3) 2)))) := rfl

/-- The derivative-top Koszul coefficient has a dimension-only fibre bound,
uniformly over every perturbation in the one-third fibre ball. -/
theorem dagTop_cap_unif :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g gm : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2) {δ : ℝ},
        δ ≤ 1 / 3 → 0 ≤ δ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ →
        (∀ (y : M) (v w : TangentSpace I y),
          gm.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g P y v w) →
        ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 4 4 x
          ((dagTopOp (I := I) (M := M) g gm).toSection x) ≤ K := by
  classical
  let n : ℝ := Module.finrank ℝ E
  let F : ℝ := n ^ 2 * (n ^ 2 * (1 / (1 - (1 / 3 : ℝ))) ^ 2)
  let K : ℝ := 3 * n * F
  refine ⟨K, by positivity, ?_⟩
  intro g gm P δ hδ_le hδ0 hP htie x
  have hsharp := rfns_sharpFlatEndoCc_le_of_lt_one
    (I := I) (M := M) g (δ₀ := (1 : ℝ) / 3)
    (by norm_num) (by norm_num) gm P htie (δ := δ) hδ_le hδ0 hP x
  have hslot := rfns_iteratedCovGrad_slotInsertEndoCc_le_endo
    (I := I) (M := M) g 2
    (fullRaisedEndoField (I := I) (M := M) g gm) 0 x
  simp only [iteratedCovGrad_zero, Nat.add_zero, Nat.reduceAdd] at hslot
  rw [← sharpFlatEndoCc_eq_slotInsert_fullRaised
    (I := I) (M := M) g gm] at hslot
  have hE :
      riemannianFiberNormSq (I := I) (M := M) g 3 3 x
          ((slotInsertEndoCc (I := I) (M := M) g 2
            (fullRaisedEndoField (I := I) (M := M) g gm)).toSection x) ≤ F := by
    refine hslot.trans ?_
    dsimp only [F, n]
    exact mul_le_mul_of_nonneg_left hsharp (sq_nonneg _)
  let E1 : SmoothCcTensor g 3 3 :=
    slotInsertEndoCc (I := I) (M := M) g 2
      (fullRaisedEndoField (I := I) (M := M) g gm)
  let Z : SmoothCcTensor g 3 3 :=
    (1 / 2 : ℝ) •
      (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 2) +
        permCoeff (I := I) (M := M) g (finRotate 3) -
        permCoeff (I := I) (M := M) g (Equiv.swap (1 : Fin 3) 2))
  let Y : SmoothCcTensor g 3 3 :=
    appCcRS (I := I) (M := M) g 3 3 3 E1 Z
  have hYsplit : Y = (1 / 2 : ℝ) •
      (reindexCoeffGen (I := I) (M := M) g 3 3 E1
          (Equiv.swap (0 : Fin 3) 2) +
        reindexCoeffGen (I := I) (M := M) g 3 3 E1 (finRotate 3) -
        reindexCoeffGen (I := I) (M := M) g 3 3 E1
          (Equiv.swap (1 : Fin 3) 2)) := by
    dsimp only [Y, Z]
    rw [appCcRS_smul_right, appCcRS_sub_right,
      appCcRS_add_right, perm_re, perm_re, perm_re]
  let q : ℝ := riemannianFiberNormSq (I := I) (M := M) g 3 3 x
    (E1.toSection x)
  have hq0 : 0 ≤ q := riemannianFiberNormSq_nonneg _ _ _ _ _
  have hre : ∀ ρ : Equiv.Perm (Fin 3),
      riemannianFiberNormSq (I := I) (M := M) g 3 3 x
          ((reindexCoeffGen (I := I) (M := M) g 3 3 E1 ρ).toSection x) = q := by
    intro ρ
    have h := rfns_iteratedCovGrad_reindexCoeffGen_eq
      (I := I) (M := M) g 3 3 E1 ρ 0 x
    simpa only [iteratedCovGrad_zero, Nat.add_zero, q] using h
  have hYq : riemannianFiberNormSq (I := I) (M := M) g 3 3 x
      (Y.toSection x) ≤ 3 * q := by
    let A := reindexCoeffGen (I := I) (M := M) g 3 3 E1
      (Equiv.swap (0 : Fin 3) 2)
    let B := reindexCoeffGen (I := I) (M := M) g 3 3 E1 (finRotate 3)
    let C := reindexCoeffGen (I := I) (M := M) g 3 3 E1
      (Equiv.swap (1 : Fin 3) 2)
    rw [hYsplit, SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul,
      Pi.smul_apply, riemannianFiberNormSq_smul]
    rw [show ((A + B - C).toSection x) =
        (A.toSection x + B.toSection x) - C.toSection x from by
      rw [SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_add]
      rfl]
    have hsub := riemannianFiberNormSq_sub_le
      (I := I) (M := M) g 3 3 x
      (A.toSection x + B.toSection x) (C.toSection x)
    have hadd := riemannianFiberNormSq_add_le
      (I := I) (M := M) g 3 3 x (A.toSection x) (B.toSection x)
    have hA := hre (Equiv.swap (0 : Fin 3) 2)
    have hB := hre (finRotate 3)
    have hC := hre (Equiv.swap (1 : Fin 3) 2)
    change riemannianFiberNormSq (I := I) (M := M) g 3 3 x
        (A.toSection x) = q at hA
    change riemannianFiberNormSq (I := I) (M := M) g 3 3 x
        (B.toSection x) = q at hB
    change riemannianFiberNormSq (I := I) (M := M) g 3 3 x
        (C.toSection x) = q at hC
    rw [hC] at hsub
    rw [hA, hB] at hadd
    nlinarith
  have hconn_id : connLowOp (I := I) (M := M) g gm =
      appCcRS (I := I) (M := M) g 3 3 3
        (permCoeff (I := I) (M := M) g lowPerm) Y := by
    rw [conn_nf]
  have hconn : riemannianFiberNormSq (I := I) (M := M) g 3 3 x
      ((connLowOp (I := I) (M := M) g gm).toSection x) ≤ 3 * F := by
    rw [hconn_id, perm_left_rfns]
    exact hYq.trans (mul_le_mul_of_nonneg_left hE (by norm_num))
  calc
    riemannianFiberNormSq (I := I) (M := M) g 4 4 x
        ((dagTopOp (I := I) (M := M) g gm).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g 4 4 x
        ((slotExtend (I := I) (M := M) g 3 3
          (connLowOp (I := I) (M := M) g gm)).toSection x) := by
          rw [dagTopOp, perm_left_rfns]
    _ = n * riemannianFiberNormSq (I := I) (M := M) g 3 3 x
        ((connLowOp (I := I) (M := M) g gm).toSection x) := by
          simpa only [n] using rfns_slotExtend_eq
            (I := I) (M := M) g 3 3
            (connLowOp (I := I) (M := M) g gm) x
    _ ≤ n * (3 * F) := mul_le_mul_of_nonneg_left hconn (by positivity)
    _ = K := by dsimp only [K]; ring

/-- The transparent Ricci top coefficient is uniformly linear in the fibre
perturbation radius on the diagonal realized segment. -/
theorem ricciTop_cap_unif :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ}, δ ≤ 1 / 3 → 0 ≤ δ →
        ∀ (hTδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
          (hδZ : gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g
              (0 : SmoothCcTensor g 0 2)) δ)
          {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 4 2 x
            ((ricciTop (I := I) (M := M) g
              (realizedFam (I := I) g T 0 hTδ hδZ s) T).toSection x) ≤
          (K * (δ / (1 - δ))) ^ 2 := by
  obtain ⟨KD, hKD0, hKD⟩ := dagTop_cap_unif (I := I) (M := M)
  let K := 2 * deTurckArmFibreConst (Module.finrank ℝ E) * (1 + KD)
  refine ⟨K, mul_nonneg
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (by linarith), ?_⟩
  intro g T hT δ hδ_le hδ0 hTδ hδZ s hs x
  let gm := realizedFam (I := I) g T 0 hTδ hδZ s
  let P := convexPerturbation (I := I) g T 0 s
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  have hsmem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      gm.inner y v w =
        g.inner y v w + ccTensorBilinSymm (I := I) g P y v w :=
    fun y v w => realizedFam_inner_of_mem
      (I := I) g T 0 hTδ hδZ hsmem y v w
  have hP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ := by
    convert convexPerturbation_gFibreOpBound
      (I := I) (M := M) g T 0 hTδ hδZ hs.1 hs.2 using 1
    all_goals ring
  have hA := daTrans_cap (I := I) (M := M) g T hT
    hδ_lt hδ0 hTδ hδZ s hs x
  have hD := hKD g gm P hδ_le hδ0 hP htie x
  have hc := riemannianFiberNormSq_compRS_le_mul
    (I := I) (M := M) g 4 4 2 x
    ((daTrans (I := I) (M := M) g gm T).toSection x)
    ((dagTopOp (I := I) (M := M) g gm).toSection x)
  rw [← appCcRS_toSection] at hc
  have hprod := mul_le_mul hA hD
    (riemannianFiberNormSq_nonneg (I := I) (M := M) g 4 4 x _)
    (sq_nonneg (2 * deTurckArmFibreConst (Module.finrank ℝ E) *
      (δ / (1 - δ))))
  calc
    _ ≤ riemannianFiberNormSq (I := I) (M := M) g 4 2 x
          ((daTrans (I := I) (M := M) g gm T).toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g 4 4 x
          ((dagTopOp (I := I) (M := M) g gm).toSection x) := by
      simpa only [ricciTop, gm] using hc
    _ ≤ (2 * deTurckArmFibreConst (Module.finrank ℝ E) *
          (δ / (1 - δ))) ^ 2 * KD := hprod
    _ ≤ (2 * deTurckArmFibreConst (Module.finrank ℝ E) *
          (δ / (1 - δ))) ^ 2 * (1 + KD) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      nlinarith
    _ = (K * (δ / (1 - δ))) ^ 2 := by
      simp only [K]
      ring

/-- The complete principal-face coefficient left after subtracting the metric
principal deviation is uniformly small in the fibre radius. -/
theorem topKer_cap_unif :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ}, δ ≤ 1 / 3 → 0 ≤ δ →
        ∀ (hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
          (hδZ : gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g
              (0 : SmoothCcTensor g 0 2)) δ)
          {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
        let gm := realizedFam (I := I) g T 0 hδ hδZ s
        riemannianFiberNormSq (I := I) (M := M) g 4 2 x
            ((lieRefold2 (I := I) (M := M) g T hδ hδZ s +
              (-2 * s : ℝ) •
                ricciTop (I := I) (M := M) g gm T).toSection x) ≤
          (K * (δ / (1 - δ) ^ 2)) ^ 2 := by
  obtain ⟨KR, hKR0, hR⟩ := ricciTop_cap_unif (I := I) (M := M)
  let KL := 4 * deTurckArmFibreConst (Module.finrank ℝ E)
  let K0 := 2 * KL ^ 2 + 8 * KR ^ 2
  have hK0 : 0 ≤ K0 := by positivity
  refine ⟨Real.sqrt K0, Real.sqrt_nonneg _, ?_⟩
  intro g T hT δ hδ_le hδ0 hδ hδZ s hs x
  dsimp only
  let gm := realizedFam (I := I) g T 0 hδ hδZ s
  let r1 := δ / (1 - δ)
  let r2 := δ / (1 - δ) ^ 2
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  have hr1 : 0 ≤ r1 := div_nonneg hδ0 (by linarith)
  have hr2 : 0 ≤ r2 := div_nonneg hδ0 (sq_nonneg _)
  have hr12 : r1 ≤ r2 := by
    have hb : 0 < 1 - δ := by linarith
    rw [div_le_div_iff₀ hb (sq_pos_of_pos hb)]
    nlinarith [mul_nonneg (sq_nonneg δ) (le_of_lt hb)]
  have hL := lieRefold2_cap (I := I) (M := M)
    g T hδ_lt hδ0 hδ hδZ hs x
  have hR1 := hR g T hT hδ_le hδ0 hδ hδZ hs x
  have hR2 := hR1.trans (pow_le_pow_left₀
    (mul_nonneg hKR0 hr1) (mul_le_mul_of_nonneg_left hr12 hKR0) 2)
  have hRs : riemannianFiberNormSq (I := I) (M := M) g 4 2 x
      (((-2 * s : ℝ) •
        ricciTop (I := I) (M := M) g gm T).toSection x) ≤
        4 * (KR * r2) ^ 2 := by
    rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
      riemannianFiberNormSq_smul]
    calc
      (-2 * s) ^ 2 * riemannianFiberNormSq (I := I) (M := M) g 4 2 x
          ((ricciTop (I := I) (M := M) g gm T).toSection x) ≤
        4 * riemannianFiberNormSq (I := I) (M := M) g 4 2 x
          ((ricciTop (I := I) (M := M) g gm T).toSection x) := by
            apply mul_le_mul_of_nonneg_right
              (by nlinarith [hs.1, hs.2])
              (riemannianFiberNormSq_nonneg
                (I := I) (M := M) g 4 2 x _)
      _ ≤ 4 * (KR * r2) ^ 2 :=
        mul_le_mul_of_nonneg_left hR2 (by norm_num)
  have hsum := riemannianFiberNormSq_add_le
    (I := I) (M := M) g 4 2 x
    ((lieRefold2 (I := I) (M := M) g T hδ hδZ s).toSection x)
    (((-2 * s : ℝ) •
      ricciTop (I := I) (M := M) g gm T).toSection x)
  have htarget : (Real.sqrt K0 * r2) ^ 2 = K0 * r2 ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hK0]
  rw [htarget]
  dsimp only [KL, K0, r1, r2] at hL hR2 hRs ⊢
  simp only [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add,
    Pi.add_apply] at hsum ⊢
  linarith

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.LowBaseInternal

end
