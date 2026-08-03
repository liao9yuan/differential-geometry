import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegBgC0Pair
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegBgC1Pair
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderLowBaseA1Pair
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderLowBaseH2Pair

/-!
# Fixed-background low first-order action pairs

This module integrates the sharp fixed-background `C0` and `C1` coefficient
pairs along the realized metric path and packages the resulting low
`H² → H¹` first-order action estimate.
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
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open LieCorr0Core

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private noncomputable def bg0Fam
    (g gB : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) : SmoothCcTensor g 2 2 :=
  LowBaseInternal.rhsSelfLow (I := I) (M := M)
      g gB T hδ hδZ s -
    LowBaseInternal.rhsSelfLow (I := I) (M := M)
      g g T hδ hδZ s

private theorem bg0Fam_eq
    (g gB : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) :
    bg0Fam (I := I) (M := M) g gB T hδ hδZ s =
      let gm := realizedFam (I := I) g T 0 hδ hδZ s
      (deTurckLieCoeffField (I := I) (M := M) g gm gB +
          lieCorr0Field (I := I) (M := M) g gm gB) -
        (deTurckLieCoeffField (I := I) (M := M) g gm g +
          lieCorr0Field (I := I) (M := M) g gm g) := by
  simp only [bg0Fam, LowBaseInternal.rhsSelfLow]
  module

private theorem bg0Fam_joint
    (g gB : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g 2
      (bg0Fam (I := I) (M := M) g gB T hδ hδZ)
      (δ := δ) (δ' := δ) := by
  exact threeArmJoint_sub (I := I) (M := M) g _ _
    (LowBaseInternal.selfLow_joint
      (I := I) (M := M) g gB T hδ hδZ)
    (LowBaseInternal.selfLow_joint
      (I := I) (M := M) g g T hδ hδZ)

private noncomputable def bg0PairInt
    (g gB : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδU : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g U) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    SmoothCcTensor g 2 2 :=
  pathIntegralCoeffField (I := I) (M := M) g 2 2
    (fun s =>
      bg0Fam (I := I) (M := M) g gB T hδT hδZ s -
        bg0Fam (I := I) (M := M) g gB U hδU hδZ s)
    (realizedSmallSet (δ := δ) (δ' := δ))
    realizedSmallSet_isOpen
    (by
      rw [Set.uIcc_of_le zero_le_one]
      exact Icc_subset_realizedSmallSet hδ_lt hδ_lt)
    (threeArmJoint_sub (I := I) (M := M) g _ _
      (bg0Fam_joint (I := I) (M := M) g gB T hδT hδZ)
      (bg0Fam_joint (I := I) (M := M) g gB U hδU hδZ))

private theorem bg0_int_eq
    (g gB : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδU : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g U) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    (LowBaseInternal.selfLowInt (I := I) (M := M)
          g gB T hδ_lt hδT hδZ -
        LowBaseInternal.selfLowInt (I := I) (M := M)
          g g T hδ_lt hδT hδZ) -
      (LowBaseInternal.selfLowInt (I := I) (M := M)
          g gB U hδ_lt hδU hδZ -
        LowBaseInternal.selfLowInt (I := I) (M := M)
          g g U hδ_lt hδU hδZ) =
      bg0PairInt (I := I) (M := M)
        g gB T U hδ_lt hδT hδU hδZ := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply TensorRSSpace.toModel_injective
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆
      realizedSmallSet (δ := δ) (δ' := δ) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_realizedSmallSet hδ_lt hδ_lt
  have hBT := jointContMDiff_toModel_continuous_slice
    (I := I) g 2 2
    (LowBaseInternal.rhsSelfLow
      (I := I) (M := M) g gB T hδT hδZ)
    (realizedSmallSet (δ := δ) (δ' := δ))
    (LowBaseInternal.selfLow_joint
      (I := I) (M := M) g gB T hδT hδZ) x
  have h0T := jointContMDiff_toModel_continuous_slice
    (I := I) g 2 2
    (LowBaseInternal.rhsSelfLow
      (I := I) (M := M) g g T hδT hδZ)
    (realizedSmallSet (δ := δ) (δ' := δ))
    (LowBaseInternal.selfLow_joint
      (I := I) (M := M) g g T hδT hδZ) x
  have hBU := jointContMDiff_toModel_continuous_slice
    (I := I) g 2 2
    (LowBaseInternal.rhsSelfLow
      (I := I) (M := M) g gB U hδU hδZ)
    (realizedSmallSet (δ := δ) (δ' := δ))
    (LowBaseInternal.selfLow_joint
      (I := I) (M := M) g gB U hδU hδZ) x
  have h0U := jointContMDiff_toModel_continuous_slice
    (I := I) g 2 2
    (LowBaseInternal.rhsSelfLow
      (I := I) (M := M) g g U hδU hδZ)
    (realizedSmallSet (δ := δ) (δ' := δ))
    (LowBaseInternal.selfLow_joint
      (I := I) (M := M) g g U hδU hδZ) x
  have hBTi : IntervalIntegrable
      (fun s : ℝ => TensorRSSpace.toModel
        ((LowBaseInternal.rhsSelfLow
          (I := I) (M := M) g gB T hδT hδZ s).toSection x))
      MeasureTheory.volume 0 1 :=
    (hBT.mono hSI).intervalIntegrable
  have h0Ti : IntervalIntegrable
      (fun s : ℝ => TensorRSSpace.toModel
        ((LowBaseInternal.rhsSelfLow
          (I := I) (M := M) g g T hδT hδZ s).toSection x))
      MeasureTheory.volume 0 1 :=
    (h0T.mono hSI).intervalIntegrable
  have hBUi : IntervalIntegrable
      (fun s : ℝ => TensorRSSpace.toModel
        ((LowBaseInternal.rhsSelfLow
          (I := I) (M := M) g gB U hδU hδZ s).toSection x))
      MeasureTheory.volume 0 1 :=
    (hBU.mono hSI).intervalIntegrable
  have h0Ui : IntervalIntegrable
      (fun s : ℝ => TensorRSSpace.toModel
        ((LowBaseInternal.rhsSelfLow
          (I := I) (M := M) g g U hδU hδZ s).toSection x))
      MeasureTheory.volume 0 1 :=
    (h0U.mono hSI).intervalIntegrable
  simp only [LowBaseInternal.selfLowInt, bg0PairInt, bg0Fam,
    pathIntegralCoeffField_toModel, SmoothCcTensor.toSection_sub,
    ContMDiffSection.coe_sub, Pi.sub_apply, TensorRSSpace.toModel_sub]
  rw [intervalIntegral.integral_sub (hBTi.sub h0Ti) (hBUi.sub h0Ui),
    intervalIntegral.integral_sub hBTi h0Ti,
    intervalIntegral.integral_sub hBUi h0Ui]

private theorem c0_bg_sub
    (g gB : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδU : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g U) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    (lowBaseData (I := I) (M := M) g gB T hδ_lt hδT hδZ).C0 -
        (lowBaseData (I := I) (M := M) g gB U hδ_lt hδU hδZ).C0 =
      lowC0Diff (I := I) (M := M) g T U hδ_lt hδT hδU hδZ +
        bg0PairInt (I := I) (M := M)
          g gB T U hδ_lt hδT hδU hδZ := by
  have hsame :
      LowBaseInternal.selfLowInt (I := I) (M := M)
          g g T hδ_lt hδT hδZ -
        LowBaseInternal.selfLowInt (I := I) (M := M)
          g g U hδ_lt hδU hδZ =
      lowC0Diff (I := I) (M := M)
        g T U hδ_lt hδT hδU hδZ := by
    calc
      _ = (lowBaseData (I := I) (M := M)
              g g T hδ_lt hδT hδZ).C0 -
            (lowBaseData (I := I) (M := M)
              g g U hδ_lt hδU hδZ).C0 := by
        rw [LowBaseInternal.c0_eq, LowBaseInternal.c0_eq]
        module
      _ = lowC0Diff (I := I) (M := M)
          g T U hδ_lt hδT hδU hδZ :=
        lowC0_sub (I := I) (M := M)
          g T U hδ_lt hδT hδU hδZ
  have hbg := bg0_int_eq (I := I) (M := M)
    g gB T U hδ_lt hδT hδU hδZ
  rw [LowBaseInternal.c0_eq, LowBaseInternal.c0_eq]
  calc
    _ = LowBaseInternal.selfLowInt (I := I) (M := M)
          g gB T hδ_lt hδT hδZ -
        LowBaseInternal.selfLowInt (I := I) (M := M)
          g gB U hδ_lt hδU hδZ := by
      module
    _ = (LowBaseInternal.selfLowInt (I := I) (M := M)
            g g T hδ_lt hδT hδZ -
          LowBaseInternal.selfLowInt (I := I) (M := M)
            g g U hδ_lt hδU hδZ) +
        ((LowBaseInternal.selfLowInt (I := I) (M := M)
              g gB T hδ_lt hδT hδZ -
            LowBaseInternal.selfLowInt (I := I) (M := M)
              g g T hδ_lt hδT hδZ) -
          (LowBaseInternal.selfLowInt (I := I) (M := M)
              g gB U hδ_lt hδU hδZ -
            LowBaseInternal.selfLowInt (I := I) (M := M)
              g g U hδ_lt hδU hδZ)) := by
      module
    _ = lowC0Diff (I := I) (M := M)
          g T U hδ_lt hδT hδU hδZ +
        bg0PairInt (I := I) (M := M)
          g gB T U hδ_lt hδT hδU hδZ := by
      rw [hsame, hbg]

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 2400000 in
set_option linter.unusedVariables false in
/-- The path-integrated order-zero background correction is `H¹`-Lipschitz
with no third or fourth derivative of the state difference. -/
theorem bg0_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B0 : ℝ → ℝ → ℝ, ∃ B1 : ℝ → ℝ,
      0 < ρ ∧
      (∀ R A : ℝ, 0 ≤ B0 R A) ∧
      (∀ A : ℝ, 0 ≤ B1 A) ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (hδ_le : δ ≤ (1 : ℝ) / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ (R A D2 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ N →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
      lowJetSq (I := I) (M := M) g 1
          (bg0PairInt (I := I) (M := M) g gB T U
            (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδU hδZ) ≤
        (B0 R A * D2 + B1 A * N) ^ 2 := by
  obtain ⟨ρ, B0, B1, hρ, hB0, hB1, hpair⟩ :=
    lie0_bg_pair_h1 (I := I) (M := M) hDim g gB
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  refine ⟨ρ, B0, B1, hρ, hB0, hB1, ?_⟩
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    hTHs hUHs R A D2 N hR hA hD2 hN hU2 hT3 hTU2 hTUn
  let hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  let Φ : ℝ → SmoothCcTensor g 2 2 := fun s =>
    bg0Fam (I := I) (M := M) g gB T hδT hδZ s -
      bg0Fam (I := I) (M := M) g gB U hδU hδZ s
  let S : Set ℝ := realizedSmallSet (δ := δ) (δ' := δ)
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ S := by
    dsimp only [S]
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_realizedSmallSet hδ_lt hδ_lt
  have hjoint : linearizedRicciThreeArmHjoint
      (I := I) (M := M) g 2 Φ (δ := δ) (δ' := δ) :=
    threeArmJoint_sub (I := I) (M := M) g _ _
      (bg0Fam_joint (I := I) (M := M) g gB T hδT hδZ)
      (bg0Fam_joint (I := I) (M := M) g gB U hδU hδZ)
  let B : ℝ := B0 R A * D2 + B1 A * N
  have hB : 0 ≤ B :=
    add_nonneg (mul_nonneg (hB0 R A) hD2)
      (mul_nonneg (hB1 A) hN)
  have hpoint : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      lowJetSq (I := I) (M := M) g 1 (Φ s) ≤ B ^ 2 := by
    intro s hs
    set gmT : SmoothRiemannianMetric I M :=
      realizedFam (I := I) g T 0 hδT hδZ s with hgmT
    set gmU : SmoothRiemannianMetric I M :=
      realizedFam (I := I) g U 0 hδU hδZ s with hgmU
    set P : SmoothCcTensor g 0 2 := s • T with hP
    set Q : SmoothCcTensor g 0 2 := s • U with hQ
    have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
      Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
    have hs2 : s ^ 2 ≤ (1 : ℝ) := by
      nlinarith [hs.1, hs.2]
    have hsabs : ‖s‖ ≤ (1 : ℝ) := by
      rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
      exact hs.2
    have hPsymm : ∀ (x : M) (u v : TangentSpace I x),
        ccTensorBilin (I := I) g P x u v =
          ccTensorBilin (I := I) g P x v u := by
      intro x u v
      simp only [hP, ccTensorBilin_apply, ccTensorModel_smul,
        ContinuousMultilinearMap.smul_apply, smul_eq_mul]
      apply congrArg (fun z : ℝ => s * z)
      simpa only [ccTensorBilin_apply] using hT x u v
    have hQsymm : ∀ (x : M) (u v : TangentSpace I x),
        ccTensorBilin (I := I) g Q x u v =
          ccTensorBilin (I := I) g Q x v u := by
      intro x u v
      simp only [hQ, ccTensorBilin_apply, ccTensorModel_smul,
        ContinuousMultilinearMap.smul_apply, smul_eq_mul]
      apply congrArg (fun z : ℝ => s * z)
      simpa only [ccTensorBilin_apply] using hU x u v
    have hPtie : ∀ (x : M) (u v : TangentSpace I x),
        gmT.inner x u v =
          g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
      intro x u v
      simpa only [hgmT, hP, convexPerturbation, smul_zero, zero_add] using
        realizedFam_inner_of_mem (I := I) g T 0 hδT hδZ hs_mem x u v
    have hQtie : ∀ (x : M) (u v : TangentSpace I x),
        gmU.inner x u v =
          g.inner x u v + ccTensorBilinSymm (I := I) g Q x u v := by
      intro x u v
      simpa only [hgmU, hQ, convexPerturbation, smul_zero, zero_add] using
        realizedFam_inner_of_mem (I := I) g U 0 hδU hδZ hs_mem x u v
    have hδP : gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g P) δ := by
      intro x u v
      have hraw := convexPerturbation_gFibreOpBound_abs
        (I := I) g T 0 hδT hδZ s x u v
      have heq : |1 - s| * δ + |s| * δ = δ := by
        rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
          abs_of_nonneg hs.1]
        ring
      simpa only [hP, convexPerturbation, smul_zero, zero_add, heq] using hraw
    have hδQ : gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g Q) δ := by
      intro x u v
      have hraw := convexPerturbation_gFibreOpBound_abs
        (I := I) g U 0 hδU hδZ s x u v
      have heq : |1 - s| * δ + |s| * δ = δ := by
        rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
          abs_of_nonneg hs.1]
        ring
      simpa only [hQ, convexPerturbation, smul_zero, zero_add, heq] using hraw
    have hPn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ := by
      rw [hP, ccTensorToHs_smul, norm_smul]
      exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
        (by simpa using hTHs)
    have hQn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρ := by
      rw [hQ, ccTensorToHs_smul, norm_smul]
      exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
        (by simpa using hUHs)
    have hQ2 : lowJetSq (I := I) (M := M) g 2 Q ≤ R ^ 2 := by
      rw [hQ, jetSmul]
      exact (mul_le_of_le_one_left
        (jetNn (I := I) (M := M) (m := 2) g U) hs2).trans hU2
    have hP3 : lowJetSq (I := I) (M := M) g 3 P ≤ A ^ 2 := by
      rw [hP, jetSmul]
      exact (mul_le_of_le_one_left
        (jetNn (I := I) (M := M) (m := 3) g T) hs2).trans hT3
    have hPQ : P - Q = s • (T - U) := by
      rw [hP, hQ, smul_sub]
    have hPQ2 : lowJetSq (I := I) (M := M) g 2 (P - Q) ≤ D2 ^ 2 := by
      rw [hPQ, jetSmul]
      exact (mul_le_of_le_one_left
        (jetNn (I := I) (M := M) (m := 2) g (T - U)) hs2).trans hTU2
    have hPQn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ≤ N := by
      rw [hPQ, ccTensorToHs_smul, norm_smul]
      exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
        (by simpa using hTUn)
    have hp := hpair gmT gmU P Q hPsymm hQsymm hPtie hQtie
      hδ_le hδ0 hδP hδ_le hδ0 hδQ hPn hQn
      R A D2 hR hA hD2 hQ2 hP3 hPQ2
    have hΦ : Φ s =
        (deTurckLieCoeffField (I := I) (M := M) g gmT gB +
            lieCorr0Field (I := I) (M := M) g gmT gB -
          (deTurckLieCoeffField (I := I) (M := M) g gmT g +
            lieCorr0Field (I := I) (M := M) g gmT g)) -
        (deTurckLieCoeffField (I := I) (M := M) g gmU gB +
            lieCorr0Field (I := I) (M := M) g gmU gB -
          (deTurckLieCoeffField (I := I) (M := M) g gmU g +
            lieCorr0Field (I := I) (M := M) g gmU g)) := by
      dsimp only [Φ]
      rw [bg0Fam_eq (I := I) (M := M) g gB T hδT hδZ s,
        bg0Fam_eq (I := I) (M := M) g gB U hδU hδZ s,
        ← hgmT, ← hgmU]
    rw [hΦ]
    have hactual0 : 0 ≤ B0 R A * D2 +
        B1 A * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ :=
      add_nonneg (mul_nonneg (hB0 R A) hD2)
        (mul_nonneg (hB1 A) (norm_nonneg _))
    have hlin : B0 R A * D2 +
        B1 A * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ≤ B := by
      dsimp only [B]
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hPQn (hB1 A))
    exact hp.trans (pow_le_pow_left₀ hactual0 hlin 2)
  have hpath := path_jetL2_le (I := I) (M := M)
    g 2 2 1 Φ S realizedSmallSet_isOpen hSI hjoint
    (B := B) hB
    (by
      intro s hs
      simpa only [lowJetSq, Nat.reduceAdd] using hpoint s hs)
  simpa only [lowJetSq, bg0PairInt, Φ, S, B, Nat.reduceAdd] using hpath

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 2400000 in
set_option linter.unusedVariables false in
/-- The full arbitrary-background order-zero low-base coefficient is `H¹`-
Lipschitz on a common spectral `H²` ball, with no fourth-jet input. -/
theorem c0_bg_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ Bs : ℝ → ℝ,
      ∃ B0 : ℝ → ℝ → ℝ, ∃ B1 : ℝ → ℝ,
      0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ Bs R) ∧
      (∀ R A : ℝ, 0 ≤ B0 R A) ∧
      (∀ A : ℝ, 0 ≤ B1 A) ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (hδ_le : δ ≤ (1 : ℝ) / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D2 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ N →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
      lowJetSq (I := I) (M := M) g 1
          ((lowBaseData (I := I) (M := M) g gB T
              (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδZ).C0 -
            (lowBaseData (I := I) (M := M) g gB U
              (lt_of_le_of_lt hδ_le (by norm_num)) hδU hδZ).C0) ≤
        2 * (Bs R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) +
          (B0 R A * D2 + B1 A * N) ^ 2) := by
  obtain ⟨ρc, Bs, hρc, hBs, hc⟩ :=
    c0Diff_tame (I := I) (M := M) hDim g
  obtain ⟨ρb, B0, B1, hρb, hB0, hB1, hb⟩ :=
    bg0_pair_h1 (I := I) (M := M) hDim g gB
  refine ⟨min ρc ρb, Bs, B0, B1, lt_min hρc hρb,
    hBs, hB0, hB1, ?_⟩
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    R A D2 N hR hA hD2 hN hT2 hU2 hT3 hU3 hTU2 hTn hUn hTUn
  have hc0 := hc T U hT hU hδ_le hδ0 hδT hδU hδZ
    R A D2 N hR hA hD2 hN hT2 hU2 hT3 hU3 hTU2
    (hTn.trans (min_le_left _ _)) (hUn.trans (min_le_left _ _)) hTUn
  have hb0 := hb T U hT hU hδ_le hδ0 hδT hδU hδZ
    (hTn.trans (min_le_right _ _)) (hUn.trans (min_le_right _ _))
    R A D2 N hR hA hD2 hN hU2 hT3 hTU2 hTUn
  rw [c0_bg_sub (I := I) (M := M) g gB T U
    (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδU hδZ]
  exact (jetAdd (I := I) (M := M) g 1 _ _).trans
    (mul_le_mul_of_nonneg_left (add_le_add hc0 hb0) (by norm_num))

private noncomputable def c1BgDiff
    (g gB : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδU : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g U) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    SmoothCcTensor g 3 2 :=
  pathIntegralCoeffField (I := I) (M := M) g 3 2
    (fun s =>
      rhsLow1Coeff (I := I) (M := M) g gB T 0 hδT hδZ s -
        rhsLow1Coeff (I := I) (M := M) g gB U 0 hδU hδZ s)
    (realizedSmallSet (δ := δ) (δ' := δ))
    realizedSmallSet_isOpen
    (by
      rw [Set.uIcc_of_le zero_le_one]
      exact Icc_subset_realizedSmallSet hδ_lt hδ_lt)
    (threeArmJoint_sub (I := I) (M := M) g _ _
      (rhsLow1_path_joint (I := I) (M := M) g gB T 0 hδT hδZ)
      (rhsLow1_path_joint (I := I) (M := M) g gB U 0 hδU hδZ))

private theorem c1_bg_sub
    (g gB : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδU : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g U) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    (lowBaseData (I := I) (M := M) g gB T hδ_lt hδT hδZ).C1 -
        (lowBaseData (I := I) (M := M) g gB U hδ_lt hδU hδZ).C1 =
      c1BgDiff (I := I) (M := M) g gB T U hδ_lt hδT hδU hδZ := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply TensorRSSpace.toModel_injective
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆
      realizedSmallSet (δ := δ) (δ' := δ) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_realizedSmallSet hδ_lt hδ_lt
  have hTcont :=
    jointContMDiff_toModel_continuous_slice
      (I := I) g 3 2
      (fun s => rhsLow1Coeff (I := I) (M := M) g gB
        T 0 hδT hδZ s)
      (realizedSmallSet (δ := δ) (δ' := δ))
      (rhsLow1_path_joint (I := I) (M := M) g gB T 0 hδT hδZ) x
  have hUcont :=
    jointContMDiff_toModel_continuous_slice
      (I := I) g 3 2
      (fun s => rhsLow1Coeff (I := I) (M := M) g gB
        U 0 hδU hδZ s)
      (realizedSmallSet (δ := δ) (δ' := δ))
      (rhsLow1_path_joint (I := I) (M := M) g gB U 0 hδU hδZ) x
  have hTint : IntervalIntegrable
      (fun s : ℝ => TensorRSSpace.toModel
        ((rhsLow1Coeff (I := I) (M := M) g gB
          T 0 hδT hδZ s).toSection x))
      MeasureTheory.volume 0 1 :=
    (hTcont.mono hSI).intervalIntegrable
  have hUint : IntervalIntegrable
      (fun s : ℝ => TensorRSSpace.toModel
        ((rhsLow1Coeff (I := I) (M := M) g gB
          U 0 hδU hδZ s).toSection x))
      MeasureTheory.volume 0 1 :=
    (hUcont.mono hSI).intervalIntegrable
  simp only [lowBaseData, rhsLow1PathIntegral, c1BgDiff,
    pathIntegralCoeffField_toModel, SmoothCcTensor.toSection_sub,
    ContMDiffSection.coe_sub, Pi.sub_apply, TensorRSSpace.toModel_sub]
  rw [intervalIntegral.integral_sub hTint hUint]

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 2400000 in
set_option linter.unusedVariables false in
/-- The complete pointwise order-one Ricci--DeTurck coefficient has the
critical pair modulus for an arbitrary fixed DeTurck background. -/
theorem rhs1_bg_pair_h2
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M) :
    ∃ ρ B0 B1 : ℝ,
      0 < ρ ∧ 0 ≤ B0 ∧ 0 ≤ B1 ∧
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
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ (A D3 : ℝ), 0 ≤ A → 0 ≤ D3 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      let D2 := ‖ccTensorToHs (I := I) (M := M)
        g 2 (2 : ℝ) (T - U)‖
      lowJetSq (I := I) (M := M) g 2
          ((-2 : ℝ) •
              (linearizedRicciConnDiffOrder1CoeffField
                  (I := I) (M := M) g gT -
                linearizedRicciConnDiffOrder1CoeffField
                  (I := I) (M := M) g gU) +
            (deTurckLieArm1Coeff (I := I) (M := M) g gT gB -
              deTurckLieArm1Coeff (I := I) (M := M) g gU gB)) ≤
        (B0 * D3 + B1 * D2 + B1 * A * D2) ^ 2 := by
  obtain ⟨ρr, R0, R1, hρr, hR0, hR1, hricci⟩ :=
    ricci1_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρl, L0, L1, hρl, hL0, hL1, hlie⟩ :=
    lie1_bg_pair_h2 (I := I) (M := M) hDim g gB
  let ρ : ℝ := min ρr ρl
  let B0 : ℝ := 4 * R0 + 2 * L0
  let B1 : ℝ := 4 * R1 + 2 * L1
  have hρ : 0 < ρ := lt_min hρr hρl
  have hB0 : 0 ≤ B0 :=
    add_nonneg (mul_nonneg (by norm_num) hR0)
      (mul_nonneg (by norm_num) hL0)
  have hB1 : 0 ≤ B1 :=
    add_nonneg (mul_nonneg (by norm_num) hR1)
      (mul_nonneg (by norm_num) hL1)
  refine ⟨ρ, B0, B1, hρ, hB0, hB1, ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δ hδ_le hδ0 hδT hδU hδZ hTHs hUHs
    A D3 hA hD3 hT3 hTU3
  dsimp only
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  let XR : ℝ := R0 * D3 + R1 * N + R1 * A * N
  let XL : ℝ := L0 * D3 + L1 * N + L1 * A * N
  let VR : SmoothCcTensor g 3 2 :=
    linearizedRicciConnDiffOrder1CoeffField
        (I := I) (M := M) g gT -
      linearizedRicciConnDiffOrder1CoeffField
        (I := I) (M := M) g gU
  let VL : SmoothCcTensor g 3 2 :=
    deTurckLieArm1Coeff (I := I) (M := M) g gT gB -
      deTurckLieArm1Coeff (I := I) (M := M) g gU gB
  have hN : 0 ≤ N := norm_nonneg _
  have hXR : 0 ≤ XR :=
    add_nonneg
      (add_nonneg (mul_nonneg hR0 hD3) (mul_nonneg hR1 hN))
      (mul_nonneg (mul_nonneg hR1 hA) hN)
  have hXL : 0 ≤ XL :=
    add_nonneg
      (add_nonneg (mul_nonneg hL0 hD3) (mul_nonneg hL1 hN))
      (mul_nonneg (mul_nonneg hL1 hA) hN)
  have hVR : lowJetSq (I := I) (M := M) g 2 VR ≤ XR ^ 2 := by
    simpa only [VR, XR, N] using
      hricci gT gU T U hT hU hTtie hUtie
        hδ_le hδ0 hδT hδU hδZ
        (hTHs.trans (min_le_left _ _))
        (hUHs.trans (min_le_left _ _))
        A D3 hA hD3 hT3 hTU3
  have hVL : lowJetSq (I := I) (M := M) g 2 VL ≤ XL ^ 2 := by
    simpa only [VL, XL, N] using
      hlie gT gU T U hT hU hTtie hUtie
        hδ_le hδ0 hδT hδU
        (hTHs.trans (min_le_right _ _))
        (hUHs.trans (min_le_right _ _))
        A D3 hA hD3 hT3 hTU3
  have hRicS :
      lowJetSq (I := I) (M := M) g 2 ((-2 : ℝ) • VR) ≤
        (2 * XR) ^ 2 := by
    rw [jetSmul]
    nlinarith
  change lowJetSq (I := I) (M := M) g 2
      ((-2 : ℝ) • VR + VL) ≤ _
  calc
    lowJetSq (I := I) (M := M) g 2 ((-2 : ℝ) • VR + VL) ≤
        2 * (lowJetSq (I := I) (M := M) g 2 ((-2 : ℝ) • VR) +
          lowJetSq (I := I) (M := M) g 2 VL) :=
      jetAdd (I := I) (M := M) g 2 ((-2 : ℝ) • VR) VL
    _ ≤ 2 * ((2 * XR) ^ 2 + XL ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hRicS hVL) (by norm_num)
    _ ≤ (2 * (2 * XR + XL)) ^ 2 := by
      nlinarith [sq_nonneg XR, sq_nonneg XL, mul_nonneg hXR hXL]
    _ = (B0 * D3 + B1 * N + B1 * A * N) ^ 2 := by
      simp only [B0, B1, XR, XL]
      ring

private theorem rhs1_bg_sub
    (g gB : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδU : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g U) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) :
    rhsLow1Coeff (I := I) (M := M) g gB T 0 hδT hδZ s -
        rhsLow1Coeff (I := I) (M := M) g gB U 0 hδU hδZ s =
      (-2 : ℝ) •
          (linearizedRicciConnDiffOrder1Coeff
              (I := I) g T 0 hδT hδZ s -
            linearizedRicciConnDiffOrder1Coeff
              (I := I) g U 0 hδU hδZ s) +
        (deTurckLieArm1Coeff (I := I) (M := M) g
            (realizedFam (I := I) g T 0 hδT hδZ s) gB -
          deTurckLieArm1Coeff (I := I) (M := M) g
            (realizedFam (I := I) g U 0 hδU hδZ s) gB) := by
  simp only [rhsLow1Coeff, smul_sub]
  abel

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 3200000 in
set_option linter.unusedVariables false in
/-- The full arbitrary-background order-one low-base coefficient is `H²`-
Lipschitz on a common spectral `H²` ball, with the critical `H³/H²` modulus. -/
theorem c1_bg_pair_h2
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M) :
    ∃ ρ B0 B1 : ℝ,
      0 < ρ ∧ 0 ≤ B0 ∧ 0 ≤ B1 ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (hδ_le : δ ≤ (1 : ℝ) / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ (A D3 : ℝ), 0 ≤ A → 0 ≤ D3 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      lowJetSq (I := I) (M := M) g 2
          ((lowBaseData (I := I) (M := M) g gB T
              (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδZ).C1 -
            (lowBaseData (I := I) (M := M) g gB U
              (lt_of_le_of_lt hδ_le (by norm_num)) hδU hδZ).C1) ≤
        (B0 * D3 +
          B1 * ‖ccTensorToHs (I := I) (M := M)
            g 2 (2 : ℝ) (T - U)‖ +
          B1 * A * ‖ccTensorToHs (I := I) (M := M)
            g 2 (2 : ℝ) (T - U)‖) ^ 2 := by
  obtain ⟨ρ, B0, B1, hρ, hB0, hB1, hkernel⟩ :=
    rhs1_bg_pair_h2 (I := I) (M := M) hDim g gB
  refine ⟨ρ, B0, B1, hρ, hB0, hB1, ?_⟩
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    hTHs hUHs A D3 hA hD3 hT3 hTU3
  let hδ_lt : δ < 1 :=
    lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)
  rw [c1_bg_sub (I := I) (M := M) g gB T U hδ_lt hδT hδU hδZ]
  let Φ : ℝ → SmoothCcTensor g 3 2 := fun s =>
    rhsLow1Coeff (I := I) (M := M) g gB T 0 hδT hδZ s -
      rhsLow1Coeff (I := I) (M := M) g gB U 0 hδU hδZ s
  let S : Set ℝ := realizedSmallSet (δ := δ) (δ' := δ)
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  let B : ℝ := B0 * D3 + B1 * N + B1 * A * N
  have hN : 0 ≤ N := norm_nonneg _
  have hB : 0 ≤ B :=
    add_nonneg
      (add_nonneg (mul_nonneg hB0 hD3) (mul_nonneg hB1 hN))
      (mul_nonneg (mul_nonneg hB1 hA) hN)
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ S := by
    dsimp only [S]
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_realizedSmallSet hδ_lt hδ_lt
  have hjoint :
      linearizedRicciThreeArmHjoint (I := I) (M := M) g 3 Φ
        (δ := δ) (δ' := δ) := by
    dsimp only [Φ]
    exact threeArmJoint_sub (I := I) (M := M) g _ _
      (rhsLow1_path_joint (I := I) (M := M) g gB T 0 hδT hδZ)
      (rhsLow1_path_joint (I := I) (M := M) g gB U 0 hδU hδZ)
  have hpoint : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      lowJetSq (I := I) (M := M) g 2 (Φ s) ≤ B ^ 2 := by
    intro s hs
    set gmT : SmoothRiemannianMetric I M :=
      realizedFam (I := I) g T 0 hδT hδZ s with hgmT
    set gmU : SmoothRiemannianMetric I M :=
      realizedFam (I := I) g U 0 hδU hδZ s with hgmU
    set P : SmoothCcTensor g 0 2 := s • T with hP
    set Q : SmoothCcTensor g 0 2 := s • U with hQ
    have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
      Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
    have hsabs : ‖s‖ ≤ (1 : ℝ) := by
      rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
      exact hs.2
    have hs2 : s ^ 2 ≤ (1 : ℝ) := by
      nlinarith [hs.1, hs.2]
    have hPsymm : ∀ (x : M) (u v : TangentSpace I x),
        ccTensorBilin (I := I) g P x u v =
          ccTensorBilin (I := I) g P x v u := by
      intro x u v
      simp only [hP, ccTensorBilin_apply, ccTensorModel_smul,
        ContinuousMultilinearMap.smul_apply, smul_eq_mul]
      apply congrArg (fun z : ℝ => s * z)
      simpa only [ccTensorBilin_apply] using hT x u v
    have hQsymm : ∀ (x : M) (u v : TangentSpace I x),
        ccTensorBilin (I := I) g Q x u v =
          ccTensorBilin (I := I) g Q x v u := by
      intro x u v
      simp only [hQ, ccTensorBilin_apply, ccTensorModel_smul,
        ContinuousMultilinearMap.smul_apply, smul_eq_mul]
      apply congrArg (fun z : ℝ => s * z)
      simpa only [ccTensorBilin_apply] using hU x u v
    have hPtie : ∀ (x : M) (u v : TangentSpace I x),
        gmT.inner x u v =
          g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
      intro x u v
      simpa only [hgmT, hP, convexPerturbation, smul_zero, zero_add] using
        realizedFam_inner_of_mem (I := I) g T 0 hδT hδZ hs_mem x u v
    have hQtie : ∀ (x : M) (u v : TangentSpace I x),
        gmU.inner x u v =
          g.inner x u v + ccTensorBilinSymm (I := I) g Q x u v := by
      intro x u v
      simpa only [hgmU, hQ, convexPerturbation, smul_zero, zero_add] using
        realizedFam_inner_of_mem (I := I) g U 0 hδU hδZ hs_mem x u v
    have hδP : gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g P) δ := by
      intro x u v
      have hraw := convexPerturbation_gFibreOpBound_abs
        (I := I) g T 0 hδT hδZ s x u v
      have heq : |1 - s| * δ + |s| * δ = δ := by
        rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
          abs_of_nonneg hs.1]
        ring
      simpa only [hP, convexPerturbation, smul_zero, zero_add, heq] using hraw
    have hδQ : gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g Q) δ := by
      intro x u v
      have hraw := convexPerturbation_gFibreOpBound_abs
        (I := I) g U 0 hδU hδZ s x u v
      have heq : |1 - s| * δ + |s| * δ = δ := by
        rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
          abs_of_nonneg hs.1]
        ring
      simpa only [hQ, convexPerturbation, smul_zero, zero_add, heq] using hraw
    have hPnorm :
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ := by
      rw [hP, ccTensorToHs_smul, norm_smul]
      exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
        (by simpa using hTHs)
    have hQnorm :
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρ := by
      rw [hQ, ccTensorToHs_smul, norm_smul]
      exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
        (by simpa using hUHs)
    have hP3 : lowJetSq (I := I) (M := M) g 3 P ≤ A ^ 2 := by
      rw [hP, jetSmul]
      exact (mul_le_of_le_one_left
        (jetNn (I := I) (M := M) (m := 3) g T) hs2).trans hT3
    have hPQ : P - Q = s • (T - U) := by
      rw [hP, hQ, smul_sub]
    have hPQ3 : lowJetSq (I := I) (M := M) g 3 (P - Q) ≤ D3 ^ 2 := by
      rw [hPQ, jetSmul]
      exact (mul_le_of_le_one_left
        (jetNn (I := I) (M := M) (m := 3) g (T - U)) hs2).trans hTU3
    have hPQn :
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ≤ N := by
      rw [hPQ, ccTensorToHs_smul, norm_smul]
      exact (mul_le_mul_of_nonneg_right hsabs hN).trans (by simp)
    have hraw := hkernel gmT gmU P Q hPsymm hQsymm hPtie hQtie
      hδ_le hδ0 hδP hδQ hδZ hPnorm hQnorm
      A D3 hA hD3 hP3 hPQ3
    have hbase0 :
        0 ≤ B0 * D3 +
          B1 * ‖ccTensorToHs (I := I) (M := M)
            g 2 (2 : ℝ) (P - Q)‖ +
          B1 * A * ‖ccTensorToHs (I := I) (M := M)
            g 2 (2 : ℝ) (P - Q)‖ :=
      add_nonneg
        (add_nonneg (mul_nonneg hB0 hD3)
          (mul_nonneg hB1 (norm_nonneg _)))
        (mul_nonneg (mul_nonneg hB1 hA) (norm_nonneg _))
    have hbase :
        B0 * D3 +
            B1 * ‖ccTensorToHs (I := I) (M := M)
              g 2 (2 : ℝ) (P - Q)‖ +
            B1 * A * ‖ccTensorToHs (I := I) (M := M)
              g 2 (2 : ℝ) (P - Q)‖ ≤ B := by
      dsimp only [B]
      have h1 := mul_le_mul_of_nonneg_left hPQn hB1
      have h2 := mul_le_mul_of_nonneg_left hPQn (mul_nonneg hB1 hA)
      dsimp only [N] at h1 h2 ⊢
      linarith
    have hΦeq :
        Φ s =
          (-2 : ℝ) •
              (linearizedRicciConnDiffOrder1CoeffField
                  (I := I) (M := M) g gmT -
                linearizedRicciConnDiffOrder1CoeffField
                  (I := I) (M := M) g gmU) +
            (deTurckLieArm1Coeff (I := I) (M := M) g gmT gB -
              deTurckLieArm1Coeff (I := I) (M := M) g gmU gB) := by
      dsimp only [Φ, gmT, gmU]
      rw [rhs1_bg_sub (I := I) (M := M) g gB T U hδT hδU hδZ s]
      rfl
    rw [hΦeq]
    exact hraw.trans (pow_le_pow_left₀ hbase0 hbase 2)
  have hpath := path_jetL2_le (I := I) (M := M)
    g 3 2 2 Φ S realizedSmallSet_isOpen hSI hjoint
    (B := B) hB hpoint
  simpa only [lowJetSq, c1BgDiff, Φ, S, N, B, Nat.reduceAdd,
    hδ_lt] using hpath

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 3200000 in
set_option linter.unusedVariables false in
/-- The completed arbitrary-background low first-order action is locally
Lipschitz on a common spectral `H²` ball, with no fourth-jet input. -/
theorem a1Lo_bg_pair
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ Bs : ℝ → ℝ,
      ∃ Z0 : ℝ → ℝ → ℝ, ∃ Z1 : ℝ → ℝ,
      ∃ O0 O1 Ca : ℝ,
      0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ Bs R) ∧
      (∀ R A : ℝ, 0 ≤ Z0 R A) ∧
      (∀ A : ℝ, 0 ≤ Z1 A) ∧
      0 ≤ O0 ∧ 0 ≤ O1 ∧ 0 ≤ Ca ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (hδ_le : δ ≤ (1 : ℝ) / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D2 D3 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ N →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        lowJetSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
      let AT := lowBaseData (I := I) (M := M) g gB T
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) hδT hδZ
      let AU := lowBaseData (I := I) (M := M) g gB U
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) hδU hδZ
      ‖AT.a1Lo (I := I) (M := M) - AU.a1Lo (I := I) (M := M)‖ ≤
        Ca *
          (Real.sqrt
              (2 *
                (Bs R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) +
                  (Z0 R A * D2 + Z1 A * N) ^ 2)) +
            (O0 * D3 + O1 * N + O1 * A * N)) := by
  obtain ⟨ρ0, Bs, Z0, Z1, hρ0, hBs, hZ0, hZ1, hc0⟩ :=
    c0_bg_pair_h1 (I := I) (M := M) hDim g gB
  obtain ⟨ρ1, O0, O1, hρ1, hO0, hO1, hc1⟩ :=
    c1_bg_pair_h2 (I := I) (M := M) hDim g gB
  obtain ⟨Ca, hCa, hop⟩ := a1Lo_diff (I := I) (M := M) hDim g
  refine ⟨min ρ0 ρ1, Bs, Z0, Z1, O0, O1, Ca,
    lt_min hρ0 hρ1, hBs, hZ0, hZ1, hO0, hO1, hCa, ?_⟩
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    R A D2 D3 N hR hA hD2 hD3 hN hT2 hU2 hT3 hU3
    hTU2 hTU3 hTn hUn hTUn
  dsimp only
  let AT := lowBaseData (I := I) (M := M) g gB T
    (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) hδT hδZ
  let AU := lowBaseData (I := I) (M := M) g gB U
    (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) hδU hδZ
  have hM0 := hc0 T U hT hU hδ_le hδ0 hδT hδU hδZ
    R A D2 N hR hA hD2 hN hT2 hU2 hT3 hU3 hTU2
    (hTn.trans (min_le_left _ _)) (hUn.trans (min_le_left _ _)) hTUn
  have hM1 := hc1 T U hT hU hδ_le hδ0 hδT hδU hδZ
    (hTn.trans (min_le_right _ _)) (hUn.trans (min_le_right _ _))
    A D3 hA hD3 hT3 hTU3
  let E0 : ℝ :=
    2 *
      (Bs R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) +
        (Z0 R A * D2 + Z1 A * N) ^ 2)
  let R0 : ℝ := Real.sqrt E0
  let R1 : ℝ := O0 * D3 + O1 * N + O1 * A * N
  have hmain : 0 ≤
      Bs R * ((1 + A + A ^ 2) ^ 4 * (D2 ^ 2 + N ^ 2)) :=
    mul_nonneg (hBs R hR)
      (mul_nonneg (by positivity)
        (add_nonneg (sq_nonneg D2) (sq_nonneg N)))
  have hE0 : 0 ≤ E0 := by
    dsimp only [E0]
    exact mul_nonneg (by norm_num)
      (add_nonneg hmain (sq_nonneg _))
  have hR0 : 0 ≤ R0 := Real.sqrt_nonneg _
  have hR1 : 0 ≤ R1 := by
    dsimp only [R1]
    exact add_nonneg
      (add_nonneg (mul_nonneg hO0 hD3) (mul_nonneg hO1 hN))
      (mul_nonneg (mul_nonneg hO1 hA) hN)
  have hj0 :
      lowJetSq (I := I) (M := M) g 1 (AT.C0 - AU.C0) ≤ R0 ^ 2 := by
    calc
      lowJetSq (I := I) (M := M) g 1 (AT.C0 - AU.C0) ≤ E0 := by
        simpa only [AT, AU, E0] using hM0
      _ = R0 ^ 2 := by
        change E0 = Real.sqrt E0 ^ 2
        exact (Real.sq_sqrt hE0).symm
  have hactual0 : 0 ≤
      O0 * D3 +
        O1 * ‖ccTensorToHs (I := I) (M := M)
          g 2 (2 : ℝ) (T - U)‖ +
        O1 * A * ‖ccTensorToHs (I := I) (M := M)
          g 2 (2 : ℝ) (T - U)‖ :=
    add_nonneg
      (add_nonneg (mul_nonneg hO0 hD3)
        (mul_nonneg hO1 (norm_nonneg _)))
      (mul_nonneg (mul_nonneg hO1 hA) (norm_nonneg _))
  have hactual_le :
      O0 * D3 +
          O1 * ‖ccTensorToHs (I := I) (M := M)
            g 2 (2 : ℝ) (T - U)‖ +
          O1 * A * ‖ccTensorToHs (I := I) (M := M)
            g 2 (2 : ℝ) (T - U)‖ ≤ R1 := by
    dsimp only [R1]
    have h1 := mul_le_mul_of_nonneg_left hTUn hO1
    have h2 := mul_le_mul_of_nonneg_left hTUn (mul_nonneg hO1 hA)
    linarith
  have hj1 :
      lowJetSq (I := I) (M := M) g 2 (AT.C1 - AU.C1) ≤ R1 ^ 2 := by
    have hm :
        lowJetSq (I := I) (M := M) g 2 (AT.C1 - AU.C1) ≤
          (O0 * D3 +
              O1 * ‖ccTensorToHs (I := I) (M := M)
                g 2 (2 : ℝ) (T - U)‖ +
              O1 * A * ‖ccTensorToHs (I := I) (M := M)
                g 2 (2 : ℝ) (T - U)‖) ^ 2 := by
      simpa only [AT, AU] using hM1
    exact hm.trans (pow_le_pow_left₀ hactual0 hactual_le 2)
  have hpair := hop AT AU R0 R1 hR0 hR1 hj0 hj1
  simpa only [AT, AU, R0, E0, R1] using hpair

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 3200000 in
set_option linter.unusedVariables false in
/-- On the same DeTurck background, the completed high first-order action is
locally Lipschitz from the spectral `H3` state core to `H3 → H2`, with no
fourth-jet input. -/
theorem a1Hi_self_pair
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, ∃ O0 O1 Ca : ℝ,
      0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      0 ≤ O0 ∧ 0 ≤ O1 ∧ 0 ≤ Ca ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (hδ_le : δ ≤ (1 : ℝ) / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D2 D3 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ N →
        lowJetSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        lowJetSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
      let AT := lowBaseData (I := I) (M := M) g g T
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) hδT hδZ
      let AU := lowBaseData (I := I) (M := M) g g U
        (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) hδU hδZ
      ‖AT.a1Hi (I := I) (M := M) - AU.a1Hi (I := I) (M := M)‖ ≤
        Ca * Real.sqrt
          ((B R * (1 + A ^ 2) * (D3 + D2 + N)) ^ 2 +
            (O0 * D3 + O1 * N + O1 * A * N) ^ 2) := by
  obtain ⟨ρ0, B, hρ0, hB, hc0⟩ :=
    c0_pair_h3 (I := I) (M := M) hDim g
  obtain ⟨ρ1, O0, O1, hρ1, hO0, hO1, hc1⟩ :=
    c1_bg_pair_h2 (I := I) (M := M) hDim g g
  obtain ⟨Ca, hCa, hop⟩ := a1_diff (I := I) (M := M) hDim g
  refine ⟨min ρ0 ρ1, B, O0, O1, Ca,
    lt_min hρ0 hρ1, hB, hO0, hO1, hCa, ?_⟩
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    R A D2 D3 N hR hA hD2 hD3 hN hT2 hU2 hT3 hU3
    hTU2 hTU3 hTn hUn hTUn
  dsimp only
  let hδ_lt : δ < 1 :=
    lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)
  let AT := lowBaseData (I := I) (M := M) g g T hδ_lt hδT hδZ
  let AU := lowBaseData (I := I) (M := M) g g U hδ_lt hδU hδZ
  have hM0 := hc0 T U hT hU hδ_le hδ0 hδT hδU hδZ
    R A D2 D3 N hR hA hD2 hD3 hN hT2 hU2 hT3 hU3 hTU2 hTU3
    (hTn.trans (min_le_left _ _)) (hUn.trans (min_le_left _ _)) hTUn
  have hM1 := hc1 T U hT hU hδ_le hδ0 hδT hδU hδZ
    (hTn.trans (min_le_right _ _)) (hUn.trans (min_le_right _ _))
    A D3 hA hD3 hT3 hTU3
  let R0 : ℝ := B R * (1 + A ^ 2) * (D3 + D2 + N)
  let R1 : ℝ := O0 * D3 + O1 * N + O1 * A * N
  let Q : ℝ := R0 ^ 2 + R1 ^ 2
  let Rt : ℝ := Real.sqrt Q
  have hR0 : 0 ≤ R0 := by
    dsimp only [R0]
    exact mul_nonneg
      (mul_nonneg (hB R hR) (add_nonneg (by norm_num) (sq_nonneg A)))
      (by linarith)
  have hR1 : 0 ≤ R1 := by
    dsimp only [R1]
    exact add_nonneg
      (add_nonneg (mul_nonneg hO0 hD3) (mul_nonneg hO1 hN))
      (mul_nonneg (mul_nonneg hO1 hA) hN)
  have hQ : 0 ≤ Q := by
    dsimp only [Q]
    exact add_nonneg (sq_nonneg R0) (sq_nonneg R1)
  have hRt : 0 ≤ Rt := Real.sqrt_nonneg _
  have hC0eq :
      AT.C0 - AU.C0 =
        lowC0Diff (I := I) (M := M) g T U
          hδ_lt hδT hδU hδZ := by
    simpa only [AT, AU] using
      lowC0_sub (I := I) (M := M) g T U hδ_lt hδT hδU hδZ
  have hj0 :
      lowJetSq (I := I) (M := M) g 2 (AT.C0 - AU.C0) ≤ R0 ^ 2 := by
    rw [hC0eq]
    simpa only [R0] using hM0
  have hactual0 : 0 ≤
      O0 * D3 +
        O1 * ‖ccTensorToHs (I := I) (M := M)
          g 2 (2 : ℝ) (T - U)‖ +
        O1 * A * ‖ccTensorToHs (I := I) (M := M)
          g 2 (2 : ℝ) (T - U)‖ :=
    add_nonneg
      (add_nonneg (mul_nonneg hO0 hD3)
        (mul_nonneg hO1 (norm_nonneg _)))
      (mul_nonneg (mul_nonneg hO1 hA) (norm_nonneg _))
  have hactual_le :
      O0 * D3 +
          O1 * ‖ccTensorToHs (I := I) (M := M)
            g 2 (2 : ℝ) (T - U)‖ +
          O1 * A * ‖ccTensorToHs (I := I) (M := M)
            g 2 (2 : ℝ) (T - U)‖ ≤ R1 := by
    dsimp only [R1]
    have h1 := mul_le_mul_of_nonneg_left hTUn hO1
    have h2 := mul_le_mul_of_nonneg_left hTUn (mul_nonneg hO1 hA)
    linarith
  have hj1 :
      lowJetSq (I := I) (M := M) g 2 (AT.C1 - AU.C1) ≤ R1 ^ 2 := by
    have hm :
        lowJetSq (I := I) (M := M) g 2 (AT.C1 - AU.C1) ≤
          (O0 * D3 +
              O1 * ‖ccTensorToHs (I := I) (M := M)
                g 2 (2 : ℝ) (T - U)‖ +
              O1 * A * ‖ccTensorToHs (I := I) (M := M)
                g 2 (2 : ℝ) (T - U)‖) ^ 2 := by
      simpa only [AT, AU] using hM1
    exact hm.trans (pow_le_pow_left₀ hactual0 hactual_le 2)
  have hcoeff :
      lowJetSq (I := I) (M := M) g 2 (AT.C0 - AU.C0) +
          lowJetSq (I := I) (M := M) g 2 (AT.C1 - AU.C1) ≤
        Rt ^ 2 := by
    calc
      _ ≤ R0 ^ 2 + R1 ^ 2 := add_le_add hj0 hj1
      _ = Rt ^ 2 := by
        change Q = Real.sqrt Q ^ 2
        exact (Real.sq_sqrt hQ).symm
  have hpair := (hop AT AU Rt hRt hcoeff).1
  simpa only [AT, AU, Rt, Q, R0, R1] using hpair

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
