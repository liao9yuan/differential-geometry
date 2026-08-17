import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderLowBaseAction
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.EdgeLowerPairing
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.EdgePathPairing

noncomputable section

open Bundle Manifold Set Filter DifferentialGeometry.Tensor0SBundle MeasureTheory intervalIntegral
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem unitModel_add_app
    (g : SmoothRiemannianMetric I M) (A B : SmoothCcTensor g 0 2)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g 2 (A + B) x v =
      unitModel (I := I) (M := M) g 2 A x v +
        unitModel (I := I) (M := M) g 2 B x v := by
  have hfun : unitModel (I := I) (M := M) g 2 (A + B) x =
      unitModel (I := I) (M := M) g 2 A x +
        unitModel (I := I) (M := M) g 2 B x := by
    simp only [unitModel]
    change Tensor0SSpace.toModel
        ((A.toSection x) (unitTensor (I := I) (M := M) x) +
          (B.toSection x) (unitTensor (I := I) (M := M) x)) = _
    rw [Tensor0SSpace.toModel_add]
    rfl
  rw [hfun, ContinuousMultilinearMap.add_apply]

theorem lowBase_path_nf
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g T x v w =
        ccTensorBilin (I := I) g T x w v)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    let hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
    let A := lowBaseData (I := I) (M := M) g g_bg T hδ_lt hδ hδZ
    A.a2 (I := I) (M := M) T + A.a1 (I := I) (M := M) T =
      operatorFieldApply (I := I) (M := M) g 2 2
          (rhsLow0PathIntegral (I := I) (M := M) g g_bg T 0
              hδ_lt hδ hδ_lt hδZ +
            phiMetCurvCoeff (I := I) g g_bg g) T +
        operatorFieldApply (I := I) (M := M) g 3 2
          (rhsLow1PathIntegral (I := I) (M := M) g g_bg T 0
            hδ_lt hδ hδ_lt hδZ)
          (iteratedCovGrad (I := I) g 0 2 1 T) +
        operatorFieldApply (I := I) (M := M) g 4 2
          (rhsTopPathIntegral (I := I) (M := M) g g_bg T 0
              hδ_lt hδ hδ_lt hδZ -
            deTurckPhiMetTotal (I := I) (M := M) g g_bg g)
          (iteratedCovGrad (I := I) g 0 2 2 T) := by
  classical
  let hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  let A := lowBaseData (I := I) (M := M) g g_bg T hδ_lt hδ hδZ
  obtain ⟨_, _, hsplit⟩ := lowData_split (I := I) (M := M) g g_bg
  have hsplitT := (hsplit T hTsymm hδ_le hδ0 hδ hδZ).1
  change A.a2 (I := I) (M := M) T + A.a1 (I := I) (M := M) T = _
  rw [← hsplitT]
  change
    (realizedRHSArm (I := I) g g_bg T hδ_lt hδ -
        rawTensorConnLapSmooth (I := I) g 0 2 T) -
      (realizedRHSArm (I := I) g g_bg (0 : SmoothCcTensor g 0 2)
          hδ_lt hδZ -
        rawTensorConnLapSmooth (I := I) g 0 2
          (0 : SmoothCcTensor g 0 2)) = _
  have hlap0 : rawTensorConnLapSmooth (I := I) g 0 2
      (0 : SmoothCcTensor g 0 2) = 0 := by
    have hzero := rawTensorConnLapSmooth_sub
      (I := I) (M := M) g 0 2 T T
    rwa [sub_self, sub_self] at hzero
  rw [hlap0, sub_zero]
  rw [show
      (realizedRHSArm (I := I) g g_bg T hδ_lt hδ -
          rawTensorConnLapSmooth (I := I) g 0 2 T) -
        realizedRHSArm (I := I) g g_bg (0 : SmoothCcTensor g 0 2)
          hδ_lt hδZ =
      (realizedRHSArm (I := I) g g_bg T hδ_lt hδ -
          realizedRHSArm (I := I) g g_bg (0 : SmoothCcTensor g 0 2)
            hδ_lt hδZ) -
        rawTensorConnLapSmooth (I := I) g 0 2 T by abel]
  rw [rhsArm_sub_eq_paths (I := I) (M := M) g g_bg T 0
    hTsymm (edgeZeroSymm (I := I) (M := M) g)
    hδ_lt hδ hδ_lt hδZ]
  simp only [sub_zero, iteratedCovGrad_zero]
  have htop := edgeTop_split (I := I) (M := M) g g_bg g T
  simp only [deTurckPrincipalCometricArm, deTurckPrincipalCometricCoeff,
    sub_self, appCc_zero_left, add_zero] at htop
  have hlap : rawTensorConnLapSmooth (I := I) g 0 2 T =
      operatorFieldApply (I := I) (M := M) g 4 2
          (deTurckPhiMetTotal (I := I) (M := M) g g_bg g)
          (iteratedCovGrad (I := I) g 0 2 2 T) -
        operatorFieldApply (I := I) (M := M) g 2 2
          (phiMetCurvCoeff (I := I) g g_bg g) T := by
    exact (eq_sub_iff_add_eq).2 htop.symm
  rw [hlap]
  simp only [appCc_add_left, appCc_sub_left]
  module

theorem lowBase_L_nf
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g T x v w =
        ccTensorBilin (I := I) g T x w v)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    let hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
    let A := lowBaseData (I := I) (M := M) g g_bg T hδ_lt hδ hδZ
    let P0 := rhsLow0PathIntegral (I := I) (M := M) g g_bg T 0
      hδ_lt hδ hδ_lt hδZ
    let P1 := rhsLow1PathIntegral (I := I) (M := M) g g_bg T 0
      hδ_lt hδ hδ_lt hδZ
    let P2 := rhsTopPathIntegral (I := I) (M := M) g g_bg T 0
      hδ_lt hδ hδ_lt hδZ
    let Φ0 := deTurckPhiMetTotal (I := I) (M := M) g g_bg g
    let K0 := phiMetCurvCoeff (I := I) g g_bg g
    let LT := oneMinusConnLapSmooth (I := I) g 0 2 T
    let B02 :=
      oneMinusConnLapSmooth (I := I) g 0 2
          (operatorFieldApply (I := I) (M := M) g 2 2 P0 T) +
        (oneMinusConnLapSmooth (I := I) g 0 2
            (operatorFieldApply (I := I) (M := M) g 4 2 P2
              (iteratedCovGrad (I := I) g 0 2 2 T)) -
          operatorFieldApply (I := I) (M := M) g 4 2 P2
            (iteratedCovGrad (I := I) g 0 2 2 LT))
    oneMinusConnLapSmooth (I := I) g 0 2
          (A.a2 (I := I) (M := M) T + A.a1 (I := I) (M := M) T) -
        operatorFieldApply (I := I) (M := M) g 4 2 (P2 - Φ0)
          (iteratedCovGrad (I := I) g 0 2 2 LT) =
      B02 +
        oneMinusConnLapSmooth (I := I) g 0 2
          (operatorFieldApply (I := I) (M := M) g 3 2 P1
            (iteratedCovGrad (I := I) g 0 2 1 T)) +
        operatorFieldApply (I := I) (M := M) g 2 2 K0 LT := by
  classical
  let hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  let A := lowBaseData (I := I) (M := M) g g_bg T hδ_lt hδ hδZ
  let P0 := rhsLow0PathIntegral (I := I) (M := M) g g_bg T 0
    hδ_lt hδ hδ_lt hδZ
  let P1 := rhsLow1PathIntegral (I := I) (M := M) g g_bg T 0
    hδ_lt hδ hδ_lt hδZ
  let P2 := rhsTopPathIntegral (I := I) (M := M) g g_bg T 0
    hδ_lt hδ hδ_lt hδZ
  let Φ0 := deTurckPhiMetTotal (I := I) (M := M) g g_bg g
  let K0 := phiMetCurvCoeff (I := I) g g_bg g
  let LT := oneMinusConnLapSmooth (I := I) g 0 2 T
  let B02 :=
    oneMinusConnLapSmooth (I := I) g 0 2
        (operatorFieldApply (I := I) (M := M) g 2 2 P0 T) +
      (oneMinusConnLapSmooth (I := I) g 0 2
          (operatorFieldApply (I := I) (M := M) g 4 2 P2
            (iteratedCovGrad (I := I) g 0 2 2 T)) -
        operatorFieldApply (I := I) (M := M) g 4 2 P2
          (iteratedCovGrad (I := I) g 0 2 2 LT))
  dsimp only
  have hpath := lowBase_path_nf (I := I) (M := M) g g_bg T hTsymm
    hδ_le hδ0 hδ hδZ
  dsimp only at hpath
  have hlap0 : rawTensorConnLapSmooth (I := I) g 0 2
      (0 : SmoothCcTensor g 0 2) = 0 := by
    have h := rawTensorConnLapSmooth_sub (I := I) (M := M) g 0 2 T T
    simpa only [sub_self] using h
  have hlap_neg (X : SmoothCcTensor g 0 2) :
      rawTensorConnLapSmooth (I := I) g 0 2 (-X) =
        -rawTensorConnLapSmooth (I := I) g 0 2 X := by
    have h := rawTensorConnLapSmooth_sub (I := I) (M := M) g 0 2
      (0 : SmoothCcTensor g 0 2) X
    simpa only [zero_sub, hlap0] using h
  have hlap_add (X Y : SmoothCcTensor g 0 2) :
      rawTensorConnLapSmooth (I := I) g 0 2 (X + Y) =
        rawTensorConnLapSmooth (I := I) g 0 2 X +
          rawTensorConnLapSmooth (I := I) g 0 2 Y := by
    have h := rawTensorConnLapSmooth_sub (I := I) (M := M) g 0 2 X (-Y)
    simpa only [sub_neg_eq_add, hlap_neg] using h
  have hL_add (X Y : SmoothCcTensor g 0 2) :
      oneMinusConnLapSmooth (I := I) g 0 2 (X + Y) =
        oneMinusConnLapSmooth (I := I) g 0 2 X +
          oneMinusConnLapSmooth (I := I) g 0 2 Y := by
    unfold oneMinusConnLapSmooth
    rw [hlap_add]
    abel
  have hL_sub (X Y : SmoothCcTensor g 0 2) :
      oneMinusConnLapSmooth (I := I) g 0 2 (X - Y) =
        oneMinusConnLapSmooth (I := I) g 0 2 X -
          oneMinusConnLapSmooth (I := I) g 0 2 Y := by
    unfold oneMinusConnLapSmooth
    rw [rawTensorConnLapSmooth_sub]
    abel
  have hL_lap :
      oneMinusConnLapSmooth (I := I) g 0 2
          (rawTensorConnLapSmooth (I := I) g 0 2 T) =
        rawTensorConnLapSmooth (I := I) g 0 2 LT := by
    simp only [LT, oneMinusConnLapSmooth,
      rawTensorConnLapSmooth_sub]
  have htopT := edgeTop_split (I := I) (M := M) g g_bg g T
  have htopLT := edgeTop_split (I := I) (M := M) g g_bg g LT
  simp only [deTurckPrincipalCometricArm, deTurckPrincipalCometricCoeff,
    sub_self, appCc_zero_left, add_zero] at htopT htopLT
  have hinside :
      operatorFieldApply (I := I) (M := M) g 2 2 (P0 + K0) T +
          operatorFieldApply (I := I) (M := M) g 3 2 P1
            (iteratedCovGrad (I := I) g 0 2 1 T) +
          operatorFieldApply (I := I) (M := M) g 4 2 (P2 - Φ0)
            (iteratedCovGrad (I := I) g 0 2 2 T) =
        (operatorFieldApply (I := I) (M := M) g 2 2 P0 T +
            operatorFieldApply (I := I) (M := M) g 3 2 P1
              (iteratedCovGrad (I := I) g 0 2 1 T) +
            operatorFieldApply (I := I) (M := M) g 4 2 P2
              (iteratedCovGrad (I := I) g 0 2 2 T)) -
          rawTensorConnLapSmooth (I := I) g 0 2 T := by
    rw [appCc_add_left, appCc_sub_left, htopT]
    module
  rw [hpath, hinside, hL_sub, hL_add, hL_add, appCc_sub_left,
    hL_lap, htopLT]
  module

theorem low0_path_refold
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g T x v w =
        ccTensorBilin (I := I) g T x w v)
    {delta : Real} (hdelta_lt : delta < 1)
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) delta) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (rhsLow0PathIntegral (I := I) (M := M) g g_bg T 0
          hdelta_lt hdelta hdelta_lt hdeltaZ) T =
      operatorFieldApply (I := I) (M := M) g 2 2
          (rhsRefold0Int (I := I) (M := M) g g_bg T
            hdelta_lt hdelta hdeltaZ) T +
        operatorFieldApply (I := I) (M := M) g 2 2
          (edgeTopPairInt (I := I) (M := M) g T T hdelta_lt
            hdelta hdeltaZ ricciRefoldQA ricciRefoldQB
              lieRefoldQ lieRefoldEps) T := by
  classical
  let S : Set Real := realizedSmallSet (δ := delta) (δ' := delta)
  have hS : IsOpen S := realizedSmallSet_isOpen
  have hSI : Set.uIcc (0 : Real) 1 ⊆ S := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_realizedSmallSet hdelta_lt hdelta_lt
  let A : Real → SmoothCcTensor g 2 2 := fun s =>
    rhsLow0Coeff (I := I) (M := M) g g_bg T 0 hdelta hdeltaZ s
  let R : Real → SmoothCcTensor g 2 2 :=
    rhsRefold0 (I := I) (M := M) g g_bg T hdelta hdeltaZ
  let Q : Real → SmoothCcTensor g 2 2 :=
    edgeTopPairBi (I := I) (M := M) g T T hdelta hdeltaZ
      ricciRefoldQA ricciRefoldQB lieRefoldQ lieRefoldEps
  have hA : linearizedRicciThreeArmHjoint (I := I) (M := M) g 2 A
      (δ := delta) (δ' := delta) := by
    simpa only [A] using rhsLow0_path_joint (I := I) (M := M)
      g g_bg T 0 hdelta hdeltaZ
  have hR : linearizedRicciThreeArmHjoint (I := I) (M := M) g 2 R
      (δ := delta) (δ' := delta) := by
    simpa only [R] using rhsRefold0_joint (I := I) (M := M)
      g g_bg T hdelta hdeltaZ
  have hQ : linearizedRicciThreeArmHjoint (I := I) (M := M) g 2 Q
      (δ := delta) (δ' := delta) := by
    simpa only [Q] using edgeTopPair_joint (I := I) (M := M)
      g T T hdelta hdeltaZ ricciRefoldQA ricciRefoldQB
        lieRefoldQ lieRefoldEps
  have hcA : ∀ x : M, ContinuousOn (fun t : Real =>
      TensorRSSpace.toModel ((A t).toSection x)) S := fun x =>
    jointContMDiff_toModel_continuous_slice (I := I) g 2 2 A S hA x
  have hcR : ∀ x : M, ContinuousOn (fun t : Real =>
      TensorRSSpace.toModel ((R t).toSection x)) S := fun x =>
    jointContMDiff_toModel_continuous_slice (I := I) g 2 2 R S hR x
  have hcQ : ∀ x : M, ContinuousOn (fun t : Real =>
      TensorRSSpace.toModel ((Q t).toSection x)) S := fun x =>
    jointContMDiff_toModel_continuous_slice (I := I) g 2 2 Q S hQ x
  have hPiA :
      rhsLow0PathIntegral (I := I) (M := M) g g_bg T 0
          hdelta_lt hdelta hdelta_lt hdeltaZ =
        pathIntegralCoeffField (I := I) (M := M) g 2 2
          A S hS hSI hA := rfl
  have hPiR :
      rhsRefold0Int (I := I) (M := M) g g_bg T
          hdelta_lt hdelta hdeltaZ =
        pathIntegralCoeffField (I := I) (M := M) g 2 2
          R S hS hSI hR := rfl
  have hPiQ :
      edgeTopPairInt (I := I) (M := M) g T T hdelta_lt
          hdelta hdeltaZ ricciRefoldQA ricciRefoldQB
            lieRefoldQ lieRefoldEps =
        pathIntegralCoeffField (I := I) (M := M) g 2 2
          Q S hS hSI hQ := rfl
  apply smoothCcTensor_ext_of_unitModel
  intro x
  apply ContinuousMultilinearMap.ext
  intro v
  rw [unitModel_add_app, hPiA, hPiR, hPiQ]
  rw [pathIntegralCoeffField_appCc_eq
      (I := I) (M := M) g 2 2 A T S hS hSI hA hcA x v,
    pathIntegralCoeffField_appCc_eq
      (I := I) (M := M) g 2 2 R T S hS hSI hR hcR x v,
    pathIntegralCoeffField_appCc_eq
      (I := I) (M := M) g 2 2 Q T S hS hSI hQ hcQ x v]
  have hIR : IntervalIntegrable (fun s : Real =>
      unitModel (I := I) (M := M) g 2
        (operatorFieldApply (I := I) (M := M) g 2 2 (R s) T) x v)
      volume 0 1 :=
    coeffApp_integrable (I := I) (M := M) g 2 2 R T S hSI hcR x v
  have hIQ : IntervalIntegrable (fun s : Real =>
      unitModel (I := I) (M := M) g 2
        (operatorFieldApply (I := I) (M := M) g 2 2 (Q s) T) x v)
      volume 0 1 :=
    coeffApp_integrable (I := I) (M := M) g 2 2 Q T S hSI hcQ x v
  rw [← intervalIntegral.integral_add hIR hIQ]
  refine intervalIntegral.integral_congr (fun s hs => ?_)
  have hsI : s ∈ Set.Icc (0 : Real) 1 := by
    simpa only [Set.uIcc_of_le zero_le_one] using hs
  have hdiag :
      operatorFieldApply (I := I) (M := M) g 2 2 (Q s) T =
        operatorFieldApply (I := I) (M := M) g 4 2
          (rhsRefold2 (I := I) (M := M) g T hdelta hdeltaZ s)
          (iteratedCovGrad (I := I) g 0 2 2 T) := by
    change operatorFieldApply (I := I) (M := M) g 2 2
        (edgeTopPair (I := I) (M := M) g T hdelta hdeltaZ
          ricciRefoldQA ricciRefoldQB lieRefoldQ lieRefoldEps s) T = _
    simpa only [rhsRefold2, ricciRefold2, lieRefold2] using
      edgeTopPair_apply (I := I) (M := M) g T hdelta hdeltaZ
        ricciRefoldQA ricciRefoldQB lieRefoldQ lieRefoldEps s
  have hpoint :
      operatorFieldApply (I := I) (M := M) g 2 2 (A s) T =
        operatorFieldApply (I := I) (M := M) g 2 2 (R s) T +
          operatorFieldApply (I := I) (M := M) g 2 2 (Q s) T := by
    rw [hdiag]
    simpa only [A, R] using rhsLow0_refold (I := I) (M := M)
      g g_bg T hTsymm hdelta_lt hdelta hdeltaZ hsI
  simpa only [unitModel_add_app] using congrArg
    (fun W => unitModel (I := I) (M := M) g 2 W x v) hpoint

theorem b02_raw_nf
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g T x v w =
        ccTensorBilin (I := I) g T x w v)
    {delta : Real} (hdelta_lt : delta < 1)
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) delta) :
    let P0 := rhsLow0PathIntegral (I := I) (M := M) g g_bg T 0
      hdelta_lt hdelta hdelta_lt hdeltaZ
    let P2 := rhsTopPathIntegral (I := I) (M := M) g g_bg T 0
      hdelta_lt hdelta hdelta_lt hdeltaZ
    let R0 := rhsRefold0Int (I := I) (M := M) g g_bg T
      hdelta_lt hdelta hdeltaZ
    let Q := fun U : SmoothCcTensor g 0 2 =>
      edgeTopPairInt (I := I) (M := M) g T U hdelta_lt
        hdelta hdeltaZ ricciRefoldQA ricciRefoldQB lieRefoldQ lieRefoldEps
    let LT := oneMinusConnLapSmooth (I := I) g 0 2 T
    let B02 :=
      oneMinusConnLapSmooth (I := I) g 0 2
          (operatorFieldApply (I := I) (M := M) g 2 2 P0 T) +
        (oneMinusConnLapSmooth (I := I) g 0 2
            (operatorFieldApply (I := I) (M := M) g 4 2 P2
              (iteratedCovGrad (I := I) g 0 2 2 T)) -
          operatorFieldApply (I := I) (M := M) g 4 2 P2
            (iteratedCovGrad (I := I) g 0 2 2 LT))
    let PairComm :=
      oneMinusConnLapSmooth (I := I) g 0 2
          (operatorFieldApply (I := I) (M := M) g 2 2 (Q T) T) -
        operatorFieldApply (I := I) (M := M) g 2 2 (Q LT) T -
        operatorFieldApply (I := I) (M := M) g 2 2 (Q T) LT +
        operatorFieldApply (I := I) (M := M) g 2 2 (Q T) T
    let RawComm :=
      oneMinusConnLapSmooth (I := I) g 0 2
          (operatorFieldApply (I := I) (M := M) g 2 2 R0 T) + PairComm
    let TopComm :=
      oneMinusConnLapSmooth (I := I) g 0 2
          (operatorFieldApply (I := I) (M := M) g 4 2 P2
            (iteratedCovGrad (I := I) g 0 2 2 T)) -
        operatorFieldApply (I := I) (M := M) g 4 2 P2
          (iteratedCovGrad (I := I) g 0 2 2 LT)
    B02 =
      RawComm + TopComm +
        operatorFieldApply (I := I) (M := M) g 2 2 (Q LT) T +
        operatorFieldApply (I := I) (M := M) g 2 2 (Q T) LT -
        operatorFieldApply (I := I) (M := M) g 2 2 (Q T) T := by
  classical
  dsimp only
  rw [low0_path_refold (I := I) (M := M) g g_bg T hTsymm
    hdelta_lt hdelta hdeltaZ]
  rw [oneMinusConn_add (I := I) (M := M) g 0 2]
  module

theorem b02_center_nf
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g T x v w =
        ccTensorBilin (I := I) g T x w v)
    {delta : Real} (hdelta_lt : delta < 1)
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) delta) :
    let P0 := rhsLow0PathIntegral (I := I) (M := M) g g_bg T 0
      hdelta_lt hdelta hdelta_lt hdeltaZ
    let P2 := rhsTopPathIntegral (I := I) (M := M) g g_bg T 0
      hdelta_lt hdelta hdelta_lt hdeltaZ
    let R0 := rhsRefold0Int (I := I) (M := M) g g_bg T
      hdelta_lt hdelta hdeltaZ
    let Φ0 := deTurckPhiMetTotal (I := I) (M := M) g g_bg g
    let K0 := phiMetCurvCoeff (I := I) g g_bg g
    let LT := oneMinusConnLapSmooth (I := I) g 0 2 T
    let Q := fun U : SmoothCcTensor g 0 2 =>
      edgeTopPairInt (I := I) (M := M) g T U hdelta_lt
        hdelta hdeltaZ ricciRefoldQA ricciRefoldQB lieRefoldQ lieRefoldEps
    let Z := operatorFieldApply (I := I) (M := M) g 2 2 (Q T) T
    let Cross :=
      operatorFieldApply (I := I) (M := M) g 2 2 (Q LT) T +
        operatorFieldApply (I := I) (M := M) g 2 2 (Q T) LT
    let PairComm :=
      oneMinusConnLapSmooth (I := I) g 0 2 Z -
        operatorFieldApply (I := I) (M := M) g 2 2 (Q LT) T -
        operatorFieldApply (I := I) (M := M) g 2 2 (Q T) LT + Z
    let C := P2 - Φ0
    let B02 :=
      oneMinusConnLapSmooth (I := I) g 0 2
          (operatorFieldApply (I := I) (M := M) g 2 2 P0 T) +
        (oneMinusConnLapSmooth (I := I) g 0 2
            (operatorFieldApply (I := I) (M := M) g 4 2 P2
              (iteratedCovGrad (I := I) g 0 2 2 T)) -
          operatorFieldApply (I := I) (M := M) g 4 2 P2
            (iteratedCovGrad (I := I) g 0 2 2 LT))
    let J :=
      oneMinusConnLapSmooth (I := I) g 0 2
          (operatorFieldApply (I := I) (M := M) g 2 2 (R0 + K0) T) +
        PairComm +
        (oneMinusConnLapSmooth (I := I) g 0 2
            (operatorFieldApply (I := I) (M := M) g 4 2 C
              (iteratedCovGrad (I := I) g 0 2 2 T)) -
          operatorFieldApply (I := I) (M := M) g 4 2 C
            (iteratedCovGrad (I := I) g 0 2 2 LT)) - Z
    B02 + operatorFieldApply (I := I) (M := M) g 2 2 K0 LT = J + Cross := by
  classical
  dsimp only
  have hraw := b02_raw_nf (I := I) (M := M) g g_bg T hTsymm
    hdelta_lt hdelta hdeltaZ
  dsimp only at hraw
  rw [hraw]
  have hL_sub (X Y : SmoothCcTensor g 0 2) :
      oneMinusConnLapSmooth (I := I) g 0 2 (X - Y) =
        oneMinusConnLapSmooth (I := I) g 0 2 X -
          oneMinusConnLapSmooth (I := I) g 0 2 Y := by
    unfold oneMinusConnLapSmooth
    rw [rawTensorConnLapSmooth_sub]
    abel
  let LT := oneMinusConnLapSmooth (I := I) g 0 2 T
  have hL_lap :
      oneMinusConnLapSmooth (I := I) g 0 2
          (rawTensorConnLapSmooth (I := I) g 0 2 T) =
        rawTensorConnLapSmooth (I := I) g 0 2 LT := by
    simp only [LT, oneMinusConnLapSmooth, rawTensorConnLapSmooth_sub]
  have htopT := edgeTop_split (I := I) (M := M) g g_bg g T
  have htopLT := edgeTop_split (I := I) (M := M) g g_bg g LT
  simp only [deTurckPrincipalCometricArm, deTurckPrincipalCometricCoeff,
    sub_self, appCc_zero_left, add_zero] at htopT htopLT
  rw [appCc_add_left, oneMinusConn_add (I := I) (M := M) g 0 2,
    appCc_sub_left, hL_sub, appCc_sub_left, htopT, htopLT,
    oneMinusConn_add (I := I) (M := M) g 0 2, hL_lap]
  module

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
