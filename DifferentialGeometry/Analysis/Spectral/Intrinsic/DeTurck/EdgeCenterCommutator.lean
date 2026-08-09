import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.EdgeCenterNormal
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderLowBaseAction

/-!
# Complete centered edge commutator

This leaf module peels the fixed-parameter diagonal zero/top block into its
transparent lower action, the explicit principal Hessian head, the complete
curvature defect, and the three rough-Laplacian Leibniz corners.  No derivative
is moved onto an energy test tensor.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 3200000

open Bundle Manifold Set Tensor0SBundle
open scoped Manifold ContDiff RealInnerProductSpace BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
      [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E

private theorem appCc_sub_right_ec
    (g : SmoothRiemannianMetric I M) (r s : Nat)
    (Phi : SmoothCcTensor g r s) (W1 W2 : SmoothCcTensor g 0 r) :
    appCc (I := I) (M := M) g r s Phi (W1 - W2) =
      appCc (I := I) (M := M) g r s Phi W1 -
        appCc (I := I) (M := M) g r s Phi W2 := by
  have h : appCc (I := I) (M := M) g r s Phi (W1 - W2) +
      appCc (I := I) (M := M) g r s Phi W2 =
        appCc (I := I) (M := M) g r s Phi W1 := by
    rw [← appCc_add_right]
    congr 1
    abel
  exact eq_sub_of_add_eq h

/-- The exact non-Green peel of the fixed-parameter centered diagonal edge
block.  The three product-rule corners and the Hessian--Laplacian curvature
defect remain explicit; the two off-diagonal pair actions remain as `Cross`. -/
theorem edge_center_peel
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g T x v w =
        ccTensorBilin (I := I) g T x w v)
    {delta : Real} (hdelta_lt : delta < 1)
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) delta)
    (s : Real) (hs : s ∈ Set.Icc (0 : Real) 1) :
    let gs : SmoothRiemannianMetric I M :=
      edgeMetric (I := I) (M := M) g T hdelta s
    let R0 : SmoothCcTensor g 2 2 :=
      rhsRefold0 (I := I) (M := M) g g_bg T hdelta hdeltaZ s
    let K0 : SmoothCcTensor g 2 2 := phiMetCurvCoeff (I := I) g g_bg g
    let LT : SmoothCcTensor g 0 2 := oneMinusConnLapSmooth (I := I) g 0 2 T
    let HT : SmoothCcTensor g 0 4 := iteratedCovGrad (I := I) g 0 2 2 T
    let HLT : SmoothCcTensor g 0 4 := iteratedCovGrad (I := I) g 0 2 2 LT
    let Q : SmoothCcTensor g 0 2 → SmoothCcTensor g 2 2 := fun U =>
      edgeTopPairBi (I := I) (M := M) g T U hdelta hdeltaZ
        ricciRefoldQA ricciRefoldQB lieRefoldQ lieRefoldEps s
    let Z : SmoothCcTensor g 0 2 :=
      appCc (I := I) (M := M) g 2 2 (Q T) T
    let Cross : SmoothCcTensor g 0 2 :=
      appCc (I := I) (M := M) g 2 2 (Q LT) T +
        appCc (I := I) (M := M) g 2 2 (Q T) LT
    let PairComm : SmoothCcTensor g 0 2 :=
      oneMinusConnLapSmooth (I := I) g 0 2 Z -
        appCc (I := I) (M := M) g 2 2 (Q LT) T -
        appCc (I := I) (M := M) g 2 2 (Q T) LT + Z
    let C : SmoothCcTensor g 4 2 :=
      deTurckPhiMetTotal (I := I) (M := M) g g_bg gs -
        deTurckPhiMetTotal (I := I) (M := M) g g_bg g
    let J : SmoothCcTensor g 0 2 :=
      oneMinusConnLapSmooth (I := I) g 0 2
          (appCc (I := I) (M := M) g 2 2 (R0 + K0) T) +
        PairComm +
        (oneMinusConnLapSmooth (I := I) g 0 2
            (appCc (I := I) (M := M) g 4 2 C HT) -
          appCc (I := I) (M := M) g 4 2 C HLT) - Z
    let A : SmoothCcTensor g 2 2 :=
      LowBaseInternal.rhsSelfLow
          (I := I) (M := M) g g_bg T hdelta hdeltaZ s + K0
    let B : SmoothCcTensor g 4 2 :=
      lieRefold2 (I := I) (M := M) g T hdelta hdeltaZ s + C +
        (-2 * s : Real) • LowBaseInternal.ricciTop
          (I := I) (M := M) g gs T
    let G : SmoothCcTensor g 0 4 :=
      covGrad (I := I) (M := M) g 0 3
          (pointwiseTensorCurv (I := I) (M := M) g 2 T) +
        pointwiseTensorCurv (I := I) (M := M) g 3
          (covGrad (I := I) (M := M) g 0 2 T)
    let Tr : SmoothCcTensor g 4 2 :=
      DeTurck.cometricDoubleTraceField (I := I) g 2
    let P20 : SmoothCcTensor g 0 2 :=
      appCc (I := I) (M := M) g 4 2 Tr
        (appCc (I := I) (M := M) g 4 4
          (covGrad (I := I) (M := M) g 4 3
            (covGrad (I := I) (M := M) g 4 2 B)) HT)
    let P11L : SmoothCcTensor g 0 2 :=
      appCc (I := I) (M := M) g 4 2 Tr
        (appCc (I := I) (M := M) g 5 4
          (slotExtend (I := I) (M := M) g 4 3
            (covGrad (I := I) (M := M) g 4 2 B))
          (covGrad (I := I) (M := M) g 0 4 HT))
    let P11R : SmoothCcTensor g 0 2 :=
      appCc (I := I) (M := M) g 4 2 Tr
        (appCc (I := I) (M := M) g 5 4
          (covGrad (I := I) (M := M) g 5 3
            (slotExtend (I := I) (M := M) g 4 2 B))
          (covGrad (I := I) (M := M) g 0 4 HT))
    J =
      oneMinusConnLapSmooth (I := I) g 0 2
          (appCc (I := I) (M := M) g 2 2 A T) +
        appCc (I := I) (M := M) g 4 2 (B - C) HLT -
        appCc (I := I) (M := M) g 4 2 B G -
        P20 - P11L - P11R - Cross := by
  classical
  let gs : SmoothRiemannianMetric I M :=
    edgeMetric (I := I) (M := M) g T hdelta s
  let R0 : SmoothCcTensor g 2 2 :=
    rhsRefold0 (I := I) (M := M) g g_bg T hdelta hdeltaZ s
  let K0 : SmoothCcTensor g 2 2 := phiMetCurvCoeff (I := I) g g_bg g
  let LT : SmoothCcTensor g 0 2 := oneMinusConnLapSmooth (I := I) g 0 2 T
  let HT : SmoothCcTensor g 0 4 := iteratedCovGrad (I := I) g 0 2 2 T
  let HLT : SmoothCcTensor g 0 4 := iteratedCovGrad (I := I) g 0 2 2 LT
  let Q : SmoothCcTensor g 0 2 → SmoothCcTensor g 2 2 := fun U =>
    edgeTopPairBi (I := I) (M := M) g T U hdelta hdeltaZ
      ricciRefoldQA ricciRefoldQB lieRefoldQ lieRefoldEps s
  let Z : SmoothCcTensor g 0 2 :=
    appCc (I := I) (M := M) g 2 2 (Q T) T
  let Cross : SmoothCcTensor g 0 2 :=
    appCc (I := I) (M := M) g 2 2 (Q LT) T +
      appCc (I := I) (M := M) g 2 2 (Q T) LT
  let PairComm : SmoothCcTensor g 0 2 :=
    oneMinusConnLapSmooth (I := I) g 0 2 Z -
      appCc (I := I) (M := M) g 2 2 (Q LT) T -
      appCc (I := I) (M := M) g 2 2 (Q T) LT + Z
  let C : SmoothCcTensor g 4 2 :=
    deTurckPhiMetTotal (I := I) (M := M) g g_bg gs -
      deTurckPhiMetTotal (I := I) (M := M) g g_bg g
  let J : SmoothCcTensor g 0 2 :=
    oneMinusConnLapSmooth (I := I) g 0 2
        (appCc (I := I) (M := M) g 2 2 (R0 + K0) T) +
      PairComm +
      (oneMinusConnLapSmooth (I := I) g 0 2
          (appCc (I := I) (M := M) g 4 2 C HT) -
        appCc (I := I) (M := M) g 4 2 C HLT) - Z
  let A : SmoothCcTensor g 2 2 :=
    LowBaseInternal.rhsSelfLow
        (I := I) (M := M) g g_bg T hdelta hdeltaZ s + K0
  let B : SmoothCcTensor g 4 2 :=
    lieRefold2 (I := I) (M := M) g T hdelta hdeltaZ s + C +
      (-2 * s : Real) • LowBaseInternal.ricciTop
        (I := I) (M := M) g gs T
  let G : SmoothCcTensor g 0 4 :=
    covGrad (I := I) (M := M) g 0 3
        (pointwiseTensorCurv (I := I) (M := M) g 2 T) +
      pointwiseTensorCurv (I := I) (M := M) g 3
        (covGrad (I := I) (M := M) g 0 2 T)
  let Tr : SmoothCcTensor g 4 2 :=
    DeTurck.cometricDoubleTraceField (I := I) g 2
  let P20 : SmoothCcTensor g 0 2 :=
    appCc (I := I) (M := M) g 4 2 Tr
      (appCc (I := I) (M := M) g 4 4
        (covGrad (I := I) (M := M) g 4 3
          (covGrad (I := I) (M := M) g 4 2 B)) HT)
  let P11L : SmoothCcTensor g 0 2 :=
    appCc (I := I) (M := M) g 4 2 Tr
      (appCc (I := I) (M := M) g 5 4
        (slotExtend (I := I) (M := M) g 4 3
          (covGrad (I := I) (M := M) g 4 2 B))
        (covGrad (I := I) (M := M) g 0 4 HT))
  let P11R : SmoothCcTensor g 0 2 :=
    appCc (I := I) (M := M) g 4 2 Tr
      (appCc (I := I) (M := M) g 5 4
        (covGrad (I := I) (M := M) g 5 3
          (slotExtend (I := I) (M := M) g 4 2 B))
        (covGrad (I := I) (M := M) g 0 4 HT))
  have hself :
      appCc (I := I) (M := M) g 2 2 R0 T =
        appCc (I := I) (M := M) g 2 2
            (LowBaseInternal.rhsSelfLow
              (I := I) (M := M) g g_bg T hdelta hdeltaZ s) T +
          appCc (I := I) (M := M) g 4 2
            (LowBaseInternal.rhsSelfTop
              (I := I) (M := M) g T hdelta hdeltaZ s) HT := by
    dsimp only [R0, HT]
    exact LowBaseInternal.self_refold
      (I := I) (M := M) g g_bg T hTsymm
        hdelta_lt hdelta hdeltaZ hs
  have hQ :
      Z = appCc (I := I) (M := M) g 4 2
        (rhsRefold2 (I := I) (M := M) g T hdelta hdeltaZ s) HT := by
    dsimp only [Z, Q, HT]
    rw [edgeTopPairBi_eq_G]
    simpa only [rhsRefold2, ricciRefold2, lieRefold2] using
      edgeTopG_apply (I := I) (M := M) g T
        (iteratedCovGrad (I := I) g 0 2 2 T) hdelta hdeltaZ
          ricciRefoldQA ricciRefoldQB lieRefoldQ lieRefoldEps s
  have hB :
      rhsRefold2 (I := I) (M := M) g T hdelta hdeltaZ s +
          LowBaseInternal.rhsSelfTop
            (I := I) (M := M) g T hdelta hdeltaZ s + C = B := by
    have hmetric := edgeMetric_bal (I := I) (M := M) g T
      hdelta_lt hdelta hdeltaZ hs
    have hkernel := LowBaseInternal.topKernel_eq
      (I := I) (M := M) g g_bg T hdelta hdeltaZ s
    dsimp only [B, C, gs]
    rw [hmetric]
    dsimp only at hkernel
    rw [← hkernel]
    simp only [rhsRefoldTop]
    module
  have hBapp := congrArg
    (fun F : SmoothCcTensor g 4 2 =>
      appCc (I := I) (M := M) g 4 2 F HT) hB
  simp only [appCc_add_left] at hBapp
  have hinside :
      appCc (I := I) (M := M) g 2 2 (R0 + K0) T + Z +
          appCc (I := I) (M := M) g 4 2 C HT =
        appCc (I := I) (M := M) g 2 2 A T +
          appCc (I := I) (M := M) g 4 2 B HT := by
    dsimp only [A]
    simp only [appCc_add_left]
    rw [hself, hQ]
    rw [← hBapp]
    module
  have hJ :
      J =
        oneMinusConnLapSmooth (I := I) g 0 2
            (appCc (I := I) (M := M) g 2 2 A T) +
          oneMinusConnLapSmooth (I := I) g 0 2
            (appCc (I := I) (M := M) g 4 2 B HT) -
          appCc (I := I) (M := M) g 4 2 C HLT - Cross := by
    change J = _
    dsimp only [J, PairComm]
    calc
      oneMinusConnLapSmooth (I := I) g 0 2
            (appCc (I := I) (M := M) g 2 2 (R0 + K0) T) +
          (oneMinusConnLapSmooth (I := I) g 0 2 Z -
              appCc (I := I) (M := M) g 2 2 (Q LT) T -
              appCc (I := I) (M := M) g 2 2 (Q T) LT + Z) +
          (oneMinusConnLapSmooth (I := I) g 0 2
              (appCc (I := I) (M := M) g 4 2 C HT) -
            appCc (I := I) (M := M) g 4 2 C HLT) - Z =
        (oneMinusConnLapSmooth (I := I) g 0 2
            (appCc (I := I) (M := M) g 2 2 (R0 + K0) T) +
          oneMinusConnLapSmooth (I := I) g 0 2 Z +
          oneMinusConnLapSmooth (I := I) g 0 2
            (appCc (I := I) (M := M) g 4 2 C HT)) -
          appCc (I := I) (M := M) g 4 2 C HLT - Cross := by
            dsimp only [Cross]
            module
      _ = oneMinusConnLapSmooth (I := I) g 0 2
            (appCc (I := I) (M := M) g 2 2 (R0 + K0) T + Z +
              appCc (I := I) (M := M) g 4 2 C HT) -
          appCc (I := I) (M := M) g 4 2 C HLT - Cross := by
            rw [oneMinusConn_add (I := I) (M := M) g 0 2,
              oneMinusConn_add (I := I) (M := M) g 0 2]
      _ = oneMinusConnLapSmooth (I := I) g 0 2
            (appCc (I := I) (M := M) g 2 2 A T +
              appCc (I := I) (M := M) g 4 2 B HT) -
          appCc (I := I) (M := M) g 4 2 C HLT - Cross := by
            rw [hinside]
      _ = oneMinusConnLapSmooth (I := I) g 0 2
              (appCc (I := I) (M := M) g 2 2 A T) +
            oneMinusConnLapSmooth (I := I) g 0 2
              (appCc (I := I) (M := M) g 4 2 B HT) -
          appCc (I := I) (M := M) g 4 2 C HLT - Cross := by
            rw [oneMinusConn_add (I := I) (M := M) g 0 2]
  have hHLT :
      HLT = HT - iteratedCovGrad (I := I) g 0 2 2
        (rawTensorConnLapSmooth (I := I) g 0 2 T) := by
    dsimp only [HLT, HT, LT, oneMinusConnLapSmooth]
    rw [iteratedCovGrad_sub]
  have hprod := rawTensorConnLap_appCc_comm_of_rank
    (I := I) (M := M) g 4 2 B HT
  have harg := rawConnLap_iteratedCovGrad_two_comm
    (I := I) (M := M) g 2 T
  have hLtop :
      oneMinusConnLapSmooth (I := I) g 0 2
          (appCc (I := I) (M := M) g 4 2 B HT) =
        appCc (I := I) (M := M) g 4 2 B HLT -
          appCc (I := I) (M := M) g 4 2 B G -
          P20 - P11L - P11R := by
    dsimp only [oneMinusConnLapSmooth]
    rw [hprod, harg]
    simp only [appCc_add_right]
    rw [hHLT, appCc_sub_right_ec]
    dsimp only [G, P20, P11L, P11R, Tr]
    simp only [appCc_add_right]
    module
  change J =
    oneMinusConnLapSmooth (I := I) g 0 2
        (appCc (I := I) (M := M) g 2 2 A T) +
      appCc (I := I) (M := M) g 4 2 (B - C) HLT -
      appCc (I := I) (M := M) g 4 2 B G -
      P20 - P11L - P11R - Cross
  rw [hJ, hLtop,
    appCc_sub_left (I := I) (M := M) g 4 2 B C HLT]
  module

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
