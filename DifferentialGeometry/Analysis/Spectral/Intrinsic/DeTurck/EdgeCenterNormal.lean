import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.EdgeRefoldPairingPolarized
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RHSZeroRefold
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.ConnLapPairing
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.RoughLaplacianAppCcCommutation

noncomputable section


open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open Bundle Manifold Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff RealInnerProductSpace BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
      [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E

omit [BoundarylessManifold I M] in
theorem edge_q_six
    (g : SmoothRiemannianMetric I M) (T U : SmoothCcTensor g 0 2)
    {delta : Real}
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) delta)
    (s : Real) :
    let gm := realizedFam (I := I) g T 0 hdelta hdeltaZ s
    let G := iteratedCovGrad (I := I) g 0 2 2 U
    edgeTopPairBi (I := I) (M := M) g T U hdelta hdeltaZ
        ricciRefoldQA ricciRefoldQB lieRefoldQ lieRefoldEps s =
      (s / 2) •
        (edgePairMono (I := I) (M := M) g gm G (ricciRefoldQA 1) +
          edgePairMono (I := I) (M := M) g gm G (ricciRefoldQB 1) -
          edgePairMono (I := I) (M := M) g gm G (ricciRefoldQA 3) -
          edgePairMono (I := I) (M := M) g gm G (ricciRefoldQB 3) -
          edgePairMono (I := I) (M := M) g gm G (lieRefoldQ 1) -
          edgePairMono (I := I) (M := M) g gm G
            ((lieRefoldQ 1).trans (Equiv.swap (0 : Fin 4) 1))) := by
  classical
  have hB0 : ricciRefoldQB 0 = lieRefoldQ 0 := by
    apply Equiv.ext
    intro i
    fin_cases i <;> rfl
  have hA0 : ricciRefoldQA 0 =
      (lieRefoldQ 0).trans (Equiv.swap (0 : Fin 4) 1) := by
    apply Equiv.ext
    intro i
    fin_cases i <;> rfl
  have hA2 : ricciRefoldQA 2 = lieRefoldQ 2 := by
    apply Equiv.ext
    intro i
    fin_cases i <;> rfl
  have hB2 : ricciRefoldQB 2 =
      (lieRefoldQ 2).trans (Equiv.swap (0 : Fin 4) 1) := by
    apply Equiv.ext
    intro i
    fin_cases i <;> rfl
  simp only [edgeTopPairBi, edgeTopPairG, edgeKernelPair, Fin.sum_univ_three]
  rw [hB0, hA0, hA2, hB2]
  simp [lieRefoldEps]
  module

omit [BoundarylessManifold I M] in
theorem edgeTopG_rhs
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (G : SmoothCcTensor g 0 4) {delta : Real}
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) delta)
    (s : Real) :
    appCc (I := I) (M := M) g 2 2
        (edgeTopPairG (I := I) (M := M) g T G hdelta hdeltaZ
          ricciRefoldQA ricciRefoldQB lieRefoldQ lieRefoldEps s) T =
      appCc (I := I) (M := M) g 4 2
        (rhsRefold2 (I := I) (M := M) g T hdelta hdeltaZ s) G := by
  simpa only [rhsRefold2, ricciRefold2, lieRefold2] using
    edgeTopG_apply (I := I) (M := M) g T G hdelta hdeltaZ
      ricciRefoldQA ricciRefoldQB lieRefoldQ lieRefoldEps s

theorem edge_arg2_nf
    (g : SmoothRiemannianMetric I M) (T U : SmoothCcTensor g 0 2)
    {delta : Real}
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) delta)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4))
    (q : Fin 3 → Equiv.Perm (Fin 4)) (epsilon : Fin 3 → Real)
    (s : Real) :
    edgeTopPairG (I := I) (M := M) g T
        (rawTensorConnLapSmooth (I := I) g 0 4
          (iteratedCovGrad (I := I) g 0 2 2 U))
        hdelta hdeltaZ qA qB q epsilon s =
      edgeTopPairG (I := I) (M := M) g T
        (iteratedCovGrad (I := I) g 0 2 2
            (rawTensorConnLapSmooth (I := I) g 0 2 U) +
          covGrad (I := I) (M := M) g 0 3
            (pointwiseTensorCurv (I := I) (M := M) g 2 U) +
          pointwiseTensorCurv (I := I) (M := M) g 3
            (covGrad (I := I) (M := M) g 0 2 U))
        hdelta hdeltaZ qA qB q epsilon s := by
  rw [rawConnLap_iteratedCovGrad_two_comm (I := I) (M := M) g 2 U]

theorem phiMet_fold_comm
    (g₀ g_bg g : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) :
    let Φd : SmoothCcTensor g₀ 4 2 :=
      deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g -
        ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g
    let K : SmoothCcTensor g₀ 2 2 :=
      phiMetCurvCoeff (I := I) g₀ g_bg g
    oneMinusConnLapSmooth (I := I) g₀ 0 2
          (appCc (I := I) (M := M) g₀ 4 2 Φd
            (iteratedCovGrad (I := I) g₀ 0 2 2 S)) -
        appCc (I := I) (M := M) g₀ 4 2 Φd
          (iteratedCovGrad (I := I) g₀ 0 2 2
            (oneMinusConnLapSmooth (I := I) g₀ 0 2 S)) =
      oneMinusConnLapSmooth (I := I) g₀ 0 2
          (appCc (I := I) (M := M) g₀ 2 2 K S) -
        appCc (I := I) (M := M) g₀ 2 2 K
          (oneMinusConnLapSmooth (I := I) g₀ 0 2 S) := by
  dsimp only
  have hS :
      appCc (I := I) (M := M) g₀ 4 2
          (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g -
            ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g)
          (iteratedCovGrad (I := I) g₀ 0 2 2 S) =
        appCc (I := I) (M := M) g₀ 2 2
          (phiMetCurvCoeff (I := I) g₀ g_bg g)
          (iteratedCovGrad (I := I) g₀ 0 2 0 S) :=
    phiMet_curv_fold (I := I) (M := M) g₀ g_bg g S
  have hLS :
      appCc (I := I) (M := M) g₀ 4 2
          (deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g -
            ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g)
          (iteratedCovGrad (I := I) g₀ 0 2 2
            (oneMinusConnLapSmooth (I := I) g₀ 0 2 S)) =
        appCc (I := I) (M := M) g₀ 2 2
          (phiMetCurvCoeff (I := I) g₀ g_bg g)
          (iteratedCovGrad (I := I) g₀ 0 2 0
            (oneMinusConnLapSmooth (I := I) g₀ 0 2 S)) :=
    phiMet_curv_fold (I := I) (M := M) g₀ g_bg g
      (oneMinusConnLapSmooth (I := I) g₀ 0 2 S)
  rw [hS, hLS]
  simp only [iteratedCovGrad_zero]

theorem edge_center_s_nf
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
    let Ks : SmoothCcTensor g 2 2 := phiMetCurvCoeff (I := I) g g_bg gs
    let E0 : SmoothCcTensor g 2 2 := edgeCarry0 (I := I) (M := M) g g_bg +
      edgeQuad0 (I := I) (M := M) g gs g_bg
    let Ds : SmoothCcTensor g 0 2 → SmoothCcTensor g 0 2 := fun W =>
      deTurckPrincipalCometricArm (I := I) (M := M) g gs W
    let LT : SmoothCcTensor g 0 2 := oneMinusConnLapSmooth (I := I) g 0 2 T
    let Q : SmoothCcTensor g 0 2 → SmoothCcTensor g 2 2 := fun U =>
      edgeTopPairBi (I := I) (M := M) g T U hdelta hdeltaZ
        ricciRefoldQA ricciRefoldQB lieRefoldQ lieRefoldEps s
    let Z : SmoothCcTensor g 0 2 := appCc (I := I) (M := M) g 2 2 (Q T) T
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
            (appCc (I := I) (M := M) g 4 2 C
              (iteratedCovGrad (I := I) g 0 2 2 T)) -
          appCc (I := I) (M := M) g 4 2 C
            (iteratedCovGrad (I := I) g 0 2 2 LT)) - Z
    J =
      oneMinusConnLapSmooth (I := I) g 0 2
          (appCc (I := I) (M := M) g 2 2 E0 T) +
        (oneMinusConnLapSmooth (I := I) g 0 2 (Ds T) - Ds LT) -
        appCc (I := I) (M := M) g 2 2 (Ks - K0) LT - Cross := by
  classical
  let gs : SmoothRiemannianMetric I M :=
    edgeMetric (I := I) (M := M) g T hdelta s
  let A0 : SmoothCcTensor g 2 2 := DeTurckCoefficients.rhsLow0Coeff
    (I := I) (M := M) g g_bg T 0 hdelta hdeltaZ s
  let R0 : SmoothCcTensor g 2 2 :=
    rhsRefold0 (I := I) (M := M) g g_bg T hdelta hdeltaZ s
  let K0 : SmoothCcTensor g 2 2 := phiMetCurvCoeff (I := I) g g_bg g
  let Ks : SmoothCcTensor g 2 2 := phiMetCurvCoeff (I := I) g g_bg gs
  let E0 : SmoothCcTensor g 2 2 := edgeCarry0 (I := I) (M := M) g g_bg +
    edgeQuad0 (I := I) (M := M) g gs g_bg
  let Ds : SmoothCcTensor g 0 2 → SmoothCcTensor g 0 2 := fun W =>
    deTurckPrincipalCometricArm (I := I) (M := M) g gs W
  let LT : SmoothCcTensor g 0 2 := oneMinusConnLapSmooth (I := I) g 0 2 T
  let Q : SmoothCcTensor g 0 2 → SmoothCcTensor g 2 2 := fun U =>
    edgeTopPairBi (I := I) (M := M) g T U hdelta hdeltaZ
      ricciRefoldQA ricciRefoldQB lieRefoldQ lieRefoldEps s
  let Z : SmoothCcTensor g 0 2 := appCc (I := I) (M := M) g 2 2 (Q T) T
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
          (appCc (I := I) (M := M) g 4 2 C
            (iteratedCovGrad (I := I) g 0 2 2 T)) -
        appCc (I := I) (M := M) g 4 2 C
          (iteratedCovGrad (I := I) g 0 2 2 LT)) - Z
  have hQdiag :
      Z = appCc (I := I) (M := M) g 4 2
        (rhsRefold2 (I := I) (M := M) g T hdelta hdeltaZ s)
        (iteratedCovGrad (I := I) g 0 2 2 T) := by
    dsimp only [Z, Q]
    change appCc (I := I) (M := M) g 2 2
        (edgeTopPair (I := I) (M := M) g T hdelta hdeltaZ
          ricciRefoldQA ricciRefoldQB lieRefoldQ lieRefoldEps s) T = _
    simpa only [rhsRefold2, ricciRefold2, lieRefold2] using
      edgeTopPair_apply (I := I) (M := M) g T hdelta hdeltaZ
        ricciRefoldQA ricciRefoldQB lieRefoldQ lieRefoldEps s
  have hrefold :
      appCc (I := I) (M := M) g 2 2 A0 T =
        appCc (I := I) (M := M) g 2 2 R0 T + Z := by
    dsimp only [A0, R0]
    rw [hQdiag]
    exact rhsLow0_refold (I := I) (M := M) g g_bg T hTsymm
      hdelta_lt hdelta hdeltaZ hs
  have hlow : A0 + Ks = E0 := by
    have hmetric := edgeMetric_bal (I := I) (M := M) g T
      hdelta_lt hdelta hdeltaZ hs
    dsimp only [A0, Ks, E0, gs]
    rw [hmetric]
    simpa only [DeTurckCoefficients.rhsLow0Coeff,
      linearizedRicciConnDiffOrder0Coeff] using
        edgeLow0_split (I := I) (M := M) g
          (realizedFam (I := I) g T 0 hdelta hdeltaZ s) g_bg
  have htop (W : SmoothCcTensor g 0 2) :
      appCc (I := I) (M := M) g 4 2 C
          (iteratedCovGrad (I := I) g 0 2 2 W) =
        Ds W + appCc (I := I) (M := M) g 2 2 (Ks - K0) W := by
    have hgs := edgeTop_split (I := I) (M := M) g g_bg gs W
    have hg := edgeTop_split (I := I) (M := M) g g_bg g W
    simp only [deTurckPrincipalCometricArm,
      deTurckPrincipalCometricCoeff, sub_self, appCc_zero_left, add_zero] at hg
    dsimp only [C, Ds, Ks, K0]
    change operatorFieldApply (I := I) (M := M) g 4 2
        (deTurckPhiMetTotal (I := I) (M := M) g g_bg gs -
          deTurckPhiMetTotal (I := I) (M := M) g g_bg g)
        (iteratedCovGrad (I := I) g 0 2 2 W) =
      deTurckPrincipalCometricArm (I := I) (M := M) g gs W +
        operatorFieldApply (I := I) (M := M) g 2 2
          (phiMetCurvCoeff (I := I) g g_bg gs -
            phiMetCurvCoeff (I := I) g g_bg g) W
    rw [appCc_sub_left, hgs, hg, appCc_sub_left]
    module
  have hlowApp := congrArg
    (fun F : SmoothCcTensor g 2 2 =>
      appCc (I := I) (M := M) g 2 2 F T) hlow
  simp only [appCc_add_left] at hlowApp
  change operatorFieldApply (I := I) (M := M) g 2 2 A0 T =
      operatorFieldApply (I := I) (M := M) g 2 2 R0 T + Z at hrefold
  change operatorFieldApply (I := I) (M := M) g 2 2 A0 T +
      operatorFieldApply (I := I) (M := M) g 2 2 Ks T =
        operatorFieldApply (I := I) (M := M) g 2 2 E0 T at hlowApp
  have hinside :
      appCc (I := I) (M := M) g 2 2 (R0 + K0) T + Z +
          appCc (I := I) (M := M) g 4 2 C
            (iteratedCovGrad (I := I) g 0 2 2 T) =
        appCc (I := I) (M := M) g 2 2 E0 T + Ds T := by
    rw [htop T]
    simp only [appCc_add_left, appCc_sub_left]
    change _ = operatorFieldApply (I := I) (M := M) g 2 2 E0 T + Ds T
    rw [← hlowApp, hrefold]
    module
  change J =
    oneMinusConnLapSmooth (I := I) g 0 2
        (appCc (I := I) (M := M) g 2 2 E0 T) +
      (oneMinusConnLapSmooth (I := I) g 0 2 (Ds T) - Ds LT) -
      appCc (I := I) (M := M) g 2 2 (Ks - K0) LT - Cross
  dsimp only [J, PairComm]
  calc
    oneMinusConnLapSmooth (I := I) g 0 2
          (appCc (I := I) (M := M) g 2 2 (R0 + K0) T) +
        (oneMinusConnLapSmooth (I := I) g 0 2 Z -
            appCc (I := I) (M := M) g 2 2 (Q LT) T -
            appCc (I := I) (M := M) g 2 2 (Q T) LT + Z) +
        (oneMinusConnLapSmooth (I := I) g 0 2
            (appCc (I := I) (M := M) g 4 2 C
              (iteratedCovGrad (I := I) g 0 2 2 T)) -
          appCc (I := I) (M := M) g 4 2 C
            (iteratedCovGrad (I := I) g 0 2 2 LT)) - Z =
      (oneMinusConnLapSmooth (I := I) g 0 2
          (appCc (I := I) (M := M) g 2 2 (R0 + K0) T) +
        oneMinusConnLapSmooth (I := I) g 0 2 Z +
        oneMinusConnLapSmooth (I := I) g 0 2
          (appCc (I := I) (M := M) g 4 2 C
            (iteratedCovGrad (I := I) g 0 2 2 T))) -
        appCc (I := I) (M := M) g 4 2 C
          (iteratedCovGrad (I := I) g 0 2 2 LT) - Cross := by
            dsimp only [Cross]
            module
    _ = oneMinusConnLapSmooth (I := I) g 0 2
          (appCc (I := I) (M := M) g 2 2 (R0 + K0) T + Z +
            appCc (I := I) (M := M) g 4 2 C
              (iteratedCovGrad (I := I) g 0 2 2 T)) -
        appCc (I := I) (M := M) g 4 2 C
          (iteratedCovGrad (I := I) g 0 2 2 LT) - Cross := by
            rw [oneMinusConn_add (I := I) (M := M) g 0 2,
              oneMinusConn_add (I := I) (M := M) g 0 2]
    _ = oneMinusConnLapSmooth (I := I) g 0 2
          (appCc (I := I) (M := M) g 2 2 E0 T + Ds T) -
        appCc (I := I) (M := M) g 4 2 C
          (iteratedCovGrad (I := I) g 0 2 2 LT) - Cross := by
            rw [hinside]
    _ = oneMinusConnLapSmooth (I := I) g 0 2
          (appCc (I := I) (M := M) g 2 2 E0 T + Ds T) -
        (Ds LT + appCc (I := I) (M := M) g 2 2 (Ks - K0) LT) -
        Cross := by
            rw [htop LT]
    _ = oneMinusConnLapSmooth (I := I) g 0 2
          (appCc (I := I) (M := M) g 2 2 E0 T) +
        (oneMinusConnLapSmooth (I := I) g 0 2 (Ds T) - Ds LT) -
        appCc (I := I) (M := M) g 2 2 (Ks - K0) LT - Cross := by
            rw [oneMinusConn_add (I := I) (M := M) g 0 2]
            module

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
