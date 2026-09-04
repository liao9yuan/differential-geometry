import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.PointedActionLower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.PointedSegment
import Mathlib.Topology.Order.WithTop

set_option autoImplicit false

/-!
# Pointed convergence of restricted L-values

This file assembles fixed-competitor upper convergence and varying-minimizer
lower semicontinuity under explicit compact/chart confinement.
-/

noncomputable section

namespace DifferentialGeometry.HCGCompactness

open Bundle Filter Function MeasureTheory Set
open scoped ContDiff Manifold Topology Interval

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

section

variable [hFinrank : NeZero (Module.finrank Real E)]
  [hBoundaryless : I.Boundaryless]

set_option maxHeartbeats 1200000 in
-- The statement exposes the full pointed-confinement data consumed by both bounds.
include hFinrank hBoundaryless in
/-- Exact restricted L-values converge under pointed smooth convergence when
source attainers have a common compact fixed-chart realization and a limit
attainer supplies the transported upper competitor. -/
theorem lSegValue_pt_lim
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    {subseq : Nat → Nat}
    (Phi : PointedCGHMaps (I := I) X (L.atTime 0) subseq)
    (R : letI : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
      letI : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
      letI : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
      SmoothRiemannianMetric I (L.atTime 0).M)
    (bf : BumpFamily (I := I) Phi) (hSrc : SrcSigma Phi) (hTgt : TgtSigma Phi)
    (beta psi cLow : Real) (hcLow : 0 < cLow)
    (hBound : letI : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
        letI : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
        letI : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
      ∀ (k : Nat) (t : Real), t ∈ Icc beta psi →
        ∀ (z : SourceDomain (I := I) Phi k)
          (v : letI : TopologicalSpace (SourceDomain (I := I) Phi k) :=
              sourceDomTop (I := I) Phi k
            letI : ChartedSpace H (SourceDomain (I := I) Phi k) :=
              sourceDomCharted (I := I) Phi k
            TangentSpace I z),
          cLow * R.inner (z : (L.atTime 0).M) v v ≤
            letI : TopologicalSpace (SourceDomain (I := I) Phi k) :=
              sourceDomTop (I := I) Phi k
            letI : ChartedSpace H (SourceDomain (I := I) Phi k) :=
              sourceDomCharted (I := I) Phi k
            letI : IsManifold I ∞ (SourceDomain (I := I) Phi k) :=
              sourceDomSmooth (I := I) Phi k
            (srcMetric (I := I) Phi hSrc hTgt k t).inner z v v)
    (hCovTail : letI : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
        letI : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
        letI : T2Space (L.atTime 0).M := (L.atTime 0).t2
        letI : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
        letI : SigmaCompactSpace (L.atTime 0).M := (L.atTime 0).sigmaCompact
      ∀ q : Nat, ∃ C : Real, ∀ (k : Nat) (t : Real), t ∈ Icc beta psi →
        ∀ z : (L.atTime 0).M, z ∈ bf.grow k →
          metricCovDerivNorm (I := I) q
            (gSeqExt (I := I) Phi R bf hSrc hTgt k t) R z ≤ C)
    (co : ConvOut (I := I) Phi R bf hSrc hTgt beta psi)
    (hInf : letI : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
      letI : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
      letI : T2Space (L.atTime 0).M := (L.atTime 0).t2
      letI : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
      letI : SigmaCompactSpace (L.atTime 0).M := (L.atTime 0).sigmaCompact
      MetricFamilySmoothOn (I := I) (M := (L.atTime 0).M) X.D co.gInf)
    (hReg : Icc beta psi ⊆ X.D.regular)
    (hLMetric : letI : TopologicalSpace L.M := L.topology
        letI : ChartedSpace H L.M := L.charted
        letI : T2Space L.M := L.t2
        letI : IsManifold I ∞ L.M := L.smooth
        letI : SigmaCompactSpace L.M := L.sigmaCompact
      ∀ t ∈ Icc beta psi, L.S.family.metric t = co.gInf t)
    (hLimRegular : letI : TopologicalSpace L.M := L.topology
      RegularSpace L.M)
    (hLimConnected : letI : TopologicalSpace L.M := L.topology
      ConnectedSpace L.M)
    (T a b K0 : Real) (ha : 0 ≤ a) (hab : a ≤ b)
    (x y : L.M) (ΩLim : Set (L.M × Real))
    (Ω : (k : Nat) → Set ((X.term (subseq (co.φ k))).M × Real))
    (hTermRegular : ∀ k,
      letI : TopologicalSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).topology
      RegularSpace (X.term (subseq (co.φ k))).M)
    (hTermConnected : ∀ k,
      letI : TopologicalSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).topology
      ConnectedSpace (X.term (subseq (co.φ k))).M)
    (hScalar : ∀ᶠ k in atTop,
      letI : TopologicalSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).topology
      letI : ChartedSpace H (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).charted
      letI : T2Space (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).t2
      letI : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).smooth
      letI : SigmaCompactSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).sigmaCompact
      ∀ q ∈ Ω k, -K0 ≤ (X.term (subseq (co.φ k))).S.scalar q.2 q.1)
    (hScalarLim : letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : T2Space L.M := L.t2
      letI : IsManifold I ∞ L.M := L.smooth
      letI : SigmaCompactSpace L.M := L.sigmaCompact
      ∀ q ∈ ΩLim, -K0 ≤ L.S.scalar q.2 q.1)
    (delta : Real → L.M)
    (hDeltaC1 : letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : IsManifold I ∞ L.M := L.smooth
      ContMDiff 𝓘(Real, Real) I 1 delta)
    (hDeltaAtt : letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : IsManifold I ∞ L.M := L.smooth
      letI : RegularSpace L.M := hLimRegular
      letI : ConnectedSpace L.M := hLimConnected
      IsLSegAttainer L.S T ΩLim (a ^ 2) (b ^ 2) x y delta)
    (hDeltaMap : ∀ᶠ k in atTop,
      letI : TopologicalSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).topology
      letI : ChartedSpace H (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).charted
      letI : T2Space (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).t2
      letI : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).smooth
      letI : SigmaCompactSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).sigmaCompact
      letI : RegularSpace (X.term (subseq (co.φ k))).M := hTermRegular k
      letI : ConnectedSpace (X.term (subseq (co.φ k))).M := hTermConnected k
      IsLSegCurve (X.term (subseq (co.φ k))).S T (Ω k)
        (a ^ 2) (b ^ 2) (fun r ↦ Phi.map (co.φ k) (delta r)))
    (alpha : Nat → Real → L.M) (alphaLim : Real → L.M)
    (hAlpha : letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : IsManifold I ∞ L.M := L.smooth
      ∀ n, ContMDiffOn 𝓘(Real, Real) I 1 (alpha n) (Icc a b))
    (hTermAtt : ∀ k,
      letI : TopologicalSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).topology
      letI : ChartedSpace H (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).charted
      letI : T2Space (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).t2
      letI : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).smooth
      letI : SigmaCompactSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).sigmaCompact
      letI : RegularSpace (X.term (subseq (co.φ k))).M := hTermRegular k
      letI : ConnectedSpace (X.term (subseq (co.φ k))).M := hTermConnected k
      IsLSegAttainer (X.term (subseq (co.φ k))).S T (Ω k)
        (a ^ 2) (b ^ 2) (Phi.map (co.φ k) x) (Phi.map (co.φ k) y)
        (sqrtReparam (fun s ↦ Phi.map (co.φ k) (alpha k s))))
    (hLimSeg : letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : IsManifold I ∞ L.M := L.smooth
      letI : RegularSpace L.M := hLimRegular
      letI : ConnectedSpace L.M := hLimConnected
      IsLSegCurve L.S T ΩLim (a ^ 2) (b ^ 2) (sqrtReparam alphaLim))
    (hLimA : sqrtReparam alphaLim (a ^ 2) = x)
    (hLimB : sqrtReparam alphaLim (b ^ 2) = y)
    (u : Nat → timeH1 E (b - a)) (uLim : timeH1 E (b - a))
    (z0 : L.M)
    (hChart : letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      ∀ n, MapsTo (alpha n) (Icc a b) (chartAt H z0).source)
    (hRep : letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : IsManifold I ∞ L.M := L.smooth
      ∀ n, EqOn (u n).toFun
        (fun r ↦ extChartAt I z0 (alpha n (a + r))) (Icc (0 : Real) (b - a)))
    (hLimChart : letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      MapsTo alphaLim (Icc a b) (chartAt H z0).source)
    (hLimRep : letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : IsManifold I ∞ L.M := L.smooth
      EqOn uLim.toFun
        (fun r ↦ extChartAt I z0 (alphaLim (a + r))) (Icc (0 : Real) (b - a)))
    (Q : Set L.M)
    (hQc : letI : TopologicalSpace L.M := L.topology; IsCompact Q)
    (hQ : ∀ n (s : Icc a b), alpha n s.1 ∈ Q)
    (Kc : Set E) (hKc : IsCompact Kc)
    (hKChart : letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : IsManifold I ∞ L.M := L.smooth
      Kc ⊆ interior (extChartAt I z0).target)
    (huK : ∀ n (r : Icc (0 : Real) (b - a)), (u n).toFun r.1 ∈ Kc)
    (hu : TendstoUniformly
      (fun n (r : Icc (0 : Real) (b - a)) ↦ (u n).toFun r.1)
      (fun r ↦ uLim.toFun r.1) atTop)
    (hdu : ∀ z : timeL2 E (b - a), Tendsto
      (fun n ↦ inner Real (u n).deriv z) atTop
      (nhds (inner Real uLim.deriv z)))
    (dP : PseudoMetricSpace L.M)
    (hTop : dP.toUniformSpace.toTopologicalSpace = L.topology)
    (hAlphaLim : letI : PseudoMetricSpace L.M := dP
      TendstoUniformly
        (fun n (s : Icc a b) ↦ alpha n s.1)
        (fun s ↦ alphaLim s.1) atTop)
    (hBackSq : MapsTo (fun s ↦ T - s ^ 2) (Icc a b) (Icc beta psi))
    (hBackRaw : MapsTo (fun s ↦ T - s)
      (Icc (a ^ 2) (b ^ 2)) (Icc beta psi)) :
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : IsManifold I ∞ L.M := L.smooth
    letI : RegularSpace L.M := hLimRegular
    letI : ConnectedSpace L.M := hLimConnected
    Tendsto (fun k ↦
      letI : TopologicalSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).topology
      letI : ChartedSpace H (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).charted
      letI : T2Space (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).t2
      letI : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).smooth
      letI : SigmaCompactSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).sigmaCompact
      letI : RegularSpace (X.term (subseq (co.φ k))).M := hTermRegular k
      letI : ConnectedSpace (X.term (subseq (co.φ k))).M := hTermConnected k
      lSegValue (X.term (subseq (co.φ k))).S T (Ω k)
        (a ^ 2) (b ^ 2) (Phi.map (co.φ k) x) (Phi.map (co.φ k) y))
      atTop (nhds (lSegValue L.S T ΩLim (a ^ 2) (b ^ 2) x y)) := by
  classical
  letI : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
  letI : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
  letI : T2Space (L.atTime 0).M := (L.atTime 0).t2
  letI : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
  letI : SigmaCompactSpace (L.atTime 0).M := (L.atTime 0).sigmaCompact
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : T2Space L.M := L.t2
  letI : IsManifold I ∞ L.M := L.smooth
  letI : SigmaCompactSpace L.M := L.sigmaCompact
  letI : RegularSpace L.M := hLimRegular
  letI : ConnectedSpace L.M := hLimConnected
  have hb : 0 ≤ b := ha.trans hab
  have habSq : a ^ 2 ≤ b ^ 2 := (sq_le_sq₀ ha hb).2 hab
  let A : Nat → Real := fun k ↦
    letI : TopologicalSpace (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).topology
    letI : ChartedSpace H (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).charted
    letI : T2Space (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).t2
    letI : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).smooth
    letI : SigmaCompactSpace (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).sigmaCompact
    lRegAction (X.term (subseq (co.φ k))).S T
      (fun s ↦ Phi.map (co.φ k) (alpha k s)) a b
  let A0 : Real := lLength L.S T delta (a ^ 2) (b ^ 2)
  let V : Nat → WithTop Real := fun k ↦
    letI : TopologicalSpace (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).topology
    letI : ChartedSpace H (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).charted
    letI : T2Space (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).t2
    letI : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).smooth
    letI : SigmaCompactSpace (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).sigmaCompact
    letI : RegularSpace (X.term (subseq (co.φ k))).M := hTermRegular k
    letI : ConnectedSpace (X.term (subseq (co.φ k))).M := hTermConnected k
    lSegValue (X.term (subseq (co.φ k))).S T (Ω k)
      (a ^ 2) (b ^ 2) (Phi.map (co.φ k) x) (Phi.map (co.φ k) y)
  let V0 : WithTop Real := lSegValue L.S T ΩLim (a ^ 2) (b ^ 2) x y
  have hVal (k : Nat) : V k = (A k : WithTop Real) := by
    letI : TopologicalSpace (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).topology
    letI : ChartedSpace H (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).charted
    letI : T2Space (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).t2
    letI : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).smooth
    letI : SigmaCompactSpace (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).sigmaCompact
    letI : RegularSpace (X.term (subseq (co.φ k))).M := hTermRegular k
    letI : ConnectedSpace (X.term (subseq (co.φ k))).M := hTermConnected k
    calc
      V k = (lLength (X.term (subseq (co.φ k))).S T
          (sqrtReparam (fun s ↦ Phi.map (co.φ k) (alpha k s)))
          (a ^ 2) (b ^ 2) : WithTop Real) := (hTermAtt k).2.2.2
      _ = (A k : WithTop Real) := congrArg (fun r : Real ↦ (r : WithTop Real))
        (lLength_sqrt_Icc (I := I) (X.term (subseq (co.φ k))).S T
          (fun s ↦ Phi.map (co.φ k) (alpha k s)) a b ha hab)
  have hVal0 : V0 = (A0 : WithTop Real) := (hDeltaAtt).2.2.2
  have hTime : Icc beta psi ⊆ X.D.carrier := hReg.trans X.D.regular_subset
  have hUpper (ε : Real) (hε : 0 < ε) :
      ∀ᶠ k in atTop, A k < A0 + ε := by
    have h := lSegValue_limsup (I := I) Phi R bf hSrc hTgt beta psi cLow hcLow
      hBound hCovTail co hTime hLMetric T (a ^ 2) (b ^ 2) (sq_nonneg a)
      habSq delta hDeltaC1 hBackRaw Ω K0 hTermRegular hTermConnected hScalar
      hDeltaMap hε
    filter_upwards [h] with k hk
    have hk' : V k < ((A0 + ε : Real) : WithTop Real) := by
      simpa only [V, A0, hDeltaAtt.2.1, hDeltaAtt.2.2.1] using hk
    rw [hVal k] at hk'
    exact WithTop.coe_lt_coe.mp hk'
  have hAct : IsBoundedUnder (· ≤ ·) atTop A :=
    isBoundedUnder_of_eventually_le ((hUpper 1 one_pos).mono fun _ h ↦ h.le)
  have hLsc : lRegAction L.S T alphaLim a b ≤ liminf A atTop := by
    simpa only [A] using
      lRegAction_pt_lsc (I := I) Phi R bf hSrc hTgt beta psi cLow hcLow
        hBound hCovTail co hInf hReg hLMetric T a b hab z0 alpha alphaLim
        hAlpha u uLim hChart hRep hLimChart hLimRep Q hQc hQ Kc hKc
        hKChart huK hu hdu dP hTop hAlphaLim hAct hBackSq
  have hCurve : A0 ≤ lRegAction L.S T alphaLim a b := by
    apply WithTop.coe_le_coe.mp
    calc
      (A0 : WithTop Real) = V0 := hVal0.symm
      _ ≤ (lLength L.S T (sqrtReparam alphaLim)
          (a ^ 2) (b ^ 2) : WithTop Real) :=
        lSegValue_le L.S T K0 ΩLim (sq_nonneg a) habSq hScalarLim
          x y (sqrtReparam alphaLim) hLimSeg hLimA hLimB
      _ = (lRegAction L.S T alphaLim a b : WithTop Real) :=
        congrArg (fun r : Real ↦ (r : WithTop Real))
          (lLength_sqrt_Icc (I := I) L.S T alphaLim a b ha hab)
  have hLow : A0 ≤ liminf A atTop := hCurve.trans hLsc
  let C : Real := -(2 * K0 / 3) *
    (b ^ 2 * Real.sqrt (b ^ 2) - a ^ 2 * Real.sqrt (a ^ 2))
  have hAloEv : ∀ᶠ k in atTop, C ≤ A k := by
    filter_upwards [hScalar] with k hScalarK
    letI : TopologicalSpace (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).topology
    letI : ChartedSpace H (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).charted
    letI : T2Space (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).t2
    letI : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).smooth
    letI : SigmaCompactSpace (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).sigmaCompact
    letI : RegularSpace (X.term (subseq (co.φ k))).M := hTermRegular k
    letI : ConnectedSpace (X.term (subseq (co.φ k))).M := hTermConnected k
    have hAtt := hTermAtt k
    have hAttCurve : IsLSegCurve (X.term (subseq (co.φ k))).S T (Ω k)
        (a ^ 2) (b ^ 2)
        (sqrtReparam (fun s ↦ Phi.map (co.φ k) (alpha k s))) := hAtt.1
    have hAttInt : IntervalIntegrable
        (lDensity (X.term (subseq (co.φ k))).S T
          (sqrtReparam (fun s ↦ Phi.map (co.φ k) (alpha k s))))
        volume (a ^ 2) (b ^ 2) := hAttCurve.2.2.1
    have hAttGraph : ∀ s ∈ Icc (a ^ 2) (b ^ 2),
        (sqrtReparam (fun r ↦ Phi.map (co.φ k) (alpha k r)) s, T - s) ∈ Ω k :=
      hAttCurve.2.2.2
    have hScalarCurve : ∀ s ∈ Icc (a ^ 2) (b ^ 2),
        -K0 ≤ (X.term (subseq (co.φ k))).S.scalar (T - s)
          (sqrtReparam (fun r ↦ Phi.map (co.φ k) (alpha k r)) s) :=
      fun s hs ↦ hScalarK
        (sqrtReparam (fun r ↦ Phi.map (co.φ k) (alpha k r)) s, T - s)
        (hAttGraph s hs)
    have hLower := lLength_lower (I := I) (X.term (subseq (co.φ k))).S
      T (a ^ 2) (b ^ 2) K0 (sq_nonneg a) habSq
      (sqrtReparam (fun s ↦ Phi.map (co.φ k) (alpha k s))) hScalarCurve hAttInt
    rw [lLength_sqrt_Icc (I := I) (X.term (subseq (co.φ k))).S T
      (fun s ↦ Phi.map (co.φ k) (alpha k s)) a b ha hab] at hLower
    simpa only [C, A] using hLower
  have hAlo : IsBoundedUnder (· ≥ ·) atTop A :=
    isBoundedUnder_of_eventually_ge hAloEv
  have hA : Tendsto A atTop (nhds A0) := by
    refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
    have hlo : ∀ᶠ k in atTop, A0 - ε < A k :=
      eventually_lt_of_lt_liminf
        ((sub_lt_self A0 hε).trans_le hLow) hAlo
    have hhi := hUpper ε hε
    have hd : ∀ᶠ k in atTop, dist (A k) A0 < ε := by
      filter_upwards [hlo, hhi] with k hklo hkhi
      rw [Real.dist_eq]
      exact abs_lt.2 ⟨by linarith, by linarith⟩
    exact hd.exists_forall_of_atTop
  have hCoe : Tendsto (fun k ↦ (A k : WithTop Real)) atTop
      (nhds (A0 : WithTop Real)) :=
    WithTop.continuous_coe.continuousAt.tendsto.comp hA
  have hV : Tendsto V atTop (nhds V0) := by
    rw [hVal0]
    exact hCoe.congr' (Eventually.of_forall fun k ↦ (hVal k).symm)
  simpa only [V, V0] using hV

end

end DifferentialGeometry.HCGCompactness
