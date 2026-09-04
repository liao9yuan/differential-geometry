import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.PointedValue
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.SegmentDensity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ActionRawMin
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume

set_option autoImplicit false

/-!
# Pointwise pointed convergence of reduced density

This file specializes pointed same-clock segment-value convergence to ordinary
L-cost and then applies the reduced-length normalization and exponential.
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
-- The specialization instantiates the full pointed compactness package twice.
include hFinrank hBoundaryless in
/-- Under the compact/chart confinement used by pointed L-value stability,
the fixed-time reduced densities converge pointwise. -/
theorem redDensity_pt_lim
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
    (T K0 tau : Real) (htau : 0 < tau)
    (x y : L.M)
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
      ∀ q : (X.term (subseq (co.φ k))).M × Real, q ∈ Set.univ →
        -K0 ≤ (X.term (subseq (co.φ k))).S.scalar q.2 q.1)
    (hScalarLim : letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : T2Space L.M := L.t2
      letI : IsManifold I ∞ L.M := L.smooth
      letI : SigmaCompactSpace L.M := L.sigmaCompact
      ∀ q : L.M × Real, q ∈ Set.univ → -K0 ≤ L.S.scalar q.2 q.1)
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
      IsLSegAttainer L.S T Set.univ ((0 : Real) ^ 2) ((Real.sqrt tau) ^ 2) x y delta)
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
      IsLSegCurve (X.term (subseq (co.φ k))).S T (Set.univ)
        ((0 : Real) ^ 2) ((Real.sqrt tau) ^ 2) (fun r ↦ Phi.map (co.φ k) (delta r)))
    (alpha : Nat → Real → L.M) (alphaLim : Real → L.M)
    (hAlpha : letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : IsManifold I ∞ L.M := L.smooth
      ∀ n, ContMDiffOn 𝓘(Real, Real) I 1 (alpha n) (Icc (0 : Real) (Real.sqrt tau)))
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
      IsLSegAttainer (X.term (subseq (co.φ k))).S T (Set.univ)
        ((0 : Real) ^ 2) ((Real.sqrt tau) ^ 2) (Phi.map (co.φ k) x) (Phi.map (co.φ k) y)
        (sqrtReparam (fun s ↦ Phi.map (co.φ k) (alpha k s))))
    (hLimSeg : letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : IsManifold I ∞ L.M := L.smooth
      letI : RegularSpace L.M := hLimRegular
      letI : ConnectedSpace L.M := hLimConnected
      IsLSegCurve L.S T Set.univ ((0 : Real) ^ 2) ((Real.sqrt tau) ^ 2) (sqrtReparam alphaLim))
    (hLimA : sqrtReparam alphaLim ((0 : Real) ^ 2) = x)
    (hLimB : sqrtReparam alphaLim ((Real.sqrt tau) ^ 2) = y)
    (u : Nat → timeH1 E ((Real.sqrt tau) - (0 : Real))) (uLim : timeH1 E ((Real.sqrt tau) - (0 : Real)))
    (z0 : L.M)
    (hChart : letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      ∀ n, MapsTo (alpha n) (Icc (0 : Real) (Real.sqrt tau)) (chartAt H z0).source)
    (hRep : letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : IsManifold I ∞ L.M := L.smooth
      ∀ n, EqOn (u n).toFun
        (fun r ↦ extChartAt I z0 (alpha n ((0 : Real) + r))) (Icc (0 : Real) ((Real.sqrt tau) - (0 : Real))))
    (hLimChart : letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      MapsTo alphaLim (Icc (0 : Real) (Real.sqrt tau)) (chartAt H z0).source)
    (hLimRep : letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : IsManifold I ∞ L.M := L.smooth
      EqOn uLim.toFun
        (fun r ↦ extChartAt I z0 (alphaLim ((0 : Real) + r))) (Icc (0 : Real) ((Real.sqrt tau) - (0 : Real))))
    (Q : Set L.M)
    (hQc : letI : TopologicalSpace L.M := L.topology; IsCompact Q)
    (hQ : ∀ n (s : Icc (0 : Real) (Real.sqrt tau)), alpha n s.1 ∈ Q)
    (Kc : Set E) (hKc : IsCompact Kc)
    (hKChart : letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : IsManifold I ∞ L.M := L.smooth
      Kc ⊆ interior (extChartAt I z0).target)
    (huK : ∀ n (r : Icc (0 : Real) ((Real.sqrt tau) - (0 : Real))), (u n).toFun r.1 ∈ Kc)
    (hu : TendstoUniformly
      (fun n (r : Icc (0 : Real) ((Real.sqrt tau) - (0 : Real))) ↦ (u n).toFun r.1)
      (fun r ↦ uLim.toFun r.1) atTop)
    (hdu : ∀ z : timeL2 E ((Real.sqrt tau) - (0 : Real)), Tendsto
      (fun n ↦ inner Real (u n).deriv z) atTop
      (nhds (inner Real uLim.deriv z)))
    (dP : PseudoMetricSpace L.M)
    (hTop : dP.toUniformSpace.toTopologicalSpace = L.topology)
    (hAlphaLim : letI : PseudoMetricSpace L.M := dP
      TendstoUniformly
        (fun n (s : Icc (0 : Real) (Real.sqrt tau)) ↦ alpha n s.1)
        (fun s ↦ alphaLim s.1) atTop)
    (hBackSq : MapsTo (fun s ↦ T - s ^ 2) (Icc (0 : Real) (Real.sqrt tau)) (Icc beta psi))
    (hBackRaw : MapsTo (fun s ↦ T - s)
      (Icc ((0 : Real) ^ 2) ((Real.sqrt tau) ^ 2)) (Icc beta psi)) :
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : IsManifold I ∞ L.M := L.smooth
    letI : RegularSpace L.M := hLimRegular
    letI : ConnectedSpace L.M := hLimConnected
    letI : PseudoMetricSpace L.M := lSegmentMetric L.S T
    letI : TopologicalSpace L.M := L.topology
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
      letI : PseudoMetricSpace (X.term (subseq (co.φ k))).M :=
        lSegmentMetric (X.term (subseq (co.φ k))).S T
      letI : TopologicalSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).topology
      redDensity (X.term (subseq (co.φ k))).S T
        (Phi.map (co.φ k) x) (Phi.map (co.φ k) y) tau)
      atTop (nhds (redDensity L.S T x y tau)) := by
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
  letI : PseudoMetricSpace L.M := lSegmentMetric L.S T
  letI : TopologicalSpace L.M := L.topology
  have hb : 0 ≤ Real.sqrt tau := Real.sqrt_nonneg tau
  have hValue := lSegValue_pt_lim (I := I) Phi R bf hSrc hTgt
    beta psi cLow hcLow hBound hCovTail co hInf hReg hLMetric
    hLimRegular hLimConnected T 0 (Real.sqrt tau) K0 (le_refl 0) hb x y
    Set.univ (fun _ ↦ Set.univ) hTermRegular hTermConnected hScalar hScalarLim
    delta hDeltaC1 hDeltaAtt hDeltaMap alpha alphaLim hAlpha hTermAtt
    hLimSeg hLimA hLimB u uLim z0 hChart hRep hLimChart hLimRep Q hQc hQ
    Kc hKc hKChart huK hu hdu dP hTop hAlphaLim hBackSq hBackRaw
  let C : Nat → Real := fun k ↦
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
    lCost (X.term (subseq (co.φ k))).S T
      (Phi.map (co.φ k) x) (Phi.map (co.φ k) y) tau
  let C0 : Real := lCost L.S T x y tau
  have hregSq : ∀ s ∈ Icc (0 : Real) (Real.sqrt tau),
      T - s ^ 2 ∈ X.D.regular :=
    fun s hs ↦ hReg (hBackSq hs)
  have hEqLim :
      lSegValue L.S T Set.univ (0 ^ 2) ((Real.sqrt tau) ^ 2) x y =
        (C0 : WithTop Real) := by
    let topM : TopologicalSpace L.M := inferInstance
    letI : PseudoMetricSpace L.M := lSegmentMetric L.S T
    letI : TopologicalSpace L.M := topM
    have hMet : MetricFamilySmoothOn (I := I) (M := L.M) X.D
        L.S.family.metric := L.isSolution.smoothMetric
    have hSc : ScalarSTContOn (I := I) (M := L.M) L.S :=
      ⟨L.isSolution.scalarCont⟩
    rw [lSegValue_eq_of_seg (I := I) L.S hMet hSc T K0 0
      (Real.sqrt tau) (le_refl 0) hb
      (fun r hr z ↦ hScalarLim (z, T - r) (by simp))
      hregSq x y delta hDeltaAtt.1 hDeltaAtt.2.1 hDeltaAtt.2.2.1]
    exact congrArg (fun r : Real ↦ (r : WithTop Real))
      (lCost_eq_reg (I := I) L.S T x y tau htau.le).symm
  have hEqTerm : ∀ᶠ k in atTop,
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
      lSegValue (X.term (subseq (co.φ k))).S T Set.univ
        (0 ^ 2) ((Real.sqrt tau) ^ 2)
        (Phi.map (co.φ k) x) (Phi.map (co.φ k) y) =
          (C k : WithTop Real) := by
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
    let topM : TopologicalSpace (X.term (subseq (co.φ k))).M := inferInstance
    letI : PseudoMetricSpace (X.term (subseq (co.φ k))).M :=
      lSegmentMetric (X.term (subseq (co.φ k))).S T
    letI : TopologicalSpace (X.term (subseq (co.φ k))).M := topM
    have hMet : MetricFamilySmoothOn (I := I)
        (M := (X.term (subseq (co.φ k))).M) X.D
        (X.term (subseq (co.φ k))).S.family.metric :=
      (X.term (subseq (co.φ k))).isSolution.smoothMetric
    have hSc : ScalarSTContOn (I := I)
        (M := (X.term (subseq (co.φ k))).M)
        (X.term (subseq (co.φ k))).S :=
      ⟨(X.term (subseq (co.φ k))).isSolution.scalarCont⟩
    rw [lSegValue_eq_of_seg (I := I) (X.term (subseq (co.φ k))).S
      hMet hSc T K0 0 (Real.sqrt tau) (le_refl 0) hb
      (fun r hr z ↦ hScalarK (z, T - r) (by simp))
      hregSq (Phi.map (co.φ k) x) (Phi.map (co.φ k) y)
      (sqrtReparam (fun s ↦ Phi.map (co.φ k) (alpha k s)))
      (hTermAtt k).1 (hTermAtt k).2.1 (hTermAtt k).2.2.1]
    exact congrArg (fun r : Real ↦ (r : WithTop Real))
      (lCost_eq_reg (I := I) (X.term (subseq (co.φ k))).S T
        (Phi.map (co.φ k) x) (Phi.map (co.φ k) y) tau htau.le).symm
  have hCoe : Tendsto (fun k ↦ (C k : WithTop Real)) atTop
      (nhds (C0 : WithTop Real)) := by
    rw [← hEqLim]
    exact hValue.congr' hEqTerm
  have hCost : Tendsto C atTop (nhds C0) := by
    have h :=
      (WithTop.tendsto_untopD (0 : Real)
        (WithTop.coe_ne_top : (C0 : WithTop Real) ≠ ⊤)).comp hCoe
    simpa only [WithTop.untopD_coe] using h
  have hRed : Tendsto (fun k ↦
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
      letI : PseudoMetricSpace (X.term (subseq (co.φ k))).M :=
        lSegmentMetric (X.term (subseq (co.φ k))).S T
      letI : TopologicalSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).topology
      redLength (X.term (subseq (co.φ k))).S T
        (Phi.map (co.φ k) x) (Phi.map (co.φ k) y) tau)
      atTop (nhds (redLength L.S T x y tau)) := by
    simpa only [redLength, C, C0] using
      hCost.div_const (2 * Real.sqrt tau)
  have hExp := ((hRed.neg.sub_const
      (((Module.finrank Real E : Real) / 2) * Real.log tau)).sub_const
      (((Module.finrank Real E : Real) / 2) * Real.log (4 * Real.pi)))
  simpa only [redDensity] using
    Real.continuous_exp.continuousAt.tendsto.comp hExp

end

end DifferentialGeometry.HCGCompactness
