import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.PointedDensitySourceTest
import DifferentialGeometry.Analysis.Integration.Measure.PartialDiffeomorphLocal

set_option autoImplicit false

/-!
# Compactly supported tests for pointed reduced density

This file prepares the finite preferred-chart assembly for compactly supported
tests on the fixed limit space.  The completed endpoint must use raw transported
`Measure`s; no global finiteness or tightness belongs in this layer.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped CompactlySupported ContDiff Manifold Topology

namespace DifferentialGeometry.HCGCompactness

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman

universe u uA uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

private noncomputable def srcTest
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    {subseq : Nat → Nat}
    (Phi : PointedCGHMaps (I := I) X (L.atTime 0) subseq)
    (phi : Nat → Nat)
    (hTermRegular : ∀ k,
      letI : TopologicalSpace (X.term (subseq (phi k))).M :=
        (X.term (subseq (phi k))).topology
      RegularSpace (X.term (subseq (phi k))).M)
    (hTermConnected : ∀ k,
      letI : TopologicalSpace (X.term (subseq (phi k))).M :=
        (X.term (subseq (phi k))).topology
      ConnectedSpace (X.term (subseq (phi k))).M)
    (T tau : Real) (x alpha : L.M) (B : Set E) (w : E → Real) (k : Nat) : ENNReal := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : TopologicalSpace (X.term (subseq (phi k))).M :=
    (X.term (subseq (phi k))).topology
  letI : ChartedSpace H (X.term (subseq (phi k))).M :=
    (X.term (subseq (phi k))).charted
  letI : T2Space (X.term (subseq (phi k))).M := (X.term (subseq (phi k))).t2
  letI : IsManifold I ∞ (X.term (subseq (phi k))).M := (X.term (subseq (phi k))).smooth
  letI : SigmaCompactSpace (X.term (subseq (phi k))).M :=
    (X.term (subseq (phi k))).sigmaCompact
  letI : RegularSpace (X.term (subseq (phi k))).M := hTermRegular k
  letI : ConnectedSpace (X.term (subseq (phi k))).M := hTermConnected k
  letI : PseudoMetricSpace (X.term (subseq (phi k))).M :=
    lSegmentMetric (X.term (subseq (phi k))).S T
  letI : TopologicalSpace (X.term (subseq (phi k))).M :=
    (X.term (subseq (phi k))).topology
  exact ∫⁻ y in (mapChartParam (J := I) Phi (phi k) alpha) '' B,
    ENNReal.ofReal (w ((mapChartParam (J := I) Phi (phi k) alpha).symm y)) *
      ENNReal.ofReal (redDensity (X.term (subseq (phi k))).S T (Phi.map (phi k) x) y tau)
    ∂riemannianVolumeMeasure (I := I) (M := (X.term (subseq (phi k))).M)
      ((X.term (subseq (phi k))).S.base.metric (T - tau))

private noncomputable def limTest
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    {subseq : Nat → Nat}
    {Phi : PointedCGHMaps (I := I) X (L.atTime 0) subseq}
    {R : letI : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
      letI : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
      letI : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
      SmoothRiemannianMetric I (L.atTime 0).M}
    {bf : BumpFamily (I := I) Phi} {hSrc : SrcSigma Phi} {hTgt : TgtSigma Phi}
    {beta psi : Real} (co : ConvOut (I := I) Phi R bf hSrc hTgt beta psi)
    (hLimRegular : letI : TopologicalSpace L.M := L.topology; RegularSpace L.M)
    (hLimConnected : letI : TopologicalSpace L.M := L.topology; ConnectedSpace L.M)
    (T tau : Real) (x alpha : L.M) (B : Set E) (w : E → Real) : ENNReal := by
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
  exact ∫⁻ y in (extChartAt I alpha).symm '' B,
    ENNReal.ofReal (w (extChartAt I alpha y)) *
      ENNReal.ofReal (redDensity L.S T x y tau)
    ∂riemannianVolumeMeasure (I := I) (M := L.M) (co.gInf (T - tau))

/-- The reduced-density measure on one approximating terminal manifold. -/
noncomputable def redDensityTermMeas
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    {subseq : Nat → Nat}
    (Phi : PointedCGHMaps (I := I) X (L.atTime 0) subseq)
    (phi : Nat → Nat)
    (hTermRegular : ∀ k,
      letI : TopologicalSpace (X.term (subseq (phi k))).M :=
        (X.term (subseq (phi k))).topology
      RegularSpace (X.term (subseq (phi k))).M)
    (hTermConnected : ∀ k,
      letI : TopologicalSpace (X.term (subseq (phi k))).M :=
        (X.term (subseq (phi k))).topology
      ConnectedSpace (X.term (subseq (phi k))).M)
    (T tau : Real) (x : L.M) (k : Nat) :
    letI : TopologicalSpace (X.term (subseq (phi k))).M :=
      (X.term (subseq (phi k))).topology
    letI : MeasurableSpace (X.term (subseq (phi k))).M :=
      borel (X.term (subseq (phi k))).M
    Measure (X.term (subseq (phi k))).M := by
  letI : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
  letI : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
  letI : T2Space (L.atTime 0).M := (L.atTime 0).t2
  letI : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
  letI : SigmaCompactSpace (L.atTime 0).M := (L.atTime 0).sigmaCompact
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : TopologicalSpace (X.term (subseq (phi k))).M :=
    (X.term (subseq (phi k))).topology
  letI : ChartedSpace H (X.term (subseq (phi k))).M :=
    (X.term (subseq (phi k))).charted
  letI : T2Space (X.term (subseq (phi k))).M := (X.term (subseq (phi k))).t2
  letI : IsManifold I ∞ (X.term (subseq (phi k))).M :=
    (X.term (subseq (phi k))).smooth
  letI : SigmaCompactSpace (X.term (subseq (phi k))).M :=
    (X.term (subseq (phi k))).sigmaCompact
  letI : RegularSpace (X.term (subseq (phi k))).M := hTermRegular k
  letI : ConnectedSpace (X.term (subseq (phi k))).M := hTermConnected k
  letI : PseudoMetricSpace (X.term (subseq (phi k))).M :=
    lSegmentMetric (X.term (subseq (phi k))).S T
  letI : TopologicalSpace (X.term (subseq (phi k))).M :=
    (X.term (subseq (phi k))).topology
  letI : MeasurableSpace (X.term (subseq (phi k))).M :=
    borel (X.term (subseq (phi k))).M
  letI : BorelSpace (X.term (subseq (phi k))).M := ⟨rfl⟩
  exact (riemannianVolumeMeasure (I := I)
      (M := (X.term (subseq (phi k))).M)
      ((X.term (subseq (phi k))).S.base.metric (T - tau))).withDensity
    (fun y ↦ ENNReal.ofReal (redDensity (X.term (subseq (phi k))).S T
      (Phi.map (phi k) x) y tau))

/-- The approximating reduced-density measure transported to the fixed limit
manifold through the inverse pointed comparison map. -/
noncomputable def redDensitySrcMeas
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    {subseq : Nat → Nat}
    (Phi : PointedCGHMaps (I := I) X (L.atTime 0) subseq)
    (phi : Nat → Nat)
    (hTermRegular : ∀ k,
      letI : TopologicalSpace (X.term (subseq (phi k))).M :=
        (X.term (subseq (phi k))).topology
      RegularSpace (X.term (subseq (phi k))).M)
    (hTermConnected : ∀ k,
      letI : TopologicalSpace (X.term (subseq (phi k))).M :=
        (X.term (subseq (phi k))).topology
      ConnectedSpace (X.term (subseq (phi k))).M)
    (T tau : Real) (x : L.M) (k : Nat) :
    letI : TopologicalSpace L.M := L.topology
    letI : MeasurableSpace L.M := borel L.M
    Measure L.M := by
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
  letI : MeasurableSpace L.M := borel L.M
  letI : BorelSpace L.M := ⟨rfl⟩
  letI : TopologicalSpace (X.term (subseq (phi k))).M :=
    (X.term (subseq (phi k))).topology
  letI : ChartedSpace H (X.term (subseq (phi k))).M :=
    (X.term (subseq (phi k))).charted
  letI : T2Space (X.term (subseq (phi k))).M := (X.term (subseq (phi k))).t2
  letI : IsManifold I ∞ (X.term (subseq (phi k))).M :=
    (X.term (subseq (phi k))).smooth
  letI : SigmaCompactSpace (X.term (subseq (phi k))).M :=
    (X.term (subseq (phi k))).sigmaCompact
  let e := Phi.partialDiffeomorph (phi k)
  letI : RegularSpace (X.term (subseq (phi k))).M := hTermRegular k
  letI : ConnectedSpace (X.term (subseq (phi k))).M := hTermConnected k
  letI : PseudoMetricSpace (X.term (subseq (phi k))).M :=
    lSegmentMetric (X.term (subseq (phi k))).S T
  letI : TopologicalSpace (X.term (subseq (phi k))).M :=
    (X.term (subseq (phi k))).topology
  letI : MeasurableSpace (X.term (subseq (phi k))).M :=
    borel (X.term (subseq (phi k))).M
  letI : BorelSpace (X.term (subseq (phi k))).M := ⟨rfl⟩
  let mu := redDensityTermMeas Phi phi hTermRegular hTermConnected T tau x k
  exact Measure.map e.symm (mu.restrict e.target)

omit [I.Boundaryless] in
/-- Reverse ball capture transfers a terminal reduced-density tail bound to the
complement of the captured compact set in the fixed limit manifold. -/
theorem redSrc_tail_le
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    {subseq : Nat → Nat}
    (Phi : PointedCGHMaps (I := I) X (L.atTime 0) subseq)
    (phi : Nat → Nat)
    (hTermRegular : ∀ k,
      letI : TopologicalSpace (X.term (subseq (phi k))).M :=
        (X.term (subseq (phi k))).topology
      RegularSpace (X.term (subseq (phi k))).M)
    (hTermConnected : ∀ k,
      letI : TopologicalSpace (X.term (subseq (phi k))).M :=
        (X.term (subseq (phi k))).topology
      ConnectedSpace (X.term (subseq (phi k))).M)
    (T tau : Real) (x : L.M) (k : Nat) :
    letI : TopologicalSpace L.M := L.topology
    letI : MeasurableSpace L.M := borel L.M
    letI : TopologicalSpace (X.term (subseq (phi k))).M :=
      (X.term (subseq (phi k))).topology
    letI : MeasurableSpace (X.term (subseq (phi k))).M :=
      borel (X.term (subseq (phi k))).M
    ∀ {K : Set L.M}, IsCompact K → K ⊆ Phi.source (phi k) →
      ∀ {B : Set (X.term (subseq (phi k))).M},
        B ⊆ Phi.map (phi k) '' K →
          redDensitySrcMeas Phi phi hTermRegular hTermConnected T tau x k Kᶜ ≤
            redDensityTermMeas Phi phi hTermRegular hTermConnected T tau x k Bᶜ := by
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
  letI : MeasurableSpace L.M := borel L.M
  letI : BorelSpace L.M := ⟨rfl⟩
  letI : TopologicalSpace (X.term (subseq (phi k))).M :=
    (X.term (subseq (phi k))).topology
  letI : ChartedSpace H (X.term (subseq (phi k))).M :=
    (X.term (subseq (phi k))).charted
  letI : T2Space (X.term (subseq (phi k))).M := (X.term (subseq (phi k))).t2
  letI : IsManifold I ∞ (X.term (subseq (phi k))).M :=
    (X.term (subseq (phi k))).smooth
  letI : SigmaCompactSpace (X.term (subseq (phi k))).M :=
    (X.term (subseq (phi k))).sigmaCompact
  letI : RegularSpace (X.term (subseq (phi k))).M := hTermRegular k
  letI : ConnectedSpace (X.term (subseq (phi k))).M := hTermConnected k
  letI : PseudoMetricSpace (X.term (subseq (phi k))).M :=
    lSegmentMetric (X.term (subseq (phi k))).S T
  letI : TopologicalSpace (X.term (subseq (phi k))).M :=
    (X.term (subseq (phi k))).topology
  letI : MeasurableSpace (X.term (subseq (phi k))).M :=
    borel (X.term (subseq (phi k))).M
  letI : BorelSpace (X.term (subseq (phi k))).M := ⟨rfl⟩
  intro K hK hKsrc B hcap
  let e : PartialDiffeomorph I I L.M (X.term (subseq (phi k))).M 1 :=
    { toPartialEquiv := (Phi.partialDiffeomorph (phi k)).toPartialEquiv
      open_source := (Phi.partialDiffeomorph (phi k)).open_source
      open_target := (Phi.partialDiffeomorph (phi k)).open_target
      contMDiffOn_toFun :=
        (Phi.partialDiffeomorph (phi k)).contMDiffOn_toFun.of_le (by norm_num)
      contMDiffOn_invFun :=
        (Phi.partialDiffeomorph (phi k)).contMDiffOn_invFun.of_le (by norm_num) }
  let mu := redDensityTermMeas Phi phi hTermRegular hTermConnected T tau x k
  change K ⊆ e.source at hKsrc
  change B ⊆ (e : L.M → (X.term (subseq (phi k))).M) '' K at hcap
  change Measure.map e.symm (mu.restrict e.target) Kᶜ ≤ mu Bᶜ
  exact map_inv_tail_le (I := I) e mu hK.measurableSet hKsrc hcap

/-- The reduced density on the fixed limit manifold, with its metric instances
installed internally so that local measurability hypotheses use a stable
function. -/
noncomputable def redDensityLimDens
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    (hLimRegular : letI : TopologicalSpace L.M := L.topology; RegularSpace L.M)
    (hLimConnected : letI : TopologicalSpace L.M := L.topology; ConnectedSpace L.M)
    (T tau : Real) (x : L.M) :
    letI : TopologicalSpace L.M := L.topology
    L.M → ENNReal := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : T2Space L.M := L.t2
  letI : IsManifold I ∞ L.M := L.smooth
  letI : SigmaCompactSpace L.M := L.sigmaCompact
  letI : RegularSpace L.M := hLimRegular
  letI : ConnectedSpace L.M := hLimConnected
  letI : PseudoMetricSpace L.M := lSegmentMetric L.S T
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : T2Space L.M := L.t2
  letI : IsManifold I ∞ L.M := L.smooth
  letI : SigmaCompactSpace L.M := L.sigmaCompact
  exact fun y ↦ ENNReal.ofReal (redDensity L.S T x y tau)

/-- The Riemannian volume measure used by the fixed limit reduced density. -/
noncomputable def redDensityLimVol
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    {subseq : Nat → Nat}
    {Phi : PointedCGHMaps (I := I) X (L.atTime 0) subseq}
    {R : letI : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
      letI : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
      letI : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
      SmoothRiemannianMetric I (L.atTime 0).M}
    {bf : BumpFamily (I := I) Phi} {hSrc : SrcSigma Phi} {hTgt : TgtSigma Phi}
    {beta psi : Real} (co : ConvOut (I := I) Phi R bf hSrc hTgt beta psi)
    (T tau : Real) :
    letI : TopologicalSpace L.M := L.topology
    letI : MeasurableSpace L.M := borel L.M
    Measure L.M := by
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
  letI : MeasurableSpace L.M := borel L.M
  letI : BorelSpace L.M := ⟨rfl⟩
  exact riemannianVolumeMeasure (I := I) (M := L.M) (co.gInf (T - tau))

/-- The reduced-density measure on the fixed limit manifold. -/
noncomputable def redDensityLimMeas
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    {subseq : Nat → Nat}
    {Phi : PointedCGHMaps (I := I) X (L.atTime 0) subseq}
    {R : letI : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
      letI : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
      letI : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
      SmoothRiemannianMetric I (L.atTime 0).M}
    {bf : BumpFamily (I := I) Phi} {hSrc : SrcSigma Phi} {hTgt : TgtSigma Phi}
    {beta psi : Real} (co : ConvOut (I := I) Phi R bf hSrc hTgt beta psi)
    (hLimRegular : letI : TopologicalSpace L.M := L.topology; RegularSpace L.M)
    (hLimConnected : letI : TopologicalSpace L.M := L.topology; ConnectedSpace L.M)
    (T tau : Real) (x : L.M) :
    letI : TopologicalSpace L.M := L.topology
    letI : MeasurableSpace L.M := borel L.M
    Measure L.M := by
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
  letI : MeasurableSpace L.M := borel L.M
  letI : BorelSpace L.M := ⟨rfl⟩
  exact (redDensityLimVol co T tau).withDensity
    (redDensityLimDens hLimRegular hLimConnected T tau x)

/-- The finite preferred-chart set meeting the support of a compact test. -/
noncomputable def ccChartSet
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
    (f : C_c(M, Real)) : Finset M := by
  let rho := chartAtlasPOU I M
  let S : Set M := {alpha | (tsupport (rho alpha) ∩ tsupport (f : M → Real)).Nonempty}
  exact (rho.locallyFinite.closure.finite_nonempty_inter_compact
    f.hasCompactSupport).toFinset

/-- The part of a compact test support assigned to one preferred chart. -/
noncomputable def ccCarrier
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
    (f : C_c(M, Real)) (alpha : M) : Set M :=
  tsupport ((chartAtlasPOU I M) alpha) ∩ tsupport (f : M → Real)

/-- The preferred-coordinate image of one compact-test chart carrier. -/
noncomputable def ccChartImage
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
    (f : C_c(M, Real)) (alpha : M) : Set E :=
  extChartAt I alpha '' ccCarrier (I := I) f alpha

/-- The positive compact-test weight in preferred coordinates. -/
noncomputable def ccPosWeight
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
    (f : C_c(M, Real)) (alpha : M) (z : E) : Real :=
  (chartAtlasPOU I M) alpha ((extChartAt I alpha).symm z) *
    (f.nnrealPart ((extChartAt I alpha).symm z) : Real)

/-- The negative compact-test weight in preferred coordinates. -/
noncomputable def ccNegWeight
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
    (f : C_c(M, Real)) (alpha : M) (z : E) : Real :=
  (chartAtlasPOU I M) alpha ((extChartAt I alpha).symm z) *
    ((-f).nnrealPart ((extChartAt I alpha).symm z) : Real)

omit [CompleteSpace E] [I.Boundaryless] in
private theorem ccCarrier_compact
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  (f : C_c(M, Real)) (alpha : M) :
    IsCompact (ccCarrier (I := I) f alpha) := by
  exact f.hasCompactSupport.of_isClosed_subset
    ((isClosed_tsupport _).inter (isClosed_tsupport _)) inter_subset_right

omit [CompleteSpace E] [I.Boundaryless] in
private theorem ccCarrier_source
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
    (f : C_c(M, Real)) (alpha : M) :
    ccCarrier (I := I) f alpha ⊆ (extChartAt I alpha).source := by
  intro y hy
  rw [extChartAt_source_eq_chartAt_source (I := I)]
  exact (chartAtlasPOU_isSubordinate I M alpha) hy.1

omit [CompleteSpace E] [I.Boundaryless] in
private theorem ccImage_compact
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
    (f : C_c(M, Real)) (alpha : M) :
    IsCompact (ccChartImage (I := I) f alpha) := by
  exact (ccCarrier_compact (I := I) f alpha).image_of_continuousOn
    ((continuousOn_extChartAt (I := I) alpha).mono
      (ccCarrier_source (I := I) f alpha))

omit [CompleteSpace E] in
private theorem ccImage_target
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
    (f : C_c(M, Real)) (alpha : M) :
    ccChartImage (I := I) f alpha ⊆ interior (extChartAt I alpha).target := by
  rw [(isOpen_extChartAt_target alpha).interior_eq]
  rintro z ⟨y, hy, rfl⟩
  exact (extChartAt I alpha).map_source (ccCarrier_source (I := I) f alpha hy)

omit [CompleteSpace E] [I.Boundaryless] in
private theorem ccComp_image
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
    {N : Type*} (q : M → N) (f : C_c(M, Real)) (alpha : M) :
    q '' ccCarrier (I := I) f alpha =
      (fun z ↦ q ((extChartAt I alpha).symm z)) ''
        ccChartImage (I := I) f alpha := by
  apply Set.Subset.antisymm
  · rintro y ⟨p, hp, rfl⟩
    refine ⟨extChartAt I alpha p, ⟨p, hp, rfl⟩, ?_⟩
    change q ((extChartAt I alpha).symm (extChartAt I alpha p)) = q p
    rw [(extChartAt I alpha).left_inv (ccCarrier_source (I := I) f alpha hp)]
  · rintro y ⟨z, ⟨p, hp, rfl⟩, rfl⟩
    refine ⟨p, hp, ?_⟩
    change q p = q ((extChartAt I alpha).symm (extChartAt I alpha p))
    rw [(extChartAt I alpha).left_inv (ccCarrier_source (I := I) f alpha hp)]

omit [I.Boundaryless] in
private theorem ccCarrier_src_ev
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    {subseq : Nat → Nat}
    (Phi : PointedCGHMaps (I := I) X (L.atTime 0) subseq)
    {R : letI : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
      letI : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
      letI : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
      SmoothRiemannianMetric I (L.atTime 0).M}
    {bf : BumpFamily (I := I) Phi} {hSrc : SrcSigma Phi} {hTgt : TgtSigma Phi}
    {beta psi : Real} (co : ConvOut (I := I) Phi R bf hSrc hTgt beta psi)
    (f : letI : TopologicalSpace L.M := L.topology; C_c(L.M, Real))
    (alpha : L.M) :
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : T2Space L.M := L.t2
    letI : IsManifold I ∞ L.M := L.smooth
    letI : SigmaCompactSpace L.M := L.sigmaCompact
    ∀ᶠ k in atTop,
      ccCarrier (I := I) f alpha ⊆ Phi.source (co.φ k) := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : T2Space L.M := L.t2
  letI : IsManifold I ∞ L.M := L.smooth
  letI : SigmaCompactSpace L.M := L.sigmaCompact
  obtain ⟨k0, hk0⟩ := Phi.source_subset (ccCarrier_compact (I := I) f alpha)
  filter_upwards [Filter.eventually_ge_atTop k0] with k hk
  exact hk0 (co.φ k) (hk.trans (co.hφ.id_le k))

private theorem ccImage_src_ev
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    {subseq : Nat → Nat}
    (Phi : PointedCGHMaps (I := I) X (L.atTime 0) subseq)
    {R : letI : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
      letI : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
      letI : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
      SmoothRiemannianMetric I (L.atTime 0).M}
    {bf : BumpFamily (I := I) Phi} {hSrc : SrcSigma Phi} {hTgt : TgtSigma Phi}
    {beta psi : Real} (co : ConvOut (I := I) Phi R bf hSrc hTgt beta psi)
    (f : letI : TopologicalSpace L.M := L.topology; C_c(L.M, Real))
    (alpha : L.M) :
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : T2Space L.M := L.t2
    letI : IsManifold I ∞ L.M := L.smooth
    letI : SigmaCompactSpace L.M := L.sigmaCompact
    ∀ᶠ k in atTop,
      letI : TopologicalSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).topology
      letI : ChartedSpace H (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).charted
      ccChartImage (I := I) f alpha ⊆
        (mapChartParam (J := I) Phi (co.φ k) alpha).source := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : T2Space L.M := L.t2
  letI : IsManifold I ∞ L.M := L.smooth
  letI : SigmaCompactSpace L.M := L.sigmaCompact
  filter_upwards [ccCarrier_src_ev Phi co f alpha] with k hk
  letI : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
  letI : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
  letI : T2Space (L.atTime 0).M := (L.atTime 0).t2
  letI : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
  letI : TopologicalSpace (X.term (subseq (co.φ k))).M :=
    (X.term (subseq (co.φ k))).topology
  letI : ChartedSpace H (X.term (subseq (co.φ k))).M :=
    (X.term (subseq (co.φ k))).charted
  rintro z ⟨p, hp, rfl⟩
  change extChartAt I alpha p ∈ (extChartAt I alpha).target ∩
    (extChartAt I alpha).symm ⁻¹' (Phi.partialDiffeomorph (co.φ k)).source
  refine ⟨(extChartAt I alpha).map_source
    (ccCarrier_source (I := I) f alpha hp), ?_⟩
  change (extChartAt I alpha).symm (extChartAt I alpha p) ∈
    (Phi.partialDiffeomorph (co.φ k)).source
  rw [(extChartAt I alpha).left_inv (ccCarrier_source (I := I) f alpha hp)]
  exact hk hp

omit [I.Boundaryless] in
private theorem ccChi_one_ev
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    {subseq : Nat → Nat}
    (Phi : PointedCGHMaps (I := I) X (L.atTime 0) subseq)
    {R : letI : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
      letI : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
      letI : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
      SmoothRiemannianMetric I (L.atTime 0).M}
    {bf : BumpFamily (I := I) Phi} {hSrc : SrcSigma Phi} {hTgt : TgtSigma Phi}
    {beta psi : Real} (co : ConvOut (I := I) Phi R bf hSrc hTgt beta psi)
    (f : letI : TopologicalSpace L.M := L.topology; C_c(L.M, Real))
    (alpha : L.M) :
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : T2Space L.M := L.t2
    letI : IsManifold I ∞ L.M := L.smooth
    letI : SigmaCompactSpace L.M := L.sigmaCompact
    ∀ᶠ k in atTop, ∀ z, z ∈ ccChartImage (I := I) f alpha →
      bf.chi (co.φ k) ((extChartAt I alpha).symm z) = 1 := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : T2Space L.M := L.t2
  letI : IsManifold I ∞ L.M := L.smooth
  letI : SigmaCompactSpace L.M := L.sigmaCompact
  let K := ccCarrier (I := I) f alpha
  have hK : IsCompact K := ccCarrier_compact (I := I) f alpha
  have hGrow : ∃ k0, ∀ k, k0 ≤ k → K ⊆ bf.grow k := by
    letI : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
    letI : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
    letI : T2Space (L.atTime 0).M := (L.atTime 0).t2
    letI : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
    exact bf.grow_cover K hK
  obtain ⟨k0, hk0⟩ := hGrow
  filter_upwards [Filter.eventually_ge_atTop k0] with k hk
  rintro z ⟨p, hp, rfl⟩
  have hpGrow : p ∈ bf.grow (co.φ k) :=
    hk0 (co.φ k) (hk.trans (co.hφ.id_le k)) hp
  obtain ⟨W, _hWopen, hGrowW, hOne⟩ : ∃ W : Set L.M,
      IsOpen W ∧ bf.grow (co.φ k) ⊆ W ∧ ∀ x ∈ W, bf.chi (co.φ k) x = 1 := by
    letI : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
    letI : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
    letI : T2Space (L.atTime 0).M := (L.atTime 0).t2
    letI : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
    exact bf.chi_one (co.φ k)
  rw [(extChartAt I alpha).left_inv (ccCarrier_source (I := I) f alpha hp)]
  exact hOne p (hGrowW hpGrow)

omit [CompleteSpace E] [I.Boundaryless] in
private theorem ccPouSum
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
    (f : C_c(M, Real)) (y : M) :
    ∑ alpha ∈ ccChartSet (I := I) f,
        (chartAtlasPOU I M) alpha y * f y = f y := by
  classical
  let rho := chartAtlasPOU I M
  let K := tsupport (f : M → Real)
  let S : Set M := {alpha | (tsupport (rho alpha) ∩ K).Nonempty}
  have hSfin : S.Finite :=
    rho.locallyFinite.closure.finite_nonempty_inter_compact f.hasCompactSupport
  by_cases hy : y ∈ K
  · have hfins : rho.finsupport y ⊆ hSfin.toFinset := by
      intro alpha halpha
      rw [hSfin.mem_toFinset]
      rw [rho.mem_finsupport] at halpha
      exact ⟨y, subset_tsupport _ halpha, hy⟩
    have hone : ∑ alpha ∈ hSfin.toFinset, rho alpha y = 1 :=
      rho.sum_finsupport' y (Set.mem_univ y) hfins
    change (∑ alpha ∈ hSfin.toFinset, rho alpha y * f y) = f y
    rw [← Finset.sum_mul, hone, one_mul]
  · have hfy : f y = 0 := by
      by_contra hne
      exact hy (subset_tsupport _ hne)
    simp only [hfy, mul_zero, Finset.sum_const_zero]

omit [CompleteSpace E] [I.Boundaryless] in
private theorem ccPouSum_of
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
    (f g : C_c(M, Real)) (hg : tsupport (g : M → Real) ⊆
      tsupport (f : M → Real)) (y : M) :
    ∑ alpha ∈ ccChartSet (I := I) f,
        (chartAtlasPOU I M) alpha y * g y = g y := by
  classical
  let rho := chartAtlasPOU I M
  let K := tsupport (f : M → Real)
  let S : Set M := {alpha | (tsupport (rho alpha) ∩ K).Nonempty}
  have hSfin : S.Finite :=
    rho.locallyFinite.closure.finite_nonempty_inter_compact f.hasCompactSupport
  by_cases hy : y ∈ tsupport (g : M → Real)
  · have hfins : rho.finsupport y ⊆ hSfin.toFinset := by
      intro alpha halpha
      rw [hSfin.mem_toFinset]
      rw [rho.mem_finsupport] at halpha
      exact ⟨y, subset_tsupport _ halpha, hg hy⟩
    have hone : ∑ alpha ∈ hSfin.toFinset, rho alpha y = 1 :=
      rho.sum_finsupport' y (Set.mem_univ y) hfins
    change (∑ alpha ∈ hSfin.toFinset, rho alpha y * g y) = g y
    rw [← Finset.sum_mul, hone, one_mul]
  · have hgy : g y = 0 := by
      by_contra hne
      exact hy (subset_tsupport _ hne)
    simp only [hgy, mul_zero, Finset.sum_const_zero]

omit [CompleteSpace E] [I.Boundaryless] in
private theorem ccPos_map_lint
    {M N : Type u} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
    [MeasurableSpace M] [BorelSpace M]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold I 1 N]
    [T2Space N] [MeasurableSpace N] [OpensMeasurableSpace N]
    (e : PartialDiffeomorph I I M N 1) (mu : Measure N)
    (f g : C_c(M, Real)) (hg0 : 0 ≤ g)
    (hgSupp : tsupport (g : M → Real) ⊆ tsupport (f : M → Real))
    (hSrc : ∀ alpha ∈ ccChartSet (I := I) f,
      ccCarrier (I := I) f alpha ⊆ e.source) :
    ∫⁻ y, ENNReal.ofReal (g y)
        ∂Measure.map e.symm (mu.restrict e.target) =
      ∑ alpha ∈ ccChartSet (I := I) f,
        ∫⁻ y in e '' ccCarrier (I := I) f alpha,
          ENNReal.ofReal ((chartAtlasPOU I M) alpha (e.symm y) * g (e.symm y)) ∂mu := by
  classical
  apply lint_map_fin_loc e mu (ccChartSet (I := I) f)
    (fun y ↦ ENNReal.ofReal (g y))
    (fun alpha y ↦ ENNReal.ofReal ((chartAtlasPOU I M) alpha y * g y))
    (fun alpha ↦ ccCarrier (I := I) f alpha)
  · exact ENNReal.measurable_ofReal.comp g.continuous.measurable
  · intro alpha _
    exact ENNReal.measurable_ofReal.comp
      ((chartAtlasPOU I M alpha).contMDiff.continuous.measurable.mul
        g.continuous.measurable)
  · intro y
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · rw [ccPouSum_of (I := I) f g hgSupp y]
    · intro alpha _
      exact mul_nonneg ((chartAtlasPOU I M).nonneg alpha y) (hg0 y)
  · exact hSrc
  · intro alpha _ y hy
    have hprod : (chartAtlasPOU I M) alpha y * g y ≠ 0 := by
      intro hzero
      exact hy (by simp only [hzero, ENNReal.ofReal_zero])
    have hrho : (chartAtlasPOU I M) alpha y ≠ 0 := left_ne_zero_of_mul hprod
    have hgy : g y ≠ 0 := right_ne_zero_of_mul hprod
    exact ⟨subset_tsupport _ hrho, hgSupp (subset_tsupport _ hgy)⟩
  · intro alpha ha
    exact ((ccCarrier_compact (I := I) f alpha).image_of_continuousOn
      (e.contMDiffOn_toFun.continuousOn.mono (hSrc alpha ha))).measurableSet

omit [CompleteSpace E] [I.Boundaryless] in
private theorem ccPos_lint
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
    [MeasurableSpace M] [BorelSpace M]
    (mu : Measure M) (f g : C_c(M, Real)) (hg0 : 0 ≤ g)
    (hgSupp : tsupport (g : M → Real) ⊆ tsupport (f : M → Real)) :
    ∫⁻ y, ENNReal.ofReal (g y) ∂mu =
      ∑ alpha ∈ ccChartSet (I := I) f,
        ∫⁻ y in ccCarrier (I := I) f alpha,
          ENNReal.ofReal ((chartAtlasPOU I M) alpha y * g y) ∂mu := by
  classical
  let G : M → M → ENNReal := fun alpha y ↦
    ENNReal.ofReal ((chartAtlasPOU I M) alpha y * g y)
  have hG : ∀ alpha, Measurable (G alpha) := by
    intro alpha
    exact ENNReal.measurable_ofReal.comp
      ((chartAtlasPOU I M alpha).contMDiff.continuous.measurable.mul
        g.continuous.measurable)
  calc
    ∫⁻ y, ENNReal.ofReal (g y) ∂mu =
        ∫⁻ y, ∑ alpha ∈ ccChartSet (I := I) f, G alpha y ∂mu := by
      apply MeasureTheory.lintegral_congr
      intro y
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · rw [ccPouSum_of (I := I) f g hgSupp y]
      · intro alpha _
        exact mul_nonneg ((chartAtlasPOU I M).nonneg alpha y) (hg0 y)
    _ = ∑ alpha ∈ ccChartSet (I := I) f, ∫⁻ y, G alpha y ∂mu := by
      rw [MeasureTheory.lintegral_finset_sum']
      intro alpha _
      exact (hG alpha).aemeasurable
    _ = ∑ alpha ∈ ccChartSet (I := I) f,
        ∫⁻ y in ccCarrier (I := I) f alpha, G alpha y ∂mu := by
      apply Finset.sum_congr rfl
      intro alpha _
      have hK : MeasurableSet (ccCarrier (I := I) f alpha) :=
        (ccCarrier_compact (I := I) f alpha).measurableSet
      rw [← MeasureTheory.lintegral_indicator hK]
      apply MeasureTheory.lintegral_congr
      intro y
      by_cases hy : y ∈ ccCarrier (I := I) f alpha
      · rw [Set.indicator_of_mem hy]
      · rw [Set.indicator_of_notMem hy]
        have hzero : G alpha y = 0 := by
          by_contra hne
          have hprod : (chartAtlasPOU I M) alpha y * g y ≠ 0 := by
            intro hz
            exact hne (by simp only [G, hz, ENNReal.ofReal_zero])
          have hrho : y ∈ tsupport ((chartAtlasPOU I M) alpha) :=
            subset_tsupport _ (left_ne_zero_of_mul hprod)
          have hgy : y ∈ tsupport (f : M → Real) :=
            hgSupp (subset_tsupport _ (right_ne_zero_of_mul hprod))
          exact hy ⟨hrho, hgy⟩
        exact hzero

omit [FiniteDimensional Real E] [CompleteSpace E] [I.Boundaryless] in
private theorem lint_wdens_mul
    {M : Type*} [MeasurableSpace M] (mu : Measure M)
    (dens h : M → ENNReal) {s : Set M}
    (hs : MeasurableSet s)
    (hDens : AEMeasurable dens (mu.restrict s))
    (hTop : ∀ᵐ y ∂mu.restrict s, dens y < ⊤) :
    ∫⁻ y in s, h y ∂mu.withDensity dens =
      ∫⁻ y in s, h y * dens y ∂mu := by
  rw [MeasureTheory.setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀
    mu hDens h hs hTop]
  apply MeasureTheory.setLIntegral_congr_fun hs
  intro y _
  ac_rfl

omit [FiniteDimensional Real E] [CompleteSpace E] [I.Boundaryless] in
private theorem ccPos_support
    {M : Type*} [TopologicalSpace M] (f : C_c(M, Real)) :
    tsupport (f.nnrealPart.toReal : M → Real) ⊆ tsupport (f : M → Real) := by
  apply closure_mono
  intro y hy
  simp only [Function.mem_support] at hy ⊢
  intro hfy
  apply hy
  simp only [CompactlySupportedContinuousMap.toReal_apply,
    CompactlySupportedContinuousMap.nnrealPart_apply, hfy,
    Real.toNNReal_zero, NNReal.coe_zero]

omit [FiniteDimensional Real E] [CompleteSpace E] [I.Boundaryless] in
private theorem ccNeg_support
    {M : Type*} [TopologicalSpace M] (f : C_c(M, Real)) :
    tsupport ((-f).nnrealPart.toReal : M → Real) ⊆ tsupport (f : M → Real) := by
  apply closure_mono
  intro y hy
  simp only [Function.mem_support] at hy ⊢
  intro hfy
  apply hy
  simp only [CompactlySupportedContinuousMap.toReal_apply,
    CompactlySupportedContinuousMap.nnrealPart_apply,
    CompactlySupportedContinuousMap.neg_apply, hfy, neg_zero,
    Real.toNNReal_zero, NNReal.coe_zero]

omit [FiniteDimensional Real E] [CompleteSpace E] [I.Boundaryless] in
private theorem partialInv_ae
    {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [MeasurableSpace M] [BorelSpace M]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold I 1 N]
    [MeasurableSpace N]
    [OpensMeasurableSpace N]
    (Psi : PartialDiffeomorph I I M N 1) (mu : Measure N) :
    AEMeasurable Psi.symm (mu.restrict Psi.target) :=
  Psi.contMDiffOn_invFun.continuousOn.aemeasurable Psi.open_target.measurableSet

omit [FiniteDimensional Real E] [CompleteSpace E] [I.Boundaryless] in
private theorem partialInv_lint
    {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [MeasurableSpace M] [BorelSpace M]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold I 1 N]
    [MeasurableSpace N] [OpensMeasurableSpace N]
    (Psi : PartialDiffeomorph I I M N 1) (mu : Measure N)
    (F : M → ENNReal)
    (hF : AEMeasurable F (Measure.map Psi.symm (mu.restrict Psi.target))) :
    ∫⁻ x, F x ∂Measure.map Psi.symm (mu.restrict Psi.target) =
      ∫⁻ y in Psi.target, F (Psi.symm y) ∂mu := by
  rw [MeasureTheory.lintegral_map' hF (partialInv_ae (I := I) Psi mu)]

omit [FiniteDimensional Real E] [CompleteSpace E] [I.Boundaryless] in
private theorem integral_eq_cc_parts
    {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
    [OpensMeasurableSpace M]
    (mu : Measure M) (f : C_c(M, Real)) (p n : ENNReal)
    (hPos : ∫⁻ y, ENNReal.ofReal (f.nnrealPart.toReal y) ∂mu = p)
    (hNeg : ∫⁻ y, ENNReal.ofReal ((-f).nnrealPart.toReal y) ∂mu = n)
    (hp : p ≠ ⊤) (hn : n ≠ ⊤) :
    ∫ y, f y ∂mu = p.toReal - n.toReal := by
  have hPosMeas : AEStronglyMeasurable
      (fun y ↦ f.nnrealPart.toReal y) mu :=
    f.nnrealPart.toReal.continuous.aestronglyMeasurable
  have hNegMeas : AEStronglyMeasurable
      (fun y ↦ (-f).nnrealPart.toReal y) mu :=
    (-f).nnrealPart.toReal.continuous.aestronglyMeasurable
  have hPosInt : Integrable (fun y ↦ f.nnrealPart.toReal y) mu :=
    (lintegral_ofReal_ne_top_iff_integrable hPosMeas
      (Eventually.of_forall fun y ↦ by simp)).mp (hPos.trans_ne hp)
  have hNegInt : Integrable (fun y ↦ (-f).nnrealPart.toReal y) mu :=
    (lintegral_ofReal_ne_top_iff_integrable hNegMeas
      (Eventually.of_forall fun y ↦ by simp)).mp (hNeg.trans_ne hn)
  rw [← CompactlySupportedContinuousMap.nnrealPart_sub_nnrealPart_neg f]
  change ∫ y, (f.nnrealPart.toReal y - (-f).nnrealPart.toReal y) ∂mu = _
  rw [integral_sub hPosInt hNegInt]
  rw [integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun y ↦ by simp) hPosMeas,
    integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun y ↦ by simp) hNegMeas,
    hPos, hNeg]

omit [FiniteDimensional Real E] [CompleteSpace E] [I.Boundaryless] in
private theorem ccSeq_split
    {M A : Type*} [TopologicalSpace M] [MeasurableSpace M]
    [OpensMeasurableSpace M]
    (mu : Nat → Measure M) (f : C_c(M, Real)) (s : Finset A)
    (p n : A → Nat → ENNReal)
    (hPos : ∀ᶠ k in atTop,
      ∫⁻ y, ENNReal.ofReal (f.nnrealPart.toReal y) ∂mu k = ∑ a ∈ s, p a k)
    (hNeg : ∀ᶠ k in atTop,
      ∫⁻ y, ENNReal.ofReal ((-f).nnrealPart.toReal y) ∂mu k = ∑ a ∈ s, n a k)
    (hp : ∀ a ∈ s, ∀ᶠ k in atTop, p a k ≠ ⊤)
    (hn : ∀ a ∈ s, ∀ᶠ k in atTop, n a k ≠ ⊤) :
    ∀ᶠ k in atTop, ∫ y, f y ∂mu k =
      (∑ a ∈ s, (p a k).toReal) - ∑ a ∈ s, (n a k).toReal := by
  classical
  have hpAll : ∀ᶠ k in atTop, ∀ a ∈ s, p a k ≠ ⊤ :=
    (Finset.eventually_all s).2 hp
  have hnAll : ∀ᶠ k in atTop, ∀ a ∈ s, n a k ≠ ⊤ :=
    (Finset.eventually_all s).2 hn
  filter_upwards [hPos, hNeg, hpAll, hnAll] with k hkPos hkNeg hkP hkN
  rw [integral_eq_cc_parts (mu k) f _ _ hkPos hkNeg
    (ENNReal.sum_ne_top.2 hkP) (ENNReal.sum_ne_top.2 hkN)]
  rw [ENNReal.toReal_sum hkP, ENNReal.toReal_sum hkN]

omit [FiniteDimensional Real E] [CompleteSpace E] [I.Boundaryless] in
private theorem ccLimit_split
    {M A : Type*} [TopologicalSpace M] [MeasurableSpace M]
    [OpensMeasurableSpace M]
    (mu : Measure M) (f : C_c(M, Real)) (s : Finset A)
    (p n : A → ENNReal)
    (hPos : ∫⁻ y, ENNReal.ofReal (f.nnrealPart.toReal y) ∂mu = ∑ a ∈ s, p a)
    (hNeg : ∫⁻ y, ENNReal.ofReal ((-f).nnrealPart.toReal y) ∂mu = ∑ a ∈ s, n a)
    (hp : ∀ a ∈ s, p a ≠ ⊤) (hn : ∀ a ∈ s, n a ≠ ⊤) :
    ∫ y, f y ∂mu = (∑ a ∈ s, (p a).toReal) - ∑ a ∈ s, (n a).toReal := by
  classical
  rw [integral_eq_cc_parts mu f _ _ hPos hNeg
    (ENNReal.sum_ne_top.2 hp) (ENNReal.sum_ne_top.2 hn)]
  rw [ENNReal.toReal_sum hp, ENNReal.toReal_sum hn]

private theorem ccSrc_pos
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    {subseq : Nat → Nat}
    (Phi : PointedCGHMaps (I := I) X (L.atTime 0) subseq)
    {R : letI : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
      letI : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
      letI : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
      SmoothRiemannianMetric I (L.atTime 0).M}
    {bf : BumpFamily (I := I) Phi} {hSrc : SrcSigma Phi} {hTgt : TgtSigma Phi}
    {beta psi : Real} (co : ConvOut (I := I) Phi R bf hSrc hTgt beta psi)
    (hTermRegular : ∀ k,
      letI : TopologicalSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).topology
      RegularSpace (X.term (subseq (co.φ k))).M)
    (hTermConnected : ∀ k,
      letI : TopologicalSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).topology
      ConnectedSpace (X.term (subseq (co.φ k))).M)
    (T tau : Real) (x : L.M)
    (f g : letI : TopologicalSpace L.M := L.topology; C_c(L.M, Real))
    (hg0 : 0 ≤ g)
    (hgSupp : letI : TopologicalSpace L.M := L.topology
      tsupport (g : L.M → Real) ⊆ tsupport (f : L.M → Real))
    (hDensMeas : letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : T2Space L.M := L.t2
      letI : IsManifold I ∞ L.M := L.smooth
      letI : SigmaCompactSpace L.M := L.sigmaCompact
      let K : L.M → Set L.M := fun alpha ↦ ccCarrier (I := I) f alpha
      letI : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
      letI : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
      letI : T2Space (L.atTime 0).M := (L.atTime 0).t2
      letI : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
      ∀ᶠ k in atTop,
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
        letI : PseudoMetricSpace (X.term (subseq (co.φ k))).M :=
          lSegmentMetric (X.term (subseq (co.φ k))).S T
        letI : TopologicalSpace (X.term (subseq (co.φ k))).M :=
          (X.term (subseq (co.φ k))).topology
        ∀ alpha ∈ ccChartSet (I := I) f,
          AEMeasurable
            (fun y ↦ ENNReal.ofReal (redDensity
              (X.term (subseq (co.φ k))).S T (Phi.map (co.φ k) x) y tau))
            ((riemannianVolumeMeasure (I := I)
                (M := (X.term (subseq (co.φ k))).M)
                ((X.term (subseq (co.φ k))).S.base.metric (T - tau))).restrict
              ((Phi.partialDiffeomorph (co.φ k)) ''
                K alpha))) :
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : T2Space L.M := L.t2
    letI : IsManifold I ∞ L.M := L.smooth
    letI : SigmaCompactSpace L.M := L.sigmaCompact
    letI : MeasurableSpace L.M := borel L.M
    ∀ᶠ k in atTop,
      ∫⁻ y, ENNReal.ofReal (g y)
          ∂redDensitySrcMeas Phi co.φ hTermRegular hTermConnected T tau x k =
        ∑ alpha ∈ ccChartSet (I := I) f,
          srcTest Phi co.φ hTermRegular hTermConnected T tau x alpha
            (ccChartImage (I := I) f alpha)
            (fun z ↦ (chartAtlasPOU I L.M) alpha ((extChartAt I alpha).symm z) *
              g ((extChartAt I alpha).symm z)) k := by
  classical
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : T2Space L.M := L.t2
  letI : IsManifold I ∞ L.M := L.smooth
  letI : SigmaCompactSpace L.M := L.sigmaCompact
  letI : MeasurableSpace L.M := borel L.M
  letI : BorelSpace L.M := ⟨rfl⟩
  have hSrcAll : ∀ᶠ k in atTop, ∀ alpha ∈ ccChartSet (I := I) f,
      ccCarrier (I := I) f alpha ⊆ Phi.source (co.φ k) :=
    (Finset.eventually_all (ccChartSet (I := I) f)).2 fun alpha _ ↦
      ccCarrier_src_ev Phi co f alpha
  filter_upwards [hSrcAll, hDensMeas] with k hk hkDens
  letI : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
  letI : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
  letI : T2Space (L.atTime 0).M := (L.atTime 0).t2
  letI : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
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
  letI : PseudoMetricSpace (X.term (subseq (co.φ k))).M :=
    lSegmentMetric (X.term (subseq (co.φ k))).S T
  letI : TopologicalSpace (X.term (subseq (co.φ k))).M :=
    (X.term (subseq (co.φ k))).topology
  letI : MeasurableSpace (X.term (subseq (co.φ k))).M :=
    borel (X.term (subseq (co.φ k))).M
  letI : BorelSpace (X.term (subseq (co.φ k))).M := ⟨rfl⟩
  let e : PartialDiffeomorph I I L.M (X.term (subseq (co.φ k))).M 1 :=
    { toPartialEquiv := (Phi.partialDiffeomorph (co.φ k)).toPartialEquiv
      open_source := (Phi.partialDiffeomorph (co.φ k)).open_source
      open_target := (Phi.partialDiffeomorph (co.φ k)).open_target
      contMDiffOn_toFun :=
        (Phi.partialDiffeomorph (co.φ k)).contMDiffOn_toFun.of_le (by norm_num)
      contMDiffOn_invFun :=
        (Phi.partialDiffeomorph (co.φ k)).contMDiffOn_invFun.of_le (by norm_num) }
  let vol := riemannianVolumeMeasure (I := I)
    (M := (X.term (subseq (co.φ k))).M)
    ((X.term (subseq (co.φ k))).S.base.metric (T - tau))
  let dens : (X.term (subseq (co.φ k))).M → ENNReal := fun y ↦
    ENNReal.ofReal (redDensity (X.term (subseq (co.φ k))).S T
      (Phi.map (co.φ k) x) y tau)
  have hRaw := ccPos_map_lint (I := I) (M := L.M)
    (N := (X.term (subseq (co.φ k))).M)
    e (vol.withDensity dens) f g hg0 hgSupp
    (fun alpha ha ↦ hk alpha ha)
  change (∫⁻ y, ENNReal.ofReal (g y)
      ∂Measure.map e.symm ((vol.withDensity dens).restrict e.target)) = _
  rw [hRaw]
  apply Finset.sum_congr rfl
  intro alpha ha
  have hSet : MeasurableSet (e '' ccCarrier (I := I) f alpha) :=
    ((ccCarrier_compact (I := I) f alpha).image_of_continuousOn
      (e.contMDiffOn_toFun.continuousOn.mono (hk alpha ha))).measurableSet
  rw [lint_wdens_mul vol dens _ hSet
    (hkDens alpha ha) (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  unfold srcTest
  rw [ccComp_image (I := I) e f alpha]
  change (∫⁻ y in (mapChartParam (J := I) Phi (co.φ k) alpha) ''
      ccChartImage (I := I) f alpha,
      ENNReal.ofReal ((chartAtlasPOU I L.M) alpha (e.symm y) * g (e.symm y)) *
        dens y ∂vol) = _
  have hSetMap : MeasurableSet
      ((mapChartParam (J := I) Phi (co.φ k) alpha) ''
        ccChartImage (I := I) f alpha) := by
    have hBsrc : ccChartImage (I := I) f alpha ⊆
        (mapChartParam (J := I) Phi (co.φ k) alpha).source := by
      rintro z ⟨p, hp, rfl⟩
      change extChartAt I alpha p ∈ (extChartAt I alpha).target ∩
        (extChartAt I alpha).symm ⁻¹' e.source
      refine ⟨(extChartAt I alpha).map_source
        (ccCarrier_source (I := I) f alpha hp), ?_⟩
      change (extChartAt I alpha).symm (extChartAt I alpha p) ∈ e.source
      rw [(extChartAt I alpha).left_inv (ccCarrier_source (I := I) f alpha hp)]
      exact hk alpha ha hp
    exact ((ccImage_compact (I := I) f alpha).image_of_continuousOn
      ((mapChartParam (J := I) Phi (co.φ k) alpha).contMDiffOn_toFun.continuousOn.mono
        hBsrc)).measurableSet
  apply MeasureTheory.setLIntegral_congr_fun hSetMap
  intro y hy
  obtain ⟨z, ⟨p, hp, rfl⟩, rfl⟩ := hy
  have hpSrc : p ∈ e.source := hk alpha ha hp
  have hforward : (mapChartParam (J := I) Phi (co.φ k) alpha)
      (extChartAt I alpha p) = e p := by
    change e ((extChartAt I alpha).symm (extChartAt I alpha p)) = e p
    rw [(extChartAt I alpha).left_inv (ccCarrier_source (I := I) f alpha hp)]
  have hzSrc : extChartAt I alpha p ∈
      (mapChartParam (J := I) Phi (co.φ k) alpha).source := by
    change extChartAt I alpha p ∈ (extChartAt I alpha).target ∩
      (extChartAt I alpha).symm ⁻¹' e.source
    refine ⟨(extChartAt I alpha).map_source
      (ccCarrier_source (I := I) f alpha hp), ?_⟩
    change (extChartAt I alpha).symm (extChartAt I alpha p) ∈ e.source
    rw [(extChartAt I alpha).left_inv (ccCarrier_source (I := I) f alpha hp)]
    exact hpSrc
  have hmap := (mapChartParam (J := I) Phi (co.φ k) alpha).left_inv hzSrc
  have hmap' : (mapChartParam (J := I) Phi (co.φ k) alpha).symm (e p) =
      extChartAt I alpha p := by
    rw [← hforward]
    exact hmap
  have heInv : e.symm.toPartialEquiv (e.toPartialEquiv p) = p :=
    e.toPartialEquiv.left_inv hpSrc
  have hChartInv : (extChartAt I alpha).symm (extChartAt I alpha p) = p :=
    (extChartAt I alpha).left_inv (ccCarrier_source (I := I) f alpha hp)
  rw [hforward]
  change ENNReal.ofReal ((chartAtlasPOU I L.M) alpha (e.symm (e p)) *
      g (e.symm (e p))) * dens (e p) =
    ENNReal.ofReal ((chartAtlasPOU I L.M) alpha
        ((extChartAt I alpha).symm
          ((mapChartParam (J := I) Phi (co.φ k) alpha).symm (e p))) *
      g ((extChartAt I alpha).symm
        ((mapChartParam (J := I) Phi (co.φ k) alpha).symm (e p))) ) * dens (e p)
  rw [heInv, hmap', hChartInv]

omit [I.Boundaryless] in
private theorem ccLim_pos
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    {subseq : Nat → Nat}
    {Phi : PointedCGHMaps (I := I) X (L.atTime 0) subseq}
    {R : letI : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
      letI : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
      letI : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
      SmoothRiemannianMetric I (L.atTime 0).M}
    {bf : BumpFamily (I := I) Phi} {hSrc : SrcSigma Phi} {hTgt : TgtSigma Phi}
    {beta psi : Real} (co : ConvOut (I := I) Phi R bf hSrc hTgt beta psi)
    (hLimRegular : letI : TopologicalSpace L.M := L.topology; RegularSpace L.M)
    (hLimConnected : letI : TopologicalSpace L.M := L.topology; ConnectedSpace L.M)
    (T tau : Real) (x : L.M)
    (f g : letI : TopologicalSpace L.M := L.topology; C_c(L.M, Real))
    (hg0 : 0 ≤ g)
    (hgSupp : letI : TopologicalSpace L.M := L.topology
      tsupport (g : L.M → Real) ⊆ tsupport (f : L.M → Real))
    (hDensMeas : letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : T2Space L.M := L.t2
      letI : IsManifold I ∞ L.M := L.smooth
      letI : SigmaCompactSpace L.M := L.sigmaCompact
      letI : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
      letI : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
      letI : T2Space (L.atTime 0).M := (L.atTime 0).t2
      letI : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
      letI : SigmaCompactSpace (L.atTime 0).M := (L.atTime 0).sigmaCompact
      ∀ alpha ∈ ccChartSet (I := I) f,
        AEMeasurable (redDensityLimDens hLimRegular hLimConnected T tau x)
          ((redDensityLimVol co T tau).restrict (ccCarrier (I := I) f alpha))) :
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : T2Space L.M := L.t2
    letI : IsManifold I ∞ L.M := L.smooth
    letI : SigmaCompactSpace L.M := L.sigmaCompact
    letI : MeasurableSpace L.M := borel L.M
    ∫⁻ y, ENNReal.ofReal (g y)
        ∂redDensityLimMeas co hLimRegular hLimConnected T tau x =
      ∑ alpha ∈ ccChartSet (I := I) f,
        limTest co hLimRegular hLimConnected T tau x alpha
          (ccChartImage (I := I) f alpha)
          (fun z ↦ (chartAtlasPOU I L.M) alpha ((extChartAt I alpha).symm z) *
            g ((extChartAt I alpha).symm z)) := by
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
  letI : ChartedSpace H L.M := L.charted
  letI : T2Space L.M := L.t2
  letI : IsManifold I ∞ L.M := L.smooth
  letI : SigmaCompactSpace L.M := L.sigmaCompact
  letI : MeasurableSpace L.M := borel L.M
  letI : BorelSpace L.M := ⟨rfl⟩
  let vol := redDensityLimVol co T tau
  let dens : L.M → ENNReal :=
    redDensityLimDens hLimRegular hLimConnected T tau x
  have hRaw := ccPos_lint (I := I) (vol.withDensity dens) f g hg0 hgSupp
  change (∫⁻ y, ENNReal.ofReal (g y) ∂vol.withDensity dens) = _
  rw [hRaw]
  apply Finset.sum_congr rfl
  intro alpha ha
  have hSet : MeasurableSet (ccCarrier (I := I) f alpha) :=
    (ccCarrier_compact (I := I) f alpha).measurableSet
  have hDensTop : ∀ᵐ y ∂vol.restrict (ccCarrier (I := I) f alpha), dens y < ⊤ :=
    Eventually.of_forall fun y ↦ by
      change ENNReal.ofReal (redDensity L.S T x y tau) < ⊤
      exact ENNReal.ofReal_lt_top
  rw [lint_wdens_mul vol dens _ hSet (hDensMeas alpha ha)
    hDensTop]
  unfold limTest
  have hCarrier : ccCarrier (I := I) f alpha =
      (extChartAt I alpha).symm '' ccChartImage (I := I) f alpha := by
    simpa only [image_id'] using
      (ccComp_image (I := I) (fun y : L.M ↦ y) f alpha)
  rw [hCarrier]
  change (∫⁻ y in (extChartAt I alpha).symm '' ccChartImage (I := I) f alpha,
      ENNReal.ofReal ((chartAtlasPOU I L.M) alpha y * g y) * dens y ∂vol) = _
  have hSetMap : MeasurableSet
      ((extChartAt I alpha).symm '' ccChartImage (I := I) f alpha) := by
    rw [← hCarrier]
    exact hSet
  apply MeasureTheory.setLIntegral_congr_fun hSetMap
  intro y hy
  obtain ⟨z, ⟨p, hp, rfl⟩, rfl⟩ := hy
  have hChartInv : (extChartAt I alpha).symm (extChartAt I alpha p) = p :=
    (extChartAt I alpha).left_inv (ccCarrier_source (I := I) f alpha hp)
  change ENNReal.ofReal ((chartAtlasPOU I L.M) alpha
      ((extChartAt I alpha).symm (extChartAt I alpha p)) *
        g ((extChartAt I alpha).symm (extChartAt I alpha p))) *
      dens ((extChartAt I alpha).symm (extChartAt I alpha p)) = _
  rw [hChartInv]
  change ENNReal.ofReal ((chartAtlasPOU I L.M) alpha p * g p) *
      ENNReal.ofReal (redDensity L.S T x p tau) = _
  dsimp only
  rw [hChartInv]

private theorem redDensity_cc_aux
    {A : Type uA}
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    {subseq : Nat → Nat}
    (Phi : PointedCGHMaps (I := I) X (L.atTime 0) subseq)
    (R : letI : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
      letI : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
      letI : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
      SmoothRiemannianMetric I (L.atTime 0).M)
    (bf : BumpFamily (I := I) Phi) (hSrc : SrcSigma Phi) (hTgt : TgtSigma Phi)
    (beta psi : Real) (co : ConvOut (I := I) Phi R bf hSrc hTgt beta psi)
    (hInf : letI : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
      letI : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
      letI : T2Space (L.atTime 0).M := (L.atTime 0).t2
      letI : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
      letI : SigmaCompactSpace (L.atTime 0).M := (L.atTime 0).sigmaCompact
      MetricFamilySmoothOn (I := I) (M := (L.atTime 0).M) X.D co.gInf)
    (hReg : Icc beta psi ⊆ X.D.regular)
    (T tau : Real) (x : L.M) (hTime : T - tau ∈ Icc beta psi)
    (hLimRegular : letI : TopologicalSpace L.M := L.topology; RegularSpace L.M)
    (hLimConnected : letI : TopologicalSpace L.M := L.topology; ConnectedSpace L.M)
    (hTermRegular : ∀ k,
      letI : TopologicalSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).topology
      RegularSpace (X.term (subseq (co.φ k))).M)
    (hTermConnected : ∀ k,
      letI : TopologicalSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).topology
      ConnectedSpace (X.term (subseq (co.φ k))).M)
    (f : letI : TopologicalSpace L.M := L.topology; C_c(L.M, Real))
    (muSeq : letI : TopologicalSpace L.M := L.topology
      letI : MeasurableSpace L.M := borel L.M
      Nat → Measure L.M)
    (muLim : letI : TopologicalSpace L.M := L.topology
      letI : MeasurableSpace L.M := borel L.M
      Measure L.M)
    (s : Finset A) (alpha : A → L.M) (B : A → Set E)
    (wPos wNeg : A → E → Real)
    (CPos CNeg CRed : A → NNReal)
    (hBChart : ∀ a ∈ s,
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      B a ⊆ interior (extChartAt I (alpha a)).target)
    (hBc : ∀ a ∈ s, IsCompact (B a))
    (hBSrc : ∀ a ∈ s,
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      ∀ᶠ k in atTop,
        letI : TopologicalSpace (X.term (subseq (co.φ k))).M :=
          (X.term (subseq (co.φ k))).topology
        letI : ChartedSpace H (X.term (subseq (co.φ k))).M :=
          (X.term (subseq (co.φ k))).charted
        B a ⊆ (mapChartParam (J := I) Phi (co.φ k) (alpha a)).source)
    (hOne : ∀ a ∈ s,
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      ∀ᶠ k in atTop, ∀ z, z ∈ B a →
        bf.chi (co.φ k) ((extChartAt I (alpha a)).symm z) = 1)
    (hPosMeas : ∀ a ∈ s, AEMeasurable (fun z ↦ ENNReal.ofReal (wPos a z))
      ((modelHaar (E := E)).restrict (B a)))
    (hNegMeas : ∀ a ∈ s, AEMeasurable (fun z ↦ ENNReal.ofReal (wNeg a z))
      ((modelHaar (E := E)).restrict (B a)))
    (hPosBd : ∀ a ∈ s, ∀ᵐ z ∂((modelHaar (E := E)).restrict (B a)),
      ENNReal.ofReal (wPos a z) ≤ (CPos a : ENNReal))
    (hNegBd : ∀ a ∈ s, ∀ᵐ z ∂((modelHaar (E := E)).restrict (B a)),
      ENNReal.ofReal (wNeg a z) ≤ (CNeg a : ENNReal))
    (hRedMeas : ∀ a ∈ s,
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : T2Space L.M := L.t2
      letI : IsManifold I ∞ L.M := L.smooth
      letI : SigmaCompactSpace L.M := L.sigmaCompact
      ∀ᶠ k in atTop, AEMeasurable
        (fun z : E ↦
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
          letI : PseudoMetricSpace (X.term (subseq (co.φ k))).M :=
            lSegmentMetric (X.term (subseq (co.φ k))).S T
          letI : TopologicalSpace (X.term (subseq (co.φ k))).M :=
            (X.term (subseq (co.φ k))).topology
          ENNReal.ofReal (redDensity (X.term (subseq (co.φ k))).S T
            (Phi.map (co.φ k) x)
            (Phi.map (co.φ k) ((extChartAt I (alpha a)).symm z)) tau))
        ((modelHaar (E := E)).restrict (B a)))
    (hRedLim : ∀ a ∈ s,
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : T2Space L.M := L.t2
      letI : IsManifold I ∞ L.M := L.smooth
      letI : SigmaCompactSpace L.M := L.sigmaCompact
      letI : RegularSpace L.M := hLimRegular
      letI : ConnectedSpace L.M := hLimConnected
      letI : PseudoMetricSpace L.M := lSegmentMetric L.S T
      letI : TopologicalSpace L.M := L.topology
      ∀ z ∈ B a, Tendsto
        (fun k ↦
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
          letI : PseudoMetricSpace (X.term (subseq (co.φ k))).M :=
            lSegmentMetric (X.term (subseq (co.φ k))).S T
          letI : TopologicalSpace (X.term (subseq (co.φ k))).M :=
            (X.term (subseq (co.φ k))).topology
          redDensity (X.term (subseq (co.φ k))).S T (Phi.map (co.φ k) x)
            (Phi.map (co.φ k) ((extChartAt I (alpha a)).symm z)) tau)
        atTop (nhds (redDensity L.S T x ((extChartAt I (alpha a)).symm z) tau)))
    (hRedBd : ∀ a ∈ s,
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      ∀ᶠ k in atTop, ∀ᵐ z ∂((modelHaar (E := E)).restrict (B a)),
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
        letI : PseudoMetricSpace (X.term (subseq (co.φ k))).M :=
          lSegmentMetric (X.term (subseq (co.φ k))).S T
        letI : TopologicalSpace (X.term (subseq (co.φ k))).M :=
          (X.term (subseq (co.φ k))).topology
        ENNReal.ofReal (redDensity (X.term (subseq (co.φ k))).S T
          (Phi.map (co.φ k) x)
          (Phi.map (co.φ k) ((extChartAt I (alpha a)).symm z)) tau) ≤
            (CRed a : ENNReal))
    (hPosFin : ∀ a ∈ s,
      limTest co hLimRegular hLimConnected T tau x (alpha a) (B a) (wPos a) ≠ ⊤)
    (hNegFin : ∀ a ∈ s,
      limTest co hLimRegular hLimConnected T tau x (alpha a) (B a) (wNeg a) ≠ ⊤)
    (hSeqSplit : ∀ᶠ k in atTop,
      letI : TopologicalSpace L.M := L.topology
      letI : MeasurableSpace L.M := borel L.M
      ∫ y, f y ∂muSeq k =
        (∑ a ∈ s, (srcTest Phi co.φ hTermRegular hTermConnected T tau x
          (alpha a) (B a) (wPos a) k).toReal) -
        ∑ a ∈ s, (srcTest Phi co.φ hTermRegular hTermConnected T tau x
          (alpha a) (B a) (wNeg a) k).toReal)
    (hLimSplit :
      letI : TopologicalSpace L.M := L.topology
      letI : MeasurableSpace L.M := borel L.M
      ∫ y, f y ∂muLim =
        (∑ a ∈ s, (limTest co hLimRegular hLimConnected T tau x
          (alpha a) (B a) (wPos a)).toReal) -
        ∑ a ∈ s, (limTest co hLimRegular hLimConnected T tau x
          (alpha a) (B a) (wNeg a)).toReal) :
    letI : TopologicalSpace L.M := L.topology
    letI : MeasurableSpace L.M := borel L.M
    Tendsto (fun k ↦ ∫ y, f y ∂muSeq k) atTop (nhds (∫ y, f y ∂muLim)) := by
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
  letI : MeasurableSpace L.M := borel L.M
  have hPos : ∀ a ∈ s, Tendsto
      (fun k ↦ (srcTest Phi co.φ hTermRegular hTermConnected T tau x
        (alpha a) (B a) (wPos a) k).toReal) atTop
      (nhds ((limTest co hLimRegular hLimConnected T tau x
        (alpha a) (B a) (wPos a)).toReal)) := by
    intro a ha
    apply (ENNReal.tendsto_toReal (hPosFin a ha)).comp
    simpa only [srcTest, limTest] using
      redDensity_src_wgt Phi R bf hSrc hTgt beta psi co hInf hReg T tau x
        (alpha a) hTime (hBChart a ha) (hBc a ha) (hBSrc a ha) (hOne a ha)
        hLimRegular hLimConnected hTermRegular hTermConnected (wPos a)
        (hPosMeas a ha) (CPos a) (hPosBd a ha) (hRedMeas a ha)
        (hRedLim a ha) (CRed a) (hRedBd a ha)
  have hNeg : ∀ a ∈ s, Tendsto
      (fun k ↦ (srcTest Phi co.φ hTermRegular hTermConnected T tau x
        (alpha a) (B a) (wNeg a) k).toReal) atTop
      (nhds ((limTest co hLimRegular hLimConnected T tau x
        (alpha a) (B a) (wNeg a)).toReal)) := by
    intro a ha
    apply (ENNReal.tendsto_toReal (hNegFin a ha)).comp
    simpa only [srcTest, limTest] using
      redDensity_src_wgt Phi R bf hSrc hTgt beta psi co hInf hReg T tau x
        (alpha a) hTime (hBChart a ha) (hBc a ha) (hBSrc a ha) (hOne a ha)
        hLimRegular hLimConnected hTermRegular hTermConnected (wNeg a)
        (hNegMeas a ha) (CNeg a) (hNegBd a ha) (hRedMeas a ha)
        (hRedLim a ha) (CRed a) (hRedBd a ha)
  rw [hLimSplit]
  apply Tendsto.congr' (hSeqSplit.mono fun k hk ↦ hk.symm)
  exact (tendsto_finset_sum s hPos).sub (tendsto_finset_sum s hNeg)

/-- Raw transported reduced-density measures converge against every compactly
supported real test once the canonical preferred-chart local estimates hold. -/
theorem redDensity_cc_lim
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    {subseq : Nat → Nat}
    (Phi : PointedCGHMaps (I := I) X (L.atTime 0) subseq)
    (R : letI : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
      letI : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
      letI : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
      SmoothRiemannianMetric I (L.atTime 0).M)
    (bf : BumpFamily (I := I) Phi) (hSrc : SrcSigma Phi) (hTgt : TgtSigma Phi)
    (beta psi : Real) (co : ConvOut (I := I) Phi R bf hSrc hTgt beta psi)
    (hInf : letI : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
      letI : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
      letI : T2Space (L.atTime 0).M := (L.atTime 0).t2
      letI : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
      letI : SigmaCompactSpace (L.atTime 0).M := (L.atTime 0).sigmaCompact
      MetricFamilySmoothOn (I := I) (M := (L.atTime 0).M) X.D co.gInf)
    (hReg : Icc beta psi ⊆ X.D.regular)
    (T tau : Real) (x : L.M) (hTime : T - tau ∈ Icc beta psi)
    (hLimRegular : letI : TopologicalSpace L.M := L.topology; RegularSpace L.M)
    (hLimConnected : letI : TopologicalSpace L.M := L.topology; ConnectedSpace L.M)
    (hTermRegular : ∀ k,
      letI : TopologicalSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).topology
      RegularSpace (X.term (subseq (co.φ k))).M)
    (hTermConnected : ∀ k,
      letI : TopologicalSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).topology
      ConnectedSpace (X.term (subseq (co.φ k))).M)
    (f : letI : TopologicalSpace L.M := L.topology; C_c(L.M, Real))
    (hSrcDensMeas : letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : T2Space L.M := L.t2
      letI : IsManifold I ∞ L.M := L.smooth
      letI : SigmaCompactSpace L.M := L.sigmaCompact
      let K : L.M → Set L.M := fun a ↦ ccCarrier (I := I) f a
      letI : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
      letI : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
      letI : T2Space (L.atTime 0).M := (L.atTime 0).t2
      letI : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
      ∀ᶠ k in atTop,
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
        letI : PseudoMetricSpace (X.term (subseq (co.φ k))).M :=
          lSegmentMetric (X.term (subseq (co.φ k))).S T
        letI : TopologicalSpace (X.term (subseq (co.φ k))).M :=
          (X.term (subseq (co.φ k))).topology
        ∀ a ∈ ccChartSet (I := I) f,
          AEMeasurable
            (fun y ↦ ENNReal.ofReal (redDensity
              (X.term (subseq (co.φ k))).S T (Phi.map (co.φ k) x) y tau))
            ((riemannianVolumeMeasure (I := I)
                (M := (X.term (subseq (co.φ k))).M)
                ((X.term (subseq (co.φ k))).S.base.metric (T - tau))).restrict
              ((Phi.partialDiffeomorph (co.φ k)) '' K a)))
    (hLimDensMeas : letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : T2Space L.M := L.t2
      letI : IsManifold I ∞ L.M := L.smooth
      letI : SigmaCompactSpace L.M := L.sigmaCompact
      letI : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
      letI : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
      letI : T2Space (L.atTime 0).M := (L.atTime 0).t2
      letI : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
      letI : SigmaCompactSpace (L.atTime 0).M := (L.atTime 0).sigmaCompact
      ∀ a ∈ ccChartSet (I := I) f,
        AEMeasurable (redDensityLimDens hLimRegular hLimConnected T tau x)
          ((redDensityLimVol co T tau).restrict (ccCarrier (I := I) f a)))
    (CPos CNeg CRed : L.M → NNReal)
    (hPosMeas : letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : T2Space L.M := L.t2
      letI : IsManifold I ∞ L.M := L.smooth
      letI : SigmaCompactSpace L.M := L.sigmaCompact
      ∀ a ∈ ccChartSet (I := I) f,
      AEMeasurable (fun z ↦ ENNReal.ofReal (ccPosWeight (I := I) f a z))
        ((modelHaar (E := E)).restrict (ccChartImage (I := I) f a)))
    (hNegMeas : letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : T2Space L.M := L.t2
      letI : IsManifold I ∞ L.M := L.smooth
      letI : SigmaCompactSpace L.M := L.sigmaCompact
      ∀ a ∈ ccChartSet (I := I) f,
      AEMeasurable (fun z ↦ ENNReal.ofReal (ccNegWeight (I := I) f a z))
        ((modelHaar (E := E)).restrict (ccChartImage (I := I) f a)))
    (hPosBd : letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : T2Space L.M := L.t2
      letI : IsManifold I ∞ L.M := L.smooth
      letI : SigmaCompactSpace L.M := L.sigmaCompact
      ∀ a ∈ ccChartSet (I := I) f,
      ∀ᵐ z ∂((modelHaar (E := E)).restrict (ccChartImage (I := I) f a)),
        ENNReal.ofReal (ccPosWeight (I := I) f a z) ≤ (CPos a : ENNReal))
    (hNegBd : letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : T2Space L.M := L.t2
      letI : IsManifold I ∞ L.M := L.smooth
      letI : SigmaCompactSpace L.M := L.sigmaCompact
      ∀ a ∈ ccChartSet (I := I) f,
      ∀ᵐ z ∂((modelHaar (E := E)).restrict (ccChartImage (I := I) f a)),
        ENNReal.ofReal (ccNegWeight (I := I) f a z) ≤ (CNeg a : ENNReal))
    (hRedMeas : letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : T2Space L.M := L.t2
      letI : IsManifold I ∞ L.M := L.smooth
      letI : SigmaCompactSpace L.M := L.sigmaCompact
      ∀ a ∈ ccChartSet (I := I) f,
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : T2Space L.M := L.t2
      letI : IsManifold I ∞ L.M := L.smooth
      letI : SigmaCompactSpace L.M := L.sigmaCompact
      ∀ᶠ k in atTop, AEMeasurable
        (fun z : E ↦
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
          letI : PseudoMetricSpace (X.term (subseq (co.φ k))).M :=
            lSegmentMetric (X.term (subseq (co.φ k))).S T
          letI : TopologicalSpace (X.term (subseq (co.φ k))).M :=
            (X.term (subseq (co.φ k))).topology
          ENNReal.ofReal (redDensity (X.term (subseq (co.φ k))).S T
            (Phi.map (co.φ k) x)
            (Phi.map (co.φ k) ((extChartAt I a).symm z)) tau))
        ((modelHaar (E := E)).restrict (ccChartImage (I := I) f a)))
    (hRedLim : letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : T2Space L.M := L.t2
      letI : IsManifold I ∞ L.M := L.smooth
      letI : SigmaCompactSpace L.M := L.sigmaCompact
      ∀ a ∈ ccChartSet (I := I) f,
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : T2Space L.M := L.t2
      letI : IsManifold I ∞ L.M := L.smooth
      letI : SigmaCompactSpace L.M := L.sigmaCompact
      letI : RegularSpace L.M := hLimRegular
      letI : ConnectedSpace L.M := hLimConnected
      letI : PseudoMetricSpace L.M := lSegmentMetric L.S T
      letI : TopologicalSpace L.M := L.topology
      ∀ z ∈ ccChartImage (I := I) f a, Tendsto
        (fun k ↦
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
          letI : PseudoMetricSpace (X.term (subseq (co.φ k))).M :=
            lSegmentMetric (X.term (subseq (co.φ k))).S T
          letI : TopologicalSpace (X.term (subseq (co.φ k))).M :=
            (X.term (subseq (co.φ k))).topology
          redDensity (X.term (subseq (co.φ k))).S T (Phi.map (co.φ k) x)
            (Phi.map (co.φ k) ((extChartAt I a).symm z)) tau)
        atTop (nhds (redDensity L.S T x ((extChartAt I a).symm z) tau)))
    (hRedBd : letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : T2Space L.M := L.t2
      letI : IsManifold I ∞ L.M := L.smooth
      letI : SigmaCompactSpace L.M := L.sigmaCompact
      ∀ a ∈ ccChartSet (I := I) f,
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      ∀ᶠ k in atTop,
        ∀ᵐ z ∂((modelHaar (E := E)).restrict (ccChartImage (I := I) f a)),
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
          letI : PseudoMetricSpace (X.term (subseq (co.φ k))).M :=
            lSegmentMetric (X.term (subseq (co.φ k))).S T
          letI : TopologicalSpace (X.term (subseq (co.φ k))).M :=
            (X.term (subseq (co.φ k))).topology
          ENNReal.ofReal (redDensity (X.term (subseq (co.φ k))).S T
            (Phi.map (co.φ k) x)
            (Phi.map (co.φ k) ((extChartAt I a).symm z)) tau) ≤
              (CRed a : ENNReal))
    (hPosFin : letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : T2Space L.M := L.t2
      letI : IsManifold I ∞ L.M := L.smooth
      letI : SigmaCompactSpace L.M := L.sigmaCompact
      letI : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
      letI : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
      letI : T2Space (L.atTime 0).M := (L.atTime 0).t2
      letI : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
      letI : SigmaCompactSpace (L.atTime 0).M := (L.atTime 0).sigmaCompact
      ∀ a ∈ ccChartSet (I := I) f,
      limTest co hLimRegular hLimConnected T tau x a
        (ccChartImage (I := I) f a) (ccPosWeight (I := I) f a) ≠ ⊤)
    (hNegFin : letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : T2Space L.M := L.t2
      letI : IsManifold I ∞ L.M := L.smooth
      letI : SigmaCompactSpace L.M := L.sigmaCompact
      letI : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
      letI : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
      letI : T2Space (L.atTime 0).M := (L.atTime 0).t2
      letI : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
      letI : SigmaCompactSpace (L.atTime 0).M := (L.atTime 0).sigmaCompact
      ∀ a ∈ ccChartSet (I := I) f,
      limTest co hLimRegular hLimConnected T tau x a
        (ccChartImage (I := I) f a) (ccNegWeight (I := I) f a) ≠ ⊤) :
    letI : TopologicalSpace L.M := L.topology
    letI : MeasurableSpace L.M := borel L.M
    Tendsto (fun k ↦ ∫ y, f y ∂redDensitySrcMeas Phi co.φ
      hTermRegular hTermConnected T tau x k) atTop
      (nhds (∫ y, f y ∂redDensityLimMeas co hLimRegular hLimConnected T tau x)) := by
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
  letI : MeasurableSpace L.M := borel L.M
  letI : BorelSpace L.M := ⟨rfl⟩
  let s := ccChartSet (I := I) f
  let p : L.M → Nat → ENNReal := fun a k ↦
    srcTest Phi co.φ hTermRegular hTermConnected T tau x a
      (ccChartImage (I := I) f a) (ccPosWeight (I := I) f a) k
  let n : L.M → Nat → ENNReal := fun a k ↦
    srcTest Phi co.φ hTermRegular hTermConnected T tau x a
      (ccChartImage (I := I) f a) (ccNegWeight (I := I) f a) k
  let pLim : L.M → ENNReal := fun a ↦
    limTest co hLimRegular hLimConnected T tau x a
      (ccChartImage (I := I) f a) (ccPosWeight (I := I) f a)
  let nLim : L.M → ENNReal := fun a ↦
    limTest co hLimRegular hLimConnected T tau x a
      (ccChartImage (I := I) f a) (ccNegWeight (I := I) f a)
  have hPosConv : ∀ a ∈ s, Tendsto (p a) atTop (nhds (pLim a)) := by
    intro a ha
    apply redDensity_src_wgt Phi R bf hSrc hTgt beta psi co hInf hReg T tau x
      a hTime (ccImage_target (I := I) f a) (ccImage_compact (I := I) f a)
      (ccImage_src_ev Phi co f a) (ccChi_one_ev Phi co f a)
      hLimRegular hLimConnected hTermRegular hTermConnected
      (ccPosWeight (I := I) f a) (hPosMeas a ha) (CPos a) (hPosBd a ha)
      (hRedMeas a ha) (hRedLim a ha) (CRed a) (hRedBd a ha)
  have hNegConv : ∀ a ∈ s, Tendsto (n a) atTop (nhds (nLim a)) := by
    intro a ha
    apply redDensity_src_wgt Phi R bf hSrc hTgt beta psi co hInf hReg T tau x
      a hTime (ccImage_target (I := I) f a) (ccImage_compact (I := I) f a)
      (ccImage_src_ev Phi co f a) (ccChi_one_ev Phi co f a)
      hLimRegular hLimConnected hTermRegular hTermConnected
      (ccNegWeight (I := I) f a) (hNegMeas a ha) (CNeg a) (hNegBd a ha)
      (hRedMeas a ha) (hRedLim a ha) (CRed a) (hRedBd a ha)
  have hSrcPos : ∀ᶠ k in atTop,
      ∫⁻ y, ENNReal.ofReal (f.nnrealPart.toReal y)
          ∂redDensitySrcMeas Phi co.φ hTermRegular hTermConnected T tau x k =
        ∑ a ∈ s, p a k := by
    simpa only [s, p, ccPosWeight, CompactlySupportedContinuousMap.toReal_apply] using
      ccSrc_pos Phi co hTermRegular hTermConnected T tau x f f.nnrealPart.toReal
        (fun y ↦ by
          simpa only [CompactlySupportedContinuousMap.zero_apply,
            CompactlySupportedContinuousMap.toReal_apply] using
              NNReal.coe_nonneg (f.nnrealPart y))
        (ccPos_support f) hSrcDensMeas
  have hSrcNeg : ∀ᶠ k in atTop,
      ∫⁻ y, ENNReal.ofReal ((-f).nnrealPart.toReal y)
          ∂redDensitySrcMeas Phi co.φ hTermRegular hTermConnected T tau x k =
        ∑ a ∈ s, n a k := by
    simpa only [s, n, ccNegWeight, CompactlySupportedContinuousMap.toReal_apply] using
      ccSrc_pos Phi co hTermRegular hTermConnected T tau x f (-f).nnrealPart.toReal
        (fun y ↦ by
          simpa only [CompactlySupportedContinuousMap.zero_apply,
            CompactlySupportedContinuousMap.toReal_apply] using
              NNReal.coe_nonneg ((-f).nnrealPart y))
        (ccNeg_support f) hSrcDensMeas
  have hLimPos :
      ∫⁻ y, ENNReal.ofReal (f.nnrealPart.toReal y)
          ∂redDensityLimMeas co hLimRegular hLimConnected T tau x =
        ∑ a ∈ s, pLim a := by
    simpa only [s, pLim, ccPosWeight,
      CompactlySupportedContinuousMap.toReal_apply] using
      ccLim_pos co hLimRegular hLimConnected T tau x f f.nnrealPart.toReal
        (fun y ↦ by
          simpa only [CompactlySupportedContinuousMap.zero_apply,
            CompactlySupportedContinuousMap.toReal_apply] using
              NNReal.coe_nonneg (f.nnrealPart y))
        (ccPos_support f) hLimDensMeas
  have hLimNeg :
      ∫⁻ y, ENNReal.ofReal ((-f).nnrealPart.toReal y)
          ∂redDensityLimMeas co hLimRegular hLimConnected T tau x =
        ∑ a ∈ s, nLim a := by
    simpa only [s, nLim, ccNegWeight,
      CompactlySupportedContinuousMap.toReal_apply] using
      ccLim_pos co hLimRegular hLimConnected T tau x f (-f).nnrealPart.toReal
        (fun y ↦ by
          simpa only [CompactlySupportedContinuousMap.zero_apply,
            CompactlySupportedContinuousMap.toReal_apply] using
              NNReal.coe_nonneg ((-f).nnrealPart y))
        (ccNeg_support f) hLimDensMeas
  have hSeqSplit := ccSeq_split
    (redDensitySrcMeas Phi co.φ hTermRegular hTermConnected T tau x)
    f s p n hSrcPos hSrcNeg
    (fun a ha ↦ (hPosConv a ha).eventually_ne (hPosFin a ha))
    (fun a ha ↦ (hNegConv a ha).eventually_ne (hNegFin a ha))
  have hLimSplit := ccLimit_split
    (redDensityLimMeas co hLimRegular hLimConnected T tau x)
    f s pLim nLim hLimPos hLimNeg hPosFin hNegFin
  exact redDensity_cc_aux Phi R bf hSrc hTgt beta psi co hInf hReg T tau x hTime
    hLimRegular hLimConnected hTermRegular hTermConnected f
    (redDensitySrcMeas Phi co.φ hTermRegular hTermConnected T tau x)
    (redDensityLimMeas co hLimRegular hLimConnected T tau x)
    s (fun a ↦ a) (ccChartImage (I := I) f)
    (ccPosWeight (I := I) f) (ccNegWeight (I := I) f)
    CPos CNeg CRed
    (fun a _ ↦ ccImage_target (I := I) f a)
    (fun a _ ↦ ccImage_compact (I := I) f a)
    (fun a _ ↦ ccImage_src_ev Phi co f a)
    (fun a _ ↦ ccChi_one_ev Phi co f a)
    hPosMeas hNegMeas hPosBd hNegBd hRedMeas hRedLim hRedBd
    hPosFin hNegFin hSeqSplit hLimSplit

end DifferentialGeometry.HCGCompactness
