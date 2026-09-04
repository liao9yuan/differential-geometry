import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.PointedDensityCompact

set_option autoImplicit false

/-!
# Source-manifold convergence of reduced density

This file changes variables in the compact common-coordinate convergence
theorem.  The approximating integrals live on the actual pointed-flow terms,
while the limiting integral lives in the preferred chart of the limit.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.HCGCompactness

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

/-- On a compact preferred-chart region, reduced-density integrals on the
approximating source manifolds converge to the corresponding limit integral. -/
theorem redDensity_src_lim
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
    (T tau : Real) (x alpha : L.M) {B : Set E}
    (hTime : T - tau ∈ Icc beta psi)
    (hBChart : letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      B ⊆ interior (extChartAt I alpha).target)
    (hBc : IsCompact B)
    (hBSrc : letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      ∀ᶠ k in atTop,
        letI : TopologicalSpace (X.term (subseq (co.φ k))).M :=
          (X.term (subseq (co.φ k))).topology
        letI : ChartedSpace H (X.term (subseq (co.φ k))).M :=
          (X.term (subseq (co.φ k))).charted
        B ⊆ (mapChartParam (J := I) Phi (co.φ k) alpha).source)
    (hOne : letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      ∀ᶠ k in atTop,
        ∀ z, z ∈ B → bf.chi (co.φ k) ((extChartAt I alpha).symm z) = 1)
    (hLimRegular : letI : TopologicalSpace L.M := L.topology
      RegularSpace L.M)
    (hLimConnected : letI : TopologicalSpace L.M := L.topology
      ConnectedSpace L.M)
    (hTermRegular : ∀ k,
      letI : TopologicalSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).topology
      RegularSpace (X.term (subseq (co.φ k))).M)
    (hTermConnected : ∀ k,
      letI : TopologicalSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).topology
      ConnectedSpace (X.term (subseq (co.φ k))).M)
    (hRedMeas : letI : TopologicalSpace L.M := L.topology
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
            (Phi.map (co.φ k) ((extChartAt I alpha).symm z)) tau))
        ((modelHaar (E := E)).restrict B))
    (hRedLim : letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : T2Space L.M := L.t2
      letI : IsManifold I ∞ L.M := L.smooth
      letI : SigmaCompactSpace L.M := L.sigmaCompact
      letI : RegularSpace L.M := hLimRegular
      letI : ConnectedSpace L.M := hLimConnected
      letI : PseudoMetricSpace L.M := lSegmentMetric L.S T
      letI : TopologicalSpace L.M := L.topology
      ∀ z ∈ B, Tendsto
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
          redDensity (X.term (subseq (co.φ k))).S T
            (Phi.map (co.φ k) x)
            (Phi.map (co.φ k) ((extChartAt I alpha).symm z)) tau)
        atTop (nhds (redDensity L.S T x ((extChartAt I alpha).symm z) tau)))
    (Cred : NNReal)
    (hRedBd : letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      ∀ᶠ k in atTop, ∀ᵐ z ∂((modelHaar (E := E)).restrict B),
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
          (Phi.map (co.φ k) ((extChartAt I alpha).symm z)) tau) ≤
            (Cred : ENNReal)) :
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
    Tendsto
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
        ∫⁻ y in (mapChartParam (J := I) Phi (co.φ k) alpha) '' B,
          ENNReal.ofReal (redDensity (X.term (subseq (co.φ k))).S T
            (Phi.map (co.φ k) x) y tau)
          ∂riemannianVolumeMeasure (I := I)
            (M := (X.term (subseq (co.φ k))).M)
            ((X.term (subseq (co.φ k))).S.base.metric (T - tau)))
      atTop
      (nhds (∫⁻ y in (extChartAt I alpha).symm '' B,
        ENNReal.ofReal (redDensity L.S T x y tau)
        ∂riemannianVolumeMeasure (I := I) (M := L.M)
          (co.gInf (T - tau)))) := by
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
  have hCommon := redDensity_cpt_lim (I := I) Phi R bf hSrc hTgt beta psi co
    hInf hReg T tau x alpha hTime hBChart hBc hLimRegular hLimConnected
    hTermRegular hTermConnected hRedMeas hRedLim Cred hRedBd
  have hTerm : ∀ᶠ k in atTop,
      (letI : TopologicalSpace (X.term (subseq (co.φ k))).M :=
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
       ∫⁻ y in (mapChartParam (J := I) Phi (co.φ k) alpha) '' B,
         ENNReal.ofReal (redDensity (X.term (subseq (co.φ k))).S T
           (Phi.map (co.φ k) x) y tau)
         ∂riemannianVolumeMeasure (I := I)
           (M := (X.term (subseq (co.φ k))).M)
           ((X.term (subseq (co.φ k))).S.base.metric (T - tau))) =
        ∫⁻ z in B,
          ENNReal.ofReal (chartDensity (I := I)
            (gSeqExt (I := I) Phi R bf hSrc hTgt (co.φ k) (T - tau)) alpha
            ((extChartAt I alpha).symm z)) *
          (letI : TopologicalSpace (X.term (subseq (co.φ k))).M :=
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
             (Phi.map (co.φ k) ((extChartAt I alpha).symm z)) tau))
          ∂(modelHaar (E := E)) := by
    filter_upwards [hBSrc, hOne] with k hkSrc hkOne
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
    rw [riemVol_param_lint (I := I)
      ((X.term (subseq (co.φ k))).S.base.metric (T - tau))
      (mapChartParam (J := I) Phi (co.φ k) alpha)
      (fun y ↦ ENNReal.ofReal (redDensity (X.term (subseq (co.φ k))).S T
        (Phi.map (co.φ k) x) y tau)) hBc.measurableSet hkSrc]
    apply setLIntegral_congr_fun hBc.measurableSet
    intro z hz
    change
      ENNReal.ofReal (paramDensity (I := I)
          ((X.term (subseq (co.φ k))).S.base.metric (T - tau))
          (mapChartParam (J := I) Phi (co.φ k) alpha) z) *
        ENNReal.ofReal (redDensity (X.term (subseq (co.φ k))).S T
          (Phi.map (co.φ k) x)
          (mapChartParam (J := I) Phi (co.φ k) alpha z) tau) =
      ENNReal.ofReal (chartDensity (I := I)
          (gSeqExt (I := I) Phi R bf hSrc hTgt (co.φ k) (T - tau)) alpha
          ((extChartAt I alpha).symm z)) *
        ENNReal.ofReal (redDensity (X.term (subseq (co.φ k))).S T
          (Phi.map (co.φ k) x)
          (Phi.map (co.φ k) ((extChartAt I alpha).symm z)) tau)
    rw [paramDens_src_eq (J := I) Phi R bf hSrc hTgt (co.φ k) (T - tau)
      alpha (hkSrc hz) (hkOne z hz)]
    rfl
  have hLimit :
      (∫⁻ y in (extChartAt I alpha).symm '' B,
          ENNReal.ofReal (redDensity L.S T x y tau)
          ∂riemannianVolumeMeasure (I := I) (M := L.M)
            (co.gInf (T - tau))) =
        ∫⁻ z in B,
          ENNReal.ofReal (chartDensity (I := I) (co.gInf (T - tau)) alpha
            ((extChartAt I alpha).symm z)) *
          ENNReal.ofReal (redDensity L.S T x ((extChartAt I alpha).symm z) tau)
          ∂(modelHaar (E := E)) := by
    exact riemVol_chart_lint (I := I) (co.gInf (T - tau)) alpha
      (fun y ↦ ENNReal.ofReal (redDensity L.S T x y tau)) hBc.measurableSet
      (hBChart.trans interior_subset)
  rw [hLimit]
  exact hCommon.congr' (Filter.EventuallyEq.symm hTerm)

end DifferentialGeometry.HCGCompactness
