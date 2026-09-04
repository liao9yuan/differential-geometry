import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.PointedDensitySource
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.PointedDensityTest

set_option autoImplicit false

/-!
# Weighted source-manifold convergence of reduced density

This file carries a fixed nonnegative model-coordinate weight through the
source-manifold and limit-chart change-of-variables formulas.  Its common-chart
analytic input is `redDensity_wgt_lim`.
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

/-- A fixed nonnegative model-coordinate weight can be transported through the
pointed source parametrizations.  On each approximating manifold the weight is
read using the inverse source parametrization; on the limit it is read in the
preferred chart. -/
theorem redDensity_src_wgt
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
    (w : E → Real)
    (hWMeas : AEMeasurable (fun z ↦ ENNReal.ofReal (w z))
      ((modelHaar (E := E)).restrict B))
    (Cw : NNReal)
    (hWBd : ∀ᵐ z ∂((modelHaar (E := E)).restrict B),
      ENNReal.ofReal (w z) ≤ (Cw : ENNReal))
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
          ENNReal.ofReal (w ((mapChartParam (J := I) Phi (co.φ k) alpha).symm y)) *
            ENNReal.ofReal (redDensity (X.term (subseq (co.φ k))).S T
              (Phi.map (co.φ k) x) y tau)
          ∂riemannianVolumeMeasure (I := I)
            (M := (X.term (subseq (co.φ k))).M)
            ((X.term (subseq (co.φ k))).S.base.metric (T - tau)))
      atTop
      (nhds (∫⁻ y in (extChartAt I alpha).symm '' B,
        ENNReal.ofReal (w (extChartAt I alpha y)) *
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
  let vol : Nat → E → Real := fun k z ↦ chartDensity (I := I)
    (gSeqExt (I := I) Phi R bf hSrc hTgt (co.φ k) (T - tau)) alpha
    ((extChartAt I alpha).symm z)
  let volLim : E → Real := fun z ↦ chartDensity (I := I)
    (co.gInf (T - tau)) alpha ((extChartAt I alpha).symm z)
  let red : Nat → E → Real := fun k z ↦
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
      (Phi.map (co.φ k) ((extChartAt I alpha).symm z)) tau
  let redLim : E → Real := fun z ↦
    redDensity L.S T x ((extChartAt I alpha).symm z) tau
  have hCoord : TendstoUniformly
      (fun _ : Nat ↦ fun z : B ↦ z.1) (fun z : B ↦ z.1) atTop := by
    rw [tendstoUniformly_iff_tendsto]
    exact tendsto_diag_uniformity ((fun z : B ↦ z.1) ∘ Prod.snd) (atTop ×ˢ ⊤)
  have hVolU := ConvOut.volDens_compOn (J := I) (Y := X) Phi R bf hSrc hTgt
    beta psi co hInf hReg alpha hBChart hBc
    (Q := B) (tau := fun _ ↦ T - tau)
    (u := fun _ z ↦ z.1) (uLim := fun z ↦ z.1)
    (fun _ ↦ hTime) (Eventually.of_forall fun _ z ↦ z.2) (fun z ↦ z.2) hCoord
  obtain ⟨Mvol, hMvolPos, hMvol⟩ : ∃ Mvol : Real, 0 < Mvol ∧
      ∀ z ∈ B, volLim z ≤ Mvol := by
    by_cases hBne : B.Nonempty
    · simpa only [volLim] using
        (DifferentialGeometry.Analysis.Sobolev.Chart.exists_sup_chartDensity_on_compact_pos
          (I := I) (M := (L.atTime 0).M) (co.gInf (T - tau)) alpha hBc hBne
          (hBChart.trans interior_subset))
    · exact ⟨1, zero_lt_one, fun z hz ↦ (hBne ⟨z, hz⟩).elim⟩
  let Cvol : NNReal := ⟨Mvol + 1, by positivity⟩
  have hNear := (Metric.tendstoUniformly_iff.1 hVolU) 1 zero_lt_one
  have hVolBd : ∀ᶠ k in atTop, ∀ᵐ z ∂((modelHaar (E := E)).restrict B),
      ENNReal.ofReal (vol k z) ≤ (Cvol : ENNReal) := by
    filter_upwards [hNear] with k hk
    filter_upwards [ae_restrict_mem hBc.measurableSet] with z hz
    have hdist : |vol k z - volLim z| < 1 := by
      simpa only [Real.dist_eq, abs_sub_comm] using hk ⟨z, hz⟩
    have hseq : vol k z ≤ Mvol + 1 := by
      linarith [le_abs_self (vol k z - volLim z), hMvol z hz]
    simpa only [Cvol, ENNReal.coe_nnreal_eq, NNReal.coe_mk] using
      ENNReal.ofReal_le_ofReal hseq
  have hVolLim : ∀ z ∈ B, Tendsto (fun k ↦ vol k z) atTop (nhds (volLim z)) := by
    intro z hz
    simpa only [vol, volLim] using hVolU.tendsto_at ⟨z, hz⟩
  have hVolMeas (k : Nat) : AEMeasurable
      (fun z ↦ ENNReal.ofReal (vol k z)) ((modelHaar (E := E)).restrict B) := by
    have hTarget := aemeasurable_chartDensity_symm_pullback
      (I := I) (gSeqExt (I := I) Phi R bf hSrc hTgt (co.φ k) (T - tau)) alpha
    exact hTarget.mono_measure
      (Measure.restrict_mono (hBChart.trans interior_subset) le_rfl)
  have hRedMeas' : ∀ᶠ k in atTop, AEMeasurable
      (fun z ↦ ENNReal.ofReal (red k z)) ((modelHaar (E := E)).restrict B) := by
    filter_upwards [hRedMeas] with k hk
    simpa only [red] using hk
  have hRedLim' : ∀ z ∈ B, Tendsto (fun k ↦ red k z) atTop
      (nhds (redLim z)) := by
    intro z hz
    simpa only [red, redLim] using hRedLim z hz
  have hCommon : Tendsto
      (fun k ↦ ∫⁻ z in B, ENNReal.ofReal (w z) *
        (ENNReal.ofReal (vol k z) * ENNReal.ofReal (red k z))
        ∂(modelHaar (E := E))) atTop
      (nhds (∫⁻ z in B, ENNReal.ofReal (w z) *
        (ENNReal.ofReal (volLim z) * ENNReal.ofReal (redLim z))
        ∂(modelHaar (E := E)))) :=
    redDensity_wgt_lim hBc w hWMeas hVolMeas hRedMeas' hVolLim hRedLim'
      Cw Cvol Cred hWBd hVolBd hRedBd
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
         ENNReal.ofReal
            (w ((mapChartParam (J := I) Phi (co.φ k) alpha).symm y)) *
           ENNReal.ofReal (redDensity (X.term (subseq (co.φ k))).S T
             (Phi.map (co.φ k) x) y tau)
         ∂riemannianVolumeMeasure (I := I)
           (M := (X.term (subseq (co.φ k))).M)
           ((X.term (subseq (co.φ k))).S.base.metric (T - tau))) =
        ∫⁻ z in B, ENNReal.ofReal (w z) *
          (ENNReal.ofReal (vol k z) * ENNReal.ofReal (red k z))
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
      (fun y ↦ ENNReal.ofReal
          (w ((mapChartParam (J := I) Phi (co.φ k) alpha).symm y)) *
        ENNReal.ofReal (redDensity (X.term (subseq (co.φ k))).S T
          (Phi.map (co.φ k) x) y tau)) hBc.measurableSet hkSrc]
    apply setLIntegral_congr_fun hBc.measurableSet
    intro z hz
    change
      ENNReal.ofReal (paramDensity (I := I)
          ((X.term (subseq (co.φ k))).S.base.metric (T - tau))
          (mapChartParam (J := I) Phi (co.φ k) alpha) z) *
        (ENNReal.ofReal (w ((mapChartParam (J := I) Phi (co.φ k) alpha).symm
            ((mapChartParam (J := I) Phi (co.φ k) alpha) z))) *
          ENNReal.ofReal (redDensity (X.term (subseq (co.φ k))).S T
            (Phi.map (co.φ k) x)
            (mapChartParam (J := I) Phi (co.φ k) alpha z) tau)) =
      ENNReal.ofReal (w z) *
        (ENNReal.ofReal (vol k z) * ENNReal.ofReal (red k z))
    have hleft :
        (mapChartParam (J := I) Phi (co.φ k) alpha).symm.toPartialEquiv
            ((mapChartParam (J := I) Phi (co.φ k) alpha).toPartialEquiv z) = z :=
      (mapChartParam (J := I) Phi (co.φ k) alpha).left_inv (hkSrc hz)
    rw [hleft]
    rw [paramDens_src_eq (J := I) Phi R bf hSrc hTgt (co.φ k) (T - tau)
      alpha (hkSrc hz) (hkOne z hz)]
    change _ = ENNReal.ofReal (w z) *
      (ENNReal.ofReal (vol k z) * ENNReal.ofReal (red k z))
    simp only [vol, red]
    ac_rfl
  have hLimit :
      (∫⁻ y in (extChartAt I alpha).symm '' B,
          ENNReal.ofReal (w (extChartAt I alpha y)) *
            ENNReal.ofReal (redDensity L.S T x y tau)
          ∂riemannianVolumeMeasure (I := I) (M := L.M)
            (co.gInf (T - tau))) =
        ∫⁻ z in B, ENNReal.ofReal (w z) *
          (ENNReal.ofReal (volLim z) * ENNReal.ofReal (redLim z))
          ∂(modelHaar (E := E)) := by
    calc
      _ = ∫⁻ z in B,
          ENNReal.ofReal (chartDensity (I := I) (co.gInf (T - tau)) alpha
            ((extChartAt I alpha).symm z)) *
          (ENNReal.ofReal (w (extChartAt I alpha
              ((extChartAt I alpha).symm z))) *
            ENNReal.ofReal
              (redDensity L.S T x ((extChartAt I alpha).symm z) tau))
          ∂(modelHaar (E := E)) := by
        exact riemVol_chart_lint (I := I) (co.gInf (T - tau)) alpha
          (fun y ↦ ENNReal.ofReal (w (extChartAt I alpha y)) *
            ENNReal.ofReal (redDensity L.S T x y tau)) hBc.measurableSet
          (hBChart.trans interior_subset)
      _ = _ := by
        apply setLIntegral_congr_fun hBc.measurableSet
        intro z hz
        change
          ENNReal.ofReal (chartDensity (I := I) (co.gInf (T - tau)) alpha
              ((extChartAt I alpha).symm z)) *
            (ENNReal.ofReal
                (w (extChartAt I alpha ((extChartAt I alpha).symm z))) *
              ENNReal.ofReal
                (redDensity L.S T x ((extChartAt I alpha).symm z) tau)) =
          ENNReal.ofReal (w z) *
            (ENNReal.ofReal (volLim z) * ENNReal.ofReal (redLim z))
        have hright : extChartAt I alpha ((extChartAt I alpha).symm z) = z :=
          (extChartAt I alpha).right_inv (interior_subset (hBChart hz))
        rw [hright]
        simp only [volLim, redLim]
        ac_rfl
  rw [hLimit]
  exact hCommon.congr' (Filter.EventuallyEq.symm hTerm)

end DifferentialGeometry.HCGCompactness
