import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.VolumeConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.PointedDensity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.RedVolumeParam

set_option autoImplicit false

/-!
# Compact common-coordinate convergence of reduced density

This file combines pointwise reduced-density convergence with fixed-chart
volume-density convergence and uniform compact-set bounds.  The conclusion is
deliberately a common-coordinate `lintegral`; changing variables back to the
source manifolds requires a separate parametric-density bridge.
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
variable {I : ModelWithCorners Real E H}

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

omit [CompleteSpace E] in
private theorem compact_prod_lim
    {B : Set E} (hBc : IsCompact B)
    {vol red : Nat → E → Real} {volLim redLim : E → Real}
    (hVolMeas : ∀ n, AEMeasurable (fun z ↦ ENNReal.ofReal (vol n z))
      ((modelHaar (E := E)).restrict B))
    (hRedMeas : ∀ᶠ n in atTop, AEMeasurable (fun z ↦ ENNReal.ofReal (red n z))
      ((modelHaar (E := E)).restrict B))
    (hVolLim : ∀ z ∈ B, Tendsto (fun n ↦ vol n z) atTop (nhds (volLim z)))
    (hRedLim : ∀ z ∈ B, Tendsto (fun n ↦ red n z) atTop (nhds (redLim z)))
    (Cvol Cred : NNReal)
    (hVolBd : ∀ᶠ n in atTop, ∀ᵐ z ∂((modelHaar (E := E)).restrict B),
      ENNReal.ofReal (vol n z) ≤ (Cvol : ENNReal))
    (hRedBd : ∀ᶠ n in atTop, ∀ᵐ z ∂((modelHaar (E := E)).restrict B),
      ENNReal.ofReal (red n z) ≤ (Cred : ENNReal)) :
    Tendsto
      (fun n ↦ ∫⁻ z in B,
        ENNReal.ofReal (vol n z) * ENNReal.ofReal (red n z)
        ∂(modelHaar (E := E)))
      atTop
      (nhds (∫⁻ z in B,
        ENNReal.ofReal (volLim z) * ENNReal.ofReal (redLim z)
        ∂(modelHaar (E := E)))) := by
  let μ : Measure E := (modelHaar (E := E)).restrict B
  let F : Nat → E → ENNReal := fun n z ↦
    ENNReal.ofReal (vol n z) * ENNReal.ofReal (red n z)
  let f : E → ENNReal := fun z ↦
    ENNReal.ofReal (volLim z) * ENNReal.ofReal (redLim z)
  let C : E → ENNReal := fun _ ↦ (Cvol : ENNReal) * (Cred : ENNReal)
  have hFMeas : ∀ᶠ n in atTop, AEMeasurable (F n) μ := by
    filter_upwards [hRedMeas] with n hn
    simpa only [F, μ] using (hVolMeas n).mul hn
  have hBound : ∀ᶠ n in atTop, F n ≤ᵐ[μ] C := by
    filter_upwards [hVolBd, hRedBd] with n hnVol hnRed
    filter_upwards [hnVol, hnRed] with z hzVol hzRed
    exact mul_le_mul' hzVol hzRed
  have hFin : ∫⁻ z, C z ∂μ ≠ ⊤ := by
    rw [lintegral_const]
    apply ENNReal.mul_ne_top
    · exact ENNReal.mul_ne_top (by simp) (by simp)
    · simpa only [μ, Measure.restrict_apply_univ] using hBc.measure_lt_top.ne
  have hMem : ∀ᵐ z ∂μ, z ∈ B := by
    simpa only [μ] using ae_restrict_mem hBc.measurableSet
  have hLim : ∀ᵐ z ∂μ, Tendsto (fun n ↦ F n z) atTop (nhds (f z)) := by
    filter_upwards [hMem] with z hz
    apply ENNReal.Tendsto.mul
    · exact (ENNReal.continuous_ofReal.tendsto _).comp (hVolLim z hz)
    · exact Or.inr ENNReal.ofReal_ne_top
    · exact (ENNReal.continuous_ofReal.tendsto _).comp (hRedLim z hz)
    · exact Or.inr ENNReal.ofReal_ne_top
  have hReady := hFMeas.and hBound
  rw [eventually_atTop] at hReady
  obtain ⟨N, hN⟩ := hReady
  have hShiftLim : ∀ᵐ z ∂μ,
      Tendsto (fun n ↦ F (n + N) z) atTop (nhds (f z)) :=
    hLim.mono fun _ hz ↦ hz.comp (tendsto_add_atTop_nat N)
  have hShift := tendsto_lintegral_of_dominated_convergence' C
    (fun n ↦ (hN (n + N) (Nat.le_add_left N n)).1)
    (fun n ↦ (hN (n + N) (Nat.le_add_left N n)).2)
    hFin hShiftLim
  have hOrig : Tendsto (fun n ↦ ∫⁻ z, F n z ∂μ) atTop
      (nhds (∫⁻ z, f z ∂μ)) :=
    (tendsto_add_atTop_iff_nat N).1 hShift
  simpa only [F, f, C, μ] using hOrig

/-- Fixed-time reduced-density integrals converge on a compact set in one
common limit chart.  This is the pointed-flow compact-test endpoint before the
separate source-manifold change-of-variables bridge. -/
theorem redDensity_cpt_lim
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
      (fun k ↦ ∫⁻ z in B,
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
        ∂(modelHaar (E := E)))
      atTop
      (nhds (∫⁻ z in B,
        ENNReal.ofReal (chartDensity (I := I) (co.gInf (T - tau)) alpha
          ((extChartAt I alpha).symm z)) *
        ENNReal.ofReal (redDensity L.S T x ((extChartAt I alpha).symm z) tau)
        ∂(modelHaar (E := E)))) := by
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
  simpa only [vol, volLim, red, redLim] using
    (compact_prod_lim (E := E) hBc hVolMeas hRedMeas' hVolLim hRedLim'
      Cvol Cred hVolBd hRedBd)

end DifferentialGeometry.HCGCompactness
