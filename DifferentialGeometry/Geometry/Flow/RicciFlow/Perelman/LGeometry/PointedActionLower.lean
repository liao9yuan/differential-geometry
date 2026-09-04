import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ActionCapstone
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ActionC1
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.PointedConvergence

set_option autoImplicit false

/-!
# Lower semicontinuity for pointed L-actions

This file supplies the compact-confinement direct-method step needed for
varying curves under pointed smooth Ricci-flow convergence.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Function MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology Interval

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {D : RealTimeInterval}

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] in
/-- A reference-energy-bounded sequence confined to one compact set has a
uniformly convergent subsequence on its compact parameter interval. -/
theorem lEnergy_cpt_subseq
    (gRef : SmoothRiemannianMetric I M)
    (a b B : Real)
    (alpha : Nat → Real → M)
    (halpha : ∀ n, ContMDiffOn 𝓘(Real, Real) I 1 (alpha n) (Icc a b))
    (hE : ∀ n, IntegrableOn
      (fun s ↦ gRef.inner (alpha n s) (lVelocity (I := I) (alpha n) s)
        (lVelocity (I := I) (alpha n) s)) (Icc a b))
    (henergy : ∀ n, curveEnergy (I := I) gRef (alpha n) a b ≤ B)
    (Q : Set M) (hQc : IsCompact Q)
    (hQ : ∀ n (s : Icc a b), alpha n s.1 ∈ Q) :
    ∃ (phi : Nat → Nat) (g : C(Icc a b, M)),
      StrictMono phi ∧
        TendstoUniformly
          (fun n (s : Icc a b) ↦ alpha (phi n) s.1) g atTop := by
  classical
  have hriedist (n : Nat) {s t : Real}
      (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
      riemannianEDistOf (I := I) gRef (alpha n s) (alpha n t) ≤
        ENNReal.ofReal (Real.sqrt (t - s) * Real.sqrt B) := by
    have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc has htb
    have hsubE : curveEnergy (I := I) gRef (alpha n) s t ≤
        curveEnergy (I := I) gRef (alpha n) a b :=
      curveEnergy_mono (I := I) gRef has hst htb (hE n)
    exact edistOf_le_budget (I := I) gRef hst
      ((halpha n).mono hsub) ((hE n).mono_set hsub)
      (hsubE.trans (henergy n))
  let f : Nat → C(Icc a b, M) := fun n ↦
    ⟨fun s ↦ alpha n s.1, (halpha n).continuousOn.restrict⟩
  have hmod : Tendsto (fun r : Real ↦ Real.sqrt r * Real.sqrt B)
      (𝓝 0) (𝓝 0) := by
    have hcont : Continuous (fun r : Real ↦ Real.sqrt r * Real.sqrt B) :=
      Real.continuous_sqrt.mul continuous_const
    simpa only [Real.sqrt_zero, zero_mul] using hcont.tendsto (0 : Real)
  have hunif : UniformEquicontinuous (fun n ↦ (f n : Icc a b → M)) := by
    rw [Metric.uniformEquicontinuous_iff]
    intro epsilon hepsilon
    obtain ⟨rho, hrho, htoDist⟩ :=
      dist_lt_riedist_cpt (I := I) gRef Q hQc hepsilon
    obtain ⟨delta, hdelta, hmodDelta⟩ :=
      Metric.tendsto_nhds_nhds.1 hmod rho hrho
    refine ⟨delta, hdelta, ?_⟩
    intro s t hst n
    have hsmall : Real.sqrt (dist s t) * Real.sqrt B < rho := by
      have h := hmodDelta (x := dist s t) (by simpa using hst)
      simpa only [Real.dist_eq, sub_zero,
        abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
        using h
    have hofReal : ENNReal.ofReal (Real.sqrt (dist s t) * Real.sqrt B) <
        ENNReal.ofReal rho := (ENNReal.ofReal_lt_ofReal_iff hrho).2 hsmall
    rcases le_total s.1 t.1 with hst' | hts
    · have hriem := hriedist n s.2.1 hst' t.2.2
      have hriem' := hriem.trans_lt (by
        simpa only [Subtype.dist_eq, Real.dist_eq,
          abs_of_nonpos (sub_nonpos.mpr hst'), neg_sub] using hofReal)
      simpa only [f] using
        htoDist (alpha n s.1) (hQ n s) (alpha n t.1) (hQ n t) hriem'
    · have hriem := hriedist n t.2.1 hts s.2.2
      have hriem' := hriem.trans_lt (by
        simpa only [Subtype.dist_eq, Real.dist_eq,
          abs_of_nonneg (sub_nonneg.mpr hts)] using hofReal)
      have hout :=
        htoDist (alpha n t.1) (hQ n t) (alpha n s.1) (hQ n s) hriem'
      simpa only [f, dist_comm] using hout
  obtain ⟨phi, g, hphi, hconv⟩ :=
    DifferentialGeometry.Analysis.arzela_subseq_cpt Q hQc f hQ hunif.equicontinuous
  exact ⟨phi, g, hphi, by simpa only [f] using hconv⟩

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] in
/-- The compact-confined reference-energy subsequence preserves fixed endpoints. -/
theorem lEnergy_cpt_fix
    (gRef : SmoothRiemannianMetric I M)
    (a b B : Real) (hab : a ≤ b)
    (alpha : Nat → Real → M)
    (halpha : ∀ n, ContMDiffOn 𝓘(Real, Real) I 1 (alpha n) (Icc a b))
    (hE : ∀ n, IntegrableOn
      (fun s ↦ gRef.inner (alpha n s) (lVelocity (I := I) (alpha n) s)
        (lVelocity (I := I) (alpha n) s)) (Icc a b))
    (henergy : ∀ n, curveEnergy (I := I) gRef (alpha n) a b ≤ B)
    (Q : Set M) (hQc : IsCompact Q)
    (hQ : ∀ n (s : Icc a b), alpha n s.1 ∈ Q)
    (x y : M) (hfixa : ∀ n, alpha n a = x)
    (hfixb : ∀ n, alpha n b = y) :
    ∃ (phi : Nat → Nat) (g : C(Icc a b, M)),
      StrictMono phi ∧
        TendstoUniformly
          (fun n (s : Icc a b) ↦ alpha (phi n) s.1) g atTop ∧
        g ⟨a, le_rfl, hab⟩ = x ∧ g ⟨b, hab, le_rfl⟩ = y := by
  obtain ⟨phi, g, hphi, hconv⟩ :=
    lEnergy_cpt_subseq (I := I) gRef a b B alpha halpha hE henergy Q hQc hQ
  refine ⟨phi, g, hphi, hconv, ?_, ?_⟩
  · have hlim := hconv.tendsto_at (⟨a, le_rfl, hab⟩ : Icc a b)
    have hlim' : Tendsto (fun _ : Nat ↦ x) atTop
        (𝓝 (g ⟨a, le_rfl, hab⟩)) := by
      simpa only [hfixa] using hlim
    exact tendsto_nhds_unique hlim' tendsto_const_nhds
  · have hlim := hconv.tendsto_at (⟨b, hab, le_rfl⟩ : Icc a b)
    have hlim' : Tendsto (fun _ : Nat ↦ y) atTop
        (𝓝 (g ⟨b, hab, le_rfl⟩)) := by
      simpa only [hfixb] using hlim
    exact tendsto_nhds_unique hlim' tendsto_const_nhds

end DifferentialGeometry.PDE.RicciFlow.Perelman

namespace DifferentialGeometry.HCGCompactness

open Bundle Filter Function MeasureTheory Set
open scoped ContDiff Manifold Topology Interval

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

private theorem pt_liminf_add
    {q r : Nat → Real} {q0 r0 : Real}
    (hq : q0 ≤ liminf q atTop)
    (hqLo : IsBoundedUnder (· ≥ ·) atTop q)
    (hqHi : IsBoundedUnder (· ≤ ·) atTop q)
    (hr : Tendsto r atTop (nhds r0)) :
    q0 + r0 ≤ liminf (fun n ↦ q n + r n) atTop := by
  calc
    q0 + r0 ≤ liminf q atTop + r0 := add_le_add_left hq r0
    _ = liminf q atTop + liminf r atTop := by rw [hr.liminf_eq]
    _ ≤ liminf (fun n ↦ q n + r n) atTop := by
      simpa only [Pi.add_apply] using
        (le_liminf_add hqLo hqHi
          hr.isBoundedUnder_ge hr.isCoboundedUnder_ge)

section PointedAction

variable [CompleteSpace E]
  [hFinrank : NeZero (Module.finrank Real E)]
  [hBoundaryless : I.Boundaryless]

set_option maxHeartbeats 400000 in
-- The compact-confinement, chart-liminf, and scalar DCT assembly exceeds the default budget.
include hFinrank hBoundaryless in
/-- On one fixed limit chart, pointed smooth convergence makes the actual
regularized L-action lower semicontinuous for compact-confined `C¹` curves
whose chart representatives converge weakly in time `H¹`. -/
theorem lRegAction_pt_lsc
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
        ∀ (y : SourceDomain (I := I) Phi k)
          (v : letI : TopologicalSpace (SourceDomain (I := I) Phi k) :=
              sourceDomTop (I := I) Phi k
            letI : ChartedSpace H (SourceDomain (I := I) Phi k) :=
              sourceDomCharted (I := I) Phi k
            TangentSpace I y),
          cLow * R.inner (y : (L.atTime 0).M) v v ≤
            letI : TopologicalSpace (SourceDomain (I := I) Phi k) :=
              sourceDomTop (I := I) Phi k
            letI : ChartedSpace H (SourceDomain (I := I) Phi k) :=
              sourceDomCharted (I := I) Phi k
            letI : IsManifold I ∞ (SourceDomain (I := I) Phi k) :=
              sourceDomSmooth (I := I) Phi k
            (srcMetric (I := I) Phi hSrc hTgt k t).inner y v v)
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
    (T a b : Real) (hab : a ≤ b) (p : L.M)
    (alpha : Nat → Real → L.M) (alphaLim : Real → L.M)
    (halpha : letI : TopologicalSpace L.M := L.topology
        letI : ChartedSpace H L.M := L.charted
        letI : IsManifold I ∞ L.M := L.smooth
      ∀ n, ContMDiffOn 𝓘(Real, Real) I 1 (alpha n) (Icc a b))
    (u : Nat → timeH1 E (b - a)) (uLim : timeH1 E (b - a))
    (hChart : letI : TopologicalSpace L.M := L.topology
        letI : ChartedSpace H L.M := L.charted
      ∀ n, MapsTo (alpha n) (Icc a b) (chartAt H p).source)
    (hRep : letI : TopologicalSpace L.M := L.topology
        letI : ChartedSpace H L.M := L.charted
        letI : IsManifold I ∞ L.M := L.smooth
      ∀ n, EqOn (u n).toFun
        (fun r ↦ extChartAt I p (alpha n (a + r))) (Icc (0 : Real) (b - a)))
    (hLimChart : letI : TopologicalSpace L.M := L.topology
        letI : ChartedSpace H L.M := L.charted
      MapsTo alphaLim (Icc a b) (chartAt H p).source)
    (hLimRep : letI : TopologicalSpace L.M := L.topology
        letI : ChartedSpace H L.M := L.charted
        letI : IsManifold I ∞ L.M := L.smooth
      EqOn uLim.toFun
        (fun r ↦ extChartAt I p (alphaLim (a + r))) (Icc (0 : Real) (b - a)))
    (Q : Set L.M)
    (hQc : letI : TopologicalSpace L.M := L.topology; IsCompact Q)
    (hQ : ∀ n (s : Icc a b), alpha n s.1 ∈ Q)
    (K : Set E) (hKc : IsCompact K)
    (hKChart : letI : TopologicalSpace L.M := L.topology
        letI : ChartedSpace H L.M := L.charted
        letI : IsManifold I ∞ L.M := L.smooth
      K ⊆ interior (extChartAt I p).target)
    (huK : ∀ n (r : Icc (0 : Real) (b - a)), (u n).toFun r.1 ∈ K)
    (hu : TendstoUniformly
      (fun n (r : Icc (0 : Real) (b - a)) ↦ (u n).toFun r.1)
      (fun r ↦ uLim.toFun r.1) atTop)
    (hdu : ∀ z : timeL2 E (b - a), Tendsto
      (fun n ↦ inner Real (u n).deriv z) atTop
      (nhds (inner Real uLim.deriv z)))
    (dP : PseudoMetricSpace L.M)
    (hTop : dP.toUniformSpace.toTopologicalSpace = L.topology)
    (halphaLim : letI : PseudoMetricSpace L.M := dP
      TendstoUniformly
        (fun n (s : Icc a b) ↦ alpha n s.1)
        (fun s ↦ alphaLim s.1) atTop)
    (hAct : IsBoundedUnder (· ≤ ·) atTop (fun k ↦
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
        (fun s ↦ Phi.map (co.φ k) (alpha k s)) a b))
    (hBack : MapsTo (fun s ↦ T - s ^ 2) (Icc a b) (Icc beta psi)) :
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : T2Space L.M := L.t2
    letI : IsManifold I ∞ L.M := L.smooth
    letI : SigmaCompactSpace L.M := L.sigmaCompact
    lRegAction L.S T alphaLim a b ≤ liminf (fun k ↦
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
        (fun s ↦ Phi.map (co.φ k) (alpha k s)) a b) atTop := by
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
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.M := by
    change IsManifold I ∞ L.M
    infer_instance
  letI : SigmaCompactSpace L.M := L.sigmaCompact
  have hLimQ : ∀ s : Icc a b, alphaLim s.1 ∈ Q := by
    intro s
    have hAt : Tendsto (fun n ↦ alpha n s.1) atTop
        (@nhds L.M dP.toUniformSpace.toTopologicalSpace (alphaLim s.1)) := by
      letI : PseudoMetricSpace L.M := dP
      exact halphaLim.tendsto_at s
    rw [hTop] at hAt
    apply hQc.isClosed.mem_of_tendsto hAt
    exact Eventually.of_forall fun n ↦ hQ n s
  let len : Real := b - a
  let tau : Real → Real := fun r ↦ T - (a + r) ^ 2
  let GSeq : Nat → MetricConnectionFamilyOn (I := I) (M := (L.atTime 0).M) X.D := fun n ↦
    (lcMetricFamily (I := I) (M := (L.atTime 0).M)
      (fun t ↦ gSeqExt (I := I) Phi R bf hSrc hTgt (co.φ n) t)).restrict X.D
  let GInf : MetricConnectionFamilyOn (I := I) (M := (L.atTime 0).M) X.D :=
    (lcMetricFamily (I := I) (M := (L.atTime 0).M) co.gInf).restrict X.D
  let mapped (n : Nat) : Real → (X.term (subseq (co.φ n))).M :=
    fun s ↦ Phi.map (co.φ n) (alpha n s)
  let kinChart : Nat → Real := fun n ↦
    ∫ r in (0 : Real)..len, (1 / 2 : Real) * inner Real
      (chartGramOp (I := I) (GSeq n) p
        (tau r, (u n).toFun r) ((u n).deriv r)) ((u n).deriv r)
  let kinLimChart : Real :=
    ∫ r in (0 : Real)..len, (1 / 2 : Real) * inner Real
      (chartGramOp (I := I) GInf p
        (tau r, uLim.toFun r) (uLim.deriv r)) (uLim.deriv r)
  let kin : Nat → Real := fun n ↦
    letI : TopologicalSpace (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).topology
    letI : ChartedSpace H (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).charted
    letI : T2Space (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).t2
    letI : IsManifold I ∞ (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).smooth
    letI : SigmaCompactSpace (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).sigmaCompact
    ∫ s in a..b, (1 / 2 : Real) *
      ((X.term (subseq (co.φ n))).S.base.metric (T - s ^ 2)).inner
        (mapped n s) (lVelocity (I := I) (mapped n) s)
        (lVelocity (I := I) (mapped n) s)
  let pot : Nat → Real := fun n ↦
    letI : TopologicalSpace (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).topology
    letI : ChartedSpace H (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).charted
    letI : T2Space (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).t2
    letI : IsManifold I ∞ (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).smooth
    letI : SigmaCompactSpace (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).sigmaCompact
    ∫ s in a..b, 2 * s ^ 2 *
      (X.term (subseq (co.φ n))).S.scalar (T - s ^ 2) (mapped n s)
  let act : Nat → Real := fun n ↦
    letI : TopologicalSpace (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).topology
    letI : ChartedSpace H (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).charted
    letI : T2Space (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).t2
    letI : IsManifold I ∞ (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).smooth
    letI : SigmaCompactSpace (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).sigmaCompact
    lRegAction (X.term (subseq (co.φ n))).S T (mapped n) a b
  let kinLim : Real := ∫ s in a..b, (1 / 2 : Real) *
    (L.S.base.metric (T - s ^ 2)).inner (alphaLim s)
      (lVelocity (I := I) alphaLim s) (lVelocity (I := I) alphaLim s)
  let potLim : Real := ∫ s in a..b,
    2 * s ^ 2 * L.S.scalar (T - s ^ 2) (alphaLim s)
  have hLen : 0 ≤ len := by simpa only [len] using sub_nonneg.mpr hab
  have hTauCont : ContinuousOn tau (Icc (0 : Real) len) := by
    exact continuousOn_const.sub ((continuousOn_const.add continuousOn_id).pow 2)
  have hTau : MapsTo tau (Icc (0 : Real) len) (Icc beta psi) := by
    intro r hr
    apply hBack
    exact ⟨le_add_of_nonneg_right hr.1, by dsimp only [len] at hr; linarith [hr.2]⟩
  have hTime : Icc beta psi ⊆ X.D.carrier :=
    fun _ ht ↦ X.D.regular_subset (hReg ht)
  have hDiff (n : Nat) : ∀ᵐ r ∂timeMeasure len,
      MDifferentiableAt 𝓘(Real, Real) I (alpha n) (a + r) := by
    simpa only [len] using
      curve_mdiff_local I p (alpha n) (u n) hab (hChart n) (hRep n)
  have hLimDiff : ∀ᵐ r ∂timeMeasure len,
      MDifferentiableAt 𝓘(Real, Real) I alphaLim (a + r) := by
    simpa only [len] using
      curve_mdiff_local I p alphaLim uLim hab hLimChart hLimRep
  have hLimCont : ContinuousOn alphaLim (Icc a b) :=
    curve_cont_local I p alphaLim uLim hab hLimChart hLimRep
  have huLimK : ∀ r : Icc (0 : Real) len, uLim.toFun r.1 ∈ K := by
    intro r
    apply hKc.isClosed.mem_of_tendsto (hu.tendsto_at r)
    exact Eventually.of_forall fun n ↦ by simpa only [len] using huK n r
  have hKinRaw := ConvOut.chartKin_liminf (J := I) (Y := X)
    Phi R bf hSrc hTgt beta psi co hInf hReg p hLen tau hTauCont hTau
    hKc hKChart u uLim (by simpa only [len] using huK)
    huLimK (by simpa only [len] using hu) (by simpa only [len] using hdu)
  have hKinRaw' : kinLimChart ≤ liminf kinChart atTop := by
    simpa only [kinLimChart, kinChart, GInf, GSeq, tau, len] using hKinRaw
  have hLimMetric : kinLim = kinLimChart := by
    have hMetricEq : (∫ s in a..b, (1 / 2 : Real) *
        (L.S.base.metric (T - s ^ 2)).inner (alphaLim s)
          (lVelocity (I := I) alphaLim s) (lVelocity (I := I) alphaLim s)) =
        ∫ s in a..b, (1 / 2 : Real) *
          (co.gInf (T - s ^ 2)).inner (alphaLim s)
            (lVelocity (I := I) alphaLim s)
            (lVelocity (I := I) alphaLim s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      apply congrArg ((1 / 2 : Real) * ·)
      change (L.S.family.metric (T - s ^ 2)).inner _ _ _ = _
      rw [hLMetric (T - s ^ 2) (hBack (by
        simpa only [uIcc_of_le hab] using hs))]
      rfl
    dsimp only [kinLim]
    rw [hMetricEq]
    simpa only [kinLimChart, GInf, tau, len,
      MetricConnectionFamily.restrict_metric, lcMetricFamily,
      ContinuousLinearMap.smul_apply, real_inner_smul_left] using
      (lKinetic_local_of GInf (fun s ↦ T - s ^ 2) alphaLim p a b hab uLim
        hLimChart hLimRep hLimDiff)
  obtain ⟨kGrow, hkGrow⟩ := bf.grow_cover Q hQc
  have hGrow : ∀ᶠ n in atTop,
      ∀ s : Icc a b, alpha n s.1 ∈ bf.grow (co.φ n) := by
    filter_upwards [eventually_ge_atTop kGrow] with n hn
    intro s
    exact hkGrow (co.φ n) (hn.trans (co.hφ.id_le n)) (hQ n s)
  have hKinEq : kinChart =ᶠ[atTop] kin := by
    filter_upwards [hGrow] with n hn
    letI : TopologicalSpace (SourceDomain (I := I) Phi (co.φ n)) :=
      sourceDomTop (I := I) Phi (co.φ n)
    letI : ChartedSpace H (SourceDomain (I := I) Phi (co.φ n)) :=
      sourceDomCharted (I := I) Phi (co.φ n)
    letI : T2Space (SourceDomain (I := I) Phi (co.φ n)) :=
      sourceDomT2 (I := I) Phi (co.φ n)
    letI : IsManifold I ∞ (SourceDomain (I := I) Phi (co.φ n)) :=
      sourceDomSmooth (I := I) Phi (co.φ n)
    letI : SigmaCompactSpace (SourceDomain (I := I) Phi (co.φ n)) :=
      sourceDomSigmaOf (I := I) Phi (co.φ n) (hSrc (co.φ n))
    letI : TopologicalSpace (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).topology
    letI : ChartedSpace H (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).charted
    letI : T2Space (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).t2
    letI : IsManifold I ∞ (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).smooth
    letI : SigmaCompactSpace (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).sigmaCompact
    obtain ⟨W, _hWOpen, hGrowW, hOne⟩ := bf.chi_one (co.φ n)
    have hChartAE := lKinetic_ae (GSeq n) (fun s ↦ T - s ^ 2)
      (alpha n) p a b hab (u n) (hChart n) (hRep n) (hDiff n)
    have hMem : ∀ᵐ r ∂timeMeasure len, r ∈ Ioo (0 : Real) len := by
      unfold timeMeasure
      rw [← restrict_Ioo_eq_restrict_Icc]
      exact ae_restrict_mem measurableSet_Ioo
    have hPoint :
        (fun r ↦ (1 / 2 : Real) * inner Real
          (chartGramOp (I := I) (GSeq n) p
            (tau r, (u n).toFun r) ((u n).deriv r)) ((u n).deriv r))
          =ᵐ[timeMeasure len]
        fun r ↦ (1 / 2 : Real) *
          ((X.term (subseq (co.φ n))).S.base.metric (T - (r + a) ^ 2)).inner
            (mapped n (r + a)) (lVelocity (I := I) (mapped n) (r + a))
            (lVelocity (I := I) (mapped n) (r + a)) := by
      filter_upwards [hChartAE, hDiff n, hMem] with r hChartR hDiffR hr
      have hrcc : r ∈ Icc (0 : Real) len := ⟨hr.1.le, hr.2.le⟩
      have hsab : r + a ∈ Icc a b := by
        constructor
        · linarith [hrcc.1]
        · dsimp only [len] at hrcc
          linarith [hrcc.2]
      have hGrowAt := hn ⟨r + a, hsab⟩
      have hSource := bf.grow_subset (co.φ n) hGrowAt
      have hChi : bf.chi (co.φ n) (alpha n (r + a)) = 1 :=
        hOne _ (hGrowW hGrowAt)
      have hDiffR' : MDiffAt (alpha n) (r + a) := by
        simpa only [add_comm r a] using hDiffR
      have hExt := gSeqExt_inner_of_mem (I := I) Phi R bf hSrc hTgt
        (co.φ n) (T - (r + a) ^ 2) (alpha n (r + a)) hSource
        (lVelocity (I := I) (alpha n) (r + a))
        (lVelocity (I := I) (alpha n) (r + a))
      have hMap := lKinetic_map (I := I) Phi hSrc hTgt
        (co.φ n) (T - (r + a) ^ 2)
        (alpha n) (r + a) hSource hDiffR'
      have hExt' :
          (gSeqExt (I := I) Phi R bf hSrc hTgt
            (co.φ n) (T - (r + a) ^ 2)).inner
              (alpha n (r + a)) (lVelocity (I := I) (alpha n) (r + a))
              (lVelocity (I := I) (alpha n) (r + a)) =
            (srcMetric (I := I) Phi hSrc hTgt
              (co.φ n) (T - (r + a) ^ 2)).inner
              ⟨alpha n (r + a), hSource⟩
              (lVelocity (I := I) (alpha n) (r + a))
              (lVelocity (I := I) (alpha n) (r + a)) := by
        simpa only [hChi, one_smul, sub_self, zero_smul, add_zero] using hExt
      have hPhys :
          ((GSeq n).metric (T - (r + a) ^ 2)).inner
              (alpha n (r + a)) (lVelocity (I := I) (alpha n) (r + a))
              (lVelocity (I := I) (alpha n) (r + a)) =
            ((X.term (subseq (co.φ n))).S.base.metric (T - (r + a) ^ 2)).inner
              (mapped n (r + a)) (lVelocity (I := I) (mapped n) (r + a))
              (lVelocity (I := I) (mapped n) (r + a)) := by
        simpa only [GSeq, mapped, MetricConnectionFamily.restrict_metric,
          lcMetricFamily, SolutionOn.family_metric] using hExt'.trans hMap
      have hChartR' :
          inner Real
              (((1 / 2 : Real) • chartGramOp (I := I) (GSeq n) p
                ((fun s ↦ T - s ^ 2) (a + r), (u n).toFun r)) ((u n).deriv r))
              ((u n).deriv r) =
            (1 / 2 : Real) *
              ((GSeq n).metric (T - (r + a) ^ 2)).inner
                (alpha n (r + a)) (lVelocity (I := I) (alpha n) (r + a))
                (lVelocity (I := I) (alpha n) (r + a)) := by
        simpa only [Function.comp_apply] using hChartR.symm
      simpa only [tau, ContinuousLinearMap.smul_apply, real_inner_smul_left,
        Function.comp_apply] using
        hChartR'.trans (congrArg ((1 / 2 : Real) * ·) hPhys)
    have hInt : kinChart n =
        ∫ r in (0 : Real)..len, (1 / 2 : Real) *
          ((X.term (subseq (co.φ n))).S.base.metric (T - (r + a) ^ 2)).inner
            (mapped n (r + a)) (lVelocity (I := I) (mapped n) (r + a))
            (lVelocity (I := I) (mapped n) (r + a)) := by
      apply intervalIntegral.integral_congr_ae_restrict
      simpa only [kinChart, timeMeasure, uIoc_of_le hLen,
        restrict_Ioc_eq_restrict_Icc] using hPoint
    rw [hInt]
    let q : Real → Real := fun s ↦ (1 / 2 : Real) *
      ((X.term (subseq (co.φ n))).S.base.metric (T - s ^ 2)).inner
        (mapped n s) (lVelocity (I := I) (mapped n) s)
        (lVelocity (I := I) (mapped n) s)
    change (∫ r in (0 : Real)..len, q (r + a)) = ∫ s in a..b, q s
    simpa only [zero_add, len, sub_add_cancel] using
      (intervalIntegral.integral_comp_add_right q
        (a := 0) (b := b - a) a)
  have hKin : kinLim ≤ liminf kin atTop := by
    rw [hLimMetric]
    rw [Filter.liminf_congr hKinEq] at hKinRaw'
    exact hKinRaw'
  let scalarSeq : Nat → Icc a b → Real := fun n s ↦
    letI : TopologicalSpace (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).topology
    letI : ChartedSpace H (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).charted
    letI : T2Space (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).t2
    letI : IsManifold I ∞ (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).smooth
    letI : SigmaCompactSpace (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).sigmaCompact
    (X.term (subseq (co.φ n))).S.scalar (T - s.1 ^ 2) (mapped n s.1)
  let scalarLim : Icc a b → Real := fun s ↦
    L.S.scalar (T - s.1 ^ 2) (alphaLim s.1)
  have hScalarRaw := ConvOut.scalar_compOn (I := I) Phi R bf hSrc hTgt
    beta psi cLow hcLow hBound hCovTail co a b
    (fun s ↦ T - s.1 ^ 2) (fun n s ↦ alpha n s.1) (fun s ↦ alphaLim s.1)
    dP hTop halphaLim Q hQc (Eventually.of_forall hQ) hLimQ
    (fun s ↦ hBack s.2) hTime
  have hScalarEq :
      (fun s : Icc a b ↦
        metricScalarAt (I := I) (co.gInf (T - s.1 ^ 2)) (alphaLim s.1)) =
        scalarLim := by
    funext s
    change metricScalarAt (I := I) (co.gInf (T - s.1 ^ 2)) (alphaLim s.1) =
      metricScalarAt (I := I) (L.S.base.metric (T - s.1 ^ 2)) (alphaLim s.1)
    rw [← SolutionOn.family_metric,
      hLMetric (T - s.1 ^ 2) (hBack s.2)]
    rfl
  have hScalar : TendstoUniformly scalarSeq scalarLim atTop := by
    rw [← hScalarEq]
    simpa only [scalarSeq, mapped] using hScalarRaw
  let F : Nat → Real → Real := fun n s ↦
    letI : TopologicalSpace (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).topology
    letI : ChartedSpace H (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).charted
    letI : T2Space (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).t2
    letI : IsManifold I ∞ (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).smooth
    letI : SigmaCompactSpace (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).sigmaCompact
    2 * s ^ 2 * (X.term (subseq (co.φ n))).S.scalar
      (T - s ^ 2) (mapped n s)
  let f : Real → Real := fun s ↦
    2 * s ^ 2 * L.S.scalar (T - s ^ 2) (alphaLim s)
  have hScalarLimCont : ContinuousOn
      (fun s : Real ↦ L.S.scalar (T - s ^ 2) (alphaLim s)) (Icc a b) := by
    have hPair : ContinuousOn (fun s : Real ↦ (T - s ^ 2, alphaLim s))
        (Icc a b) :=
      (continuous_const.sub (continuous_id.pow 2)).continuousOn.prodMk hLimCont
    have hMaps : MapsTo (fun s : Real ↦ (T - s ^ 2, alphaLim s))
        (Icc a b) (X.D.carrier ×ˢ (univ : Set L.M)) :=
      fun _ hs ↦ ⟨hTime (hBack hs), mem_univ _⟩
    simpa only [Function.comp_def] using
      L.isSolution.scalarCont.comp hPair hMaps
  have hPotLimInt : IntervalIntegrable f volume a b := by
    have hCont : ContinuousOn f (Icc a b) := by
      exact (continuous_const.mul (continuous_id.pow 2)).continuousOn.mul
        hScalarLimCont
    have hCont' : ContinuousOn f [[a, b]] := by
      simpa only [uIcc_of_le hab] using hCont
    exact hCont'.intervalIntegrable
  have hFMeas : ∀ᶠ n in atTop,
      AEStronglyMeasurable (F n) (volume.restrict (uIoc a b)) := by
    filter_upwards [hGrow] with n hn
    letI : TopologicalSpace (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).topology
    letI : ChartedSpace H (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).charted
    letI : T2Space (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).t2
    letI : IsManifold I ∞ (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).smooth
    letI : SigmaCompactSpace (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).sigmaCompact
    have hSource : MapsTo (alpha n) (Icc a b) (Phi.source (co.φ n)) :=
      fun s hs ↦ bf.grow_subset (co.φ n) (hn ⟨s, hs⟩)
    have hMapC1 : ContMDiffOn 𝓘(Real, Real) I 1 (mapped n) (Icc a b) := by
      simpa only [mapped, PointedCGHMaps.map] using
        ((Phi.partialDiffeomorph (co.φ n)).contMDiffOn_toFun.of_le
          (by exact_mod_cast le_top)).comp (halpha n) hSource
    have hPair : ContinuousOn (fun s : Real ↦ (T - s ^ 2, mapped n s))
        (Icc a b) :=
      (continuous_const.sub (continuous_id.pow 2)).continuousOn.prodMk
        hMapC1.continuousOn
    have hMaps : MapsTo (fun s : Real ↦ (T - s ^ 2, mapped n s))
        (Icc a b)
        (X.D.carrier ×ˢ (univ : Set (X.term (subseq (co.φ n))).M)) :=
      fun _ hs ↦ ⟨hTime (hBack hs), mem_univ _⟩
    have hScCont : ContinuousOn
        (fun s : Real ↦ (X.term (subseq (co.φ n))).S.scalar
          (T - s ^ 2) (mapped n s)) (Icc a b) := by
      simpa only [Function.comp_def] using
        (X.term (subseq (co.φ n))).isSolution.scalarCont.comp hPair hMaps
    have hCont : ContinuousOn (F n) (Icc a b) := by
      simpa only [F, mapped] using
        (continuous_const.mul (continuous_id.pow 2)).continuousOn.mul hScCont
    simpa only [uIoc_of_le hab, F, mapped] using
      (hCont.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  obtain ⟨cSc, hcSc⟩ := isCompact_Icc.bddAbove_image hScalarLimCont.norm
  let CSc : Real := max cSc 0
  have hCSc0 : 0 ≤ CSc := le_max_right _ _
  have hCSc : ∀ s : Icc a b, ‖scalarLim s‖ ≤ CSc := by
    intro s
    exact (hcSc ⟨s.1, s.2, rfl⟩).trans (le_max_left _ _)
  let weight : Real → Real := fun s ↦ 2 * s ^ 2
  have hWeightCont : ContinuousOn weight (Icc a b) :=
    (continuous_const.mul (continuous_id.pow 2)).continuousOn
  obtain ⟨cW, hcW⟩ := isCompact_Icc.bddAbove_image hWeightCont.norm
  let CW : Real := max cW 0
  have hCW0 : 0 ≤ CW := le_max_right _ _
  have hCW : ∀ s : Icc a b, ‖weight s.1‖ ≤ CW := by
    intro s
    exact (hcW ⟨s.1, s.2, rfl⟩).trans (le_max_left _ _)
  let dom : Real → Real := fun _ ↦ CW * (CSc + 1)
  have hDomInt : IntervalIntegrable dom volume a b := intervalIntegrable_const
  have hClose := (Metric.tendstoUniformly_iff.mp hScalar) 1 zero_lt_one
  have hDom : ∀ᶠ n in atTop, ∀ᵐ s ∂volume,
      s ∈ uIoc a b → ‖F n s‖ ≤ dom s := by
    filter_upwards [hClose] with n hn
    exact ae_of_all _ fun s hs ↦ by
      have hsIcc : s ∈ Icc a b := by
        simpa only [uIcc_of_le hab] using uIoc_subset_uIcc hs
      let ss : Icc a b := ⟨s, hsIcc⟩
      have hd := (hn ss).le
      have hSeq : ‖scalarSeq n ss‖ ≤ CSc + 1 := by
        calc
          ‖scalarSeq n ss‖ ≤ ‖scalarLim ss‖ +
              ‖scalarSeq n ss - scalarLim ss‖ := norm_le_norm_add_norm_sub' _ _
          _ ≤ CSc + 1 := add_le_add (hCSc ss) (by
            simpa only [Real.dist_eq, Real.norm_eq_abs, abs_sub_comm] using hd)
      change ‖weight s * scalarSeq n ss‖ ≤ CW * (CSc + 1)
      rw [norm_mul]
      exact mul_le_mul (hCW ss) hSeq (norm_nonneg _) hCW0
  have hPointPot : ∀ᵐ s ∂volume, s ∈ uIoc a b →
      Tendsto (fun n ↦ F n s) atTop (nhds (f s)) := by
    exact ae_of_all _ fun s hs ↦ by
      have hsIcc : s ∈ Icc a b := by
        simpa only [uIcc_of_le hab] using uIoc_subset_uIcc hs
      let ss : Icc a b := ⟨s, hsIcc⟩
      have hAt := hScalar.tendsto_at ss
      change Tendsto (fun n ↦ weight s * scalarSeq n ss) atTop
        (nhds (weight s * scalarLim ss))
      exact tendsto_const_nhds.mul hAt
  have hPot : Tendsto pot atTop (nhds potLim) := by
    change Tendsto (fun n ↦ ∫ s in a..b, F n s) atTop
      (nhds (∫ s in a..b, f s))
    exact intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) dom hFMeas hDom hDomInt hPointPot
  have hSplit : act =ᶠ[atTop] fun n ↦ kin n + pot n := by
    filter_upwards [hGrow] with n hn
    letI : TopologicalSpace (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).topology
    letI : ChartedSpace H (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).charted
    letI : T2Space (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).t2
    letI : IsManifold I ∞ (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).smooth
    letI : SigmaCompactSpace (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).sigmaCompact
    letI : TopologicalSpace.MetrizableSpace
        (X.term (subseq (co.φ n))).M :=
      Manifold.metrizableSpace I (X.term (subseq (co.φ n))).M
    letI : UniformSpace (X.term (subseq (co.φ n))).M :=
      TopologicalSpace.pseudoMetrizableSpaceUniformity
        (X.term (subseq (co.φ n))).M
    have hSource : MapsTo (alpha n) (Icc a b) (Phi.source (co.φ n)) :=
      fun s hs ↦ bf.grow_subset (co.φ n) (hn ⟨s, hs⟩)
    have hMapC1 : ContMDiffOn 𝓘(Real, Real) I 1 (mapped n) (Icc a b) := by
      simpa only [mapped, PointedCGHMaps.map] using
        ((Phi.partialDiffeomorph (co.φ n)).contMDiffOn_toFun.of_le
          (by exact_mod_cast le_top)).comp (halpha n) hSource
    have hMet : MetricFamilySmoothOn (I := I)
        (M := (X.term (subseq (co.φ n))).M) X.D
        (X.term (subseq (co.φ n))).S.family.metric :=
      (X.term (subseq (co.φ n))).isSolution.smoothMetric
    have hSc : ScalarSTContOn (I := I)
        (M := (X.term (subseq (co.φ n))).M)
        (X.term (subseq (co.φ n))).S :=
      ⟨(X.term (subseq (co.φ n))).isSolution.scalarCont⟩
    have hLagInt := lRegLag_int_c1 (I := I)
      (X.term (subseq (co.φ n))).S hMet hSc T a b hab
      (mapped n) hMapC1 (fun s hs ↦ hReg (hBack hs))
    have hPotInt := lScalar_int (I := I) (X.term (subseq (co.φ n))).S
      hSc T a b (mapped n)
      (fun s hs ↦ hTime (hBack (by simpa only [uIcc_of_le hab] using hs)))
      (by simpa only [uIcc_of_le hab] using hMapC1.continuousOn)
    have hKinInt : IntervalIntegrable
        (fun s ↦ (1 / 2 : Real) *
          ((X.term (subseq (co.φ n))).S.base.metric (T - s ^ 2)).inner
            (mapped n s) (lVelocity (I := I) (mapped n) s)
            (lVelocity (I := I) (mapped n) s)) volume a b := by
      simpa only [lRegLag, add_sub_cancel_right] using hLagInt.sub hPotInt
    simpa only [act, kin, pot, lRegAction, lRegLag] using
      intervalIntegral.integral_add hKinInt hPotInt
  have hKinNonneg : ∀ n, 0 ≤ kin n := by
    intro n
    letI : TopologicalSpace (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).topology
    letI : ChartedSpace H (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).charted
    letI : T2Space (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).t2
    letI : IsManifold I ∞ (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).smooth
    letI : SigmaCompactSpace (X.term (subseq (co.φ n))).M :=
      (X.term (subseq (co.φ n))).sigmaCompact
    change 0 ≤ ∫ s in a..b, (1 / 2 : Real) *
      ((X.term (subseq (co.φ n))).S.base.metric (T - s ^ 2)).inner
        (mapped n s) (lVelocity (I := I) (mapped n) s)
        (lVelocity (I := I) (mapped n) s)
    apply intervalIntegral.integral_nonneg hab
    intro s _hs
    exact mul_nonneg (by norm_num)
      (by
        by_cases hv : lVelocity (I := I) (mapped n) s = 0
        · simp only [hv, map_zero]
          exact le_rfl
        · exact (((X.term (subseq (co.φ n))).S.base.metric
            (T - s ^ 2)).pos (mapped n s)
              (lVelocity (I := I) (mapped n) s) hv).le)
  have hKinLo : IsBoundedUnder (· ≥ ·) atTop kin :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall hKinNonneg)
  change IsBoundedUnder (· ≤ ·) atTop act at hAct
  have hKinHi : IsBoundedUnder (· ≤ ·) atTop kin := by
    rcases hAct with ⟨A, hA⟩
    change ∀ᶠ n in atTop, act n ≤ A at hA
    rcases hPot.isBoundedUnder_ge with ⟨B, hB⟩
    change ∀ᶠ n in atTop, pot n ≥ B at hB
    refine ⟨A - B, ?_⟩
    change ∀ᶠ n in atTop, kin n ≤ A - B
    filter_upwards [hA, hB, hSplit] with n hn hpn hsn
    rw [hsn] at hn
    linarith
  have hSum := pt_liminf_add hKin hKinLo hKinHi hPot
  have hLiminfAct : liminf act atTop =
      liminf (fun n ↦ kin n + pot n) atTop :=
    Filter.liminf_congr hSplit
  rw [← hLiminfAct] at hSum
  have hKinLimInt : IntervalIntegrable
      (fun s ↦ (1 / 2 : Real) *
        (L.S.base.metric (T - s ^ 2)).inner (alphaLim s)
          (lVelocity (I := I) alphaLim s) (lVelocity (I := I) alphaLim s))
      volume a b :=
    lKinetic_int_local L.S L.isSolution.smoothMetric T alphaLim p a b hab uLim
      hLimChart hLimRep hLimDiff (fun s hs ↦ hReg (hBack hs))
  have hLimSplit : lRegAction L.S T alphaLim a b = kinLim + potLim := by
    simpa only [lRegAction, lRegLag, kinLim, potLim] using
      intervalIntegral.integral_add hKinLimInt hPotLimInt
  change lRegAction L.S T alphaLim a b ≤ liminf act atTop
  rw [hLimSplit]
  exact hSum

end PointedAction

end DifferentialGeometry.HCGCompactness

end
