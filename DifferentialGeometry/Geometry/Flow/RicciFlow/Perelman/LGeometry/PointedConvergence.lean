import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.KineticConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.ScalarConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.PointedAction
import DifferentialGeometry.Analysis.Calculus.MapConvergenceComp

set_option autoImplicit false

/-!
# Pointed convergence of Perelman's L-action

This file assembles the compact-exhaustion, scalar, and kinetic producers for
one fixed curve under pointed smooth Ricci-flow convergence.
-/

noncomputable section

namespace DifferentialGeometry.HCGCompactness

open Bundle Filter MeasureTheory Set
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

/-- Along a fixed `C¹` curve, compact exhaustion identifies the kinetic
quadratic form of the extended pointed metric with that of the actually
transported curve.  Hence zeroth-order pointed metric convergence gives
uniform convergence of the transported kinetic term. -/
theorem ConvOut.mapKin_convOn
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat → Nat}
    (Phi : PointedCGHMaps (I := I) X P subseq)
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Phi) (hsrc : SrcSigma Phi) (htgt : TgtSigma Phi)
    (beta psi : Real) (co : ConvOut (I := I) Phi R bf hsrc htgt beta psi)
    (T a b : Real) (alpha : Real → P.M)
    (halpha : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      ContMDiff 𝓘(Real, Real) I 1 alpha)
    (hback : MapsTo (fun s ↦ T - s) (Icc a b) (Icc beta psi)) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    TendstoUniformlyOn
      (fun k s ↦
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
        ((X.term (subseq (co.φ k))).S.family.metric (T - s)).inner
          (Phi.map (co.φ k) (alpha s))
          (lVelocity (I := I) (fun r ↦ Phi.map (co.φ k) (alpha r)) s)
          (lVelocity (I := I) (fun r ↦ Phi.map (co.φ k) (alpha r)) s))
      (fun s ↦
        (co.gInf (T - s)).inner (alpha s)
          (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s))
      atTop (Icc a b) := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  have hkin := ConvOut.kinetic_convOn (I := I) Phi R bf hsrc htgt beta psi co
    T a b alpha halpha hback
  let K : Set P.M := alpha '' Icc a b
  have hK : IsCompact K :=
    isCompact_Icc.image_of_continuousOn halpha.continuous.continuousOn
  obtain ⟨k0, hk0⟩ := bf.grow_cover K hK
  apply hkin.congr
  filter_upwards [Filter.eventually_ge_atTop k0] with k hk
  intro s hs
  have hphi : k0 ≤ co.φ k := hk.trans (co.hφ.id_le k)
  have hgrow : alpha s ∈ bf.grow (co.φ k) :=
    hk0 (co.φ k) hphi ⟨s, hs, rfl⟩
  have hsource : alpha s ∈ Phi.source (co.φ k) :=
    bf.grow_subset (co.φ k) hgrow
  obtain ⟨W, _hWopen, hgrowW, hWone⟩ := bf.chi_one (co.φ k)
  have hchi : bf.chi (co.φ k) (alpha s) = 1 := hWone _ (hgrowW hgrow)
  letI : TopologicalSpace (SourceDomain (I := I) Phi (co.φ k)) :=
    sourceDomTop (I := I) Phi (co.φ k)
  letI : ChartedSpace H (SourceDomain (I := I) Phi (co.φ k)) :=
    sourceDomCharted (I := I) Phi (co.φ k)
  letI : IsManifold I ∞ (SourceDomain (I := I) Phi (co.φ k)) :=
    sourceDomSmooth (I := I) Phi (co.φ k)
  letI : TopologicalSpace (X.term (subseq (co.φ k))).M :=
    (X.term (subseq (co.φ k))).topology
  letI : ChartedSpace H (X.term (subseq (co.φ k))).M :=
    (X.term (subseq (co.φ k))).charted
  letI : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
    (X.term (subseq (co.φ k))).smooth
  have hext :
      (gSeqExt (I := I) Phi R bf hsrc htgt (co.φ k) (T - s)).inner
          (alpha s) (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s) =
        (srcMetric (I := I) Phi hsrc htgt (co.φ k) (T - s)).inner
          ⟨alpha s, hsource⟩
          (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s) := by
    rw [gSeqExt_inner_of_mem (I := I) Phi R bf hsrc htgt
      (co.φ k) (T - s) (alpha s) hsource]
    simp only [hchi, one_smul, sub_self, zero_smul, add_zero]
  have hdiff : MDifferentiableAt 𝓘(Real, Real) I alpha s :=
    halpha.contMDiffAt.mdifferentiableAt (by norm_num)
  have hmap := lKinetic_map (I := I) Phi hsrc htgt (co.φ k) (T - s)
    alpha s hsource hdiff
  simpa only [Function.comp_apply] using hext.trans hmap

private theorem density_ae_bound
    {rSeq qSeq : Nat → Real → Real} {rLim qLim : Real → Real}
    {a b : Real}
    (hr : TendstoUniformlyOn rSeq rLim atTop (Icc a b))
    (hq : TendstoUniformlyOn qSeq qLim atTop (Icc a b))
    (hrc : ContinuousOn rLim (Icc a b))
    (hqc : ContinuousOn qLim (Icc a b)) :
    ∃ C : Real, ∀ᶠ k in atTop,
      ∀ᵐ s ∂volume.restrict (Ioc a b),
        ‖Real.sqrt s * (rSeq k s + qSeq k s)‖ ≤ C := by
  obtain ⟨Cr0, hCr0⟩ := isCompact_Icc.bddAbove_image hrc.norm
  obtain ⟨Cq0, hCq0⟩ := isCompact_Icc.bddAbove_image hqc.norm
  obtain ⟨Cs0, hCs0⟩ := isCompact_Icc.bddAbove_image
    Real.continuous_sqrt.norm.continuousOn
  let Cr : Real := max Cr0 0
  let Cq : Real := max Cq0 0
  let Cs : Real := max Cs0 0
  have hCr_nonneg : 0 ≤ Cr := le_max_right _ _
  have hCq_nonneg : 0 ≤ Cq := le_max_right _ _
  have hCs_nonneg : 0 ≤ Cs := le_max_right _ _
  have hCr : ∀ s ∈ Icc a b, ‖rLim s‖ ≤ Cr := by
    intro s hs
    exact (hCr0 ⟨s, hs, rfl⟩).trans (le_max_left _ _)
  have hCq : ∀ s ∈ Icc a b, ‖qLim s‖ ≤ Cq := by
    intro s hs
    exact (hCq0 ⟨s, hs, rfl⟩).trans (le_max_left _ _)
  have hCs : ∀ s ∈ Icc a b, ‖Real.sqrt s‖ ≤ Cs := by
    intro s hs
    exact (hCs0 ⟨s, hs, rfl⟩).trans (le_max_left _ _)
  have hrSeq := TendstoUniformlyOn.eventually_norm_le hr hCr
  have hqSeq := TendstoUniformlyOn.eventually_norm_le hq hCq
  refine ⟨Cs * ((Cr + 1) + (Cq + 1)), ?_⟩
  filter_upwards [hrSeq, hqSeq] with k hrk hqk
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have hsIcc : s ∈ Icc a b := ⟨hs.1.le, hs.2⟩
  have hsum : ‖rSeq k s + qSeq k s‖ ≤ (Cr + 1) + (Cq + 1) :=
    (norm_add_le _ _).trans (add_le_add (hrk s hsIcc) (hqk s hsIcc))
  rw [norm_mul]
  exact mul_le_mul (hCs s hsIcc) hsum (norm_nonneg _)
    hCs_nonneg

section ActionLimit

variable [NeZero (Module.finrank Real E)] [I.Boundaryless]

/-- On a fixed compact backward-time interval, the L-length of a fixed `C¹`
curve converges to its limit-flow L-length under pointed smooth flow
convergence, provided the native scalar-curvature convergence inputs hold and
the limit metric is the realized pointed limit. -/
theorem lLength_conv_curve
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    {subseq : Nat → Nat}
    (Phi : PointedCGHMaps (I := I) X (L.atTime 0) subseq)
    (R : letI : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
      letI : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
      letI : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
      SmoothRiemannianMetric I (L.atTime 0).M)
    (bf : BumpFamily (I := I) Phi) (hsrc : SrcSigma Phi) (htgt : TgtSigma Phi)
    (beta psi : Real) (cLow : Real) (hcLow : 0 < cLow)
    (hbound : letI : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
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
            (srcMetric (I := I) Phi hsrc htgt k t).inner y v v)
    (hcovTail : letI : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
        letI : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
        letI : T2Space (L.atTime 0).M := (L.atTime 0).t2
        letI : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
        letI : SigmaCompactSpace (L.atTime 0).M := (L.atTime 0).sigmaCompact
      ∀ q : Nat, ∃ C : Real, ∀ (k : Nat) (t : Real), t ∈ Icc beta psi →
        ∀ z : (L.atTime 0).M, z ∈ bf.grow k →
          metricCovDerivNorm (I := I) q
            (gSeqExt (I := I) Phi R bf hsrc htgt k t) R z ≤ C)
    (co : ConvOut (I := I) Phi R bf hsrc htgt beta psi)
    (htime : Icc beta psi ⊆ X.D.carrier)
    (hLmetric : letI : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
        letI : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
        letI : T2Space (L.atTime 0).M := (L.atTime 0).t2
        letI : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
        letI : SigmaCompactSpace (L.atTime 0).M := (L.atTime 0).sigmaCompact
        letI : TopologicalSpace L.M := L.topology
        letI : ChartedSpace H L.M := L.charted
        letI : T2Space L.M := L.t2
        letI : IsManifold I ∞ L.M := L.smooth
        letI : SigmaCompactSpace L.M := L.sigmaCompact
      ∀ t ∈ Icc beta psi, L.S.family.metric t = co.gInf t)
    (T a b : Real) (hab : a ≤ b) (alpha : Real → (L.atTime 0).M)
    (halpha : letI : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
      letI : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
      letI : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
      ContMDiff 𝓘(Real, Real) I 1 alpha)
    (hback : MapsTo (fun s ↦ T - s) (Icc a b) (Icc beta psi)) :
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
        lLength (I := I) (X.term (subseq (co.φ k))).S T
          (fun r ↦ Phi.map (co.φ k) (alpha r)) a b)
      atTop
      (𝓝 <|
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
        lLength (I := I) L.S T alpha a b) := by
  letI : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
  letI : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
  letI : T2Space (L.atTime 0).M := (L.atTime 0).t2
  letI : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (L.atTime 0).M := by
    change IsManifold I ∞ (L.atTime 0).M
    infer_instance
  letI : SigmaCompactSpace (L.atTime 0).M := (L.atTime 0).sigmaCompact
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : T2Space L.M := L.t2
  letI : IsManifold I ∞ L.M := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.M := by
    change IsManifold I ∞ L.M
    infer_instance
  letI : SigmaCompactSpace L.M := L.sigmaCompact
  let Phi' := Phi.compSubseq co.φ co.hφ
  let scalarSeq : Nat → Real → Real := fun k s ↦
    letI : TopologicalSpace (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).topology
    letI : ChartedSpace H (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).charted
    letI : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).smooth
    letI : SigmaCompactSpace (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).sigmaCompact
    letI : T2Space (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).t2
    (X.term (subseq (co.φ k))).S.scalar (T - s)
      (Phi.map (co.φ k) (alpha s))
  let kineticSeq : Nat → Real → Real := fun k s ↦
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
    ((X.term (subseq (co.φ k))).S.family.metric (T - s)).inner
      (Phi.map (co.φ k) (alpha s))
      (lVelocity (I := I) (fun r ↦ Phi.map (co.φ k) (alpha r)) s)
      (lVelocity (I := I) (fun r ↦ Phi.map (co.φ k) (alpha r)) s)
  let scalarLim : Real → Real := fun s ↦ L.S.scalar (T - s) (alpha s)
  let kineticLim : Real → Real := fun s ↦
    (L.S.base.metric (T - s)).inner (alpha s)
      (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s)
  let densitySeq : Nat → Real → Real := fun k s ↦
    Real.sqrt s * (scalarSeq k s + kineticSeq k s)
  let K : Set L.M := alpha '' Icc a b
  have hK : IsCompact K :=
    isCompact_Icc.image_of_continuousOn halpha.continuous.continuousOn
  have hScalarRaw : TendstoUniformlyOn scalarSeq
      (fun s ↦ metricScalarAt (I := I) (co.gInf (T - s)) (alpha s))
      atTop (Icc a b) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro epsilon hepsilon
    obtain ⟨k0, hk0⟩ := ConvOut.scalar_convOn (I := I) Phi R bf hsrc htgt
      beta psi cLow hcLow hbound hcovTail co K hK epsilon hepsilon
    filter_upwards [Filter.eventually_ge_atTop k0] with k hk
    intro s hs
    simpa only [scalarSeq, Function.comp_apply, Real.dist_eq, abs_sub_comm] using
      hk0 k hk (T - s) (hback hs) (alpha s) ⟨s, hs, rfl⟩
  have hScalar : TendstoUniformlyOn scalarSeq scalarLim atTop (Icc a b) :=
    hScalarRaw.congr_right fun s hs ↦ by
      change metricScalarAt (I := I) (co.gInf (T - s)) (alpha s) =
        metricScalarAt (I := I) (L.S.base.metric (T - s)) (alpha s)
      rw [← SolutionOn.family_metric, hLmetric (T - s) (hback hs)]
      rfl
  have hKineticRaw := ConvOut.mapKin_convOn (I := I) Phi R bf hsrc htgt
    beta psi co T a b alpha halpha hback
  have hKinetic : TendstoUniformlyOn kineticSeq kineticLim atTop (Icc a b) := by
    simpa only [kineticSeq, kineticLim, Function.comp_apply] using
      hKineticRaw.congr_right (fun s hs ↦ by
        change (co.gInf (T - s)).inner (alpha s)
            (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s) =
          (L.S.base.metric (T - s)).inner (alpha s)
            (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s)
        rw [← SolutionOn.family_metric, hLmetric (T - s) (hback hs)]
        rfl)
  have hbackCarrier : MapsTo (fun s ↦ T - s) (Icc a b) X.D.carrier :=
    fun _ hs ↦ htime (hback hs)
  have hScalarCont : ContinuousOn scalarLim (Icc a b) := by
    have hpair : ContinuousOn (fun s : Real ↦ (T - s, alpha s)) (Icc a b) :=
      ((continuous_const.sub continuous_id).prodMk halpha.continuous).continuousOn
    have hmaps : MapsTo (fun s : Real ↦ (T - s, alpha s)) (Icc a b)
        (X.D.carrier ×ˢ (univ : Set L.M)) :=
      fun _ hs ↦ ⟨hbackCarrier hs, mem_univ _⟩
    simpa only [scalarLim] using L.isSolution.scalarCont.comp hpair hmaps
  have hKineticCont : ContinuousOn kineticLim (Icc a b) := by
    have hcont := lSpeedSq_contOn L.S T a b alpha L.isSolution.smoothMetric
      halpha (by simpa only [uIcc_of_le hab] using hbackCarrier)
    simpa only [kineticLim, lSpeedSq, uIcc_of_le hab] using hcont
  have hDensityBound : ∃ C : Real, ∀ᶠ k in atTop,
      ∀ᵐ s ∂volume.restrict (Ioc a b), ‖densitySeq k s‖ ≤ C := by
    simpa only [densitySeq] using
      density_ae_bound hScalar hKinetic hScalarCont hKineticCont
  obtain ⟨kgrow, hkgrow⟩ := bf.grow_cover K hK
  have hDensityMeas : ∀ᶠ k in atTop,
      AEStronglyMeasurable (densitySeq k) (volume.restrict (Ioc a b)) := by
    filter_upwards [Filter.eventually_ge_atTop kgrow] with k hk
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
    have hphi : kgrow ≤ co.φ k := hk.trans (co.hφ.id_le k)
    have hsrcCurve : MapsTo alpha (Ioo a b) (Phi.source (co.φ k)) := by
      intro s hs
      exact bf.grow_subset (co.φ k)
        (hkgrow (co.φ k) hphi ⟨s, Ioo_subset_Icc_self hs, rfl⟩)
    have hcurve : ContMDiffOn 𝓘(Real, Real) I 1
        (fun r ↦ Phi.map (co.φ k) (alpha r)) (Ioo a b) :=
      ((Phi.partialDiffeomorph (co.φ k)).contMDiffOn_toFun.of_le
        (by exact_mod_cast le_top)).comp
        halpha.contMDiffOn hsrcCurve
    have hmeas := lDensity_aemeas (I := I)
      (X.term (subseq (co.φ k))).S T a b
      (fun r ↦ Phi.map (co.φ k) (alpha r))
      (X.term (subseq (co.φ k))).isSolution.smoothMetric
      (X.term (subseq (co.φ k))).isSolution.scalarCont
      hcurve (fun _ hs ↦ htime (hback (Ioo_subset_Icc_self hs)))
    simpa only [densitySeq, scalarSeq, kineticSeq, lDensity, lSpeedSq,
      Function.comp_apply, SolutionOn.family_metric] using hmeas
  have hfinal := lLength_tendsto (I := I) Phi' T a b hab alpha
  simpa only [Phi', PointedCGHMaps.compSubseq_map, Function.comp_apply] using
    hfinal hScalar hKinetic hDensityMeas hDensityBound

end ActionLimit

end DifferentialGeometry.HCGCompactness
