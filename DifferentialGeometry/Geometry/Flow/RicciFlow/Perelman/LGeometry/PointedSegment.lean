import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.PointedConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.SegmentValue

set_option autoImplicit false

/-!
# Pointed upper bounds for restricted L-segment values

This file transfers fixed-curve pointed L-action convergence to restricted
same-clock segment values when the transported curve is explicitly admissible.
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

section

variable [NeZero (Module.finrank Real E)] [I.Boundaryless]

/-- Under explicit eventual admissibility and a common scalar lower bound, the
restricted L-segment value of a transported fixed curve is eventually bounded
by its limiting L-action plus any positive error. -/
theorem lSegValue_limsup
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
    (T a b : Real) (ha : 0 ≤ a) (hab : a ≤ b)
    (alpha : Real → (L.atTime 0).M)
    (halpha : letI : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
      letI : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
      letI : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
      ContMDiff 𝓘(Real, Real) I 1 alpha)
    (hback : MapsTo (fun s ↦ T - s) (Icc a b) (Icc beta psi))
    (Ω : (k : Nat) → Set ((X.term (subseq (co.φ k))).M × Real)) (K : Real)
    (hregular : ∀ k,
      letI : TopologicalSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).topology
      RegularSpace (X.term (subseq (co.φ k))).M)
    (hconnected : ∀ k,
      letI : TopologicalSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).topology
      ConnectedSpace (X.term (subseq (co.φ k))).M)
    (hscalar : ∀ᶠ k in atTop,
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
      ∀ q ∈ Ω k, -K ≤ (X.term (subseq (co.φ k))).S.scalar q.2 q.1)
    (hseg : ∀ᶠ k in atTop,
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
      letI : RegularSpace (X.term (subseq (co.φ k))).M := hregular k
      letI : ConnectedSpace (X.term (subseq (co.φ k))).M := hconnected k
      IsLSegCurve (X.term (subseq (co.φ k))).S T (Ω k) a b
        (fun r ↦ Phi.map (co.φ k) (alpha r)))
    {ε : Real} (hε : 0 < ε) :
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
      letI : RegularSpace (X.term (subseq (co.φ k))).M := hregular k
      letI : ConnectedSpace (X.term (subseq (co.φ k))).M := hconnected k
      lSegValue (X.term (subseq (co.φ k))).S T (Ω k) a b
          (Phi.map (co.φ k) (alpha a)) (Phi.map (co.φ k) (alpha b)) <
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
        ((lLength L.S T alpha a b + ε : Real) : WithTop Real) := by
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
  have hconv := lLength_conv_curve (I := I) Phi R bf hsrc htgt beta psi cLow hcLow
    hbound hcovTail co htime hLmetric T a b hab alpha halpha hback
  have haction : ∀ᶠ k in atTop,
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
      lLength (X.term (subseq (co.φ k))).S T
        (fun r ↦ Phi.map (co.φ k) (alpha r)) a b <
          lLength L.S T alpha a b + ε := by
    exact hconv.eventually_lt_const (by linarith)
  filter_upwards [hscalar, hseg, haction] with k hscalar_k hseg_k haction_k
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
  letI : RegularSpace (X.term (subseq (co.φ k))).M := hregular k
  letI : ConnectedSpace (X.term (subseq (co.φ k))).M := hconnected k
  calc
    lSegValue (X.term (subseq (co.φ k))).S T (Ω k) a b
        (Phi.map (co.φ k) (alpha a)) (Phi.map (co.φ k) (alpha b)) ≤
        (lLength (X.term (subseq (co.φ k))).S T
          (fun r ↦ Phi.map (co.φ k) (alpha r)) a b : WithTop Real) := by
      exact lSegValue_le (X.term (subseq (co.φ k))).S T K (Ω k) ha hab hscalar_k
        _ _ _ hseg_k rfl rfl
    _ < ((lLength L.S T alpha a b + ε : Real) : WithTop Real) :=
      WithTop.coe_lt_coe.mpr haction_k

end

end DifferentialGeometry.HCGCompactness
