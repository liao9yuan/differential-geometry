import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.PointedMaps
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.MetricExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Defs
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false

/-!
# Pointed pullback identities for Perelman's L-action

This file records the local velocity chain rule and the resulting kinetic
identity on a pointed Cheeger--Gromov source domain.  It also turns explicit
uniform scalar and kinetic convergence along a fixed curve into convergence of
its L-length.  Producing those uniform inputs from Cheeger--Gromov convergence
remains a separate frontier.
-/

noncomputable section

namespace DifferentialGeometry.HCGCompactness

open Bundle Filter MeasureTheory Set
open scoped Manifold ContDiff Topology

open DifferentialGeometry.PDE.RicciFlow.Perelman

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

/-- At a differentiability point of a source-domain curve and of the pointed
source map, the velocity of the mapped curve is the differential of the map
applied to the source velocity. -/
theorem lVelocity_src_map
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat → Nat}
    {Phi : PointedCGHMaps (I := I) X P subseq} {k : Nat}
    (D : SourceDomainMetricData (I := I) Phi k)
    (alpha : Real → SourceDomain (I := I) Phi k) (s : Real)
    (hmap :
      letI : TopologicalSpace (SourceDomain (I := I) Phi k) := D.topology
      letI : ChartedSpace H (SourceDomain (I := I) Phi k) := D.charted
      letI : IsManifold I ∞ (SourceDomain (I := I) Phi k) := D.smooth
      letI : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M :=
        (X.term (subseq k)).charted
      letI : IsManifold I ∞ (X.term (subseq k)).M :=
        (X.term (subseq k)).smooth
      MDifferentiableAt I I
        (fun y : SourceDomain (I := I) Phi k ↦ Phi.map k (y : P.M))
        (alpha s))
    (halpha :
      letI : TopologicalSpace (SourceDomain (I := I) Phi k) := D.topology
      letI : ChartedSpace H (SourceDomain (I := I) Phi k) := D.charted
      letI : IsManifold I ∞ (SourceDomain (I := I) Phi k) := D.smooth
      MDifferentiableAt 𝓘(Real, Real) I alpha s) :
    letI : TopologicalSpace (SourceDomain (I := I) Phi k) := D.topology
    letI : ChartedSpace H (SourceDomain (I := I) Phi k) := D.charted
    letI : IsManifold I ∞ (SourceDomain (I := I) Phi k) := D.smooth
    letI : TopologicalSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).topology
    letI : ChartedSpace H (X.term (subseq k)).M :=
      (X.term (subseq k)).charted
    letI : IsManifold I ∞ (X.term (subseq k)).M :=
      (X.term (subseq k)).smooth
    lVelocity (I := I) (fun r ↦ Phi.map k (alpha r : P.M)) s =
      mfderiv I I
        (fun y : SourceDomain (I := I) Phi k ↦ Phi.map k (y : P.M))
        (alpha s) (lVelocity (I := I) alpha s) := by
  letI : TopologicalSpace (SourceDomain (I := I) Phi k) := D.topology
  letI : ChartedSpace H (SourceDomain (I := I) Phi k) := D.charted
  letI : IsManifold I ∞ (SourceDomain (I := I) Phi k) := D.smooth
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  letI : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  letI : IsManifold I ∞ (X.term (subseq k)).M :=
    (X.term (subseq k)).smooth
  simpa only [lVelocity] using
    (mfderiv_comp_apply (I := 𝓘(Real, Real)) (I' := I) (I'' := I)
      (x := s) (f := alpha)
      (g := fun y : SourceDomain (I := I) Phi k ↦ Phi.map k (y : P.M))
      hmap halpha (1 : Real))

/-- The kinetic inner product of a source-domain curve in the pulled-back
metric equals the kinetic inner product of its pointed image in the term
metric, at every point where the two maps in the velocity chain are
differentiable. -/
theorem lKinetic_src_pull
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat → Nat}
    {Phi : PointedCGHMaps (I := I) X P subseq} {k : Nat}
    (D : SourceDomainMetricData (I := I) Phi k)
    (t : Real) (alpha : Real → SourceDomain (I := I) Phi k) (s : Real)
    (hmap :
      letI : TopologicalSpace (SourceDomain (I := I) Phi k) := D.topology
      letI : ChartedSpace H (SourceDomain (I := I) Phi k) := D.charted
      letI : IsManifold I ∞ (SourceDomain (I := I) Phi k) := D.smooth
      letI : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M :=
        (X.term (subseq k)).charted
      letI : IsManifold I ∞ (X.term (subseq k)).M :=
        (X.term (subseq k)).smooth
      MDifferentiableAt I I
        (fun y : SourceDomain (I := I) Phi k ↦ Phi.map k (y : P.M))
        (alpha s))
    (halpha :
      letI : TopologicalSpace (SourceDomain (I := I) Phi k) := D.topology
      letI : ChartedSpace H (SourceDomain (I := I) Phi k) := D.charted
      letI : IsManifold I ∞ (SourceDomain (I := I) Phi k) := D.smooth
      MDifferentiableAt 𝓘(Real, Real) I alpha s) :
    letI : TopologicalSpace (SourceDomain (I := I) Phi k) := D.topology
    letI : ChartedSpace H (SourceDomain (I := I) Phi k) := D.charted
    letI : T2Space (SourceDomain (I := I) Phi k) := D.t2
    letI : IsManifold I ∞ (SourceDomain (I := I) Phi k) := D.smooth
    letI : SigmaCompactSpace (SourceDomain (I := I) Phi k) := D.sigmaCompact
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    letI : TopologicalSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).topology
    letI : ChartedSpace H (X.term (subseq k)).M :=
      (X.term (subseq k)).charted
    letI : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
    letI : IsManifold I ∞ (X.term (subseq k)).M :=
      (X.term (subseq k)).smooth
    letI : SigmaCompactSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).sigmaCompact
    (D.pullbackMetric t).inner (alpha s)
        (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s) =
      ((X.term (subseq k)).S.family.metric t).inner
        (Phi.map k (alpha s : P.M))
        (lVelocity (I := I) (fun r ↦ Phi.map k (alpha r : P.M)) s)
        (lVelocity (I := I) (fun r ↦ Phi.map k (alpha r : P.M)) s) := by
  letI : TopologicalSpace (SourceDomain (I := I) Phi k) := D.topology
  letI : ChartedSpace H (SourceDomain (I := I) Phi k) := D.charted
  letI : T2Space (SourceDomain (I := I) Phi k) := D.t2
  letI : IsManifold I ∞ (SourceDomain (I := I) Phi k) := D.smooth
  letI : SigmaCompactSpace (SourceDomain (I := I) Phi k) := D.sigmaCompact
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) P.M := by
    change IsManifold I ∞ P.M
    infer_instance
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  letI : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  letI : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
  letI : IsManifold I ∞ (X.term (subseq k)).M :=
    (X.term (subseq k)).smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term (subseq k)).M := by
    change IsManifold I ∞ (X.term (subseq k)).M
    infer_instance
  letI : SigmaCompactSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).sigmaCompact
  rw [D.pullback_inner]
  rw [lVelocity_src_map (I := I) D alpha s hmap halpha]

/-- On the canonical pointed source domain, the source kinetic quadratic form
equals the term-flow kinetic form of the ambient mapped curve at every source
point where the curve is differentiable. -/
theorem lKinetic_map
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat → Nat}
    (Phi : PointedCGHMaps (I := I) X P subseq)
    (hsrc : SrcSigma Phi) (htgt : TgtSigma Phi)
    (k : Nat) (t : Real) (alpha : Real → P.M) (s : Real)
    (hs : letI : TopologicalSpace P.M := P.topology
      alpha s ∈ Phi.source k)
    (halpha : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      MDifferentiableAt 𝓘(Real, Real) I alpha s) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    letI : TopologicalSpace (SourceDomain (I := I) Phi k) :=
      sourceDomTop (I := I) Phi k
    letI : ChartedSpace H (SourceDomain (I := I) Phi k) :=
      sourceDomCharted (I := I) Phi k
    letI : T2Space (SourceDomain (I := I) Phi k) := sourceDomT2 (I := I) Phi k
    letI : IsManifold I ∞ (SourceDomain (I := I) Phi k) :=
      sourceDomSmooth (I := I) Phi k
    letI : SigmaCompactSpace (SourceDomain (I := I) Phi k) :=
      sourceDomSigmaOf (I := I) Phi k (hsrc k)
    letI : TopologicalSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).topology
    letI : ChartedSpace H (X.term (subseq k)).M :=
      (X.term (subseq k)).charted
    letI : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
    letI : IsManifold I ∞ (X.term (subseq k)).M :=
      (X.term (subseq k)).smooth
    letI : SigmaCompactSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).sigmaCompact
    (srcMetric (I := I) Phi hsrc htgt k t).inner ⟨alpha s, hs⟩
        (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s) =
      ((X.term (subseq k)).S.family.metric t).inner
        (Phi.map k (alpha s))
        (lVelocity (I := I) (fun r ↦ Phi.map k (alpha r)) s)
        (lVelocity (I := I) (fun r ↦ Phi.map k (alpha r)) s) := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) P.M := by
    change IsManifold I ∞ P.M
    infer_instance
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  letI : TopologicalSpace (SourceDomain (I := I) Phi k) :=
    sourceDomTop (I := I) Phi k
  letI : ChartedSpace H (SourceDomain (I := I) Phi k) :=
    sourceDomCharted (I := I) Phi k
  letI : T2Space (SourceDomain (I := I) Phi k) := sourceDomT2 (I := I) Phi k
  letI : IsManifold I ∞ (SourceDomain (I := I) Phi k) :=
    sourceDomSmooth (I := I) Phi k
  letI : SigmaCompactSpace (SourceDomain (I := I) Phi k) :=
    sourceDomSigmaOf (I := I) Phi k (hsrc k)
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  letI : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  letI : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
  letI : IsManifold I ∞ (X.term (subseq k)).M :=
    (X.term (subseq k)).smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term (subseq k)).M := by
    change IsManifold I ∞ (X.term (subseq k)).M
    infer_instance
  letI : SigmaCompactSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).sigmaCompact
  let D : SourceDomainMetricData (I := I) Phi k :=
    SourceDomainMetricData.ofRestrictPullback (I := I) (hsrc k) (htgt k)
      (fun _ ↦ refRes (I := I) Phi P.metric hsrc k) (fun _ ↦ P.metric)
  have hmetric :
      srcMetric (I := I) Phi hsrc htgt k t = D.pullbackMetric t := by
    simpa only [srcMetric] using
      sourceFlow_metric_eq (I := I) Phi k (hsrc k) (htgt k)
        (fun _ ↦ refRes (I := I) Phi P.metric hsrc k) (fun _ ↦ P.metric) t
  have hmap : MDifferentiableAt I I (fun x : P.M ↦ Phi.map k x) (alpha s) := by
    exact ((Phi.partialDiffeomorph k).contMDiffOn_toFun.contMDiffAt
      ((Phi.partialDiffeomorph k).open_source.mem_nhds hs)).mdifferentiableAt (by simp)
  have hinc : MDifferentiableAt I I
      (fun y : SourceDomain (I := I) Phi k ↦ (y : P.M)) ⟨alpha s, hs⟩ := by
    exact (contMDiff_subtype_val (I := I) (n := (∞ : WithTop ℕ∞))
      (U := sourceOpen (I := I) Phi k)).contMDiffAt.mdifferentiableAt (by simp)
  have hsub :
      mfderiv I I
          (fun y : SourceDomain (I := I) Phi k ↦ Phi.map k (y : P.M))
          ⟨alpha s, hs⟩ (lVelocity (I := I) alpha s) =
        mfderiv I I (fun x : P.M ↦ Phi.map k x) (alpha s)
          (lVelocity (I := I) alpha s) := by
    have hchain := mfderiv_comp_apply (I := I) (I' := I) (I'' := I)
      (x := ⟨alpha s, hs⟩)
      (f := fun y : SourceDomain (I := I) Phi k ↦ (y : P.M))
      (g := fun x : P.M ↦ Phi.map k x) hmap hinc
      (lVelocity (I := I) alpha s)
    have hval :
        mfderiv I I (fun y : SourceDomain (I := I) Phi k ↦ (y : P.M))
            ⟨alpha s, hs⟩ (lVelocity (I := I) alpha s) =
          lVelocity (I := I) alpha s := by
      simpa only using
        mfderiv_subtype_val_apply (I := I) (sourceOpen (I := I) Phi k)
          ⟨alpha s, hs⟩ (lVelocity (I := I) alpha s)
    rw [hval] at hchain
    simpa only [Function.comp_apply] using hchain
  have hvel :
      lVelocity (I := I) (fun r ↦ Phi.map k (alpha r)) s =
        mfderiv I I (fun x : P.M ↦ Phi.map k x) (alpha s)
          (lVelocity (I := I) alpha s) := by
    simpa only [lVelocity] using
      (mfderiv_comp_apply (I := 𝓘(Real, Real)) (I' := I) (I'' := I)
        (x := s) (f := alpha) (g := fun x : P.M ↦ Phi.map k x)
        hmap halpha (1 : Real))
  have hpull := D.pullback_inner t ⟨alpha s, hs⟩
    (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s)
  rw [hmetric]
  calc
    _ = ((X.term (subseq k)).S.family.metric t).inner
          (Phi.map k (↑(⟨alpha s, hs⟩ : SourceDomain (I := I) Phi k) : P.M))
          (mfderiv I I
            (fun y : SourceDomain (I := I) Phi k ↦ Phi.map k (y : P.M))
            ⟨alpha s, hs⟩ (lVelocity (I := I) alpha s))
          (mfderiv I I
            (fun y : SourceDomain (I := I) Phi k ↦ Phi.map k (y : P.M))
            ⟨alpha s, hs⟩ (lVelocity (I := I) alpha s)) := hpull
    _ = _ := by rw [hsub, hvel]

/-- Uniform convergence of the scalar and kinetic terms along a fixed curve,
together with a uniform measurable density bound, implies convergence of its
L-lengths. -/
theorem lLength_tendsto
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    {subseq : Nat → Nat}
    (Phi : PointedCGHMaps (I := I) X (L.atTime 0) subseq)
    (T a b : Real) (hab : a ≤ b) (alpha : Real → L.M) :
    let scalarSeq : Nat → Real → Real := fun k s =>
      letI : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M :=
        (X.term (subseq k)).charted
      letI : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
      letI : IsManifold I ∞ (X.term (subseq k)).M :=
        (X.term (subseq k)).smooth
      letI : SigmaCompactSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).sigmaCompact
      (X.term (subseq k)).S.scalar (T - s) (Phi.map k (alpha s))
    let kineticSeq : Nat → Real → Real := fun k s =>
      letI : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M :=
        (X.term (subseq k)).charted
      letI : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
      letI : IsManifold I ∞ (X.term (subseq k)).M :=
        (X.term (subseq k)).smooth
      letI : SigmaCompactSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).sigmaCompact
      ((X.term (subseq k)).S.base.metric (T - s)).inner
        (Phi.map k (alpha s))
        (lVelocity (I := I) (fun r => Phi.map k (alpha r)) s)
        (lVelocity (I := I) (fun r => Phi.map k (alpha r)) s)
    let scalarLim : Real → Real := fun s =>
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : T2Space L.M := L.t2
      letI : IsManifold I ∞ L.M := L.smooth
      letI : SigmaCompactSpace L.M := L.sigmaCompact
      L.S.scalar (T - s) (alpha s)
    let kineticLim : Real → Real := fun s =>
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : T2Space L.M := L.t2
      letI : IsManifold I ∞ L.M := L.smooth
      letI : SigmaCompactSpace L.M := L.sigmaCompact
      (L.S.base.metric (T - s)).inner (alpha s)
        (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s)
    let densitySeq : Nat → Real → Real := fun k s =>
      Real.sqrt s * (scalarSeq k s + kineticSeq k s)
    TendstoUniformlyOn scalarSeq scalarLim atTop (Icc a b) →
      TendstoUniformlyOn kineticSeq kineticLim atTop (Icc a b) →
        (∀ᶠ k in atTop, AEStronglyMeasurable (densitySeq k)
          (volume.restrict (Ioc a b))) →
          (∃ C : Real, ∀ᶠ k in atTop,
            ∀ᵐ s ∂volume.restrict (Ioc a b), ‖densitySeq k s‖ ≤ C) →
            Tendsto
              (fun k =>
                letI : TopologicalSpace (X.term (subseq k)).M :=
                  (X.term (subseq k)).topology
                letI : ChartedSpace H (X.term (subseq k)).M :=
                  (X.term (subseq k)).charted
                letI : T2Space (X.term (subseq k)).M :=
                  (X.term (subseq k)).t2
                letI : IsManifold I ∞ (X.term (subseq k)).M :=
                  (X.term (subseq k)).smooth
                letI : SigmaCompactSpace (X.term (subseq k)).M :=
                  (X.term (subseq k)).sigmaCompact
                lLength (I := I) (X.term (subseq k)).S T
                  (fun r => Phi.map k (alpha r)) a b)
              atTop
              (𝓝 <|
                letI : TopologicalSpace L.M := L.topology
                letI : ChartedSpace H L.M := L.charted
                letI : T2Space L.M := L.t2
                letI : IsManifold I ∞ L.M := L.smooth
                letI : SigmaCompactSpace L.M := L.sigmaCompact
                lLength (I := I) L.S T alpha a b) := by
  let scalarSeq : Nat → Real → Real := fun k s =>
    letI : TopologicalSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).topology
    letI : ChartedSpace H (X.term (subseq k)).M :=
      (X.term (subseq k)).charted
    letI : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
    letI : IsManifold I ∞ (X.term (subseq k)).M :=
      (X.term (subseq k)).smooth
    letI : SigmaCompactSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).sigmaCompact
    (X.term (subseq k)).S.scalar (T - s) (Phi.map k (alpha s))
  let kineticSeq : Nat → Real → Real := fun k s =>
    letI : TopologicalSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).topology
    letI : ChartedSpace H (X.term (subseq k)).M :=
      (X.term (subseq k)).charted
    letI : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
    letI : IsManifold I ∞ (X.term (subseq k)).M :=
      (X.term (subseq k)).smooth
    letI : SigmaCompactSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).sigmaCompact
    ((X.term (subseq k)).S.base.metric (T - s)).inner
      (Phi.map k (alpha s))
      (lVelocity (I := I) (fun r => Phi.map k (alpha r)) s)
      (lVelocity (I := I) (fun r => Phi.map k (alpha r)) s)
  let scalarLim : Real → Real := fun s =>
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : T2Space L.M := L.t2
    letI : IsManifold I ∞ L.M := L.smooth
    letI : SigmaCompactSpace L.M := L.sigmaCompact
    L.S.scalar (T - s) (alpha s)
  let kineticLim : Real → Real := fun s =>
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : T2Space L.M := L.t2
    letI : IsManifold I ∞ L.M := L.smooth
    letI : SigmaCompactSpace L.M := L.sigmaCompact
    (L.S.base.metric (T - s)).inner (alpha s)
      (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s)
  let densitySeq : Nat → Real → Real := fun k s =>
    Real.sqrt s * (scalarSeq k s + kineticSeq k s)
  let densityLim : Real → Real := fun s =>
    Real.sqrt s * (scalarLim s + kineticLim s)
  let actionSeq : Nat → Real := fun k =>
    letI : TopologicalSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).topology
    letI : ChartedSpace H (X.term (subseq k)).M :=
      (X.term (subseq k)).charted
    letI : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
    letI : IsManifold I ∞ (X.term (subseq k)).M :=
      (X.term (subseq k)).smooth
    letI : SigmaCompactSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).sigmaCompact
    lLength (I := I) (X.term (subseq k)).S T
      (fun r => Phi.map k (alpha r)) a b
  let actionLim : Real :=
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : T2Space L.M := L.t2
    letI : IsManifold I ∞ L.M := L.smooth
    letI : SigmaCompactSpace L.M := L.sigmaCompact
    lLength (I := I) L.S T alpha a b
  change TendstoUniformlyOn scalarSeq scalarLim atTop (Icc a b) →
    TendstoUniformlyOn kineticSeq kineticLim atTop (Icc a b) →
      (∀ᶠ k in atTop, AEStronglyMeasurable (densitySeq k)
        (volume.restrict (Ioc a b))) →
        (∃ C : Real, ∀ᶠ k in atTop,
          ∀ᵐ s ∂volume.restrict (Ioc a b), ‖densitySeq k s‖ ≤ C) →
          Tendsto actionSeq atTop (𝓝 actionLim)
  intro hScalar hKinetic hmeas hbound
  let mu : Measure Real := volume.restrict (Ioc a b)
  have hlim : ∀ᵐ s ∂mu,
      Tendsto (fun k => densitySeq k s) atTop (𝓝 (densityLim s)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hsIcc : s ∈ Icc a b := ⟨hs.1.le, hs.2⟩
    have hR := hScalar.tendsto_at hsIcc
    have hQ := hKinetic.tendsto_at hsIcc
    exact tendsto_const_nhds.mul (hR.add hQ)
  have hint := tendsto_integral_filter_of_norm_le_const
    (μ := mu) hmeas hbound hlim
  simpa only [actionSeq, actionLim, lLength,
    intervalIntegral.integral_of_le hab, densitySeq, densityLim,
    scalarSeq, scalarLim, kineticSeq, kineticLim, lDensity, lSpeedSq, mu]
    using hint

end DifferentialGeometry.HCGCompactness
