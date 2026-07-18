import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ConvFieldAssembly

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Uniform source-flow covariant and time-Lipschitz bounds

This file records the constants-first source-native analytic output used by the
open-window convergence assembly.  It deliberately mentions neither bump
functions nor the globally extended metrics: those are downstream localization
devices, while the estimates here belong to the pulled-back Ricci flows on the
varying source domains.
-/

noncomputable section

open Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace HCGCompactness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {X : PointedFlowSeq (I := I)}
variable {P : PointedRiemannianManifold (I := I)}
variable {subseq : Nat → Nat}

/-- Uniform, constants-first covariant and time-Lipschitz control for the
pulled-back source flows.  Both constants are chosen before the varying source
index `k`; this is the quantifier order required by the compactness argument. -/
structure SrcCovLipData
    (Φ : PointedCGHMaps (I := I) X P subseq)
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (hsrc : SrcSigma Φ) (htgt : TgtSigma Φ)
    (β ψ : ℝ) : Prop where
  /-- Every reference-covariant metric tower is uniformly bounded on every
  source domain and throughout the closed time window. -/
  cov :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    ∀ q : Nat, ∃ Cq : ℝ, 0 ≤ Cq ∧
      ∀ k : Nat,
        letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
          sourceDomTop (I := I) Φ k
        letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
          sourceDomCharted (I := I) Φ k
        letI : T2Space (SourceDomain (I := I) Φ k) :=
          sourceDomT2 (I := I) Φ k
        letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
          sourceDomSmooth (I := I) Φ k
        letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
          sourceDomSigmaOf (I := I) Φ k (hsrc k)
        ∀ t : ℝ, t ∈ Set.Icc β ψ →
          ∀ y : SourceDomain (I := I) Φ k,
            metricCovDerivNorm (I := I) q
                (srcMetric (I := I) Φ hsrc htgt k t)
                (refRes (I := I) Φ R hsrc k) y ≤ Cq
  /-- For each finite order, one Lipschitz constant controls all lower orders,
  all source domains, and every pair of times in the window. -/
  lip :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    ∀ p : Nat, ∃ Lp : ℝ, 0 ≤ Lp ∧
      ∀ k : Nat,
        letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
          sourceDomTop (I := I) Φ k
        letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
          sourceDomCharted (I := I) Φ k
        letI : T2Space (SourceDomain (I := I) Φ k) :=
          sourceDomT2 (I := I) Φ k
        letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
          sourceDomSmooth (I := I) Φ k
        letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
          sourceDomSigmaOf (I := I) Φ k (hsrc k)
        ∀ s t : ℝ, s ∈ Set.Icc β ψ → t ∈ Set.Icc β ψ →
          ∀ q : Nat, q ≤ p →
            ∀ y : SourceDomain (I := I) Φ k,
              metricDerivNorm (I := I) q
                  (srcMetric (I := I) Φ hsrc htgt k s)
                  (srcMetric (I := I) Φ hsrc htgt k t)
                  (refRes (I := I) Φ R hsrc k) y ≤ Lp * |s - t|

/-- Source-flow covariant and time-Lipschitz bounds from uniform metric
equivalence, moving Shi estimates, and one uniform initial covariant envelope.

This is the analytic owner of the varying-domain quantifier uniformity.  In
particular, it must not be replaced by applying a per-source compact estimate
after fixing `k`, since that would choose the constants in the wrong order. -/
theorem srcCovLip_of_soln
    (Φ : PointedCGHMaps (I := I) X P subseq)
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (hsrc : SrcSigma Φ) (htgt : TgtSigma Φ)
    {β ψ t₀ : ℝ}
    (hβψ : β ≤ ψ)
    (ht₀ : t₀ ∈ Set.Icc β ψ)
    (hwin : Set.Icc β ψ ⊆ X.D.regular)
    (Bmax : ℝ) (hBmax : 1 ≤ Bmax)
    (hequiv :
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : T2Space P.M := P.t2
      letI : IsManifold I ∞ P.M := P.smooth
      letI : SigmaCompactSpace P.M := P.sigmaCompact
      ∀ k : Nat,
        letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
          sourceDomTop (I := I) Φ k
        letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
          sourceDomCharted (I := I) Φ k
        letI : T2Space (SourceDomain (I := I) Φ k) :=
          sourceDomT2 (I := I) Φ k
        letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
          sourceDomSmooth (I := I) Φ k
        letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
          sourceDomSigmaOf (I := I) Φ k (hsrc k)
        ∀ t : ℝ, t ∈ Set.Icc β ψ →
          MetricUniformEquivalentOn (I := I)
            (Set.univ : Set (SourceDomain (I := I) Φ k))
            (refRes (I := I) Φ R hsrc k)
            (srcMetric (I := I) Φ hsrc htgt k t) Bmax)
    (hShi :
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : T2Space P.M := P.t2
      letI : IsManifold I ∞ P.M := P.smooth
      letI : SigmaCompactSpace P.M := P.sigmaCompact
      ∀ N : Nat, ∃ KShi : ℝ, 0 ≤ KShi ∧
        ∀ k : Nat,
          letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
            sourceDomTop (I := I) Φ k
          letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
            sourceDomCharted (I := I) Φ k
          letI : T2Space (SourceDomain (I := I) Φ k) :=
            sourceDomT2 (I := I) Φ k
          letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
            sourceDomSmooth (I := I) Φ k
          letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
            sourceDomSigmaOf (I := I) Φ k (hsrc k)
          MovingShiBoundOn (I := I)
            (Set.univ : Set (SourceDomain (I := I) Φ k)) β ψ
            (fun _ t ↦ srcMetric (I := I) Φ hsrc htgt k t) N KShi)
    (hinit :
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : T2Space P.M := P.t2
      letI : IsManifold I ∞ P.M := P.smooth
      letI : SigmaCompactSpace P.M := P.sigmaCompact
      ∀ q : Nat, ∃ Cq : ℝ, 0 ≤ Cq ∧
        ∀ k : Nat,
          letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
            sourceDomTop (I := I) Φ k
          letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
            sourceDomCharted (I := I) Φ k
          letI : T2Space (SourceDomain (I := I) Φ k) :=
            sourceDomT2 (I := I) Φ k
          letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
            sourceDomSmooth (I := I) Φ k
          letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
            sourceDomSigmaOf (I := I) Φ k (hsrc k)
          ∀ y : SourceDomain (I := I) Φ k,
            metricCovDerivNorm (I := I) q
                (srcMetric (I := I) Φ hsrc htgt k t₀)
                (refRes (I := I) Φ R hsrc k) y ≤ Cq) :
    SrcCovLipData (I := I) Φ R hsrc htgt β ψ := by
  sorry

end HCGCompactness
end DifferentialGeometry
