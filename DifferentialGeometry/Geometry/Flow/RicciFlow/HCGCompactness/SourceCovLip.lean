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
  classical
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  /- The genuine analytic frontier is the constants-first invariant induction.
  At each order it controls both the moving metric tower and the evolution
  tower in the fixed reference norm.  Keeping the two conclusions together is
  essential: the latter is the derivative bound used by the time mean-value
  argument below. -/
  have hcore : ∀ q : Nat, ∃ Cq Lq : ℝ, 0 ≤ Cq ∧ 0 ≤ Lq ∧
      (∀ k : Nat,
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
                (refRes (I := I) Φ R hsrc k) y ≤ Cq) ∧
      (∀ k : Nat,
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
            Real.sqrt
                (Tensor0SBundle.normSq0S (I := I)
                  (refRes (I := I) Φ R hsrc k) y (q + 2)
                  ((-2 : ℝ) •
                    nablaRicReal (I := I)
                      (fun _ t' ↦ srcMetric (I := I) Φ hsrc htgt k t')
                      (refRes (I := I) Φ R hsrc k) q 0 t y)) ≤ Lq) := by
    sorry
  refine
    { cov := ?_
      lip := ?_ }
  · intro q
    obtain ⟨Cq, _Lq, hCq, _hLq, hcov, _hric⟩ := hcore q
    exact ⟨Cq, hCq, hcov⟩
  · intro p
    have hricBound : ∀ q : Nat, ∃ Lq : ℝ, 0 ≤ Lq ∧
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
              Real.sqrt
                  (Tensor0SBundle.normSq0S (I := I)
                    (refRes (I := I) Φ R hsrc k) y (q + 2)
                    ((-2 : ℝ) •
                      nablaRicReal (I := I)
                        (fun _ t' ↦ srcMetric (I := I) Φ hsrc htgt k t')
                        (refRes (I := I) Φ R hsrc k) q 0 t y)) ≤ Lq := by
      intro q
      obtain ⟨_Cq, Lq, _hCq, hLq, _hcov, hric⟩ := hcore q
      exact ⟨Lq, hLq, hric⟩
    choose Lq hLq0 hric using hricBound
    let Lp : ℝ := ∑ q ∈ Finset.range (p + 1), Lq q
    have hLp0 : 0 ≤ Lp := by
      dsimp only [Lp]
      exact Finset.sum_nonneg fun q _ => hLq0 q
    refine ⟨Lp, hLp0, ?_⟩
    intro k
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
      sourceDomTop (I := I) Φ k
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
      sourceDomCharted (I := I) Φ k
    letI : T2Space (SourceDomain (I := I) Φ k) :=
      sourceDomT2 (I := I) Φ k
    letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
      sourceDomSmooth (I := I) Φ k
    letI : IsManifold I 1 (SourceDomain (I := I) Φ k) :=
      IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k)
        (n := (∞ : WithTop ℕ∞)) (by decide)
    letI : IsManifold I 2 (SourceDomain (I := I) Φ k) :=
      IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k)
        (n := (∞ : WithTop ℕ∞)) (by decide)
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1)
        (SourceDomain (I := I) Φ k) := by
      change IsManifold I ∞ (SourceDomain (I := I) Φ k)
      infer_instance
    letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
      sourceDomSigmaOf (I := I) Φ k (hsrc k)
    intro s t hs ht q hqp y
    have hDreg : ∀ {r : ℝ}, r ∈ X.D.regular → X.D.regular ∈ nhds r :=
      fun {r} hr => X.D.regular_isOpen.mem_nhds hr
    have hev := hevComp_of_solutions (I := I)
      (K := (Set.univ : Set (SourceDomain (I := I) Φ k)))
      (β := β) (ψ := ψ)
      (gSeq := fun _ t' ↦ srcMetric (I := I) Φ hsrc htgt k t')
      (gRef := refRes (I := I) Φ R hsrc k) (N := q)
      (fun _ ↦ X.D)
      (fun _ ↦ sourceFlow (I := I) Φ k (hsrc k) (htgt k))
      (fun _ ↦ isSolutionOn_sourceFlow (I := I) Φ k (hsrc k) (htgt k))
      (fun _ _ ↦ rfl)
      (fun _ ↦ hwin)
      (fun _ p' hp V x₀ ↦
        solnTowerSwap_reg (I := I) (refRes (I := I) Φ R hsrc k)
          (sourceFlow (I := I) Φ k (hsrc k) (htgt k))
          (isSolutionOn_sourceFlow (I := I) Φ k (hsrc k) (htgt k))
          q hDreg p' hp V x₀)
    have hqLip : metricDerivNorm (I := I) q
          (srcMetric (I := I) Φ hsrc htgt k s)
          (srcMetric (I := I) Φ hsrc htgt k t)
          (refRes (I := I) Φ R hsrc k) y ≤ Lq q * |s - t| := by
      exact timeLipschitz_of_hasDerivAt (I := I)
        (refRes (I := I) Φ R hsrc k) q
        (fun t' ↦ srcMetric (I := I) Φ hsrc htgt k t')
        (fun t' y' ↦ (-2 : ℝ) •
          nablaRicReal (I := I)
            (fun _ r ↦ srcMetric (I := I) Φ hsrc htgt k r)
            (refRes (I := I) Φ R hsrc k) q 0 t' y')
        Set.univ β ψ (Lq q)
        (fun y' _hy' t' ht' v ↦ hev 0 y' (Set.mem_univ y') t' ht' v)
        (fun y' _hy' t' ht' ↦ hric q k t' ht' y')
        s hs t ht y (Set.mem_univ y)
    have hqmem : q ∈ Finset.range (p + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le hqp)
    have hqle : Lq q ≤ Lp := by
      dsimp only [Lp]
      exact Finset.single_le_sum
        (fun r _hr ↦ hLq0 r) hqmem
    exact hqLip.trans
      (mul_le_mul_of_nonneg_right hqle (abs_nonneg (s - t)))

end HCGCompactness
end DifferentialGeometry
