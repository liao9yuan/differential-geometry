import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepDLimitMetrics
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCompactnessSubseq

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

/-!
# Step D6 assembly

This module aligns the shrunk-tail convergence/completeness output with the
subsequence of the original pointed sequence and performs the final Step D
field assembly.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable [I.Boundaryless]
variable [NeZero (Module.finrank ℝ E)]

/-- The concrete convergence data use the restricted limit metric itself as
their seminorm reference metric. -/
private def HasCanonRef
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Phi : PointedRiemannianCGMaps (I := I) X L subseq}
    (C : PointedRiemannianCGConverges (I := I) X L subseq Phi) : Prop :=
  forall k : Nat,
    let D := C.metrics.domain k
    letI : TopologicalSpace (MetricSourceDomain (I := I) Phi k) := D.topology
    letI : ChartedSpace H (MetricSourceDomain (I := I) Phi k) := D.charted
    letI : IsManifold I ∞ (MetricSourceDomain (I := I) Phi k) := D.smooth
    D.referenceMetric = D.limitMetric

/-- The two whole-source estimates retained by the concrete Step-D sidecar.
The tail is supplied by `D6ChainData.close`; the finite head requires the
relatively compact collar argument recorded at the assembly frontier below. -/
private def HasCanonBounds
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Phi : PointedRiemannianCGMaps (I := I) X L subseq}
    (C : PointedRiemannianCGConverges (I := I) X L subseq Phi) : Prop :=
  (exists Crel : Real, 1 <= Crel ∧
    forall k : Nat,
      let D := C.metrics.domain k
      letI : TopologicalSpace (MetricSourceDomain (I := I) Phi k) := D.topology
      letI : ChartedSpace H (MetricSourceDomain (I := I) Phi k) := D.charted
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) Phi k) := D.smooth
      MetricUniformEquivalentOn (I := I)
        (Set.univ : Set (MetricSourceDomain (I := I) Phi k))
        D.limitMetric D.pullbackMetric Crel) ∧
  (forall q : Nat, exists Cq : Real, 0 <= Cq ∧
    forall (k : Nat) (x : MetricSourceDomain (I := I) Phi k),
      let D := C.metrics.domain k
      letI : TopologicalSpace (MetricSourceDomain (I := I) Phi k) := D.topology
      letI : ChartedSpace H (MetricSourceDomain (I := I) Phi k) := D.charted
      letI : T2Space (MetricSourceDomain (I := I) Phi k) := D.t2
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) Phi k) := D.smooth
      letI : SigmaCompactSpace (MetricSourceDomain (I := I) Phi k) := D.sigmaCompact
      metricCovDerivNorm (I := I) q D.pullbackMetric D.limitMetric x <= Cq)

private structure D6ChainData
    {M : ℕ → Type u} [∀ j, MetricSpace (M j)] [∀ j, ChartedSpace H (M j)]
    [∀ j, IsManifold I ∞ (M j)] [∀ j, SigmaCompactSpace (M j)] [∀ j, T2Space (M j)]
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (g : ∀ j, SmoothRiemannianMetric I (M j)) where
  start : ℕ
  one_le : 1 ≤ start
  zero : ∀ n k, BookApproxIsoPartialData (I := I)
    (Metric.closedBall (b (start + n)) ((2 : ℝ) ^ (start + n))) (1 / 2) 0
    (chainComp (I := I) (Mf := M) Ψ (start + n) k)
    (g (start + n)) (g ((start + n) + k))
  source : ∀ n k,
    (ballOpen b (fun s => (2 : ℝ) ^ s) (start + n) : Set (M (start + n))) ⊆
      (chainComp (I := I) (Mf := M) Ψ (start + n) k).source
  maps : ∀ n,
    (chainComp (I := I) (Mf := M) Ψ (start + n) 1 :
      M (start + n) → M (start + (n + 1))) ''
        (ballOpen b (fun s => (2 : ℝ) ^ s) (start + n) : Set (M (start + n))) ⊆
      (ballOpen b (fun s => (2 : ℝ) ^ s) (start + (n + 1)) :
        Set (M (start + (n + 1))))
  metric : ∀ n, SmoothRiemannianMetric I
    (ballOpen b (fun s => (2 : ℝ) ^ s) (start + n))
  close : ∀ ε : ℝ, 0 < ε → ∀ p : ℕ, ∃ n₀ : ℕ,
    ∀ n : ℕ, n₀ ≤ n →
      letI : SigmaCompactSpace
          (ballOpen b (fun s => (2 : ℝ) ^ s) (start + n)) :=
        isSigmaCompact_iff_sigmaCompactSpace.mp
          (Geometry.isSigmaCompact_of_isOpen I
            (ballOpen b (fun s => (2 : ℝ) ^ s) (start + n)).isOpen)
      ∀ l q : ℕ, q ≤ p →
        ∀ x : ballOpen b (fun s => (2 : ℝ) ^ s) (start + n),
          metricDerivNorm (I := I) q
            (chainPullbackSeq (I := I) Ψ g
              (ballOpen b (fun s => (2 : ℝ) ^ s) (start + n)) (source n) l)
            (metric n) (metric n) x ≤ ε
  step : ∀ n,
    let F : ballOpen b (fun s => (2 : ℝ) ^ s) (start + n) →
        ballOpen b (fun s => (2 : ℝ) ^ s) (start + (n + 1)) :=
      PartialDiffeomorph.opensMap
        (chainComp (I := I) (Mf := M) Ψ (start + n) 1) (source n 1) (maps n)
    ∀ (x : ballOpen b (fun s => (2 : ℝ) ^ s) (start + n))
      (v w : TangentSpace I x),
      (metric n).inner x v w =
        (metric (n + 1)).inner (F x)
          (mfderiv I I F x v) (mfderiv I I F x w)

@[reducible] private noncomputable def alignedMetric
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)} (k : ℕ)
    (P : ProperMetricOn (I := I) (X.obj k)) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    MetricSpace (X.obj k).M := by
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  exact P.ms.replaceTopology (ProperMetricOn.top_eq (X.obj k) P).symm

/-- Properness of the realized metric after replacing its bundled topology by
the definitionally aligned manifold topology. -/
private theorem alignedProper
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)} (k : ℕ)
    (P : ProperMetricOn (I := I) (X.obj k)) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : MetricSpace (X.obj k).M := alignedMetric (I := I) k P
    ProperSpace (X.obj k).M := by
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : MetricSpace (X.obj k).M := alignedMetric (I := I) k P
  constructor
  intro x r
  have hcompact :
      @IsCompact (X.obj k).M
        P.ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
        (letI : MetricSpace (X.obj k).M := P.ms
         Metric.closedBall x r) := by
    letI : MetricSpace (X.obj k).M := P.ms
    letI : ProperSpace (X.obj k).M := P.proper
    exact isCompact_closedBall x r
  rw [ProperMetricOn.top_eq (X.obj k) P] at hcompact
  exact hcompact

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Direct-limit comparison maps whose targets are the original pointed-sequence members. -/
noncomputable def tailMemberMaps
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (P : ∀ k, ProperMetricOn (I := I) (X.obj k)) (σ : ℕ → ℕ) :
    letI : ∀ j, TopologicalSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).topology
    letI : ∀ j, ChartedSpace H (X.obj (σ j)).M := fun j => (X.obj (σ j)).charted
    letI : ∀ j, IsManifold I ∞ (X.obj (σ j)).M := fun j => (X.obj (σ j)).smooth
    letI : ∀ j, T2Space (X.obj (σ j)).M := fun j => (X.obj (σ j)).t2
    letI : ∀ j, SigmaCompactSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).sigmaCompact
    letI : ∀ j, MetricSpace (X.obj (σ j)).M := fun j =>
      alignedMetric (I := I) (σ j) (P (σ j))
    letI : ∀ j, IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj (σ j)).M := fun j => by
      change IsManifold I ∞ (X.obj (σ j)).M
      infer_instance
    letI : ∀ j, Bundle.RiemannianBundle
        (fun x : (X.obj (σ j)).M => TangentSpace I x) :=
      fun j => (X.obj (σ j)).riemBundle
    letI : ∀ j, IsRiemannianManifold I (X.obj (σ j)).M := fun j => by
      refine ⟨fun x y => ?_⟩
      have hreal := (P (σ j)).realizes x y
      rw [edist_dist, ← hreal]
      rfl
    ∀ (Ψ : ∀ j, PartialDiffeomorph I I (X.obj (σ j)).M
        (X.obj (σ (j + 1))).M (∞ : WithTop ℕ∞))
      (hbase : ∀ j, (Ψ j : (X.obj (σ j)).M → (X.obj (σ (j + 1))).M)
        (X.obj (σ j)).basepoint = (X.obj (σ (j + 1))).basepoint)
      (j₀ : ℕ)
      (D₀ : ∀ n k, BookApproxIsoPartialData (I := I)
        (Metric.closedBall (X.obj (σ (j₀ + n))).basepoint ((2 : ℝ) ^ (j₀ + n)))
        (1 / 2) 0
        (chainComp (I := I) (Mf := fun j => (X.obj (σ j)).M) Ψ (j₀ + n) k)
        (X.obj (σ (j₀ + n))).metric (X.obj (σ ((j₀ + n) + k))).metric),
      let b := fun j => (X.obj (σ j)).basepoint
      let g := fun j => (X.obj (σ j)).metric
      letI : ∀ n, Nonempty (tailBallOpen b j₀ n) := fun n => tailBall_nonempty b j₀ n
      let S := tailBallSystem (I := I) b Ψ hbase g (by
        intro j x v
        simpa using
          (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
            (I := I) (g j) x v)) j₀ D₀
      letI : ∀ n, SigmaCompactSpace (tailBallOpen b j₀ n) := fun n =>
        isSigmaCompact_iff_sigmaCompactSpace.mp
          (Geometry.isSigmaCompact_of_isOpen I (tailBallOpen b j₀ n).isOpen)
      ∀ (gTail : ∀ n, SmoothRiemannianMetric I (tailBallOpen b j₀ n))
        (hgTail : S.MetricCocycle gTail),
        PointedRiemannianCGMaps (I := I) X
          (limitPointedCoc S (tailCenter b j₀ 0) gTail hgTail)
          (fun n => σ (j₀ + n)) := by
  letI : ∀ j, TopologicalSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).topology
  letI : ∀ j, ChartedSpace H (X.obj (σ j)).M := fun j => (X.obj (σ j)).charted
  letI : ∀ j, IsManifold I ∞ (X.obj (σ j)).M := fun j => (X.obj (σ j)).smooth
  letI : ∀ j, T2Space (X.obj (σ j)).M := fun j => (X.obj (σ j)).t2
  letI : ∀ j, SigmaCompactSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).sigmaCompact
  letI : ∀ j, MetricSpace (X.obj (σ j)).M := fun j =>
    alignedMetric (I := I) (σ j) (P (σ j))
  letI : ∀ j, IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj (σ j)).M := fun j => by
    change IsManifold I ∞ (X.obj (σ j)).M
    infer_instance
  letI : ∀ j, Bundle.RiemannianBundle
      (fun x : (X.obj (σ j)).M => TangentSpace I x) :=
    fun j => (X.obj (σ j)).riemBundle
  letI : ∀ j, IsRiemannianManifold I (X.obj (σ j)).M := fun j => by
    refine ⟨fun x y => ?_⟩
    have hreal := (P (σ j)).realizes x y
    rw [edist_dist, ← hreal]
    rfl
  intro Ψ hbase j₀ D₀
  let b := fun j => (X.obj (σ j)).basepoint
  let g := fun j => (X.obj (σ j)).metric
  letI : ∀ n, Nonempty (tailBallOpen b j₀ n) := fun n => tailBall_nonempty b j₀ n
  let S := tailBallSystem (I := I) b Ψ hbase g (by
    intro j x v
    simpa using
      (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) (g j) x v)) j₀ D₀
  letI : ∀ n, SigmaCompactSpace (tailBallOpen b j₀ n) := fun n =>
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I (tailBallOpen b j₀ n).isOpen)
  dsimp only
  intro gTail hgTail
  let Φ : ∀ n, PartialDiffeomorph I I S.toSeqSystem.Lim
      (X.obj (σ (j₀ + n))).M (∞ : WithTop ℕ∞) := fun n =>
    PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo n) rfl
  refine
    { partialDiffeomorph := Φ
      source_exhausts := ?_
      base_mem := fun n => ?_
      basepoint_map := fun n => ?_ }
  · change ExhaustsByOpen (fun k => Set.range (S.toSeqSystem.incl k))
    exact rangeExhausts S
  · change S.toSeqSystem.incl 0 (tailCenter b j₀ 0) ∈
      Set.range (S.toSeqSystem.incl n)
    exact ⟨S.toSeqSystem.F (Nat.zero_le n) (tailCenter b j₀ 0),
      S.toSeqSystem.incl_comp (Nat.zero_le n) (tailCenter b j₀ 0)⟩
  · calc
      Φ n (S.toSeqSystem.incl 0 (tailCenter b j₀ 0)) =
          (S.toSeqSystem.F (Nat.zero_le n) (tailCenter b j₀ 0) :
            (X.obj (σ (j₀ + n))).M) :=
        congrArg Subtype.val
          (S.invIncl_incl_le (Nat.zero_le n) (tailCenter b j₀ 0))
      _ = (X.obj (σ (j₀ + n))).basepoint := by
        exact congrArg Subtype.val
          (tailCenter_map (I := I) b Ψ hbase g (by
            intro j x v
            simpa using
              (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
                (I := I) (g j) x v)) j₀ D₀ n)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Convergence of the repointed tail sequence transfers to the original
sequence once the lifted inclusions are known to hit its basepoints. -/
noncomputable def tailMemberConv
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (P : ∀ k, ProperMetricOn (I := I) (X.obj k)) (σ : ℕ → ℕ) :
    letI : ∀ j, TopologicalSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).topology
    letI : ∀ j, ChartedSpace H (X.obj (σ j)).M := fun j => (X.obj (σ j)).charted
    letI : ∀ j, IsManifold I ∞ (X.obj (σ j)).M := fun j => (X.obj (σ j)).smooth
    letI : ∀ j, T2Space (X.obj (σ j)).M := fun j => (X.obj (σ j)).t2
    letI : ∀ j, SigmaCompactSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).sigmaCompact
    letI : ∀ j, MetricSpace (X.obj (σ j)).M := fun j =>
      alignedMetric (I := I) (σ j) (P (σ j))
    letI : ∀ j, IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj (σ j)).M := fun j => by
      change IsManifold I ∞ (X.obj (σ j)).M
      infer_instance
    letI : ∀ j, Bundle.RiemannianBundle
        (fun x : (X.obj (σ j)).M => TangentSpace I x) :=
      fun j => (X.obj (σ j)).riemBundle
    letI : ∀ j, IsRiemannianManifold I (X.obj (σ j)).M := fun j => by
      refine ⟨fun x y => ?_⟩
      have hreal := (P (σ j)).realizes x y
      rw [edist_dist, ← hreal]
      rfl
    ∀ (Ψ : ∀ j, PartialDiffeomorph I I (X.obj (σ j)).M
        (X.obj (σ (j + 1))).M (∞ : WithTop ℕ∞))
      (hbase : ∀ j, (Ψ j : (X.obj (σ j)).M → (X.obj (σ (j + 1))).M)
        (X.obj (σ j)).basepoint = (X.obj (σ (j + 1))).basepoint)
      (j₀ : ℕ)
      (D₀ : ∀ n k, BookApproxIsoPartialData (I := I)
        (Metric.closedBall (X.obj (σ (j₀ + n))).basepoint ((2 : ℝ) ^ (j₀ + n)))
        (1 / 2) 0
        (chainComp (I := I) (Mf := fun j => (X.obj (σ j)).M) Ψ (j₀ + n) k)
        (X.obj (σ (j₀ + n))).metric (X.obj (σ ((j₀ + n) + k))).metric),
      let b := fun j => (X.obj (σ j)).basepoint
      let g := fun j => (X.obj (σ j)).metric
      letI : ∀ n, Nonempty (tailBallOpen b j₀ n) := fun n => tailBall_nonempty b j₀ n
      let S := tailBallSystem (I := I) b Ψ hbase g (by
        intro j x v
        simpa using
          (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
            (I := I) (g j) x v)) j₀ D₀
      letI : ∀ n, SigmaCompactSpace (tailBallOpen b j₀ n) := fun n =>
        isSigmaCompact_iff_sigmaCompactSpace.mp
          (Geometry.isSigmaCompact_of_isOpen I (tailBallOpen b j₀ n).isOpen)
      ∀ (gTail : ∀ n, SmoothRiemannianMetric I (tailBallOpen b j₀ n))
        (hgTail : S.MetricCocycle gTail),
        PointedRiemannianCGConverges (I := I)
            (chainAmbientSeq (I := I) j₀ (tailBallOpen b j₀) S
              (tailCenter b j₀ 0) g)
            (limitPointedCoc S (tailCenter b j₀ 0) gTail hgTail) id
            (chainAmbientMaps (I := I) j₀ (tailBallOpen b j₀) S
              (tailCenter b j₀ 0) g gTail hgTail) →
          PointedRiemannianCGConverges (I := I) X
            (limitPointedCoc S (tailCenter b j₀ 0) gTail hgTail)
            (fun n => σ (j₀ + n))
            (tailMemberMaps (I := I) P σ Ψ hbase j₀ D₀ gTail hgTail) := by
  letI : ∀ j, TopologicalSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).topology
  letI : ∀ j, ChartedSpace H (X.obj (σ j)).M := fun j => (X.obj (σ j)).charted
  letI : ∀ j, IsManifold I ∞ (X.obj (σ j)).M := fun j => (X.obj (σ j)).smooth
  letI : ∀ j, T2Space (X.obj (σ j)).M := fun j => (X.obj (σ j)).t2
  letI : ∀ j, SigmaCompactSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).sigmaCompact
  letI : ∀ j, MetricSpace (X.obj (σ j)).M := fun j =>
    alignedMetric (I := I) (σ j) (P (σ j))
  letI : ∀ j, IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj (σ j)).M := fun j => by
    change IsManifold I ∞ (X.obj (σ j)).M
    infer_instance
  letI : ∀ j, Bundle.RiemannianBundle
      (fun x : (X.obj (σ j)).M => TangentSpace I x) :=
    fun j => (X.obj (σ j)).riemBundle
  letI : ∀ j, IsRiemannianManifold I (X.obj (σ j)).M := fun j => by
    refine ⟨fun x y => ?_⟩
    have hreal := (P (σ j)).realizes x y
    rw [edist_dist, ← hreal]
    rfl
  intro Ψ hbase j₀ D₀
  let b := fun j => (X.obj (σ j)).basepoint
  let g := fun j => (X.obj (σ j)).metric
  letI : ∀ n, Nonempty (tailBallOpen b j₀ n) := fun n => tailBall_nonempty b j₀ n
  let S := tailBallSystem (I := I) b Ψ hbase g (by
    intro j x v
    simpa using
      (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) (g j) x v)) j₀ D₀
  letI : ∀ n, SigmaCompactSpace (tailBallOpen b j₀ n) := fun n =>
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I (tailBallOpen b j₀ n).isOpen)
  dsimp only
  intro gTail hgTail C
  let XTail := X.subseq (fun n => σ (j₀ + n))
  let bTail : ∀ n, (XTail.obj n).M := fun n =>
    (S.toSeqSystem.F (Nat.zero_le n) (tailCenter b j₀ 0) :
      (X.obj (σ (j₀ + n))).M)
  let L := limitPointedCoc S (tailCenter b j₀ 0) gTail hgTail
  let Φr : PointedRiemannianCGMaps (I := I) (XTail.repoint bTail) L id := by
    change PointedRiemannianCGMaps (I := I)
      (chainAmbientSeq (I := I) j₀ (tailBallOpen b j₀) S
        (tailCenter b j₀ 0) g) L id
    exact chainAmbientMaps (I := I) j₀ (tailBallOpen b j₀) S
      (tailCenter b j₀ 0) g gTail hgTail
  have hbase' : ∀ n,
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : TopologicalSpace (XTail.obj (id n)).M := (XTail.obj (id n)).topology
      letI : ChartedSpace H (XTail.obj (id n)).M := (XTail.obj (id n)).charted
      Φr.partialDiffeomorph n L.basepoint = (XTail.obj (id n)).basepoint := by
    intro n
    calc
      Φr.partialDiffeomorph n (S.toSeqSystem.incl 0 (tailCenter b j₀ 0)) =
          (S.toSeqSystem.F (Nat.zero_le n) (tailCenter b j₀ 0) :
            (X.obj (σ (j₀ + n))).M) :=
        congrArg Subtype.val
          (S.invIncl_incl_le (Nat.zero_le n) (tailCenter b j₀ 0))
      _ = (X.obj (σ (j₀ + n))).basepoint := by
        exact congrArg Subtype.val
          (tailCenter_map (I := I) b Ψ hbase g (by
            intro j x v
            simpa using
              (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
                (I := I) (g j) x v)) j₀ D₀ n)
  have Cr : PointedRiemannianCGConverges (I := I) (XTail.repoint bTail) L id Φr := by
    change PointedRiemannianCGConverges (I := I)
      (chainAmbientSeq (I := I) j₀ (tailBallOpen b j₀) S
        (tailCenter b j₀ 0) g) L id
      (chainAmbientMaps (I := I) j₀ (tailBallOpen b j₀) S
        (tailCenter b j₀ 0) g gTail hgTail)
    exact C
  have Cu := Cr.unrepoint bTail hbase'
  exact Cu.ofSubseq (fun n => σ (j₀ + n))

namespace StepDCanonData

/-- Sigma-compactness of a comparison map's canonical source open set. -/
noncomputable def canonSrc
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Phi : PointedRiemannianCGMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace L.M := L.topology
    IsSigmaCompact (Phi.source k) := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : SigmaCompactSpace L.M := L.sigmaCompact
  exact Geometry.isSigmaCompact_of_isOpen I (Phi.source_open k)

/-- Sigma-compactness of a comparison map's canonical target open set. -/
noncomputable def canonTgt
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Phi : PointedRiemannianCGMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace (X.obj (subseq k)).M := (X.obj (subseq k)).topology
    IsSigmaCompact (Phi.target k) := by
  letI : TopologicalSpace (X.obj (subseq k)).M := (X.obj (subseq k)).topology
  letI : ChartedSpace H (X.obj (subseq k)).M := (X.obj (subseq k)).charted
  letI : SigmaCompactSpace (X.obj (subseq k)).M := (X.obj (subseq k)).sigmaCompact
  exact Geometry.isSigmaCompact_of_isOpen I (Phi.target_open k)

/-- The restricted limit metric on the canonical source domain. -/
noncomputable def canonRef
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Phi : PointedRiemannianCGMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace (MetricSourceDomain (I := I) Phi k) :=
      metricSourceDomTop (I := I) Phi k
    letI : ChartedSpace H (MetricSourceDomain (I := I) Phi k) :=
      metricSourceDomCharted (I := I) Phi k
    letI : IsManifold I ∞ (MetricSourceDomain (I := I) Phi k) :=
      metricSourceDomSmooth (I := I) Phi k
    SmoothRiemannianMetric I (MetricSourceDomain (I := I) Phi k) := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : T2Space L.M := L.t2
  letI : IsManifold I ∞ L.M := L.smooth
  letI : SigmaCompactSpace L.M := L.sigmaCompact
  letI : TopologicalSpace (MetricSourceDomain (I := I) Phi k) :=
    metricSourceDomTop (I := I) Phi k
  letI : ChartedSpace H (MetricSourceDomain (I := I) Phi k) :=
    metricSourceDomCharted (I := I) Phi k
  letI : T2Space (MetricSourceDomain (I := I) Phi k) :=
    metricSourceDomT2 (I := I) Phi k
  letI : IsManifold I ∞ (MetricSourceDomain (I := I) Phi k) :=
    metricSourceDomSmooth (I := I) Phi k
  letI : SigmaCompactSpace (MetricSourceDomain (I := I) Phi k) :=
    metricSourceDomSigmaOf (I := I) Phi k (canonSrc (I := I) Phi k)
  exact L.metric.restrictOpen (I := I) (metricSourceOpen (I := I) Phi k)

/-- The canonical metric source data determined by comparison maps. -/
noncomputable def canonDomain
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Phi : PointedRiemannianCGMaps (I := I) X L subseq) (k : Nat) :
    MetricSourceData (I := I) Phi k :=
  MetricSourceData.ofRestrictPullback (I := I)
    (Φ := Phi) (k := k) (canonSrc (I := I) Phi k)
    (canonTgt (I := I) Phi k) (canonRef (I := I) Phi k)

end StepDCanonData

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Concrete Step-D output retaining the canonical reference-metric choice
made by the direct-limit convergence construction.  The public
`MetricCompactnessConclusion` deliberately forgets this provenance. -/
structure StepDCanonData
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  mc : MetricCompactnessConclusion (I := I) X
  domain_eq : forall k : Nat,
    mc.convergence.metrics.domain k = StepDCanonData.canonDomain (I := I) mc.maps k
  ref_eq : forall k : Nat,
    let D := mc.convergence.metrics.domain k
    letI : TopologicalSpace (MetricSourceDomain (I := I) mc.maps k) := D.topology
    letI : ChartedSpace H (MetricSourceDomain (I := I) mc.maps k) := D.charted
    letI : IsManifold I ∞ (MetricSourceDomain (I := I) mc.maps k) := D.smooth
    D.referenceMetric = D.limitMetric
  rel : exists Crel : Real, 1 <= Crel ∧
    forall k : Nat,
      let D := mc.convergence.metrics.domain k
      letI : TopologicalSpace (MetricSourceDomain (I := I) mc.maps k) := D.topology
      letI : ChartedSpace H (MetricSourceDomain (I := I) mc.maps k) := D.charted
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) mc.maps k) := D.smooth
      MetricUniformEquivalentOn (I := I)
        (Set.univ : Set (MetricSourceDomain (I := I) mc.maps k))
        D.limitMetric D.pullbackMetric Crel
  init_cov : forall q : Nat, exists Cq : Real, 0 <= Cq ∧
    forall (k : Nat) (x : MetricSourceDomain (I := I) mc.maps k),
      let D := mc.convergence.metrics.domain k
      letI : TopologicalSpace (MetricSourceDomain (I := I) mc.maps k) := D.topology
      letI : ChartedSpace H (MetricSourceDomain (I := I) mc.maps k) := D.charted
      letI : T2Space (MetricSourceDomain (I := I) mc.maps k) := D.t2
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) mc.maps k) := D.smooth
      letI : SigmaCompactSpace (MetricSourceDomain (I := I) mc.maps k) := D.sigmaCompact
      metricCovDerivNorm (I := I) q D.pullbackMetric D.limitMetric x <= Cq

namespace StepDCanonData

/-- Move canonical Step-D data from a sequence-level subsequence back to the
original sequence.  The source-domain metrics are rewrapped field by field, so
the canonical reference identity is preserved definitionally. -/
def ofSeqSubseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (f : Nat -> Nat) (hf : StrictMono f)
    (D : StepDCanonData (I := I) (X.subseq f)) :
    StepDCanonData (I := I) X where
  mc := D.mc.ofSeqSubseq f hf
  domain_eq := by
    intro k
    change MetricSourceData.ofSeqSubseq (I := I) f k
        (D.mc.convergence.metrics.domain k) =
      canonDomain (I := I) (D.mc.maps.ofSeqSubseq f) k
    rw [D.domain_eq k]
    rfl
  ref_eq := by
    intro k
    simpa only [MetricCompactnessConclusion.ofSeqSubseq,
      PointedRiemannianCGConverges.ofSeqSubseq,
      MetricCGConvergenceData.ofSeqSubseq,
      MetricSourceData.ofSeqSubseq] using D.ref_eq k
  rel := by
    obtain ⟨Crel, hCrel, hrel⟩ := D.rel
    refine ⟨Crel, hCrel, fun k => ?_⟩
    simpa only [MetricCompactnessConclusion.ofSeqSubseq,
      PointedRiemannianCGConverges.ofSeqSubseq,
      MetricCGConvergenceData.ofSeqSubseq,
      MetricSourceData.ofSeqSubseq] using hrel k
  init_cov := by
    intro q
    obtain ⟨Cq, hCq, hcov⟩ := D.init_cov q
    refine ⟨Cq, hCq, fun k x => ?_⟩
    simpa only [MetricCompactnessConclusion.ofSeqSubseq,
      PointedRiemannianCGConverges.ofSeqSubseq,
      MetricCGConvergenceData.ofSeqSubseq,
      MetricSourceData.ofSeqSubseq] using hcov k x

end StepDCanonData

set_option maxHeartbeats 800000 in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The complete Step D assembly from the honest B/C comparison-map package,
retaining the canonical reference-metric provenance used by its concrete
restrict/pullback convergence construction. -/
noncomputable def compactness_canon
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (P : ∀ k, ProperMetricOn (I := I) (X.obj k))
    (B : StepB1RawInput (X := X) P) :
    StepDCanonData (I := I) X := by
  classical
  let hdirectedEx := directed_of_b1 (I := I) P B
  let σ := Classical.choose hdirectedEx
  have hσpack := Classical.choose_spec hdirectedEx
  have hσ : StrictMono σ := hσpack.1
  have hdirected := hσpack.2
  letI : ∀ j, TopologicalSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).topology
  letI : ∀ j, ChartedSpace H (X.obj (σ j)).M := fun j => (X.obj (σ j)).charted
  letI : ∀ j, IsManifold I ∞ (X.obj (σ j)).M := fun j => (X.obj (σ j)).smooth
  letI : ∀ j, T2Space (X.obj (σ j)).M := fun j => (X.obj (σ j)).t2
  letI : ∀ j, SigmaCompactSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).sigmaCompact
  letI : ∀ j, MetricSpace (X.obj (σ j)).M := fun j => (P (σ j)).ms
  let Ψ := Classical.choose hdirected
  have hΨpack := Classical.choose_spec hdirected
  have hbase := hΨpack.1
  have hdata := hΨpack.2
  letI : ∀ j, MetricSpace (X.obj (σ j)).M := fun j =>
    alignedMetric (I := I) (σ j) (P (σ j))
  letI : ∀ j, IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj (σ j)).M := fun j => by
    change IsManifold I ∞ (X.obj (σ j)).M
    infer_instance
  letI : ∀ j, Bundle.RiemannianBundle
      (fun x : (X.obj (σ j)).M => TangentSpace I x) :=
    fun j => (X.obj (σ j)).riemBundle
  letI : ∀ j, IsRiemannianManifold I (X.obj (σ j)).M := fun j => by
    refine ⟨fun x y => ?_⟩
    have hreal := (P (σ j)).realizes x y
    rw [edist_dist, ← hreal]
    rfl
  letI : ∀ j, ProperSpace (X.obj (σ j)).M := fun j =>
    alignedProper (I := I) (σ j) (P (σ j))
  let b := fun j => (X.obj (σ j)).basepoint
  let g := fun j => (X.obj (σ j)).metric
  have hD : Nonempty (D6ChainData (I := I) b Ψ g) := by
    obtain ⟨j₀, hj₀, D₀, hU, hmap, _φ, _hφ, gInf, _hconv, hclose, hstep⟩ :=
      exists_limits_close (I := I) b Ψ hbase g (by
        intro j x v
        simpa using
          (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
            (I := I) (g j) x v)) hdata
    exact ⟨
      { start := j₀
        one_le := hj₀
        zero := D₀
        source := hU
        maps := hmap
        metric := gInf
        close := hclose
        step := hstep }⟩
  let D := Classical.choice hD
  let j₀ := D.start
  have hj₀ : 1 ≤ j₀ := D.one_le
  let D₀ := D.zero
  let hU := D.source
  let hmap := D.maps
  let gInf := D.metric
  have hclose := D.close
  have hstep := D.step
  letI : ∀ n, Nonempty (tailBallOpen b j₀ n) := fun n => tailBall_nonempty b j₀ n
  letI : ∀ n, SigmaCompactSpace (tailBallOpen b j₀ n) := fun n =>
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I (tailBallOpen b j₀ n).isOpen)
  let S := tailBallSystem (I := I) b Ψ hbase g (by
    intro j x v
    simpa using
      (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) (g j) x v)) j₀ D₀
  let gTail := tailMetric (I := I) b j₀ gInf
  let hgTail : S.MetricCocycle gTail :=
    tailMetricCocycle (I := I) b Ψ hbase g (by
      intro j x v
      simpa using
        (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) (g j) x v)) j₀ D₀ hU hmap gInf hstep
  let L := limitPointedCoc S (tailCenter b j₀ 0) gTail hgTail
  let maps := tailMemberMaps (I := I) P σ Ψ hbase j₀ D₀ gTail hgTail
  have hcomplete : MetricComplete (I := I) L := by
    exact tailLimitComplete (I := I) b Ψ hbase g (by
      intro j x v
      simpa using
        (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) (g j) x v)) j₀ hj₀ D₀
      hU hmap gInf hstep hclose
  let hchain := tailAmbientConv (I := I) b Ψ hbase g (by
    intro j x v
    simpa using
      (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
      (I := I) (g j) x v)) j₀ D₀
    hU hmap gInf hstep hclose
  have hchain_ref : HasCanonRef (I := I) hchain := by
    intro k
    simp only [hchain, tailAmbientConv, ambientCGConverges,
      PointedRiemannianCGConverges.ofRestrictPullback,
      MetricCGConvergenceData.ofRestrictPullback,
      MetricCGConvergenceData.of_derivNormSupOn,
      MetricSourceData.ofRestrictPullback, MetricSourceData.ofCanonical,
      limitPointedCoc, limitPointed]
  have hchain_domain : forall k : Nat,
      hchain.metrics.domain k =
        StepDCanonData.canonDomain (I := I)
          (chainAmbientMaps (I := I) j₀ (tailBallOpen b j₀) S
            (tailCenter b j₀ 0) g gTail hgTail) k := by
    intro k
    simp only [hchain, tailAmbientConv, ambientCGConverges,
      PointedRiemannianCGConverges.ofRestrictPullback,
      MetricCGConvergenceData.ofRestrictPullback,
      MetricCGConvergenceData.of_derivNormSupOn,
      StepDCanonData.canonDomain, StepDCanonData.canonRef,
      limitPointedCoc, limitPointed]
    rfl
  let hconverges : PointedRiemannianCGConverges (I := I) X L
      (fun n => σ (j₀ + n)) maps :=
    tailMemberConv (I := I) P σ Ψ hbase j₀ D₀ gTail hgTail hchain
  have hconverges_ref : HasCanonRef (I := I) hconverges := by
    intro k
    simpa only [hconverges, tailMemberConv,
      PointedRiemannianCGConverges.unrepoint,
      MetricCGConvergenceData.unrepoint,
      PointedRiemannianCGConverges.ofSubseq,
      PointedRiemannianCGConverges.ofSeqSubseq,
      MetricCGConvergenceData.ofSubseq,
      MetricCGConvergenceData.ofSeqSubseq] using hchain_ref k
  have hconverges_domain : forall k : Nat,
      hconverges.metrics.domain k =
        StepDCanonData.canonDomain (I := I) maps k := by
    intro k
    change MetricSourceData.ofSubseq (I := I) (fun n => σ (j₀ + n)) k
        (MetricSourceData.unrepoint (I := I)
          (fun n =>
            (S.toSeqSystem.F (Nat.zero_le n) (tailCenter b j₀ 0) :
              (X.obj (σ (j₀ + n))).M)
          (by
            intro n
            exact congrArg Subtype.val
              (tailCenter_map (I := I) b Ψ hbase g (by
                intro j x v
                simpa using
                  (DifferentialGeometry.Geometry.Riemannian.
                    tensor0SBundle_enorm_eq_riemannianBundle_enorm
                      (I := I) (g j) x v)) j₀ D₀ n))
          k (hchain.metrics.domain k)) =
      StepDCanonData.canonDomain (I := I) maps k
    rw [hchain_domain k]
    rfl
  let mc : MetricCompactnessConclusion (I := I) X :=
    { subseq := fun n => σ (j₀ + n)
      strictMono := fun _ _ hnm => hσ (Nat.add_lt_add_left hnm j₀)
      limit := L
      limit_complete := hcomplete
      maps := maps
      convergence := hconverges }
  have hbounds : HasCanonBounds (I := I) hconverges := by
    sorry
  refine { mc := mc, domain_eq := ?_, ref_eq := ?_, rel := ?_, init_cov := ?_ }
  · intro k
    exact hconverges_domain k
  · intro k
    exact hconverges_ref k
  · simpa only [mc] using hbounds.1
  · simpa only [mc] using hbounds.2

/-- The public Step-D conclusion, obtained by forgetting the concrete
reference-metric provenance retained by `compactness_canon`. -/
noncomputable def compactness_of_b1
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (P : ∀ k, ProperMetricOn (I := I) (X.obj k))
    (B : StepB1RawInput (X := X) P) :
    MetricCompactnessConclusion (I := I) X :=
  (compactness_canon (I := I) P B).mc

end HCGCompactness
end DifferentialGeometry
