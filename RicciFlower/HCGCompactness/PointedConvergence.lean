import RicciFlower.HCGCompactness.Basic
import RicciFlower.Tensor.RSTensor.MetricCompatibility
import RicciFlower.Tensor.RSTensor.NablaOnTensors.Regularity.TotalNabla0S
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Pointed Cheeger--Gromov Convergence Data

The maps and convergence predicates mirror MSM135 Chapter 3: exhaustions of the
limit, basepoint-preserving diffeomorphisms onto their images, and smooth
convergence on compact sets.
-/

noncomputable section

universe u

namespace RicciFlower
namespace HCGCompactness

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

section FixedManifoldMetricConvergence

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [SigmaCompactSpace M]

/-- One covariant-derivative step in the recursive definition of
`metricCovDeriv`.  Keeping the `a + 2` to `a + 3` index adjustment here makes
the recursion less sensitive to future refactors of `totalNabla0S`. -/
noncomputable def metricCovDerivStep
    (gRef : SmoothRiemannianMetric I M) (a : Nat)
    (A :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 2)) :
    Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 3) := by
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  let cov :=
    LeviCivita.leviCivitaConnectionOfMetric (I := I) gRef
  let hcov :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (I := I) (E := E) (M := M) cov (∞ : WithTop ℕ∞) := by
    simpa [cov] using
      LeviCivita.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) gRef
  let hreg :=
    Tensor0SBundle.totalNabla0S_reg (E := E) (H := H)
      (I := I) (M := M) (a + 2) cov hcov A
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, cov, hcov, hreg]
    using
      Tensor0SBundle.totalNabla0S (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (a + 2) cov A hreg

/-- The `a`-fold covariant derivative of a metric tensor, using the
Levi-Civita connection of the reference metric `gRef`.  The derivative slots
are placed first, so the output has covariant valence `a + 2`. -/
noncomputable def metricCovDeriv
    (h gRef : SmoothRiemannianMetric I M) :
    (a : Nat) ->
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 2) :=
  Nat.rec
    (motive := fun a : Nat =>
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 2))
    (by
      haveI : IsManifold I 1 M :=
        IsManifold.of_le (I := I) (M := M) (n := ∞)
          (by decide : (1 : WithTop ℕ∞) ≤ ∞)
      exact Tensor0SBundle.metricTensorField (I := I) (M := M) h)
    (fun a A =>
      by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          metricCovDerivStep (I := I) gRef a A)

/-- The pointwise tensor `∇^a(g_k - g_infty)`, represented as the difference of
the iterated covariant derivatives of the two metric tensors. -/
noncomputable def metricDiffCovDerivAt
    (a : Nat) (gk gInf gRef : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (a + 2) x :=
  metricCovDeriv (I := I) gk gRef a x -
    metricCovDeriv (I := I) gInf gRef a x

/-- The pointwise quantity `|∇^a(g_k - g_infty)|_g` from MSM135 Definition
3.1.  The covariant derivatives are taken using the Levi-Civita connection of
`gRef`, and the tensor norm is the one induced by `gRef`. -/
noncomputable def metricDerivNorm
    (a : Nat) (gk gInf gRef : SmoothRiemannianMetric I M) (x : M) : Real :=
  Real.sqrt
    (Tensor0SBundle.normSq0S (I := I) gRef x (a + 2)
      (metricDiffCovDerivAt (I := I) a gk gInf gRef x))

/-- The displayed `sup_{0 <= a <= p} sup_{x in K}` norm from MSM135
Definition 3.1.  This is a raw low-level supremum; it is only intended to be
used through `MetricCPConvOn`, where compactness of `K` is an explicit
hypothesis. -/
noncomputable def metricDerivNormSupOn
    (K : Set M) (p : Nat)
    (gk gInf gRef : SmoothRiemannianMetric I M) : Real :=
  sSup {r : Real |
    exists a : Nat, a <= p ∧
      exists x : M, x ∈ K ∧
        metricDerivNorm (I := I) a gk gInf gRef x = r}

/-- MSM135 Definition 3.1: `g_k` converges to `g∞` in `C^p`, uniformly on
`K`, with the covariant derivatives and norms measured using the reference
metric `g`.  Since `p : Nat`, the range `0 ≤ a ≤ p` is represented by
`a ≤ p`. -/
def MetricCPConvOn
    (K : Set M) (_hK : IsCompact K) (p : Nat)
    (gSeq : Nat -> SmoothRiemannianMetric I M)
    (gInf gRef : SmoothRiemannianMetric I M) : Prop :=
  forall ε : Real, 0 < ε ->
    exists k0 : Nat, forall k : Nat, k0 <= k ->
      metricDerivNormSupOn (I := I) K p (gSeq k) gInf gRef < ε

/-- `C^∞` convergence uniformly on a fixed compact set, expressed as `C^p`
convergence for every finite `p`. -/
def MetricCInfConvOn
    (K : Set M) (hK : IsCompact K)
    (gSeq : Nat -> SmoothRiemannianMetric I M)
    (gInf gRef : SmoothRiemannianMetric I M) : Prop :=
  forall p : Nat, MetricCPConvOn (I := I) K hK p gSeq gInf gRef

/-- Compact-open `C^∞` convergence on one fixed manifold: every compact set has
uniform `C^p` convergence for every finite `p`. -/
def MetricCInfConvOnCompacts
    (gSeq : Nat -> SmoothRiemannianMetric I M)
    (gInf gRef : SmoothRiemannianMetric I M) : Prop :=
  forall K : Set M, forall hK : IsCompact K,
    MetricCInfConvOn (I := I) K hK gSeq gInf gRef

/-- Data package for compact-open `C^∞` convergence of metrics on one fixed
manifold. -/
structure MetricCInfConvData
    (I : ModelWithCorners Real E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [IsManifold I ∞ M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [SigmaCompactSpace M] where
  gSeq : Nat -> SmoothRiemannianMetric I M
  gInf : SmoothRiemannianMetric I M
  gRef : SmoothRiemannianMetric I M
  converges : MetricCInfConvOnCompacts (I := I) gSeq gInf gRef

end FixedManifoldMetricConvergence

/-- A monotone exhaustion by open sets, as in the paragraph after MSM135
Definition 3.1 and in Hamilton's pointed compactness setup. -/
structure ExhaustsByOpen {M : Type*} [TopologicalSpace M]
    (U : Nat -> Set M) : Prop where
  isOpen : forall k : Nat, IsOpen (U k)
  mono_step : forall k : Nat, U k ⊆ U (k + 1)
  subset :
    forall K : Set M, IsCompact K ->
      exists k0 : Nat, forall k : Nat, k0 <= k -> K ⊆ U k

namespace ExhaustsByOpen

theorem monotone {M : Type*} [TopologicalSpace M] {U : Nat -> Set M}
    (hU : ExhaustsByOpen U) :
    Monotone U := by
  intro i j hij
  induction hij with
  | refl => intro x hx; exact hx
  | step hle ih =>
      exact Set.Subset.trans ih (hU.mono_step _)

theorem subset_of_le {M : Type*} [TopologicalSpace M] {U : Nat -> Set M}
    (hU : ExhaustsByOpen U) {i j : Nat} (hij : i <= j) :
    U i ⊆ U j :=
  hU.monotone hij

end ExhaustsByOpen

/-- Exhaustion and comparison maps for pointed Cheeger--Gromov convergence.

The comparison maps are actual smooth partial diffeomorphisms from the limit
manifold onto open images in the sequence manifolds.  Their total functions
exist globally because `PartialDiffeomorph` is implemented through a
`PartialEquiv`, but all geometric content below is restricted to `source k`. -/
structure PointedCGHMaps
    (X : PointedFlowSeq (I := I))
    (L : PointedFlowData (I := I) X.D)
    (subseq : Nat -> Nat) where
  partialDiffeomorph :
    forall k : Nat,
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M :=
        (X.term (subseq k)).charted
      PartialDiffeomorph I I L.M (X.term (subseq k)).M (∞ : WithTop ℕ∞)
  source_exhausts :
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    ExhaustsByOpen (fun k =>
      letI : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M :=
        (X.term (subseq k)).charted
      (partialDiffeomorph k).source)
  base_mem :
    forall k : Nat,
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M :=
        (X.term (subseq k)).charted
      L.basepoint ∈ (partialDiffeomorph k).source
  basepoint_map :
    forall k : Nat,
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M :=
        (X.term (subseq k)).charted
      partialDiffeomorph k L.basepoint = (X.term (subseq k)).basepoint

namespace PointedCGHMaps

def source
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X L subseq) (k : Nat) : Set L.M := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  letI : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  exact (Φ.partialDiffeomorph k).source

def target
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X L subseq) (k : Nat) :
    Set ((X.term (subseq k)).M) := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  letI : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  exact (Φ.partialDiffeomorph k).target

def map
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X L subseq) (k : Nat) :
    L.M -> (X.term (subseq k)).M := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  letI : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  exact fun x => (Φ.partialDiffeomorph k) x

theorem source_open
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace L.M := L.topology
    IsOpen (Φ.source k) := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  letI : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  exact (Φ.partialDiffeomorph k).open_source

theorem target_open
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).topology
    IsOpen (Φ.target k) := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  letI : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  exact (Φ.partialDiffeomorph k).open_target

theorem source_mono
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace L.M := L.topology
    Φ.source k ⊆ Φ.source (k + 1) := by
  letI : TopologicalSpace L.M := L.topology
  exact Φ.source_exhausts.mono_step k

theorem source_subset
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X L subseq)
    {K : Set L.M}
    (hK :
      letI : TopologicalSpace L.M := L.topology
      IsCompact K) :
    exists k0 : Nat, forall k : Nat, k0 <= k -> K ⊆ Φ.source k := by
  letI : TopologicalSpace L.M := L.topology
  exact Φ.source_exhausts.subset K hK

end PointedCGHMaps

/-- The source domain of the `k`th comparison map as a subtype.  The manifold
structure and restricted/pulled-back metrics on this subtype are supplied by
`SourceDomainMetricData`; this keeps the missing open-domain backend explicit
instead of silently extending metrics to all of the limit manifold. -/
abbrev SourceDomain
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X L subseq) (k : Nat) :=
  {x : L.M // x ∈ Φ.source k}

def sourceCompactSet
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X L subseq) (k : Nat)
    (K : Set L.M) : Set (SourceDomain (I := I) Φ k) :=
  {x | (x : L.M) ∈ K}

/-- Metrics on a source domain together with the formulas saying that they are
the restricted limit metric and the pullback of the corresponding sequence
metric along the partial diffeomorphism. -/
structure SourceDomainMetricData
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X L subseq) (k : Nat) where
  topology : TopologicalSpace (SourceDomain (I := I) Φ k)
  charted : ChartedSpace H (SourceDomain (I := I) Φ k)
  t2 : T2Space (SourceDomain (I := I) Φ k)
  smooth : IsManifold I ∞ (SourceDomain (I := I) Φ k)
  smoothPlus :
    IsManifold I ((∞ : WithTop ℕ∞) + 1) (SourceDomain (I := I) Φ k)
  sigmaCompact : SigmaCompactSpace (SourceDomain (I := I) Φ k)
  limitMetric :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := topology
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := charted
    Real -> SmoothRiemannianMetric I (SourceDomain (I := I) Φ k)
  pullbackMetric :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := topology
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := charted
    Real -> SmoothRiemannianMetric I (SourceDomain (I := I) Φ k)
  referenceMetric :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := topology
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := charted
    Real -> SmoothRiemannianMetric I (SourceDomain (I := I) Φ k)
  compact_preimage :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := topology
    letI : TopologicalSpace L.M := L.topology
    forall K : Set L.M, IsCompact K ->
      IsCompact (sourceCompactSet (I := I) Φ k K)
  limit_inner :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := topology
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := charted
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : T2Space L.M := L.t2
    letI : IsManifold I ∞ L.M := L.smooth
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.M := L.smoothPlus
    letI : SigmaCompactSpace L.M := L.sigmaCompact
    forall (t : Real) (x : SourceDomain (I := I) Φ k)
      (v w : TangentSpace I x),
        (limitMetric t).inner x v w =
          (L.S.family.metric t).inner (x : L.M)
            ((mfderiv I I (fun y : SourceDomain (I := I) Φ k => (y : L.M)) x) v)
            ((mfderiv I I (fun y : SourceDomain (I := I) Φ k => (y : L.M)) x) w)
  pullback_inner :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := topology
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := charted
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : T2Space L.M := L.t2
    letI : IsManifold I ∞ L.M := L.smooth
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.M := L.smoothPlus
    letI : SigmaCompactSpace L.M := L.sigmaCompact
    letI : TopologicalSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).topology
    letI : ChartedSpace H (X.term (subseq k)).M :=
      (X.term (subseq k)).charted
    letI : T2Space (X.term (subseq k)).M :=
      (X.term (subseq k)).t2
    letI : IsManifold I ∞ (X.term (subseq k)).M :=
      (X.term (subseq k)).smooth
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term (subseq k)).M :=
      (X.term (subseq k)).smoothPlus
    letI : SigmaCompactSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).sigmaCompact
    forall (t : Real) (x : SourceDomain (I := I) Φ k)
      (v w : TangentSpace I x),
        (pullbackMetric t).inner x v w =
          ((X.term (subseq k)).S.family.metric t).inner
            (Φ.map k (x : L.M))
            ((mfderiv I I
              (fun y : SourceDomain (I := I) Φ k => Φ.map k (y : L.M)) x) v)
            ((mfderiv I I
              (fun y : SourceDomain (I := I) Φ k => Φ.map k (y : L.M)) x) w)

namespace SourceDomainMetricData

noncomputable def derivNormSupOn
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    {k : Nat}
    {Φ : PointedCGHMaps (I := I) X L subseq}
    (D : SourceDomainMetricData (I := I) Φ k)
    (K : Set L.M) (p : Nat) (t : Real) : Real := by
  letI : TopologicalSpace (SourceDomain (I := I) Φ k) := D.topology
  letI : ChartedSpace H (SourceDomain (I := I) Φ k) := D.charted
  letI : T2Space (SourceDomain (I := I) Φ k) := D.t2
  letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := D.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1)
      (SourceDomain (I := I) Φ k) := D.smoothPlus
  letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) := D.sigmaCompact
  exact metricDerivNormSupOn (I := I)
    (sourceCompactSet (I := I) Φ k K) p
    (D.pullbackMetric t) (D.limitMetric t) (D.referenceMetric t)

end SourceDomainMetricData

def SourceMetricCPConvOn
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X L subseq)
    (D : forall k : Nat, SourceDomainMetricData (I := I) Φ k)
    (K : Set L.M)
    (_hK : letI : TopologicalSpace L.M := L.topology; IsCompact K)
    (p : Nat) (t : Real) : Prop :=
  forall ε : Real, 0 < ε ->
    exists k0 : Nat, forall k : Nat, k0 <= k ->
      K ⊆ Φ.source k /\
        (D k).derivNormSupOn (I := I) K p t < ε

def SourceMetricCPConvOnWindow
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X L subseq)
    (D : forall k : Nat, SourceDomainMetricData (I := I) Φ k)
    (K : Set L.M)
    (_hK : letI : TopologicalSpace L.M := L.topology; IsCompact K)
    (p : Nat)
    (a b : Real) : Prop :=
  forall ε : Real, 0 < ε ->
    exists k0 : Nat, forall k : Nat, k0 <= k ->
      K ⊆ Φ.source k /\
        forall t : Real, t ∈ Set.Icc a b ->
          (D k).derivNormSupOn (I := I) K p t < ε

/-- Compact-open smooth convergence of the pulled-back spatial metrics on the
source domains.  This is theorem-facing data: constructing the source subtype
manifold structures and proving the pullback formulas is the current
open-domain metric frontier. -/
structure SourceMetricConvergenceData
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X L subseq) where
  domain : forall k : Nat, SourceDomainMetricData (I := I) Φ k
  converges :
    forall K : Set L.M,
      forall hK : letI : TopologicalSpace L.M := L.topology; IsCompact K,
      forall p : Nat,
      forall t : Real, t ∈ X.D.carrier ->
        SourceMetricCPConvOn (I := I) Φ domain K hK p t

/-- Compact-open smooth convergence on spacetime windows. -/
structure SourceSpacetimeConvergenceData
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X L subseq)
    (D : forall k : Nat, SourceDomainMetricData (I := I) Φ k) where
  converges_on_windows :
    forall K : Set L.M,
      forall hK : letI : TopologicalSpace L.M := L.topology; IsCompact K,
      forall p : Nat,
      forall a b : Real, Set.Icc a b ⊆ X.D.carrier ->
        SourceMetricCPConvOnWindow (I := I) Φ D K hK p a b

/-- Pointwise pullback convergence for real-valued spacetime functions along
the Cheeger--Gromov comparison maps.  This is the typed interface needed by
Hamilton Section 12 whenever the argument only uses scalar-valued convergence,
for example scalar curvature or scale-invariant pinching ratios. -/
def FunctionPullbackTendsto
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    (Phi : PointedCGHMaps (I := I) X L subseq)
    (uSeq : forall k : Nat, Real -> (X.term (subseq k)).M -> Real)
    (uInf : Real -> L.M -> Real) : Prop :=
  forall t : Real, forall x : L.M,
    Filter.Tendsto (fun k : Nat => uSeq k t (Phi.map k x))
      Filter.atTop (nhds (uInf t x))

/-- If pulled-back real functions converge pointwise and are eventually bounded
above by quantities tending to `0`, then the limit is bounded above by every
positive number.

This is the order-closure step used by the Section 12 pinching transfer after
the rescaled estimate supplies a decaying upper bound. -/
theorem FunctionPullbackTendsto.le_of_bound0
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    {Phi : PointedCGHMaps (I := I) X L subseq}
    {uSeq : forall k : Nat, Real -> (X.term (subseq k)).M -> Real}
    {uInf : Real -> L.M -> Real}
    (hconv : FunctionPullbackTendsto (I := I) Phi uSeq uInf)
    (bound : Real -> L.M -> Nat -> Real)
    (hbound :
      forall t : Real, forall x : L.M,
        Filter.Tendsto (bound t x) Filter.atTop (nhds 0) /\
          (∀ᶠ k in Filter.atTop,
            uSeq k t (Phi.map k x) <= bound t x k)) :
    forall t : Real, forall x : L.M, forall η : Real, 0 < η ->
      uInf t x <= η := by
  intro t x η hη
  have hle0 : uInf t x <= 0 := by
    exact le_of_tendsto_of_tendsto (hconv t x) (hbound t x).1 (hbound t x).2
  exact le_trans hle0 (le_of_lt hη)

/-- Pointwise pullback convergence of scalar curvature along the comparison
maps of a smooth Cheeger--Gromov--Hamilton limit. -/
def ScalarPullbackTendsto
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    (Phi : PointedCGHMaps (I := I) X L subseq) : Prop :=
  FunctionPullbackTendsto (I := I) Phi
    (fun k t x =>
      letI : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M :=
        (X.term (subseq k)).charted
      letI : IsManifold I ∞ (X.term (subseq k)).M :=
        (X.term (subseq k)).smooth
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term (subseq k)).M :=
        (X.term (subseq k)).smoothPlus
      letI : SigmaCompactSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).sigmaCompact
      letI : T2Space (X.term (subseq k)).M :=
        (X.term (subseq k)).t2
      (X.term (subseq k)).S.scalar t x)
    (fun t x =>
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : IsManifold I ∞ L.M := L.smooth
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.M := L.smoothPlus
      letI : SigmaCompactSpace L.M := L.sigmaCompact
      letI : T2Space L.M := L.t2
      L.S.scalar t x)

/-- Smooth pointed Cheeger--Gromov convergence of the spatial metrics at one
time, packaged around the comparison maps. -/
structure PointedCGConverges
    (X : PointedFlowSeq (I := I))
    (L : PointedFlowData (I := I) X.D)
    (subseq : Nat -> Nat) where
  maps : PointedCGHMaps (I := I) X L subseq
  metrics : SourceMetricConvergenceData (I := I) maps

/-- Smooth pointed Cheeger--Gromov--Hamilton convergence of Ricci flows on the
common time interval. -/
structure SmoothCGHConverges
    (X : PointedFlowSeq (I := I))
    (L : PointedFlowData (I := I) X.D)
    (subseq : Nat -> Nat) where
  spatial : PointedCGConverges (I := I) X L subseq
  scalar_converges : ScalarPullbackTendsto (I := I) spatial.maps
  spacetime :
    SourceSpacetimeConvergenceData (I := I) spatial.maps
      spatial.metrics.domain

end HCGCompactness
end RicciFlower
