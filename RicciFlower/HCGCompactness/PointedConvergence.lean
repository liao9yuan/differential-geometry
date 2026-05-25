import RicciFlower.HCGCompactness.Basic
import RicciFlower.Tensor.RSTensor.NablaOnTensors.Regularity.TotalNabla0S

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
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

section FixedManifoldMetricConvergence

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ∞ M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [SigmaCompactSpace M]

/-- The `(0,2)` tensor field `g_k - g_infty` associated to two smooth
Riemannian metrics. -/
noncomputable def metricTensorDiff
    (gk gInf : SmoothRiemannianMetric I M) :
    Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2 :=
  RiemannianMetric.to02Tensor (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) gk -
    RiemannianMetric.to02Tensor (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) gInf

/-- The `a`-fold covariant derivative of `g_k - g_infty`, using the
Levi-Civita connection of the reference metric `g`.  The derivative slots are
placed first, so the output has covariant valence `a + 2`. -/
noncomputable def metricDiffCovDeriv
    (gk gInf gRef : SmoothRiemannianMetric I M) :
    (a : Nat) ->
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 2) :=
  Nat.rec
    (motive := fun a : Nat =>
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 2))
    (metricTensorDiff (I := I) gk gInf)
    (fun a A =>
      by
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
              (I := I) (M := M) (a + 2) cov A hreg)

/-- The pointwise quantity `|∇^a(g_k - g_infty)|_g` from MSM135 Definition
3.1.  The covariant derivatives are taken using the Levi-Civita connection of
`gRef`, and the tensor norm is the one induced by `gRef`. -/
noncomputable def metricDerivNorm
    (a : Nat) (gk gInf gRef : SmoothRiemannianMetric I M) (x : M) : Real :=
  Real.sqrt
    (Tensor0SBundle.normSq0S (I := I) gRef x (a + 2)
      (metricDiffCovDeriv (I := I) gk gInf gRef a x))

/-- The displayed `sup_{0 <= a <= p} sup_{x in K}` norm from MSM135
Definition 3.1. -/
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
    (K : Set M) (p : Nat)
    (gSeq : Nat -> SmoothRiemannianMetric I M)
    (gInf gRef : SmoothRiemannianMetric I M) : Prop :=
  forall ε : Real, 0 < ε ->
    exists k0 : Nat, forall k : Nat, k0 <= k ->
      metricDerivNormSupOn (I := I) K p (gSeq k) gInf gRef < ε

/-- `C^∞` convergence uniformly on a fixed compact set, expressed as `C^p`
convergence for every finite `p`. -/
def MetricCInfConvOn
    (K : Set M)
    (gSeq : Nat -> SmoothRiemannianMetric I M)
    (gInf gRef : SmoothRiemannianMetric I M) : Prop :=
  forall p : Nat, MetricCPConvOn (I := I) K p gSeq gInf gRef

/-- Compact-open `C^∞` convergence on one fixed manifold: every compact set has
uniform `C^p` convergence for every finite `p`. -/
def MetricCInfConvOnCompacts
    (gSeq : Nat -> SmoothRiemannianMetric I M)
    (gInf gRef : SmoothRiemannianMetric I M) : Prop :=
  forall K : Set M, IsCompact K ->
    MetricCInfConvOn (I := I) K gSeq gInf gRef

/-- Data package for compact-open `C^∞` convergence of metrics on one fixed
manifold. -/
structure MetricCInfConvData
    (I : ModelWithCorners Real E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ∞ M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [SigmaCompactSpace M] where
  gSeq : Nat -> SmoothRiemannianMetric I M
  gInf : SmoothRiemannianMetric I M
  gRef : SmoothRiemannianMetric I M
  converges : MetricCInfConvOnCompacts (I := I) gSeq gInf gRef

end FixedManifoldMetricConvergence

/-- An exhaustion by open sets, as in the paragraph after MSM135 Definition
3.1. -/
def ExhaustsByOpen {M : Type*} [TopologicalSpace M]
    (U : Nat -> Set M) : Prop :=
  (forall k : Nat, IsOpen (U k)) /\
    forall K : Set M, IsCompact K ->
      exists k0 : Nat, forall k : Nat, k0 <= k -> K ⊆ U k

namespace ExhaustsByOpen

theorem isOpen {M : Type*} [TopologicalSpace M] {U : Nat -> Set M}
    (hU : ExhaustsByOpen U) (k : Nat) :
    IsOpen (U k) :=
  hU.1 k

theorem subset {M : Type*} [TopologicalSpace M] {U : Nat -> Set M}
    (hU : ExhaustsByOpen U) {K : Set M} (hK : IsCompact K) :
    exists k0 : Nat, forall k : Nat, k0 <= k -> K ⊆ U k :=
  hU.2 K hK

end ExhaustsByOpen

/-- Exhaustion and comparison maps for pointed Cheeger--Gromov convergence. -/
structure PointedCGHMaps
    (X : PointedFlowSeq (I := I))
    (L : PointedFlowData (I := I) X.D)
    (subseq : Nat -> Nat) where
  source : Nat -> Set L.M
  target : forall k : Nat, Set ((X.term (subseq k)).M)
  map : forall k : Nat, L.M -> (X.term (subseq k)).M
  source_exhausts :
    letI : TopologicalSpace L.M := L.topology
    ExhaustsByOpen source
  target_open :
    forall k : Nat,
      letI : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      IsOpen (target k)
  base_mem : forall k : Nat, L.basepoint ∈ source k
  basepoint_map :
    forall k : Nat, map k L.basepoint = (X.term (subseq k)).basepoint
  diffeoPredicate : Prop
  diffeomorphisms : diffeoPredicate

namespace PointedCGHMaps

theorem source_open
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace L.M := L.topology
    IsOpen (Φ.source k) := by
  letI : TopologicalSpace L.M := L.topology
  exact Φ.source_exhausts.1 k

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
  exact Φ.source_exhausts.2 K hK

end PointedCGHMaps

/-- Smooth pointed Cheeger--Gromov convergence of the spatial metrics at one
time, packaged around the comparison maps. -/
structure PointedCGConverges
    (X : PointedFlowSeq (I := I))
    (L : PointedFlowData (I := I) X.D)
    (subseq : Nat -> Nat) where
  maps : PointedCGHMaps (I := I) X L subseq
  metricConvergencePredicate : Prop
  metric_converges : metricConvergencePredicate

/-- Smooth pointed Cheeger--Gromov--Hamilton convergence of Ricci flows on the
common time interval.  The spacetime convergence field is the future refinement
point for the compact-open `C^∞` topology on `M × time`. -/
structure SmoothCGHConverges
    (X : PointedFlowSeq (I := I))
    (L : PointedFlowData (I := I) X.D)
    (subseq : Nat -> Nat) where
  spatial : PointedCGConverges (I := I) X L subseq
  spacetimeConvergencePredicate : Prop
  spacetime_converges : spacetimeConvergencePredicate

end HCGCompactness
end RicciFlower
