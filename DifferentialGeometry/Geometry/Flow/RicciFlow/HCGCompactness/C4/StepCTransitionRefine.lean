import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepBTransition

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Step C transition refinement

This file records the small subsequence-stability bridge needed before Step C can
fold the fixed-pair Step-B transition producer over a finite hat family.  It does
not choose the finite hat domains; it only says that the existing transition
producer can be rerun after a previously chosen strict subsequence.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Filter Topology

section HCGNormalTransition

open Bundle
open scoped Manifold ContDiff Bundle
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

/-- Fixed-pair transition extraction after an already chosen master subsequence.

This is the refinement form needed for a later finite-hat fold: applying the
Step-B fixed-pair producer to `X.subseq phi0` gives a further strict subsequence,
and the composed subsequence `phi0 \circ phi` remains strict. -/
theorem existsTransRefine
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (input : ExpInverseDerivBoundInput (I := I) X)
    (phi0 : Nat -> Nat) (hphi0 : StrictMono phi0)
    (x y : forall k : Nat, (X.obj (phi0 k)).M)
    {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    (hovlJ : forall k, NormalOverlapOn (I := I) (X.obj (phi0 k)) (x k) (y k) U)
    (hovlJbar : forall k, NormalOverlapOn (I := I) (X.obj (phi0 k)) (y k) (x k) V)
    (hUx : forall k,
      letI : TopologicalSpace (X.obj (phi0 k)).M := (X.obj (phi0 k)).topology
      letI : ChartedSpace H (X.obj (phi0 k)).M := (X.obj (phi0 k)).charted
      letI : IsManifold I ∞ (X.obj (phi0 k)).M := (X.obj (phi0 k)).smooth
      letI : T2Space (TangentBundle I (X.obj (phi0 k)).M) :=
        (X.obj (phi0 k)).t2TangentBundle
      U ⊆ Metric.ball (0 : E)
        (min input.r₁ (expMapC2Radius (I := I) (X.obj (phi0 k)).metric (x k))))
    (hmapsJ : forall k,
      letI : TopologicalSpace (X.obj (phi0 k)).M := (X.obj (phi0 k)).topology
      letI : ChartedSpace H (X.obj (phi0 k)).M := (X.obj (phi0 k)).charted
      letI : IsManifold I ∞ (X.obj (phi0 k)).M := (X.obj (phi0 k)).smooth
      letI : T2Space (TangentBundle I (X.obj (phi0 k)).M) :=
        (X.obj (phi0 k)).t2TangentBundle
      Set.MapsTo (fun z => expMapDiffeo (I := I) (X.obj (phi0 k)).metric (x k) z) U
        ((fun v : E => (expMap (I := I) (X.obj (phi0 k)).metric (y k)
            (show TangentSpace I (y k) from v) : (X.obj (phi0 k)).M)) ''
          Metric.ball (0 : E)
            (min input.r₁ (expMapC2Radius (I := I) (X.obj (phi0 k)).metric (y k)))))
    (hVy : forall k,
      letI : TopologicalSpace (X.obj (phi0 k)).M := (X.obj (phi0 k)).topology
      letI : ChartedSpace H (X.obj (phi0 k)).M := (X.obj (phi0 k)).charted
      letI : IsManifold I ∞ (X.obj (phi0 k)).M := (X.obj (phi0 k)).smooth
      letI : T2Space (TangentBundle I (X.obj (phi0 k)).M) :=
        (X.obj (phi0 k)).t2TangentBundle
      V ⊆ Metric.ball (0 : E)
        (min input.r₁ (expMapC2Radius (I := I) (X.obj (phi0 k)).metric (y k))))
    (hmapsJbar : forall k,
      letI : TopologicalSpace (X.obj (phi0 k)).M := (X.obj (phi0 k)).topology
      letI : ChartedSpace H (X.obj (phi0 k)).M := (X.obj (phi0 k)).charted
      letI : IsManifold I ∞ (X.obj (phi0 k)).M := (X.obj (phi0 k)).smooth
      letI : T2Space (TangentBundle I (X.obj (phi0 k)).M) :=
        (X.obj (phi0 k)).t2TangentBundle
      Set.MapsTo (fun z => expMapDiffeo (I := I) (X.obj (phi0 k)).metric (y k) z) V
        ((fun v : E => (expMap (I := I) (X.obj (phi0 k)).metric (x k)
            (show TangentSpace I (x k) from v) : (X.obj (phi0 k)).M)) ''
          Metric.ball (0 : E)
            (min input.r₁ (expMapC2Radius (I := I) (X.obj (phi0 k)).metric (x k)))))
    (hLeft : forall k, forall z, z ∈ U ->
      normalTransition (I := I) (X.obj (phi0 k)) (y k) (x k)
        (normalTransition (I := I) (X.obj (phi0 k)) (x k) (y k) z) = z)
    (hRight : forall k, forall w, w ∈ V ->
      normalTransition (I := I) (X.obj (phi0 k)) (x k) (y k)
        (normalTransition (I := I) (X.obj (phi0 k)) (y k) (x k) w) = w) :
    exists (phi : Nat -> Nat) (Jinf : E -> E) (Jbarinf : E -> E),
      StrictMono phi /\ StrictMono (phi0 ∘ phi) /\
        ContDiffOn Real (⊤ : ℕ∞) Jinf U /\ ContDiffOn Real (⊤ : ℕ∞) Jbarinf V /\
        MapCInfConvOnCompacts U
          (fun k => normalTransition (I := I) (X.obj (phi0 (phi k)))
            (x (phi k)) (y (phi k))) Jinf /\
        MapCInfConvOnCompacts V
          (fun k => normalTransition (I := I) (X.obj (phi0 (phi k)))
            (y (phi k)) (x (phi k))) Jbarinf /\
        (forall z, z ∈ U -> Jinf z ∈ V -> Jbarinf (Jinf z) = z) /\
        (forall w, w ∈ V -> Jbarinf w ∈ U -> Jinf (Jbarinf w) = w) := by
  obtain ⟨phi, Jinf, Jbarinf, hphi, hJinf, hJbarinf, hJ, hJbar, hleft, hright⟩ :=
    exists_transitionLimit_normalTransition (I := I) (X := X.subseq phi0)
      (ExpInverseDerivBoundInput.subseq (I := I) input phi0) x y hU hV
      hovlJ hovlJbar hUx hmapsJ hVy hmapsJbar hLeft hRight
  refine ⟨phi, Jinf, Jbarinf, hphi, hphi0.comp hphi, hJinf, hJbarinf, ?_, ?_,
    hleft, hright⟩
  · simpa [PointedRiemannianSeq.subseq] using hJ
  · simpa [PointedRiemannianSeq.subseq] using hJbar

/-- Finite-family transition extraction with one shared subsequence.

This is the abstract finite-hat diagonal for Step C once the concrete hat layer
has supplied centers, domains, overlap containment, and cocycle data for every
active transition pair. -/
theorem existsTransFinite
    {ι : Type*} (s : Finset ι)
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (input : ExpInverseDerivBoundInput (I := I) X)
    (x y : ι -> forall k : Nat, (X.obj k).M)
    (U V : ι -> Set E)
    (hU : forall i, i ∈ s -> IsOpen (U i))
    (hV : forall i, i ∈ s -> IsOpen (V i))
    (hovlJ : forall i, i ∈ s -> forall k,
      NormalOverlapOn (I := I) (X.obj k) (x i k) (y i k) (U i))
    (hovlJbar : forall i, i ∈ s -> forall k,
      NormalOverlapOn (I := I) (X.obj k) (y i k) (x i k) (V i))
    (hUx : forall i, i ∈ s -> forall k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
      U i ⊆ Metric.ball (0 : E)
        (min input.r₁ (expMapC2Radius (I := I) (X.obj k).metric (x i k))))
    (hmapsJ : forall i, i ∈ s -> forall k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
      Set.MapsTo (fun z => expMapDiffeo (I := I) (X.obj k).metric (x i k) z) (U i)
        ((fun v : E => (expMap (I := I) (X.obj k).metric (y i k)
            (show TangentSpace I (y i k) from v) : (X.obj k).M)) ''
          Metric.ball (0 : E)
            (min input.r₁ (expMapC2Radius (I := I) (X.obj k).metric (y i k)))))
    (hVy : forall i, i ∈ s -> forall k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
      V i ⊆ Metric.ball (0 : E)
        (min input.r₁ (expMapC2Radius (I := I) (X.obj k).metric (y i k))))
    (hmapsJbar : forall i, i ∈ s -> forall k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
      Set.MapsTo (fun z => expMapDiffeo (I := I) (X.obj k).metric (y i k) z) (V i)
        ((fun v : E => (expMap (I := I) (X.obj k).metric (x i k)
            (show TangentSpace I (x i k) from v) : (X.obj k).M)) ''
          Metric.ball (0 : E)
            (min input.r₁ (expMapC2Radius (I := I) (X.obj k).metric (x i k)))))
    (hLeft : forall i, i ∈ s -> forall k, forall z, z ∈ U i ->
      normalTransition (I := I) (X.obj k) (y i k) (x i k)
        (normalTransition (I := I) (X.obj k) (x i k) (y i k) z) = z)
    (hRight : forall i, i ∈ s -> forall k, forall w, w ∈ V i ->
      normalTransition (I := I) (X.obj k) (x i k) (y i k)
        (normalTransition (I := I) (X.obj k) (y i k) (x i k) w) = w) :
    exists phi : Nat -> Nat, StrictMono phi /\
      forall i, i ∈ s -> exists Jinf : E -> E, exists Jbarinf : E -> E,
        ContDiffOn Real (⊤ : ℕ∞) Jinf (U i) /\
        ContDiffOn Real (⊤ : ℕ∞) Jbarinf (V i) /\
        MapCInfConvOnCompacts (U i)
          (fun k => normalTransition (I := I) (X.obj (phi k))
            (x i (phi k)) (y i (phi k))) Jinf /\
        MapCInfConvOnCompacts (V i)
          (fun k => normalTransition (I := I) (X.obj (phi k))
            (y i (phi k)) (x i (phi k))) Jbarinf /\
        (forall z, z ∈ U i -> Jinf z ∈ V i -> Jbarinf (Jinf z) = z) /\
        (forall w, w ∈ V i -> Jbarinf w ∈ U i -> Jinf (Jbarinf w) = w) := by
  classical
  revert hU hV hovlJ hovlJbar hUx hmapsJ hVy hmapsJbar hLeft hRight
  induction s using Finset.induction with
  | empty =>
      intro hU hV hovlJ hovlJbar hUx hmapsJ hVy hmapsJbar hLeft hRight
      exact ⟨id, strictMono_id, fun i hi => by simp at hi⟩
  | @insert a s ha IH =>
      intro hU hV hovlJ hovlJbar hUx hmapsJ hVy hmapsJbar hLeft hRight
      obtain ⟨phi0, hphi0, hprev⟩ :=
        IH
          (fun i hi => hU i (Finset.mem_insert_of_mem hi))
          (fun i hi => hV i (Finset.mem_insert_of_mem hi))
          (fun i hi => hovlJ i (Finset.mem_insert_of_mem hi))
          (fun i hi => hovlJbar i (Finset.mem_insert_of_mem hi))
          (fun i hi => hUx i (Finset.mem_insert_of_mem hi))
          (fun i hi => hmapsJ i (Finset.mem_insert_of_mem hi))
          (fun i hi => hVy i (Finset.mem_insert_of_mem hi))
          (fun i hi => hmapsJbar i (Finset.mem_insert_of_mem hi))
          (fun i hi => hLeft i (Finset.mem_insert_of_mem hi))
          (fun i hi => hRight i (Finset.mem_insert_of_mem hi))
      obtain ⟨phi1, Jinf, Jbarinf, hphi1, hcomp, hJinf, hJbarinf, hJ, hJbar,
          hleft, hright⟩ :=
        existsTransRefine (I := I) input phi0 hphi0
          (fun k => x a (phi0 k)) (fun k => y a (phi0 k))
          (hU a (Finset.mem_insert_self a s)) (hV a (Finset.mem_insert_self a s))
          (fun k => hovlJ a (Finset.mem_insert_self a s) (phi0 k))
          (fun k => hovlJbar a (Finset.mem_insert_self a s) (phi0 k))
          (fun k => hUx a (Finset.mem_insert_self a s) (phi0 k))
          (fun k => hmapsJ a (Finset.mem_insert_self a s) (phi0 k))
          (fun k => hVy a (Finset.mem_insert_self a s) (phi0 k))
          (fun k => hmapsJbar a (Finset.mem_insert_self a s) (phi0 k))
          (fun k z hz => hLeft a (Finset.mem_insert_self a s) (phi0 k) z hz)
          (fun k w hw => hRight a (Finset.mem_insert_self a s) (phi0 k) w hw)
      refine ⟨phi0 ∘ phi1, hcomp, fun i hi => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl | his
      · refine ⟨Jinf, Jbarinf, hJinf, hJbarinf, ?_, ?_, hleft, hright⟩
        · simpa [Function.comp_apply] using hJ
        · simpa [Function.comp_apply] using hJbar
      · obtain ⟨Jprev, Jbarprev, hJprev, hJbarprev, hconv, hconvbar,
            hleftprev, hrightprev⟩ := hprev i his
        refine ⟨Jprev, Jbarprev, hJprev, hJbarprev, ?_, ?_, hleftprev, hrightprev⟩
        · simpa [Function.comp_apply] using hconv.comp_subseq hphi1
        · simpa [Function.comp_apply] using hconvbar.comp_subseq hphi1

/-- Full finite-type family form of `existsTransFinite`.

The finite extractor above is convenient for induction over an arbitrary
`Finset`.  Step C's hats are indexed by a full finite type, so this theorem
specializes to `Finset.univ` and exposes the transition limits as actual
families `Jinf i` and `Jbarinf i`, with continuity facts for the averaging
bridge. -/
theorem existsTransUniv
    {ι : Type*} [Finite ι]
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (input : ExpInverseDerivBoundInput (I := I) X)
    (x y : ι -> forall k : Nat, (X.obj k).M)
    (U V : ι -> Set E)
    (hU : forall i, IsOpen (U i))
    (hV : forall i, IsOpen (V i))
    (hovlJ : forall i, forall k,
      NormalOverlapOn (I := I) (X.obj k) (x i k) (y i k) (U i))
    (hovlJbar : forall i, forall k,
      NormalOverlapOn (I := I) (X.obj k) (y i k) (x i k) (V i))
    (hUx : forall i, forall k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
      U i ⊆ Metric.ball (0 : E)
        (min input.r₁ (expMapC2Radius (I := I) (X.obj k).metric (x i k))))
    (hmapsJ : forall i, forall k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
      Set.MapsTo (fun z => expMapDiffeo (I := I) (X.obj k).metric (x i k) z) (U i)
        ((fun v : E => (expMap (I := I) (X.obj k).metric (y i k)
            (show TangentSpace I (y i k) from v) : (X.obj k).M)) ''
          Metric.ball (0 : E)
            (min input.r₁ (expMapC2Radius (I := I) (X.obj k).metric (y i k)))))
    (hVy : forall i, forall k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
      V i ⊆ Metric.ball (0 : E)
        (min input.r₁ (expMapC2Radius (I := I) (X.obj k).metric (y i k))))
    (hmapsJbar : forall i, forall k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
      Set.MapsTo (fun z => expMapDiffeo (I := I) (X.obj k).metric (y i k) z) (V i)
        ((fun v : E => (expMap (I := I) (X.obj k).metric (x i k)
            (show TangentSpace I (x i k) from v) : (X.obj k).M)) ''
          Metric.ball (0 : E)
            (min input.r₁ (expMapC2Radius (I := I) (X.obj k).metric (x i k)))))
    (hLeft : forall i, forall k, forall z, z ∈ U i ->
      normalTransition (I := I) (X.obj k) (y i k) (x i k)
        (normalTransition (I := I) (X.obj k) (x i k) (y i k) z) = z)
    (hRight : forall i, forall k, forall w, w ∈ V i ->
      normalTransition (I := I) (X.obj k) (x i k) (y i k)
        (normalTransition (I := I) (X.obj k) (y i k) (x i k) w) = w) :
    exists phi : Nat -> Nat, StrictMono phi /\
      exists Jinf : ι -> E -> E, exists Jbarinf : ι -> E -> E,
        forall i,
          ContDiffOn Real (⊤ : ℕ∞) (Jinf i) (U i) /\
          ContDiffOn Real (⊤ : ℕ∞) (Jbarinf i) (V i) /\
          ContinuousOn (Jinf i) (U i) /\
          ContinuousOn (Jbarinf i) (V i) /\
          MapCInfConvOnCompacts (U i)
            (fun k => normalTransition (I := I) (X.obj (phi k))
              (x i (phi k)) (y i (phi k))) (Jinf i) /\
          MapCInfConvOnCompacts (V i)
            (fun k => normalTransition (I := I) (X.obj (phi k))
              (y i (phi k)) (x i (phi k))) (Jbarinf i) /\
          (forall z, z ∈ U i -> Jinf i z ∈ V i -> Jbarinf i (Jinf i z) = z) /\
          (forall w, w ∈ V i -> Jbarinf i w ∈ U i -> Jinf i (Jbarinf i w) = w) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  obtain ⟨phi, hphi, hlim⟩ :=
    existsTransFinite (I := I) (Finset.univ : Finset ι) input x y U V
      (fun i _ => hU i) (fun i _ => hV i) (fun i _ => hovlJ i)
      (fun i _ => hovlJbar i) (fun i _ => hUx i) (fun i _ => hmapsJ i)
      (fun i _ => hVy i) (fun i _ => hmapsJbar i) (fun i _ => hLeft i)
      (fun i _ => hRight i)
  let Jinf : ι -> E -> E := fun i =>
    let hi : i ∈ (Finset.univ : Finset ι) := Finset.mem_univ i
    Classical.choose (hlim i hi)
  let Jbarinf : ι -> E -> E := fun i =>
    let hi : i ∈ (Finset.univ : Finset ι) := Finset.mem_univ i
    Classical.choose (Classical.choose_spec (hlim i hi))
  refine ⟨phi, hphi, Jinf, Jbarinf, fun i => ?_⟩
  let hi : i ∈ (Finset.univ : Finset ι) := Finset.mem_univ i
  have hspec :
      ContDiffOn Real (⊤ : ℕ∞) (Classical.choose (hlim i hi)) (U i) ∧
      ContDiffOn Real (⊤ : ℕ∞)
        (Classical.choose (Classical.choose_spec (hlim i hi))) (V i) ∧
      MapCInfConvOnCompacts (U i)
        (fun k => normalTransition (I := I) (X.obj (phi k))
          (x i (phi k)) (y i (phi k))) (Classical.choose (hlim i hi)) ∧
      MapCInfConvOnCompacts (V i)
        (fun k => normalTransition (I := I) (X.obj (phi k))
          (y i (phi k)) (x i (phi k)))
        (Classical.choose (Classical.choose_spec (hlim i hi))) ∧
      (forall z, z ∈ U i ->
        Classical.choose (hlim i hi) z ∈ V i ->
          Classical.choose (Classical.choose_spec (hlim i hi))
            (Classical.choose (hlim i hi) z) = z) ∧
      (forall w, w ∈ V i ->
        Classical.choose (Classical.choose_spec (hlim i hi)) w ∈ U i ->
          Classical.choose (hlim i hi)
            (Classical.choose (Classical.choose_spec (hlim i hi)) w) = w) :=
    Classical.choose_spec (Classical.choose_spec (hlim i hi))
  rcases hspec with ⟨hJinf, hJbarinf, hconv, hconvbar, hleft, hright⟩
  have hJcont : ContinuousOn (Classical.choose (hlim i hi)) (U i) :=
    hJinf.continuousOn
  have hJbarcont :
      ContinuousOn (Classical.choose (Classical.choose_spec (hlim i hi))) (V i) :=
    hJbarinf.continuousOn
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Jinf] using hJinf
  · simpa [Jbarinf] using hJbarinf
  · simpa [Jinf] using hJcont
  · simpa [Jbarinf] using hJbarcont
  · simpa [Jinf] using hconv
  · simpa [Jbarinf] using hconvbar
  · intro z hz hzV
    dsimp [Jinf, Jbarinf] at hzV ⊢
    exact hleft z hz hzV
  · intro w hw hwU
    dsimp [Jinf, Jbarinf] at hwU ⊢
    exact hright w hw hwU

end HCGNormalTransition

end HCGCompactness
end DifferentialGeometry
