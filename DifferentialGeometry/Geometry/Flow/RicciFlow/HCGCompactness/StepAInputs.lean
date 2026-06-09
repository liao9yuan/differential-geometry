import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.InjectivityRadius

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# MSM135 Chapter 4 Step A honest inputs (A0 / A0')

These three structures are the self-contained Step A honest inputs of MSM135
Chapter 4 (the proof of `metricCompactness`, Theorem 3.9):

* `PointedSeqDistance` — the supplied Riemannian distance per sequence term;
* `InjRadiusDecayInput` — the Cheeger--Gromov--Taylor injectivity-radius decay
  estimate (Proposition `lbl384`, Step A input A0);
* `VolumeComparisonInput` — the Bishop--Gromov bounded intersection multiplicity
  (Step A input A0').

They were relocated here from `GeometricInputs.lean`, whose S6 exp⁻¹-derivative
machinery (`NormalChartFor`, `normalTransitionMap`, `ExpInverseDerivBoundInput`)
currently does not compile because of a dangling
`RicciFlower.Coordinates.NormalChartData` reference.  These Step A inputs do not
depend on that machinery, so they live in their own building module.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle
open scoped Manifold ContDiff Topology ENNReal Bundle

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

/-- Distance data for a pointed Riemannian sequence.

This is intended to be the Riemannian distance associated to each stored metric.
It is kept as theorem-facing input here because `PointedRiemannianManifold`
does not store the emetric/vector-bundle instances needed to make `dist`
available globally. -/
abbrev PointedSeqDistance
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) : Type _ :=
  forall k : Nat, (X.obj k).M -> (X.obj k).M -> Real

/-- MSM135 Chapter 4, Proposition `lbl384`:
Cheeger--Gromov--Taylor injectivity-radius decay from basepoint injectivity
and curvature control.

The field `decay` is the deep external theorem.  It is consumed by Step A
covering and good-ball constructions. -/
structure InjRadiusDecayInput
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  baseInj : BaseInjBound (I := I) X
  dist : PointedSeqDistance (I := I) X
  a : Real
  C : Real
  a_pos : 0 < a
  C_nonneg : 0 <= C
  decay :
    forall k : Nat, forall x : (X.obj k).M,
      HasInjRadiusAt (I := I) (X.obj k) x
        (a * (min baseInj.ρ 1) ^ Module.finrank Real E *
          Real.exp (-C * dist k x (X.obj k).basepoint))

/-- MSM135 Chapter 4 volume-comparison input, used after Proposition `lbl384`:
the Bishop--Gromov comparison estimate gives a bounded intersection
multiplicity `I(n,C₀)`.

Mathlib may eventually provide a Bishop--Gromov theorem directly; until then,
`ballMult` is the weakest bounded-overlap form consumed by Step A. -/
structure VolumeComparisonInput
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  dist : PointedSeqDistance (I := I) X
  Imult : Nat
  /-- Consumed by Step A: in any `r`-separated finite center family, at most
  `Imult` centers can lie in a fixed controlled ball. -/
  ballMult :
    forall k : Nat, forall {α : Type u}, [Fintype α] -> [DecidableEq α] ->
      forall centers : α -> (X.obj k).M, forall r : Real, 0 < r ->
        (forall i j : α, i ≠ j ->
          r <= dist k (centers i) (centers j)) ->
        forall z : (X.obj k).M, forall J : Finset α,
          (forall j : α, j ∈ J ->
            dist k (centers j) z <= 4 * r) ->
          J.card <= Imult

end HCGCompactness
end DifferentialGeometry
