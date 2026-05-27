import RicciFlower.HCGCompactness.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Injectivity-Radius Inputs

This file contains theorem-facing injectivity-radius predicates for the
Hamilton--Cheeger--Gromov compactness interface.  The pointwise predicate is
primitive for now: it is not definitionally `True`, and future exponential-map
or geodesic-ball infrastructure should prove it for concrete metrics.
-/

noncomputable section

universe u uE uH

namespace RicciFlower
namespace HCGCompactness

open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

/-- The injectivity radius of `X` at `x` is at least `ρ`.

This is a primitive theorem-facing predicate until RicciFlower has the
exponential-map and geodesic-ball API needed to define injectivity radius
directly. -/
axiom HasInjRadiusAt
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : X.M) (ρ : Real) : Prop

/-- Uniform injectivity-radius lower bound at the basepoints of a pointed
metric sequence. -/
structure BaseInjBound
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  ρ : Real
  pos : 0 < ρ
  bound : forall i : Nat, HasInjRadiusAt (I := I) (X.obj i) (X.obj i).basepoint ρ

/-- Time-zero basepoint injectivity-radius input for a pointed flow sequence. -/
abbrev FlowBaseInjBound
    (X : PointedFlowSeq.{u, uE, uH} (I := I)) :=
  BaseInjBound (I := I) (X.atZero (I := I))

end HCGCompactness
end RicciFlower
