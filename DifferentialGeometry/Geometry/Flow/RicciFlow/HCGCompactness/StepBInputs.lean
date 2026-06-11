import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
import DifferentialGeometry.Geometry.Comparison.NormalCoordinates
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.StepAInputs

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# MSM135 Chapter 4 Step B honest input (S6 / `lbl418`)

The Jacobi/Rauch-comparison input for Step B: uniform `C^p` bounds for the
normal-coordinate transition maps `normalChart_y ∘ exp_x : E → E` on chart overlaps
(MSM135 §`lbl-2103`, "derivatives of `exp⁻¹`").  This is the rebuild of the former
`GeometricInputs.lean` S6 section on the NATIVE normal-coordinate API
(`Geometry.Riemannian.expMapDiffeo` / `normalChartAt`), replacing
the dangling `RicciFlower.Coordinates.NormalChartData` reference.

The field `exp_inv_deriv` is the deep external comparison-geometry theorem (the book
cites it; proving it from §5 `S1–S5` is optional later work).  Note the native
`expMapDiffeo` source is *some* open neighbourhood of `0`; widening the charts to the
full `λ`-ball scale (so the bounds apply on the Step A covering balls) is part of the
`lbl383` item-3 frontier, not of this input.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle
open scoped Manifold ContDiff Topology Bundle

open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

/-- The model-coordinate transition map `normalChart_y ∘ exp_x : E → E` of one
pointed Riemannian manifold, built from the native normal-coordinate charts.  Outside
the meaningful domain the partial diffeomorphisms return junk values; the derivative
bounds below are therefore stated only on the chart overlap. -/
noncomputable def normalTransition
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x y : X.M) : E → E :=
  letI : TopologicalSpace X.M := X.topology
  letI : ChartedSpace H X.M := X.charted
  letI : IsManifold I ∞ X.M := X.smooth
  letI : T2Space (TangentBundle I X.M) := X.t2TangentBundle
  fun z =>
    normalChartAt (I := I) X.metric y
      (expMapDiffeo (I := I) X.metric x z)

/-- Derivative bound for one normal-coordinate transition map on the chart overlap. -/
def NormalTransitionDerivBound
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x y : X.M)
    (p : Nat) (C : Real) : Prop :=
  letI : TopologicalSpace X.M := X.topology
  letI : ChartedSpace H X.M := X.charted
  letI : IsManifold I ∞ X.M := X.smooth
  letI : T2Space (TangentBundle I X.M) := X.t2TangentBundle
  forall z : E,
    z ∈ (expMapDiffeo (I := I) X.metric x).source ->
      expMapDiffeo (I := I) X.metric x z ∈
          (normalChartAt (I := I) X.metric y).source ->
        ‖iteratedFDeriv Real p (normalTransition (I := I) X x y) z‖ <= C

/-- MSM135 Chapter 4, section `lbl-2103` (S6 / `lbl418`): Jacobi/Rauch comparison
bounds for derivatives of the normal-coordinate transition maps `exp_y⁻¹ ∘ exp_x`.

The field `exp_inv_deriv` is the deep external theorem, consumed by Steps B/C. -/
structure ExpInverseDerivBoundInput
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  derivC : Nat -> Real
  derivC_nonneg : forall p : Nat, 0 <= derivC p
  /-- Consumed by Steps B/C: uniform `C^p` bounds for the normal-coordinate
  transition map on the overlap of two normal charts. -/
  exp_inv_deriv :
    forall k p : Nat, forall x y : (X.obj k).M,
      NormalTransitionDerivBound (I := I) (X.obj k) x y p (derivC p)

end HCGCompactness
end DifferentialGeometry
