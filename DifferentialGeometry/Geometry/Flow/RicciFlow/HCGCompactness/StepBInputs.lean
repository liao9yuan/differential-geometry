import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
import DifferentialGeometry.Geometry.Comparison.NormalCoordinates
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.StepAInputs

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# MSM135 Chapter 4 Step B honest inputs (S6 / `lbl418`, and `lbl395`)

This file collects the book-external honest inputs that Step B consumes at the
model-coordinate level.

## S6 / `lbl418` — derivatives of `exp⁻¹`

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

## `lbl395` — normal-coordinate metric bounds

MSM135 Chapter 4 Proposition `lbl395` (Hamilton [H6] Corollary 4.12): in normal
coordinates, `|∇^ℓ Rm| ≤ C_ℓ` forces `½δ ≤ g ≤ 2δ` and uniform bounds on all partial
derivatives of `g`.  This is taken as an honest input now (Planner Ruling Q1); the
native Jacobi/Grönwall discharge is the optional `B0NormalCoordBounds.md` route.

The pulled-back metric is realized concretely as `normalCoordMetric`, the model-space
bilinear-form map `E → (E →L[ℝ] E →L[ℝ] ℝ)`, mirroring `Diffeomorph.pullbackInner`.
The input `NormalCoordMetricBoundInput` records, constants-first, the Euclidean
equivalence and all-orders derivative bounds *only on the relevant normal-coordinate
ball*.  It deliberately does NOT claim total `Set.univ` (`IsometryDerivBounds`)
control; the partial-domain bridge is reserved for the later B-loc brick.
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

/-! ## `lbl395` normal-coordinate metric bounds (honest input) -/

/-- The model-coordinate **pulled-back normal-coordinate metric**
`(H_x)^* g : E → (E →L[ℝ] E →L[ℝ] ℝ)` of one pointed Riemannian manifold, where
`H_x := expMapDiffeo g x : E → M` is the exponential-side normal-coordinate
parametrization at `x`.  At `z : E` it is the continuous bilinear form
`(u, v) ↦ g_{H_x z}(d(H_x)_z u, d(H_x)_z v)`, built from the manifold derivative
`mfderiv` of `H_x` in both slots, in the slot-composition shape of
`Diffeomorph.pullbackInner`.  Outside the normal-coordinate domain the derivative is
junk; the bounds below are therefore stated only on the relevant ball. -/
noncomputable def normalCoordMetric
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    E -> (E →L[Real] E →L[Real] Real) :=
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  fun z =>
    let D : E →L[Real] TangentSpace I (expMapDiffeo (I := I) Y.metric x z) :=
      mfderiv 𝓘(Real, E) I (fun w => expMapDiffeo (I := I) Y.metric x w) z
    (ContinuousLinearMap.precomp Real D).comp
      ((Y.metric.inner (expMapDiffeo (I := I) Y.metric x z)).comp D)

/-- Local Euclidean equivalence of the pulled-back normal-coordinate metric on `U`:
`½‖v‖² ≤ g(z)(v,v) ≤ 2‖v‖²` for every `z ∈ U` and `v` — the quadratic-form form of
the book's `½(δ_ij) ≤ (g_ij) ≤ 2(δ_ij)`. -/
def NormalCoordMetricEquivOn
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) (U : Set E) :
    Prop :=
  forall z : E, z ∈ U -> forall v : E,
    (1 / 2 : Real) * ‖v‖ ^ 2 <= normalCoordMetric (I := I) Y x z v v ∧
      normalCoordMetric (I := I) Y x z v v <= 2 * ‖v‖ ^ 2

-- `iteratedFDeriv` over the nested operator-norm space `E →L[ℝ] E →L[ℝ] ℝ` with
-- `InnerProductSpace ℝ E` in scope needs the project-standard extended (terminating)
-- instance-synthesis budget.
set_option synthInstance.maxHeartbeats 800000 in
/-- Uniform `C^p` Euclidean derivative bound for the pulled-back normal-coordinate
metric on `U`: `‖∇ᵖ g‖ ≤ C` for every `z ∈ U` (`∇` the Euclidean iterated Fréchet
derivative). -/
def NormalCoordMetricDerivBound
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (U : Set E) (p : Nat) (C : Real) : Prop :=
  forall z : E, z ∈ U ->
    ‖iteratedFDeriv Real p (normalCoordMetric (I := I) Y x) z‖ <= C

/-- MSM135 Chapter 4 Proposition `lbl395` (Hamilton [H6] Corollary 4.12), as the
book-external honest input for Step B: in normal coordinates, `|∇^ℓ Rm| ≤ C_ℓ`
forces uniform Euclidean control of the pulled-back metrics.

For each term `k` of the sequence and each chart center `x`, on the
normal-coordinate ball `Metric.ball 0 (radius k x)`:

* `metric_equiv` — the pulled-back metric is uniformly Euclidean-equivalent
  (`½δ ≤ g ≤ 2δ`);
* `metric_deriv` — every Euclidean iterated derivative of order `p` is bounded by the
  uniform constant `metricC p`.

The constants `metricC` are listed first and are uniform over `k` and `x` (the book's
`C̃_ℓ` depend only on `n`, `inj`, and the curvature bounds, all uniform across the
cover); the per-center `radius` only records *where* the bounds apply.  The control is
**local** to the normal-coordinate ball: this input does not claim total `Set.univ`
control — the partial-domain bridge to `IsometryDerivBounds` is the later B-loc
brick. -/
structure NormalCoordMetricBoundInput
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  metricC : Nat -> Real
  metricC_nonneg : forall p : Nat, 0 <= metricC p
  /-- The per-center normal-coordinate radius `min{c₁/√C₀, r₀}` of `lbl395` (book
  scale), recording where the bounds below hold. -/
  radius : forall k : Nat, (X.obj k).M -> Real
  radius_pos : forall (k : Nat) (x : (X.obj k).M), 0 < radius k x
  /-- Uniform Euclidean equivalence `½δ ≤ g ≤ 2δ` of the pulled-back normal-coordinate
  metric on the relevant ball. -/
  metric_equiv :
    forall (k : Nat) (x : (X.obj k).M),
      NormalCoordMetricEquivOn (I := I) (X.obj k) x
        (Metric.ball (0 : E) (radius k x))
  /-- Uniform all-orders Euclidean derivative bounds for the pulled-back metric on the
  relevant ball, with `metricC p` independent of `k` and `x`. -/
  metric_deriv :
    forall (k p : Nat) (x : (X.obj k).M),
      NormalCoordMetricDerivBound (I := I) (X.obj k) x
        (Metric.ball (0 : E) (radius k x)) p (metricC p)

end HCGCompactness
end DifferentialGeometry
