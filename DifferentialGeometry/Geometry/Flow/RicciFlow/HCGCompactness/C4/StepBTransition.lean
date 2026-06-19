import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepBLocalizedAA
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepBInputs

set_option autoImplicit false

/-!
# Local transition-map limits + cocycle (MSM135 Ch4 Step B, `lbl394` transition part)

The transition half of `lbl394`.  For `α, β` with overlapping balls, the book's
normal-coordinate transition maps

  `J_k^{αβ} : E^α → Ē^β`,   `J̄_k^{αβ} : Ē^α → vec E^β`,   `J̄_k^{βα} ∘ J_k^{αβ} = id_β`

are Riemannian isometries between the pulled-back metrics with uniformly bounded
derivatives, so a (diagonalized) subsequence converges in `C^∞` on compacts to limit
transition maps `J_∞^{αβ}`, `J̄_∞^{αβ}` satisfying the limit cocycle
`J̄_∞^{βα} ∘ J_∞^{αβ} = id_β`.

The transition maps live on nested **Euclidean balls of the same model space `E`**
(`E^α, Ē^β ⊆ E`), so this is the `F = E` case of the localized diffeomorphism
compactness `isometry_seq_diffeo_on` (B-loc).  `exists_transitionLimit_on` packages it
in the book's `J`/`J̄` cocycle language; the inverse identities stay **conditional on
domain membership** (the inner-ball containment `E^β ⊆ Ē^β ⊆ vec E^β` discharges them in
B-glue), exactly as in `isometry_seq_diffeo_on`.

## HCG `normalTransition` wrapper — delivered by honest exposure

`exists_transitionLimit_normalTransition` wires `normalTransition` +
`ExpInverseDerivBoundInput` into `exists_transitionLimit_on`, for a fixed pair of center
sequences `x k, y k : (X.obj k).M`.  The two missing facts are **honestly exposed** as
explicit hypotheses (bare statements, not renamed predicates):

* `C^∞` smoothness `ContDiffOn ℝ ⊤ (normalTransition (X.obj k) (x k) (y k)) U` — the
  frontier-1 gap (`normalTransition = normalChartAt ∘ expMapDiffeo`, and the realized
  `expMapDiffeo` is `PartialDiffeomorph … 1`, only `C^1`; a single-radius
  `ContMDiffOn ⊤` exp on a ball is the `JacobiVariation.md` foundational TODO);
* the chart-overlap containment `NormalOverlapOn (X.obj k) (x k) (y k) U` — the honest
  domain input bridging `ExpInverseDerivBoundInput`'s overlap bounds to bounds on `U`.

The cocycle `hLeft`/`hRight` stay **conditional on `U`/`V`** (the overlap), never global
(`normalTransition` is junk off the overlap).  See `StepBTransition.md`.
-/

namespace DifferentialGeometry
namespace HCGCompactness

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Local transition-map limits + cocycle** (`lbl394` transition part, generic
model-coordinate form).  Transition maps `J k : U → V` and `J̄ k : V → U` on nested open
Euclidean domains `U, V ⊆ E`, each `C^∞` on its domain, both satisfying the localized
isometry derivative bounds, and mutually inverse, have a subsequence whose limits
`Jinf`, `J̄inf` converge in `C^∞` on compacts and satisfy the **limit cocycle**
`J̄inf (Jinf x) = x` (and symmetrically) — stated conditionally on domain membership
(`Jinf x ∈ V`, `J̄inf y ∈ U`), supplied later by the book's nested-ball containment.

This is `isometry_seq_diffeo_on` in transition (`F = E`, same model space) language. -/
theorem exists_transitionLimit_on
    {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    (J : ℕ → E → E) (Jbar : ℕ → E → E)
    (hJ : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (J k) U)
    (hJbar : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (Jbar k) V)
    (hbJ : IsometryDerivBoundsOn U J) (hbJbar : IsometryDerivBoundsOn V Jbar)
    (hLeft : ∀ k, ∀ x ∈ U, Jbar k (J k x) = x) (hRight : ∀ k, ∀ y ∈ V, J k (Jbar k y) = y) :
    ∃ (φ : ℕ → ℕ) (Jinf : E → E) (Jbarinf : E → E),
      StrictMono φ ∧ ContDiffOn ℝ (⊤ : ℕ∞) Jinf U ∧ ContDiffOn ℝ (⊤ : ℕ∞) Jbarinf V ∧
        MapCInfConvOnCompacts U (fun k => J (φ k)) Jinf ∧
        MapCInfConvOnCompacts V (fun k => Jbar (φ k)) Jbarinf ∧
        (∀ x ∈ U, Jinf x ∈ V → Jbarinf (Jinf x) = x) ∧
        (∀ y ∈ V, Jbarinf y ∈ U → Jinf (Jbarinf y) = y) :=
  isometry_seq_diffeo_on hU hV J Jbar hJ hJbar hbJ hbJbar hLeft hRight

/-! ## HCG-facing wrapper: `normalTransition` limit from the `lbl418` honest input -/

section HCGNormalTransition

open Bundle
open scoped Manifold ContDiff Bundle
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

/-- **Chart-overlap domain input** for the `normalTransition` wrapper: on `U`, every
point lies in the `exp_x`-source and its image lies in the `normalChart_y`-source, so the
overlap bound of `ExpInverseDerivBoundInput` applies.  This is the honest domain/overlap
predicate the planner asked for (the bare condition, not a completed theorem). -/
def NormalOverlapOn
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x y : Y.M) (U : Set E) : Prop :=
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  forall z : E, z ∈ U ->
    z ∈ (expMapDiffeo (I := I) Y.metric x).source ∧
      expMapDiffeo (I := I) Y.metric x z ∈ (normalChartAt (I := I) Y.metric y).source

/-- **`normalTransition` transition-limit** (`lbl394` transition, fixed-pair HCG form).
For center sequences `x k, y k : (X.obj k).M` on nested open domains `U, V`, with the
`lbl418` exp⁻¹-derivative input (`input`), the honestly-exposed `C^∞` smoothness of each
transition map (`hsmoothJ`/`hsmoothJbar`, the frontier-1 gap), the chart-overlap inputs
(`hovlJ`/`hovlJbar`), and the conditional cocycle (`hLeft`/`hRight`, valid on the
overlaps), a subsequence of the transition maps converges in `C^∞` on compacts to limit
transition maps with the limit cocycle (conditional on domain membership).  Fixed-pair
only — NOT the finite diagonal over all `α, β`. -/
theorem exists_transitionLimit_normalTransition
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (input : ExpInverseDerivBoundInput (I := I) X)
    (x y : ∀ k : ℕ, (X.obj k).M)
    {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    (hovlJ : ∀ k, NormalOverlapOn (I := I) (X.obj k) (x k) (y k) U)
    (hovlJbar : ∀ k, NormalOverlapOn (I := I) (X.obj k) (y k) (x k) V)
    (hsmoothJ : ∀ k,
      ContDiffOn ℝ (⊤ : ℕ∞) (normalTransition (I := I) (X.obj k) (x k) (y k)) U)
    (hsmoothJbar : ∀ k,
      ContDiffOn ℝ (⊤ : ℕ∞) (normalTransition (I := I) (X.obj k) (y k) (x k)) V)
    (hLeft : ∀ k, ∀ z ∈ U,
      normalTransition (I := I) (X.obj k) (y k) (x k)
        (normalTransition (I := I) (X.obj k) (x k) (y k) z) = z)
    (hRight : ∀ k, ∀ w ∈ V,
      normalTransition (I := I) (X.obj k) (x k) (y k)
        (normalTransition (I := I) (X.obj k) (y k) (x k) w) = w) :
    ∃ (φ : ℕ → ℕ) (Jinf : E → E) (Jbarinf : E → E),
      StrictMono φ ∧ ContDiffOn ℝ (⊤ : ℕ∞) Jinf U ∧ ContDiffOn ℝ (⊤ : ℕ∞) Jbarinf V ∧
        MapCInfConvOnCompacts U
          (fun k => normalTransition (I := I) (X.obj (φ k)) (x (φ k)) (y (φ k))) Jinf ∧
        MapCInfConvOnCompacts V
          (fun k => normalTransition (I := I) (X.obj (φ k)) (y (φ k)) (x (φ k))) Jbarinf ∧
        (∀ z ∈ U, Jinf z ∈ V → Jbarinf (Jinf z) = z) ∧
        (∀ w ∈ V, Jbarinf w ∈ U → Jinf (Jbarinf w) = w) :=
  exists_transitionLimit_on hU hV
    (fun k => normalTransition (I := I) (X.obj k) (x k) (y k))
    (fun k => normalTransition (I := I) (X.obj k) (y k) (x k))
    hsmoothJ hsmoothJbar
    (fun r _K _hK hKU => ⟨input.derivC r, fun k z hz =>
      input.exp_inv_deriv k r (x k) (y k) z (hovlJ k z (hKU hz)).1 (hovlJ k z (hKU hz)).2⟩)
    (fun r _K _hK hKU => ⟨input.derivC r, fun k z hz =>
      input.exp_inv_deriv k r (y k) (x k) z (hovlJbar k z (hKU hz)).1 (hovlJbar k z (hKU hz)).2⟩)
    hLeft hRight

end HCGNormalTransition

end HCGCompactness
end DifferentialGeometry
