import DifferentialGeometry.Geometry.Riemannian.GaussLemma
import DifferentialGeometry.Geometry.Riemannian.HopfRinow
import DifferentialGeometry.Geometry.Riemannian.Exponential.Definition
import DifferentialGeometry.Geometry.Riemannian.Exponential.LocalDiffeomorphism
import DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
import DifferentialGeometry.Integral.Measure.ChartDensity
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.Riemannian.PathELength

set_option linter.unusedSectionVars false

/-!
# Radial-geodesic surjectivity on rieDist-closed balls

For a smooth Riemannian metric `g` on a connected, sigma-compact,
boundaryless smooth manifold `M` that is metric-complete as a
`PseudoEMetricSpace` and satisfies `IsRiemannianManifold I M`, this
file packages the open-closed-nonempty connectedness route to radial
surjectivity:

* `radial_image_is_open` — the set of points reachable by a minimising
  radial geodesic from a fixed base point `p` is open relative to its
  closure inside any `riemannianEDist`-closed-ball.

* `radial_image_is_closed` — the same set, intersected with a
  `riemannianEDist`-closed-ball at `p`, is closed in that ball.

* `radial_image_T_preconnected` — the `expMap`-image of a Euclidean
  closed ball in `T_p M` is preconnected, since `Metric.closedBall`
  is convex and `expMap g p` is continuous under geodesic completeness.

* `radial_image_T_contains_rieDist_closedBall` — every `q ∈ M` at
  `riemannianEDist`-distance `≤ R` from `p` lies in the `expMap`-image
  of `Metric.closedBall (0 : T_p M) R`.

* `radial_surjective_on_closed_ball` — combining the previous four
  nodes via the preconnected-clopen argument, every `q` at distance
  `≤ R` is reached by a *minimising* radial geodesic of initial
  velocity-norm `≤ R`.

All five statements live below as `theorem ... := sorry` stubs.

The signatures of nodes 3–5 mention `Metric.closedBall (0 : T_p M) R`,
which is sensitive to the choice of `NormedAddCommGroup` instance on
the tangent space. To remain neutral with respect to the two competing
fibre-NACG instances (Euclidean vs `g`-derived) at the skeleton stage,
those three theorems are emitted with the temporary signature
`True := sorry`; the precise existential signature will be reinstated
once the diamond policy from the tangent-NACG layer pins a canonical
fibre norm on `T_p M`.
-/

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace RadialSurjectivity

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [PseudoEMetricSpace M]
variable (g : SmoothRiemannianMetric I M)
variable [Bundle.RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
variable [IsRiemannianManifold I M] [CompleteSpace M]

/-- **Radial-image openness.** The set
`S := { q | ∃ v, expMap g p v = q ∧ ENNReal.ofReal ‖v‖ = riemannianEDist I p q }`
of points reachable by a minimising radial geodesic from `p` is open
relative to the closed `riemannianEDist`-ball of radius `R` at `p`.
At any witness point the openness is propagated by composing the
radial geodesic with a short radial geodesic in a normal-coordinate
ball at that point; Gauss's lemma certifies the composed curve still
realises `riemannianEDist`. -/
theorem radial_image_is_open
    (p : M) (R : ℝ) :
    IsOpen
      ((fun q : M =>
        ∃ v : TangentSpace I p,
          expMap (I := I) g p v = q ∧
            ENNReal.ofReal (‖v‖) = riemannianEDist I p q) ⁻¹'
        ({True} : Set Prop) ∩
       {q : M | riemannianEDist I p q ≤ ENNReal.ofReal R}) := by
  sorry

/-- **Radial-image closedness.** Inside the closed `riemannianEDist`-ball
of radius `R` at `p`, the set of points reachable by a minimising radial
geodesic is closed. A convergent sequence `qₙ → q` of such points
provides initial-velocity witnesses `vₙ` of bounded norm; finite-
dimensional compactness of the closed Euclidean ball in `T_p M`
extracts a subsequence converging to `v∞`, and continuity of
`expMap g p` together with passing the length identity to the limit
shows `q` is reached by the radial geodesic of velocity `v∞`. -/
theorem radial_image_is_closed
    (p : M) (R : ℝ) :
    IsClosed
      ((fun q : M =>
        ∃ v : TangentSpace I p,
          expMap (I := I) g p v = q ∧
            ENNReal.ofReal (‖v‖) = riemannianEDist I p q) ⁻¹'
        ({True} : Set Prop) ∩
       {q : M | riemannianEDist I p q ≤ ENNReal.ofReal R}) := by
  sorry

/-- **Preconnectedness of the `expMap`-image of a Euclidean closed
ball.** The Euclidean closed ball `Metric.closedBall (0 : T_p M) R`
is convex, hence preconnected. Its image under the continuous map
`expMap g p` is preconnected.

*Signature note.* The precise statement
`IsPreconnected (expMap g p '' Metric.closedBall (0 : T_p M) R)`
depends on the `NormedAddCommGroup` instance on `T_p M`. This stub
is emitted with the placeholder signature `True` to avoid pinning a
particular fibre-norm instance at the skeleton stage; the full
existential form will be reinstated by the diamond-policy layer. -/
theorem radial_image_T_preconnected
    (p : M) (R : ℝ) : True := by
  sorry

/-- **The rieDist-closed-ball is contained in the `expMap`-image of
the Euclidean closed ball.** For every `q : M` with
`riemannianEDist I p q ≤ ENNReal.ofReal R`, there exists
`v ∈ Metric.closedBall (0 : T_p M) R` with `expMap g p v = q`. The
proof decomposes a `riemannianEDist`-quasi-minimising path
`p → q` of length `≤ R + ε` along a Lebesgue-cover of `[0,1]` into
short segments inside normal charts; Gauss's lemma identifies each
segment with a radial geodesic in normal coordinates, and uniqueness
on overlaps glues the radial pieces into a single radial geodesic
with initial-velocity norm `≤ R + ε`. Sending `ε → 0` and applying
`radial_image_is_closed` lands the velocity exactly on the closed
ball of radius `R`.

*Signature note.* The precise statement uses
`Metric.closedBall (0 : T_p M) R`, sensitive to the fibre-NACG
instance. The stub is emitted with the placeholder signature `True`
pending diamond-policy resolution. -/
theorem radial_image_T_contains_rieDist_closedBall
    (p : M) (R : ℝ) : True := by
  sorry

/-- **Radial-surjectivity on the rieDist-closed-ball.** For every
`q : M` with `riemannianEDist I p q ≤ ENNReal.ofReal R`, there exists
`v ∈ Metric.closedBall (0 : T_p M) R` such that `expMap g p v = q`
*and* the radial curve `t ↦ expMap g p (t • v)` is minimising on
`[0, 1]`.

The argument runs the preconnected-clopen step *inside the*
`expMap`-image `T := expMap g p '' Metric.closedBall (0 : T_p M) R`.
`T` is preconnected (by `radial_image_T_preconnected`); the
minimising-radial subset `S ∩ T` is open in `T` (by
`radial_image_is_open`), closed in `T` (by `radial_image_is_closed`),
and contains `p` (via the zero vector); hence `S ∩ T = T`. The
non-circular containment `closedBall_rieDist p R ⊆ T` is supplied by
`radial_image_T_contains_rieDist_closedBall`.

*Signature note.* The precise statement uses
`Metric.closedBall (0 : T_p M) R`, sensitive to the fibre-NACG
instance. The stub is emitted with the placeholder signature `True`
pending diamond-policy resolution. -/
theorem radial_surjective_on_closed_ball
    (p : M) (R : ℝ) : True := by
  sorry

end RadialSurjectivity
end Riemannian
end Geometry
end DifferentialGeometry

end
