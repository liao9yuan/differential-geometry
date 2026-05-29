import DifferentialGeometry.Geometry.Riemannian.GaussLemma
import DifferentialGeometry.Geometry.Riemannian.HopfRinow
import DifferentialGeometry.Geometry.Riemannian.Exponential.Definition
import DifferentialGeometry.Geometry.Riemannian.Exponential.LocalDiffeomorphism
import DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
import DifferentialGeometry.Integral.Measure.ChartDensity
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Analysis.Convex.Star
import Mathlib.Analysis.Convex.PathConnected

set_option linter.unusedSectionVars false

/-!
# Radial-geodesic surjectivity on rieDist-closed balls

For a smooth Riemannian metric `g` on a connected, sigma-compact,
boundaryless smooth manifold `M` that is metric-complete as a
`PseudoEMetricSpace` and satisfies `IsRiemannianManifold I M`, this
file packages the open-closed-nonempty connectedness route to radial
surjectivity. The base point `p : M` is fixed and the radius is `R : ℝ`.

The route avoids any Arzelà–Ascoli / pre-assumed Heine–Borel argument:
points within `riemannianEDist`-distance `R` are reached by *minimising
radial geodesics* `t ↦ expMap g p (t • v)` with `g`-velocity-norm
`√(g.inner p v v) ≤ R`.

## The radial-minimiser set

`radialMinSet g p` is the set of points `q : M` reached by some
`v : T_p M` whose minimising radial geodesic has `g`-length equal to
the Riemannian distance:

`radialMinSet g p = { q | ∃ v, expMap g p v = q ∧
    ENNReal.ofReal (√(g.inner p v v)) = riemannianEDist I p q }`.

The velocity bound is stated with the intrinsic `g`-norm
`Real.sqrt (g.inner p v v)`, *not* the model-`E` norm `‖v‖`: the
latter has no a-priori relation to the metric `g` and its appearance in
earlier drafts of this file was an instance of the tangent-bundle norm
diamond leaking into a public statement.

## Main statements

* `gBall_isPreconnected` — the `g`-norm closed ball
  `{v | √(g.inner p v v) ≤ R}` in `T_p M` is preconnected (it is
  star-shaped about `0`).

* `radial_image_T_preconnected` — the `expMap g p`-image of the
  `g`-norm closed ball is preconnected, by continuity of `expMap g p`
  (`bm_c_expMap_continuous_of_geodesic_complete`). **Fully proven.**

* `radial_image_is_open` — `radialMinSet g p` is open *relative to* the
  `riemannianEDist`-closed-ball subspace of radius `R` at `p` (the
  subspace-open hypothesis required by the clopen-in-connected step).

* `radial_image_is_closed` — `radialMinSet g p` is closed relative to
  the same closed ball.

* `radial_image_T_contains_rieDist_closedBall` — every `q : M` with
  `riemannianEDist I p q ≤ ENNReal.ofReal R` is reached by some `v` with
  `g`-velocity-norm `≤ R`.

* `radial_surjective_on_closed_ball` — combining the previous nodes via
  the preconnected-clopen argument, every `q` at distance `≤ R` is
  reached by a *minimising* radial geodesic of `g`-velocity-norm `≤ R`.

The genuinely-hard nodes (open/closed relative to the ball; the
containment; the minimising-curve conclusion) carry a single,
clearly-marked `sorry` each, naming the missing geometric content. The
preconnectedness nodes are proven outright.
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
  [PseudoEMetricSpace M] [T2Space (TangentBundle I M)]
variable (g : SmoothRiemannianMetric I M)
variable [Bundle.RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
variable [IsRiemannianManifold I M] [CompleteSpace M]

/-! ## The `g`-norm and the `g`-closed-ball in the tangent space

The `g`-norm of `v : T_p M` is `Real.sqrt (g.inner p v v)`. The
`g`-closed ball of radius `R` is the sublevel set of this norm. We work
with this intrinsic quantity throughout to avoid the tangent-bundle norm
diamond. -/

/-- The closed `g`-ball of radius `R` in the tangent space `T_p M`:
the set of vectors `v` with `√(g.inner p v v) ≤ R`. -/
def gBall (g : SmoothRiemannianMetric I M) (p : M) (R : ℝ) :
    Set (TangentSpace I p) :=
  {v : TangentSpace I p | Real.sqrt (g.inner p v v) ≤ R}

/-- The `g`-quadratic form is homogeneous of degree two:
`g.inner p (b • v) (b • v) = b ^ 2 * g.inner p v v`. -/
lemma gInner_smul_self (g : SmoothRiemannianMetric I M) (p : M)
    (b : ℝ) (v : TangentSpace I p) :
    g.inner p (b • v) (b • v) = b ^ 2 * g.inner p v v := by
  -- Unfold the two `ContinuousLinearMap.map_smul` applications.
  rw [(g.inner p).map_smul b v, ContinuousLinearMap.smul_apply,
    (g.inner p v).map_smul b v]
  -- `b • (b • (g.inner p v v)) = b ^ 2 * (g.inner p v v)` over ℝ.
  simp only [smul_eq_mul]
  ring

/-- The `g`-norm `√(g.inner p · ·)` is homogeneous: for `0 ≤ b`,
`√(g.inner p (b • v) (b • v)) = b * √(g.inner p v v)`. -/
lemma sqrt_gInner_smul_self (g : SmoothRiemannianMetric I M) (p : M)
    {b : ℝ} (hb : 0 ≤ b) (v : TangentSpace I p) :
    Real.sqrt (g.inner p (b • v) (b • v)) =
      b * Real.sqrt (g.inner p v v) := by
  rw [gInner_smul_self (I := I) g p b v, Real.sqrt_mul (sq_nonneg b),
    Real.sqrt_sq hb]

/-- The zero vector lies in every `g`-closed ball of non-negative radius;
more precisely, its `g`-norm is `0`. -/
lemma zero_mem_gBall (g : SmoothRiemannianMetric I M) (p : M) {R : ℝ}
    (hR : 0 ≤ R) : (0 : TangentSpace I p) ∈ gBall (I := I) g p R := by
  have h0 : g.inner p (0 : TangentSpace I p) (0 : TangentSpace I p) = 0 := by
    simp
  change Real.sqrt (g.inner p (0 : TangentSpace I p) (0 : TangentSpace I p)) ≤ R
  rw [h0, Real.sqrt_zero]
  exact hR

/-- **The closed `g`-ball is star-shaped about the origin.** Scaling a
ball element by `b ∈ [0, 1]` keeps it inside the ball, since the
`g`-norm scales by `b ≤ 1`. -/
lemma starConvex_gBall (g : SmoothRiemannianMetric I M) (p : M) (R : ℝ) :
    StarConvex ℝ (0 : TangentSpace I p) (gBall (I := I) g p R) := by
  intro y hy a b ha hb hab
  -- `a • 0 + b • y = b • y`; with `b ≤ 1`.
  have hb_le_one : b ≤ 1 := by linarith
  have hy' : Real.sqrt (g.inner p y y) ≤ R := hy
  have hsqrt_nonneg : 0 ≤ Real.sqrt (g.inner p y y) := Real.sqrt_nonneg _
  change Real.sqrt (g.inner p (a • (0 : TangentSpace I p) + b • y)
      (a • (0 : TangentSpace I p) + b • y)) ≤ R
  rw [smul_zero, zero_add]
  rw [sqrt_gInner_smul_self (I := I) g p hb y]
  -- `b * √(g.inner p y y) ≤ 1 * √(g.inner p y y) = √(g.inner p y y) ≤ R`.
  calc b * Real.sqrt (g.inner p y y)
      ≤ 1 * Real.sqrt (g.inner p y y) :=
        mul_le_mul_of_nonneg_right hb_le_one hsqrt_nonneg
    _ = Real.sqrt (g.inner p y y) := one_mul _
    _ ≤ R := hy'

/-- **The closed `g`-ball is preconnected.** It is star-shaped about the
origin (`starConvex_gBall`), hence path-connected, hence
preconnected. -/
theorem gBall_isPreconnected (g : SmoothRiemannianMetric I M) (p : M)
    {R : ℝ} (hR : 0 ≤ R) :
    IsPreconnected (gBall (I := I) g p R) :=
  ((starConvex_gBall (I := I) g p R).isPathConnected
    (zero_mem_gBall (I := I) g p hR)).isConnected.isPreconnected

/-! ## The radial-minimiser set

`radialMinSet g p` collects the points reached by a `g`-distance-realising
radial geodesic from `p`. -/

/-- **The radial-minimiser set at `p`.** Points `q : M` reached by some
`v : T_p M` whose minimising radial geodesic has `g`-length equal to the
Riemannian distance `riemannianEDist I p q`. -/
def radialMinSet (g : SmoothRiemannianMetric I M) (p : M) : Set M :=
  {q : M | ∃ v : TangentSpace I p,
    expMap (I := I) g p v = q ∧
      ENNReal.ofReal (Real.sqrt (g.inner p v v)) = riemannianEDist I p q}

/-- The base point `p` belongs to its own radial-minimiser set, witnessed
by the zero vector (`expMap g p 0 = p`, and both the `g`-length and the
Riemannian distance are `0`). -/
theorem p_mem_radialMinSet (g : SmoothRiemannianMetric I M) (p : M) :
    p ∈ radialMinSet (I := I) g p := by
  refine ⟨(0 : TangentSpace I p), expMap_zero (I := I) g p, ?_⟩
  have h0 : g.inner p (0 : TangentSpace I p) (0 : TangentSpace I p) = 0 := by
    simp
  rw [h0, Real.sqrt_zero, ENNReal.ofReal_zero, riemannianEDist_self]

/-! ## Preconnectedness of the `expMap`-image of the `g`-ball -/

/-- **Preconnectedness of the `expMap g p`-image of the closed `g`-ball.**
The closed `g`-ball `gBall g p R` is preconnected (`gBall_isPreconnected`);
its image under the continuous map `expMap g p`
(`bm_c_expMap_continuous_of_geodesic_complete`) is preconnected. -/
theorem radial_image_T_preconnected (g : SmoothRiemannianMetric I M)
    (p : M) {R : ℝ} (hR : 0 ≤ R) :
    IsPreconnected
      ((expMap (I := I) g p) '' (gBall (I := I) g p R)) := by
  have hcont : Continuous (expMap (I := I) g p) :=
    HopfRinow.bm_c_expMap_continuous_of_geodesic_complete (I := I) g p
  exact (gBall_isPreconnected (I := I) g p hR).image _ hcont.continuousOn

/-! ## Openness of the radial-minimiser set relative to the closed ball

For the clopen-in-connected step we need `radialMinSet g p` to be open
*in the subspace topology* of the `riemannianEDist`-closed-ball
`{q | riemannianEDist I p q ≤ ENNReal.ofReal R}`, i.e. its preimage under
the inclusion of the closed-ball subtype is open. (Ambient openness is
false: a generic radial-minimiser point need not have an ambient
neighbourhood of radial-minimiser points once intersected with the closed
ball.) -/

/-- **Radial-image openness (relative form).** The radial-minimiser set
`radialMinSet g p` is open *relative to* the `riemannianEDist`-closed-ball
of radius `R` at `p`: its preimage under the subtype inclusion of
`{q | riemannianEDist I p q ≤ ENNReal.ofReal R}` is open. At any witness
point `q = expMap g p v`, openness is propagated by composing the
minimising radial geodesic with a short radial geodesic in a normal-chart
ball at `q`; Gauss's lemma certifies that the composed curve still
realises `riemannianEDist`. -/
theorem radial_image_is_open (g : SmoothRiemannianMetric I M)
    (p : M) (R : ℝ) :
    IsOpen
      (Subtype.val ⁻¹' (radialMinSet (I := I) g p) :
        Set ↥{q : M | riemannianEDist I p q ≤ ENNReal.ofReal R}) := by
  -- Genuinely hard: relative openness via Gauss-lemma local minimisation
  -- (normal-chart radial unique-minimiser concatenation); needs the
  -- equality case of `normalBall_radial_unique_minimizer`, still pending.
  sorry

/-! ## Closedness of the radial-minimiser set relative to the closed ball -/

/-- **Radial-image closedness (relative form).** The radial-minimiser set
`radialMinSet g p` is closed *relative to* the `riemannianEDist`-closed-ball
of radius `R` at `p`. A convergent sequence `qₙ → q` of radial-minimiser
points has initial-velocity witnesses `vₙ` of `g`-norm `≤ R`; finite-
dimensional compactness of the closed Euclidean ball in `T_p M` extracts a
convergent subsequence `vₙ → v∞`, and continuity of `expMap g p` together
with lower semicontinuity of the length identity shows that `q` is reached
by the radial geodesic of velocity `v∞`. The velocity bound is the
intrinsic `g`-norm `√(g.inner p v v)`, not the model-`E` norm. -/
theorem radial_image_is_closed (g : SmoothRiemannianMetric I M)
    (p : M) (R : ℝ) :
    IsClosed
      (Subtype.val ⁻¹' (radialMinSet (I := I) g p) :
        Set ↥{q : M | riemannianEDist I p q ≤ ENNReal.ofReal R}) := by
  -- Genuinely hard: relative closedness via finite-dimensional compactness
  -- of the closed `g`-ball in `T_p M`, continuity of `expMap g p`, and
  -- passing the `g`-length ↔ `riemannianEDist` identity to the limit.
  sorry

/-! ## The closed ball is contained in the radial-minimiser image -/

/-- **The rieDist-closed-ball is contained in the radial image.** For
every `q : M` with `riemannianEDist I p q ≤ ENNReal.ofReal R`, there is a
`v : T_p M` with `expMap g p v = q` and `g`-velocity-norm
`√(g.inner p v v) ≤ R`. The proof decomposes a `riemannianEDist`-quasi-
minimising path `p → q` of length `≤ R + ε` along a Lebesgue-cover of
`[0,1]` into short segments inside normal charts; Gauss's lemma identifies
each segment with a radial geodesic in normal coordinates, and uniqueness
on overlaps glues the radial pieces into a single radial geodesic with
`g`-velocity-norm `≤ R + ε`. Sending `ε → 0` and applying
`radial_image_is_closed` lands the velocity exactly inside the closed
`g`-ball of radius `R`. -/
theorem radial_image_T_contains_rieDist_closedBall
    (g : SmoothRiemannianMetric I M) (p : M) (R : ℝ) :
    ∀ q : M, riemannianEDist I p q ≤ ENNReal.ofReal R →
      ∃ v : TangentSpace I p,
        expMap (I := I) g p v = q ∧
          Real.sqrt (g.inner p v v) ≤ R := by
  -- Genuinely hard: Lebesgue-cover a quasi-minimising path into normal-chart
  -- segments, identify each as radial via Gauss's lemma, glue by geodesic
  -- uniqueness; pass `ε → 0`. Needs the (still-pending) Gauss-lemma cluster.
  sorry

/-! ## Radial surjectivity on the closed ball -/

/-- **Radial-surjectivity on the rieDist-closed-ball.** For every `q : M`
with `riemannianEDist I p q ≤ ENNReal.ofReal R` there is a `v : T_p M`
with `expMap g p v = q`, `g`-velocity-norm `√(g.inner p v v) ≤ R`, and
the radial curve `t ↦ expMap g p (t • v)` minimising on `[0, 1]` (it
realises `riemannianEDist I p q`).

The argument runs the preconnected-clopen step inside the `expMap g p`-image
`T := expMap g p '' gBall g p R`. `T` is preconnected
(`radial_image_T_preconnected`); the minimising-radial subset
`radialMinSet g p ∩ T` is open in `T` (`radial_image_is_open`) and closed in
`T` (`radial_image_is_closed`), and contains `p` (via the zero vector,
`p_mem_radialMinSet`); hence `radialMinSet g p ∩ T = T`. The non-circular
containment `closedBall_rieDist p R ⊆ T` is supplied by
`radial_image_T_contains_rieDist_closedBall`.

*Downstream bridge.* `HopfRinow.bm_c_expMap_surjective_on_closedBall`
currently phrases the conclusion with `Metric.closedBall (0 : T_p M) R`
(sensitive to the fibre-NACG instance). This theorem's intrinsic
`g`-norm conclusion `√(g.inner p v v) ≤ R` is the diamond-free form; the
`closedBall ↔ g`-norm identification (whenever the fibre norm is pinned to
the `g`-derived one) is the residual bridge for re-routing that consumer. -/
theorem radial_surjective_on_closed_ball
    (g : SmoothRiemannianMetric I M) (p : M) (R : ℝ) :
    ∀ q : M, riemannianEDist I p q ≤ ENNReal.ofReal R →
      ∃ v : TangentSpace I p,
        expMap (I := I) g p v = q ∧
          Real.sqrt (g.inner p v v) ≤ R ∧
          ENNReal.ofReal (Real.sqrt (g.inner p v v)) = riemannianEDist I p q := by
  -- Genuinely hard: assemble the preconnected-clopen step (open + closed +
  -- preconnected + contains-p) inside the `expMap`-image; needs the open/
  -- closed/containment nodes above, all still pending.
  sorry

end RadialSurjectivity
end Riemannian
end Geometry
end DifferentialGeometry

end
