# Nonnegative-curvature plan

This directory is the B1 nonnegative-curvature lane of the post-HCG Poincare
program.  Its immediate consumers are the Cheeger--Gromoll input to
kappa-solution classification and the selected Toponogov consequences used in
bounded-curvature-at-bounded-distance arguments.  It is not a general
Alexandrov-geometry project.

## Public endpoints

The intended endpoints, in dependency order, are:

1. a minimizing-ray and minimizing-line package compatible with the intrinsic
   Hopf--Rinow API;
2. Busemann functions, their weak Laplacian comparison under nonnegative
   Ricci curvature, and the Cheeger--Gromoll splitting theorem;
3. the convexity and normal-exponential ingredients of the soul theorem;
4. the positive-sectional-curvature corollary that the soul is a point;
5. only the Toponogov hinge/angle consequences explicitly required by the
   later kappa-solution and bounded-distance proofs.

The full soul theorem should remain a genuine geometric theorem: it must
produce a compact totally convex, totally geodesic submanifold and the normal
bundle diffeomorphism.  The positive-curvature point-soul corollary is the
first downstream endpoint, but it must not be packaged as an unexplained
consumer assumption.

## Phase N0: metric Busemann layer

`Busemann.lean` now defines minimizing rays and lines, distance-minus-time
approximants, and their infimum Busemann function.  It proves monotonicity,
convergence of the approximants to the infimum, lower bounds, one-Lipschitz
continuity, the exact value along a ray, and the two-sided line
inequality/equality used by splitting.

Status:

- theorem layer: complete and focused-green;
- curvature assumptions: none;
- placeholders: none.

## Phase N1: ray and line producers

Reuse `Geometry/Exponential/MinimizingGeodesic.lean` and the intrinsic
Hopf--Rinow/properness package.  The required producer extracts a limiting
initial direction from minimizing segments to points escaping every bounded
set, then proves the resulting complete geodesic has the `IsMinRay` distance
property.  A line producer takes the pointed limit of increasingly long
minimizing segments.

Do not use the legacy sorry-bearing Hopf--Rinow capstone when the intrinsic
minimizing-exponential API suffices.

The ray half is now implemented in `Ray.lean`.  `minRay_of_escape` performs the
compact limiting-direction argument, and
`RiemannianMetricComplete.exists_minRay` constructs the required escaping
sequence on a complete connected noncompact Riemannian manifold.  The
stronger `minRay_in_of_escape` and `exists_minRay_in` preserve a closed totally
convex set along the limiting minimizing geodesic ray.  The two-sided
minimizing-line producer is the remaining N1 frontier.

## Phase N2: weak Laplacian comparison

This is the first genuine missing API.  The repository has parabolic weak
maximum principles and substantial chartwise elliptic weak-solution
infrastructure, but no small canonical predicate saying that a locally
Lipschitz scalar function satisfies `Delta f <= 0` distributionally on an
open set.

The implementation order should be:

1. locate the weakest existing chartwise integration-by-parts statement and
   expose a manifold-local scalar weak-Laplacian inequality at the elliptic
   analysis layer;
2. prove the distance-function Laplacian comparison away from the cut locus;
3. pass to Calabi support functions/barriers at cut-locus points;
4. pass the inequality to the monotone Busemann limit;
5. connect the collaborator's strong elliptic maximum principle, if available,
   to this exact predicate rather than introducing another equivalent notion.

No weak-Laplacian hypothesis may be added directly to the splitting theorem.

## Phase N3: Cheeger--Gromoll splitting

For a minimizing line, `Busemann.lean` already provides
`b_plus + b_minus >= 0` everywhere and equality on the line.  Weak Laplacian
comparison plus the strong maximum principle should give
`b_plus + b_minus = 0`.  Elliptic regularity then makes the Busemann functions
smooth and harmonic.

The invariant geometric closure is essential:

1. apply Bochner with nonnegative Ricci curvature to prove `Hess b = 0`;
2. deduce that `grad b` is a parallel unit vector field;
3. prove its flow is complete and acts by isometries;
4. show the zero level set is a complete totally geodesic hypersurface;
5. construct and verify the global isometry `N x R -> M`.

Smoothness and `norm (grad b) = 1` alone do not prove an isometric product.

## Phase N4: soul theorem

The Soul lane is active at the comparison-prerequisite stage.  Follow the
classical exhaustion/shaving route:

1. construct a proper convex exhaustion from Busemann-type functions;
2. take a compact totally convex minimum set;
3. iteratively remove boundary by maximal-distance-to-boundary sets until a
   boundaryless compact totally convex core remains;
4. prove the core is a totally geodesic submanifold;
5. construct a diffeomorphism from the total space of the soul's normal bundle
   to the ambient manifold; use the normal exponential only for the local
   tubular identification unless a separate global result is proved;
6. under positive sectional curvature, exclude a positive-dimensional soul
   and obtain the point-soul corollary.

This phase needs real convex-set, distance-to-boundary, normal-bundle, and
normal-exponential producers.  It should not be represented by a single
`SoulInput` record whose fields merely restate the theorem.

The canonical all-geodesic predicate `IsTotallyConvex` now lives in
`GeodesicConvexity.lean`, together with arbitrary-intersection closure and an
adapter to the existing Hopf--Rinow selected join.  It intentionally quantifies
every geodesic segment, not only minimizing segments.  The same module now has
all-geodesic scalar convexity and concavity predicates with sublevel and
superlevel adapters.  These predicates explicitly require continuity on the
closed segment.  `IntrinsicExp.exists_geo_eqOn_Icc` and
`IsGeodesicConcave.of_global` globalize such a segment to the existing smooth
complete geodesic API.

`ConvexExhaustion.lean` implements the correctly signed Busemann half-spaces,
their ray-family intersections, closedness, monotonicity, natural-level cover,
strict interior nesting, and the compactness contradiction.  In particular,
`raySublevel_compact` proves compactness of every real level once all
basepoint-ray Busemann functions are geodesically concave.  This conditional
route is retained as a reusable consumer.  `ray_convex_of_nonneg`,
`ray_compact_nonneg`, and `rayExhaustion` now discharge its hypothesis from
`NonnegSecMetric` and produce an actual compact totally convex exhaustion.

`Variation/EndpointNonnegative.lean` supplies `jacobi_pair_le_flat` from
`NonnegSecMetric` and the time-one specialization `intrJacobi_pair_le`.
`Variation/RadialMinimizing.lean` supplies the exact unit-speed minimizing
bridge, while `Exponential/EndpointShape.lean` exposes the all-time Jacobi
scaling identity.  `RadialLaplacian.lean` now combines these producers with
`branchHess_shape` in the perpendicular and arbitrary endpoint-vector bounds.
`DistanceCalabi.lean` supplies the exact minimizing-tail distance, broken-path
upper support, and its scalar second-derivative estimate along smooth
geodesics.  `Analysis/Calculus/UpperSupport.lean` supplies the one-dimensional
barrier calculus, while `DistanceSemiconcavity.lean` turns the Calabi supports
into a reusable semiconcavity theorem and passes concavity through pointwise
limits.

`Nonnegative/BusemannConcavity.lean` proves both global smooth-geodesic
composition concavity and the public all-segment `buse_geo_concave` theorem.
The latter combines segment globalization with the established Calabi limit
argument.  No complete Toponogov hierarchy is required for this route.

`Nonnegative/ConvexCore.lean` defines the infimum of the nonempty ray-sublevel
levels, proves that this infimum is attained, and packages the resulting
minimum core as nonempty, compact, and totally convex.

The next N4 frontier is relative-boundary shaving of this minimum core to a
terminal compact boundaryless totally geodesic submanifold.  This requires
honest inner-parallel-set, distance-to-boundary, dimension-drop, and
submanifold producers; it must not be replaced by an assumption bundle that
restates the Soul theorem.

## Honest progress

- Busemann metric theorem layer: 100%.
- Minimizing-ray producer package: 100%; the minimizing-line producer is 0%,
  so Phase N1 as a whole is approximately 50%.
- Weak Laplacian comparison theorem: 0%; required elliptic interface is not
  yet selected.
- Cheeger--Gromoll splitting theorem: unstated, therefore 0%; dedicated metric
  machinery approximately 20%.
- Total-convexity and elementary convex-exhaustion interfaces: 100%.
- `jacobi_pair_le_flat`, `intrJacobi_pair_le`, selected-branch Hessian
  comparison, Calabi scalar supports, and one-dimensional upper-support
  calculus: 100% after focused, targeted, and full-project verification.
- Smooth-geodesic Busemann composition concavity: 100% after focused and
  targeted verification and the full-project build.
- Public `IsGeodesicConcave` Busemann theorem: 100%.
- Compact totally convex exhaustion under nonnegative sectional curvature:
  100%, including the `CompactExhaustion` package and total convexity of every
  level.
- Compact totally convex minimum ray level: 100% after focused, targeted,
  full-project, and direct axiom verification.
- Soul theorem: unstated, therefore 0%; dedicated machinery approximately
  31--32% through rays, convexity, compact exhaustion and minimum core, Calabi
  comparison, and the all-segment Busemann theorem.
- Whole B1 nonnegative-curvature lane: approximately 22--25%.
- Whole post-HCG Poincare program: still approximately 15--20%; this first B1
  brick does not materially change that large denominator.
