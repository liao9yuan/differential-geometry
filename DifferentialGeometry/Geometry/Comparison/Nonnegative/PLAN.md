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
superlevel adapters.

`ConvexExhaustion.lean` implements the correctly signed Busemann half-spaces,
their ray-family intersections, closedness, monotonicity, natural-level cover,
strict interior nesting, and the compactness contradiction.  In particular,
`raySublevel_compact` proves compactness of every real level once all
basepoint-ray Busemann functions are geodesically concave.  This conditional
compactness route is complete; the curvature-dependent compact exhaustion
theorem remains unstated.

`Variation/EndpointNonnegative.lean` supplies the first genuine comparison
producer, `jacobi_pair_le_flat`, from `NonnegSecMetric`.  Its statement is for a
unit-speed geodesic on `[0, L]`; the existing intrinsic selected branch is
parameterized on `[0, 1]` with speed equal to its radial length.  The smallest
remaining bridge is therefore a unit-speed reparameterization and minimizing-
tail lemma.  It is routine geometric plumbing, but it must precede the
selected-branch Hessian comparison theorem.  Calabi upper support across the
cut locus and the one-dimensional barrier argument then give geodesic
concavity of Busemann functions.  No complete Toponogov hierarchy is required
before this selected consequence.

## Honest progress

- Busemann metric theorem layer: 100%.
- Minimizing-ray producer package: 100%; the minimizing-line producer is 0%,
  so Phase N1 as a whole is approximately 50%.
- Weak Laplacian comparison theorem: 0%; required elliptic interface is not
  yet selected.
- Cheeger--Gromoll splitting theorem: unstated, therefore 0%; dedicated metric
  machinery approximately 20%.
- Total-convexity and elementary convex-exhaustion interfaces: 100%.
- `jacobi_pair_le_flat`: 100%; selected-branch Hessian comparison: unstated,
  0%, with dedicated endpoint machinery approximately 60%.
- Busemann geodesic-concavity theorem: unstated, 0%; dedicated comparison
  machinery approximately 20%.
- Compact exhaustion under nonnegative sectional curvature: unstated, 0%; its
  downstream conditional compactness argument is 100%.
- Soul theorem: unstated, therefore 0%; dedicated machinery approximately
  15% through ray, convexity, exhaustion, and endpoint-comparison infrastructure.
- Whole B1 nonnegative-curvature lane: approximately 12--15%.
- Whole post-HCG Poincare program: still approximately 15--20%; this first B1
  brick does not materially change that large denominator.
