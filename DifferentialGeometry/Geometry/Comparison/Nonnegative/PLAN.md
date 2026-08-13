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
lower bounds, one-Lipschitz continuity, the exact value along a ray, and the
two-sided line inequality/equality used by splitting.

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

The soul lane starts only after the selected Toponogov convexity lemmas are
available.  Follow the classical exhaustion/shaving route:

1. construct a proper convex exhaustion from Busemann-type functions;
2. take a compact totally convex minimum set;
3. iteratively remove boundary by maximal-distance-to-boundary sets until a
   boundaryless compact totally convex core remains;
4. prove the core is a totally geodesic submanifold;
5. prove the normal exponential map is a diffeomorphism;
6. under positive sectional curvature, exclude a positive-dimensional soul
   and obtain the point-soul corollary.

This phase needs real convex-set, distance-to-boundary, normal-bundle, and
normal-exponential producers.  It should not be represented by a single
`SoulInput` record whose fields merely restate the theorem.

## Honest progress

- Busemann metric theorem layer: 100%.
- Ray/line existence producers: 0%; related Hopf--Rinow machinery exists.
- Weak Laplacian comparison theorem: 0%; required elliptic interface is not
  yet selected.
- Cheeger--Gromoll splitting theorem: unstated, therefore 0%; dedicated metric
  machinery approximately 20%.
- Soul theorem: unstated, therefore 0%; dedicated machinery approximately
  5--10% through general exponential/compactness infrastructure.
- Whole B1 nonnegative-curvature lane: approximately 8--12%.
- Whole post-HCG Poincare program: still approximately 15--20%; this first B1
  brick does not materially change that large denominator.
