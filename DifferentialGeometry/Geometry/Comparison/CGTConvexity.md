# CGTConvexity

## State — 2026-07-27

This module owns the compact concentric cores inside the open intrinsic
pullback ball.  `intrCore_compact` deliberately proves compactness by
identifying the subtype image with the finite-dimensional closed model ball;
it does not assert that the whole open pullback manifold is complete.

`intrRadial_len` proves that the canonical smooth radial path has exactly model
length.  `intrPull_dist_zero` is focused- and exact-green (`3902/3902`): its
lower bound uses intrinsic Gauss length control for every path starting at the
origin, while its upper bound is the canonical radial path.  Neither proof uses
whole-ball injectivity, completeness of the open pullback manifold, or
Hopf--Rinow.  The identity keeps the eventual finite energy minimizer away from
the incomplete boundary.

`intrCore_edist_lt` is focused-green.  If the first point is strictly inside
the radius-`a` core and the second is in its closed core, their pullback
extended distance is strictly less than `2*a`.  In the finite CGT orbit, the
`i`-th minimization must use the same-radius core
`intrCore R (2*i*ell)`.  Hence every orbit-point/center distance is strictly
less than `4*i*ell ≤ 2*r₀ < R/2 ≤ π/(2*sqrt K)`.  The generic center-of-mass
theorems that enlarge the minimization radius to `2*a` are not suitable here.
This exact ledger also rules out replacing the sharp Rauch step by a
small-radius Gronwall or constant-`2` estimate: the public CGT hypotheses can
approach the `π/(2*sqrt K)` endpoint.

Connectedness policy: when an older geometric capstone requires
`ConnectedSpace`, restrict all objects to the connected component containing
the relevant basepoint/points and apply the capstone there.  Do not add global
connectedness to the CGT producer or the final HCG input.

For the present finite-center argument no ambient restriction is needed:
`intrPullBall R` is the subtype of a Euclidean open ball, so `hR : 0 < R`
installs its connectedness directly from `Metric.isConnected_ball`.  If a later
legacy ambient theorem genuinely needs connectedness, use
`connectedComponent p`; radial paths put every finite orbit point in that
component through `pathComponent_subset_component`.  Only if such a theorem
also consumes the full intrinsic distance or exponential should we add the
corresponding open-subtype distance/exponential restriction adapters.  Those
heavier adapters are not prerequisites for the current CGT center.

`intrPull_pair_pos` is focused-green.  It transfers the ambient pointwise
`Rm04` bound through `intrPull_quad_le`, uses the constant-speed identity to
obtain the sharp `K * L^2 < (pi/2)^2` threshold, and applies the checked
Dirichlet/free Jacobi endpoint theorem.  The proof installs only the
Riemannian-distance realization needed by the lower comparison API.  It does
not install `CompleteSpace (intrPullBall R)` and does not use connectedness.

The compact-fenced Whitehead/join producer is now implemented in
`CGTWhitehead`: the pullback metric is extended to a complete metric on the
model space.  `exists_fenced_ext` retains the ambient minimizing geodesic,
while canonical `exists_fenced_min` returns one globally smooth
subtype-valued join and proves it is a pullback geodesic on `[0,1]`, with the
strict metric-agreement fence.  The next genuine frontier is therefore only
the local-interval Hessian-to-strict-convexity readout which turns
`intrPull_pair_pos` into Jensen convexity of each half squared-distance
summand.  Existing complete-manifold `ExpInvBranch` calculus still cannot be
instantiated directly on the open pullback ball.  A component restriction
solves only connectedness, not this incompleteness, so the proof remains local
to the compact core.

Honest accounting:

- compact CGT core API: theorem/machinery 100% after focused verification;
- pullback radial-distance identity: theorem/machinery 100%, focused and exact
  current;
- same-core pair-distance fence: theorem/machinery 100%, focused current;
- pullback Jacobi endpoint positivity: theorem/machinery 100%, focused current
  and exact refresh pending;
- compact-fenced Whitehead/join producer: theorem/machinery 100%, focused
  current, exact refresh pending;
- paper Lemma 4.6: theorem 0%, dedicated machinery about 76–80%;
- pointwise CGT producer: theorem 0%, dedicated machinery about 70–74%;
- sequence `InjRadiusDecayInput` producer: theorem 0%;
- unconditional Theorem 3.9: theorem 0%;
- whole HCG supporting machinery: about 61%.
