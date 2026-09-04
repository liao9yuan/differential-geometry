# RadialSurjectivity

## Raw sphere-jump producer

`sphere_jump_raw` is the first minimizing-direction producer in the
incomplete-ambient chain. For points at positive finite Riemannian edistance,
it chooses a sufficiently small radius and, at every smaller positive scale,
finds a unit initial direction whose raw exponential endpoint splits the total
distance exactly. The result explicitly records raw `expDomain` membership and
uses neither `CompleteSpace M` nor `expMapIntrinsic`.

The proof minimizes endpoint edistance over the raw exponential image of the
compact unit tangent sphere. Local raw exponential continuity follows from the
normal exponential radius. `edist_exp_eq_radius` supplies the exact radial
distance, while almost-shortest `C^1` paths, an intermediate-value point, and
`metricBall_subset_normalBall` give the reverse endpoint-distance estimate.
The two estimates force the exact split.

## Why this producer was needed

Three native routes were audited before implementation:

1. `MinimizingGeodesic.minExp_of_ne_top` has the desired final endpoint and
   length equality, but its public signature and its `sphere_jump` dependency
   require ambient completeness and use `expMapIntrinsic`.
2. A direct minimizing-sequence argument has almost-shortest paths from
   `exists_lt_of_riemannianEDist_lt`, but no native path-family compactness and
   lower-semicontinuity package producing an attained path-length infimum.
3. Raw radial propagation was the feasible route. The missing one-step
   producer was implemented here as `sphere_jump_raw`; later propagation can
   use `Exponential.mem_expDom_of_cpt` for the compact buffer and
   `Geodesic.maximalGeo_eqOn` for chart-independent agreement.

## Verification and progress

Focused verification passes without errors or warnings. No new assumptions,
frontier wrappers, or `sorry` were introduced.

- `sphere_jump_raw`, `sphere_jump_cpt`, and `minExp_of_cptBall`: 100%
  implemented and focused-checked.
- Dedicated compact-ball minimizing-exponential machinery: 100%.
- The whole P1a compact-closure Bishop endpoint remains unstated and unproved
  (0%).

## Compact radial buffer

`sphere_jump_cpt` composes the raw one-step minimizing direction with
`Exponential.mem_expDom_of_cpt`. Besides the exact distance split at one
positive jump, it records that every positive scaling of the chosen unit
direction below the supplied compact metric radius belongs to raw
`expDomain`. It assumes neither ambient completeness nor connectedness.

The chart-independent conversion from this pointwise domain support to one
common geodesic segment lives in `Geodesic.radialGeo_of_dom`; the two results
are intentionally separate so the rescaling theorem does not depend on the
metric compactness layer.

Focused verification of `sphere_jump_cpt` passes without warnings.

## Compact-ball minimizing endpoint

`minExp_of_cptBall` is now stated and has a source-complete proof without
ambient completeness. It first handles zero distance by the raw zero
exponential. At positive finite distance it combines `sphere_jump_cpt` with
`Geodesic.radialGeo_of_dom`, then takes the supremum of the closed ENNReal-valued
exact-split set. If the supremum is short of the endpoint, the first geodesic
segment shows that a closed ball centered at the join point is a closed subset
of the supplied compact ball. A second compact sphere jump and
`Geodesic.radialGeo_of_end` produce the next segment.

The two local segments are globalized only for the first-variation velocity
matcher, using a private smooth time clamp whose range remains in the original
open geodesic domains and whose germ is the identity along each closed segment.
Their actual chart-independent continuation is then proved by translating the
canonical `velocityLift` of the first segment and applying `gvf_eqOn` to the two
global geodesic-vector-field integral lifts. This avoids any chart-source or
ambient-completeness hypothesis in the public endpoint.

The endpoint proof is warning-free focused GREEN.  An earlier attempt had
stopped before elaborating the file because `BufferedExpDomain.olean` was then
missing; that artifact-freshness blocker is resolved.  No refresh or broader
build was run in the current parallel-task window.  The whole P1a
compact-closure Bishop endpoint is still unstated and unproved (0%).

## Focused elaboration repair

The first complete elaboration pass exposed only local proof-shape issues. The
repair kept the public statements unchanged: it corrected projection equality
orientation, preserved the geodesic witness before destructuring, unfolded
local `let` definitions explicitly, used scalar congruence for initial speeds,
made interval inclusions transitive through the ambient geodesic domain, and
disambiguated the metric-topology compactness argument. The translated interval
preimage now fixes its monotone map explicitly.

Focused verification is warning-free GREEN. Thus `sphere_jump_raw`,
`sphere_jump_cpt`, and `minExp_of_cptBall` are all checked without new
assumptions, `sorry`, or API strengthening. The compact-ball minimizing
exponential endpoint and its dedicated machinery are now 100%; the larger P1a
compact-closure Bishop endpoint remains separately unstated and unproved (0%).
