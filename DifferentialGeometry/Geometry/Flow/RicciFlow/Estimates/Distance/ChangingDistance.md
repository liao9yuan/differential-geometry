# ChangingDistance

## Scope

This file implements the fixed-endpoint short- and long-distance branches of
book 12 `lem:red-changing-distance` for an ordinary smooth Ricci flow.  It does
not introduce a Dini-derivative object: the output is the stronger
project-native data of a differentiable upper support on the right.

## Native route

- Freeze a minimizing `minJoin` for the base metric at forward time
  `T - tau` and use its backward-time path length as `phi`.
- `minJoin_arcLength` gives equality with the base distance.  A private
  low-import arc-length bridge, proved directly from
  `riemannianEDist_le_arcLength`, makes `phi` an upper support at every
  later backward time, including cut pairs.  This avoids importing the
  cut-locus/Calabi layer merely for its misplaced public bridge.
- `pathLength_timeDeriv_of_ricciFlow`, composed with the backward clock,
  identifies the support derivative.  A private one-sided integral estimate
  uses only `Ric <= A g`; no absolute Ricci bound is added.
- When the base distance is less than `2 r`, every point of the minimizing
  segment lies in one of the two endpoint `r`-balls.  The endpoint-ball Ricci
  hypothesis therefore bounds the full support derivative by
  `2 (n - 1) K r`.
- In the long branch, normalize `minimizingVec` to a unit-speed intrinsic
  geodesic.  The static producer `ricci_int_end_le` applies the endpoint-ramp
  index-form estimate to its Ricci integral; the same path-length derivative
  then gives the sharp `2 (n - 1) ((2/3) K r + 1/r)` support bound.

The equality case `x = y` is handled by the constant zero support.  Completeness
is assumed only for the base metric, where the minimizing geodesic is chosen.

## Deliberate boundary

`dist_moving_slope` now source-implements the cut-safe triangle/support
transfer from a fixed-endpoint upper support and explicit first-order
endpoint-distance bounds to the moving-endpoint upper right slope.  The fixed
endpoint long branch remains a genuine consumer of the static endpoint-Ricci
producer, not a wrapper that assumes its conclusion.

The remaining moving-endpoint frontier is geometric: derive the sharp
endpoint-distance rate from manifold differentiability and smooth variation
of the metric.  The later absolutely-continuous interval theorem also needs an
a.e. assembly.

## Status

- `dist_short_support`: source written without `sorry`, a new predicate, or a
  strengthened absolute-curvature assumption.  Static comparison with the
  existing path-length variation proof corrected the time-family parameter
  names and qualified velocity theorem, and the contact proof now factors
  through the minimizing path-length identity.  Its first focused source check
  and named module refresh were warning-free GREEN.  The unified P2 public
  axiom audit is also GREEN.
- The short fixed-endpoint endpoint `dist_short_support` is 100% complete and
  focused-check verified; its dedicated local machinery is also 100% complete.
- `dist_long_support`: source written without `sorry`, a sign assumption on
  `K`, or stronger curvature hypotheses.  It uses the normalized native
  minimizing geodesic and the focused-GREEN `ricci_int_end_le`.  Static
  repair removed the accidental `DistanceCalabi` dependency and corrected
  the right-neighborhood notation; its focused check is warning-free GREEN.
- The long fixed-endpoint endpoint `dist_long_support` is 100% complete and
  focused-check verified; its dedicated static endpoint-integral and
  fixed-path variation machinery is also 100% complete.
- `dist_moving_slope` is warning-free focused GREEN.  It proves the
  non-definitional triangle/support transfer without a new Dini object or a
  curvature assumption.
- The full book changing-distance lemma remains 0% complete as a theorem: its
  geometric endpoint-rate producer and absolutely-continuous interval chain
  are still absent.  The verified fixed-endpoint supports plus source-written
  slope transfer are roughly 65% of the dedicated machinery expected for that
  local lemma and remain well below 1% of P2b and of the whole Poincare
  formalization program.

## Weak-signature follow-up

The sole `ricci_int_end_le` call now follows the producer's weaker public
signature by omitting its removed metric-norm argument.  All remaining
arguments and the long-distance proof are unchanged.  This consumer adaptation
is warning-free focused green after the coordinated `RicciEndpoint` artifact
refresh.  No build or refresh was run in this consumer-verification window.
