# ChangingDistance

## Scope

This file implements the short-distance, fixed-endpoint branch of book 12
`lem:red-changing-distance` for an ordinary smooth Ricci flow.  It does not
introduce a Dini-derivative object: the output is the stronger project-native
data of a differentiable upper support on the right.

## Native route

- Freeze a minimizing `minJoin` for the base metric at forward time
  `T - tau` and use its backward-time path length as `phi`.
- `minJoin_arcLength` gives equality with the base distance, while
  `edistOf_le_arcLength` makes `phi` an upper support at every later backward
  time, including cut pairs.
- `pathLength_timeDeriv_of_ricciFlow`, composed with the backward clock,
  identifies the support derivative.  A private one-sided integral estimate
  uses only `Ric <= A g`; no absolute Ricci bound is added.
- When the base distance is less than `2 r`, every point of the minimizing
  segment lies in one of the two endpoint `r`-balls.  The endpoint-ball Ricci
  hypothesis therefore bounds the full support derivative by
  `2 (n - 1) K r`.

The equality case `x = y` is handled by the constant zero support.  Completeness
is assumed only for the base metric, where the minimizing geodesic is chosen.

## Deliberate boundary

The long-distance constant requires the endpoint-ramp index-form estimate.
The current comparison layer proves index-form nonnegativity only for globally
smooth fields, whereas the sharp ramp is piecewise linear.  No long-case
wrapper is added here.  Moving endpoints are also omitted: the tree has no
native absolutely-continuous endpoint chain rule for a varying metric.

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
- The full book changing-distance lemma remains 0% complete as a theorem: its
  long-distance and moving-endpoint producers are still absent.  The verified
  short endpoint is roughly 25% of the machinery expected for that local lemma
  and well below 1% of P2b and of the whole Poincare formalization program.
