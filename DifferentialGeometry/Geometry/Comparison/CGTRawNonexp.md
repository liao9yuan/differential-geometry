# Raw transport nonexpansion

## Role and accounting

This module is the generic nonexpansion consumer for raw CGT loop transport.
It accepts one caller-supplied distance-realizing path between two raw-core
points.  It neither constructs such a path nor imports minimizing-join,
curvature, Jensen, center-of-mass, collision, or fiber-count machinery.

The P1b E1/E2 theorem endpoints remain unstated and unproved at 0%.  Dedicated
P1b machinery remains conservatively about 96% complete, and the whole
Poincare endpoint remains unstated at 0%.

## Mathematical route

For a supplied path `j`, apply `rawTransport_curve` to `j.extend`.  The
transported curve has the same pullback length.  Riemannian endpoint distance
is bounded by that length, while the supplied minimizing identity identifies
the original path length with the source pullback distance.  Taking real parts
and using the Hopf--Rinow metric realization yields ordinary-distance
nonexpansion.

The source points and path stay in `rawCore`; `Path` itself records the two
endpoint identities.  No global join family or `IsRawMinJoin` package is
required.  A later minimizing-join producer may expose such a package and pass
its projections to this theorem without coupling this consumer to join
existence or Jensen.

## Reuse and assumptions

- Reused: `rawTransport_curve`,
  `Manifold.riemannianEDist_le_pathELength`, `Path.extend_zero`,
  `Path.extend_one`, `ENNReal.toReal_mono`, and
  `HopfRinow.riemMetric_dist_eq`.
- The only distance-realization assumptions are C1 regularity, global core
  containment of the extended path, and its exact length identity.
- There is no `CompleteSpace`, positive-finrank, curvature, smallness, Jensen,
  collision-vector, or ambient sigma-compactness assumption.

## Verification

Focused verification passed without warnings after the true-consumer refresh
of `CGTRawTransport`.  The first pass exposed only that connectedness of a
normed-space ball lives in the narrow Mathlib normed-module connectedness
module; importing that declaration resolved the sole error.  No proof or
geometric API blocker remains.

Static review found no `sorry` or `admit`, no declaration over the twenty-letter
budget, and none of the excluded join-existence, curvature, Jensen,
center-of-mass, completeness, or positive-finrank assumptions.
