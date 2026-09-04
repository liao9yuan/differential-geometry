# CGTRawPropeller

## Scope

This module contains only the raw loop-transport nonfixed-point producer
`rawTransport_ne`.  Iterate, orbit, fiber-count, Jensen, center-of-mass, and
injectivity declarations remain outside this file.

## Result

Focused verification passed without warnings.  The theorem takes a caller-
supplied canonical `IsLiftOn` lift of the based loop whose endpoint is nonzero
and proves that raw transport fixes no point of the norm core.

The proof compares the chosen loop-radial lift on its left half with the
caller-supplied loop lift.  On the right half it compares the same lift,
backwards from the endpoint supplied by the alleged fixed point, with the
canonical `rawFlatRay`.  Map-generic `IsLiftOn.eqOn` and `eqOn_of_eq` then force
the caller's lifted endpoint to be zero, contradicting the premise.

## Assumptions

The statement uses only the existing nonnegative length budgets, the strict
fit `L + a < R`, global radial raw-domain coverage on the model ball, the raw
local-diffeomorphism hypothesis, a flat short loop, its supplied lift, and core
membership.  It adds no curvature, minimizing-join, strict-Jensen,
center-of-mass, ambient completeness, ambient connectedness,
`SigmaCompactSpace M`, or positive-finrank premise.

## Proof notes

The only failed intermediate checks were local elaboration issues: the initial
model-with-corners notation used the wrong Unicode glyph, and membership in the
`Opens E` subtype `rawPullBall` needed an explicit definitional conversion to
model-ball membership.  No mathematical or missing-API blocker remains.

## Program accounting

- `rawTransport_ne`: complete (100%).
- `framedInj_ge_vol`: not yet declared or proved (0%); its dedicated raw P1b
  machinery remains approximately 96% complete.
- P1b endpoints: zero of two (0%).
- P1 overall: eleven of fourteen endpoints (78.6%).
- Final `poincare_of_inputs`: not declared (0%); whole P0--P9 infrastructure
  remains at the program authority's 15--25% estimate.

The next mathematical frontier is the separate raw-core strict-Jensen and
center-of-mass chain.  This module deliberately stops before that frontier.
