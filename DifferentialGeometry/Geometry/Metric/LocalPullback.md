# LocalPullback

## State — 2026-07-27

`localPullMetric` is the canonical cross-model pullback metric for a smooth
local diffeomorphism.  It does not assume global injectivity or construct an
inverse map.  Its inner-product formula is exported as
`localPullMetric_inner`.  The current-target-norm form `localPull_enorm` and
the path-length naturality theorem `localPull_pathLen` consume an explicit norm
identification, avoiding a hidden target-metric instance diamond.

The source is focused-green and the targeted artifact is exact-current.  No
`sorry`, `admit`, axiom, or new geometric assumption was added.

This closes the generic metric and path-length packaging API.  It is a reusable
prerequisite for the CGT multi-sheeted exponential ball; it does not prove
strict convexity.

Honest accounting:

- `localPullMetric` and path-length naturality: theorem/API 100%;
- local-pullback curvature naturality: theorem/API 100%;
- CGT Lemma 4.6: theorem 0%;
- whole HCG supporting machinery: about 61%.
