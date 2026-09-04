# CGTRawExtDistance

## Scope

This file owns only geodesic transfer, path-length agreement, centered radial
length, and the resulting two-point distance upper bound for the complete raw
pullback extension.  It stops before any minimizing join, fence, curvature,
convexity, Jensen, or collision argument.

## Route and reuse

- `rawPull_geo_of_ext` and `rawExt_geo_of_pull` factor their shared local
  argument through one private equivalence.  They reuse `rawExt_restrict` and
  the native open-subtype geodesic equivalence.
- `rawExt_pathLen` is hdom-free.  It uses `rawExt_inner`,
  `rawPullMetric_inner`, and the local-diffeomorphism derivative on the closed
  agreement core.
- `rawExt_radial_len` reuses `rawExt_pathLen`, `rawRadial_len`, and the native
  smooth monotone reparameterization theorem.
- `rawExt_edist_le` uses only the two radial segments from zero to its two
  endpoints and the Riemannian triangle inequality.

## Radial-domain audit

The initial no-`hdom` forecast was not supported by the live API.  Every native
route to radial length (`rawRadial_len`, `rawFlatPath_len`,
`raw_gauss_pullback`, and `rawSpeed_sq`) consumes radial `expDomain` coverage,
while `hloc` is only a pointwise local-diffeomorphism hypothesis.  The closest
domain bridge, `exp_dom_of_inj`, instead requires whole-ball injectivity.

The corrected weakest interface therefore keeps the first three theorems
hdom-free, gives `rawExt_radial_len` only the single endpoint's radial-domain
segment, and gives `rawExt_edist_le` only the two endpoint segments.  It does
not introduce a whole-ball premise or a wrapper predicate.

## Assumptions

No `CompleteSpace M`, `ConnectedSpace M`, ambient `SigmaCompactSpace M`,
`NeZero`, curvature, or global/raw-ball domain assumption is added.

## Verification

Warning-free focused verification passed after the coordinated upstream
refresh.  The only local repairs were removing an unused `Boundaryless`
assumption from the geodesic slice and making the `ContDiff` infinity level
explicit in the radial smoothness proof.  Static no-placeholder,
weakest-hypothesis, and diff reviews passed.

## Project accounting

- This distance-bridge slice: source-written and warning-free focused GREEN,
  100%.
- Dedicated P1b machinery: remains conservatively about 96% until final
  assembly.
- P1b endpoints E1/E2: both unstated and unproved, 0%.
- Aggregate P1 endpoints: eleven of fourteen, 78.6%.
- Whole Poincare theorem: unstated, 0%.
