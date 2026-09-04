# RicciEndpoint

## Role

`RicciEndpoint.lean` is the static producer for the endpoint Ricci-integral
estimate used later by the changing-distance argument.  It deliberately lives
in the P2 distance layer so that it does not collide with the claimed P1
comparison files.  It assumes no Ricci flow and no sign condition on the
endpoint bound; completeness is present only because the reused native
minimizing-geodesic second-variation producer requires it.

## Reuse and route

- The normal parallel frame and minimizing-geodesic index-form inequality come
  from `Variation/PerpFrame` and `Variation/SecondVariationMinimiser`.
- The Ricci trace identity is reused from `BonnetMyers/LengthBound`.
- The nonsmooth endpoint trapezoid is approached by the exact-endpoint flat
  smooth density theorem, and its quadratic limit is handled by
  `TimeQuadraticStrong`.
- The only local bridge is a private arbitrary-smooth-weight version of the
  integrability and pointwise frame-sum calculation; the existing comparison
  versions are specialized to the sine test field.

## Verification

Focused verification is warning-free green through the complete generic-weight,
second-variation, strong-limit, and endpoint-defect argument.  The two required
time-Sobolev producer artifacts were refreshed in an exclusive window before
the successful check.  Three command-internal empty lines reported only during
the downstream replay were removed, and the focused regression remains
warning-free green; no declaration or proof term changed.

The first passes exposed only local elaboration issues: wrong Unicode variants
of the manifold and filter notation, the connection namespace, the standard
tangent-space norm-instance diamond, and dependent scalar-linearity rewrite
shape.  These were repaired using the repository's native notation, scoped
instance removal, and fully applied scalar identities.  A private derivative
representative bridge is used so this module does not depend on the still-stale
`TimeH1TentC1` artifact.

## Frontier

The theorem `ricci_int_end_le` is complete.  Its current native proof uses the
existing minimizing-geodesic second-variation theorem, so the public statement
honestly carries the complete time-slice hypothesis required by that producer.
Its exact consumer `dist_long_support` is now warning-free focused and
named-refresh green.  The subsequent cut-safe `dist_moving_slope` transfer is
also checked.  The next distance frontier is no longer this static Ricci
estimate; it is the sharp endpoint-distance rate for a differentiable curve
under the smoothly varying metric.

## Weak-signature adaptation

The sole call to `indexForm_nonneg_of_minimising_geodesic` now follows its
weaker argument list: the metric-norm witness and the separately supplied
smoothness proof for the central geodesic are no longer passed.  The existing
`g`, curve, interval length, variation field, field smoothness, geodesic,
minimizing, unit-speed, perpendicularity, and endpoint data are unchanged.
The metric-norm witness consequently became unused in both the private smooth
index helper and the public endpoint theorem, so it was removed from those two
signatures.  This only weakens the assumptions; the conclusion and mathematical
proof are unchanged.

After the coordinated upstream artifact refresh, focused verification is
warning-free green.  No build or refresh was run in this adaptation window.
## Weak-signature artifact handoff (2026-09-01)

The completeness-free index-form signature migration is warning-free focused
GREEN, and the explicitly named `RicciEndpoint` refresh passed.  The refresh
replayed unrelated dependency warnings but the target module was clean.  The
single `ChangingDistance` consumer may now be focused-checked against the new
public signature.
