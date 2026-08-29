# P2AxiomCheck

## Role

This diagnostic module imports the completed late-floor, uniform controlled-
ball, and compact smooth-flow noncollapsing chain and asks Lean for the axioms
of its public endpoints. It is not part of the L-geometry umbrella and
introduces no declarations.

## Verification

The compact P2a audit is warning-free green. Every previously printed endpoint,
including `redVolume_ball_unif` and `smooth_nlc`, depends only on Lean's standard
logical axioms (`propext`, `Classical.choice`, and `Quot.sound`).

The audit now also covers the fixed-diffeomorphism action identities, the
smooth crossing bound, the pointed source-domain velocity/kinetic identities,
and the short changing-distance support.  Focused verification is warning-free
green after the four real producer imports were explicitly named-refreshed.
Every one of the 19 printed declarations depends only on `propext`,
`Classical.choice`, and `Quot.sound`; in particular, the unresolved
`estimate_complete` placeholder does not leak into these endpoints.  The
diagnostic module itself exports no declarations and is not named-refreshed.
