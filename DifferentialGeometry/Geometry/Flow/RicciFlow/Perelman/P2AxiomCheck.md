# P2AxiomCheck

## Role

This diagnostic module imports the completed late-floor, uniform controlled-
ball, and compact smooth-flow noncollapsing chain and asks Lean for the axioms
of its public endpoints. It is not part of the L-geometry umbrella and
introduces no declarations.

## Verification

Focused verification is warning-free green. Every printed endpoint, including
`redVolume_ball_unif` and `smooth_nlc`, depends only on Lean's standard logical
axioms (`propext`, `Classical.choice`, and `Quot.sound`). No named artifact
refresh is needed because this diagnostic module exports no declarations.
