# HsTwoJet

## Purpose

This module isolates the curvature-free easy comparison from the covariant
two-jet to the intrinsic spectral `H^2` norm.  The explicit constant depends
only on the model dimension, so it is available before a metric class member
is chosen.

## Status

Focused verification passed.  The public endpoint depends only on the expected
`propext`, `Classical.choice`, and `Quot.sound` axioms.

## A2 implication

This closes only the output conversion in a class-first `H^4 -> H^2`
second-derivative action estimate.  The remaining input conversion is the hard
finite `H^4` Gårding comparison.  The repository currently contains only the
finite `H^2` and `H^3` hard comparisons, while its class-first curvature-action
packet stores only the rank-two and rank-three order-zero actions.

Extending the existing finite Bochner route to `H^4` for a covariant two-tensor
requires controlling one covariant derivative of `pointwiseTensorCurv`.  The
resulting expression contains a second covariant derivative of Riemann
curvature, so a class-first producer naturally needs metric jets through order
four.  The current order-three class packet gives only curvature and its first
covariant derivative.  Thus `appRS_h22_unif` plus this easy comparison does not
by itself yield a truthful class-three `appD2Hs_norm_unif`.
