# DirectionalJet

## Role

This module provides the local calculus bridge from affine-line derivatives to
repeated directional evaluations of iterated Frechet derivatives.

## Status

`iteratedDeriv_line` assumes only a `C∞` germ at the base point, shrinks to an
open neighborhood, and applies the existing translation and continuous-linear
precomposition formulas. `iteratedDeriv_clm` records that postcomposition by a
continuous linear map commutes with ordinary iterated derivatives under the
same `C∞` assumption.

The source is focused-green. An exact artifact refresh is deferred until the
shared writer window is returned.

## Next target

Consume these theorems in `H6MetricJet` to identify repeated-direction
`iteratedFDeriv` evaluations of a normal-chart metric with its affine-line Gram
jets. The remaining lower-layer calculus frontier is permutation symmetry of
`iteratedFDeriv` under `C∞` regularity; the Mathlib theorem requiring `ω`
cannot be used for H6.
