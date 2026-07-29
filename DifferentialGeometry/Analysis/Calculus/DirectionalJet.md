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

The finite-regularity set-level commutation theorem now underlies three
germ-level APIs:

- `fderiv_iter_apply`, for a fixed directional derivative;
- `iterFDeriv_clm_apply` and the two-slot `iterFDeriv_apply₂`;
- `iterFDeriv_perm`, proving invariance under every permutation at `C∞`.

The full permutation proof uses cyclic rotation, an adjacent swap obtained by
induction on the fixed final direction, and the standard finite-permutation
generation theorem. It does not strengthen `C∞` to analytic regularity.

The source is focused-green. The exact artifact refresh is deferred while
another lane owns the shared writer window.

## Next target

Refresh this module once the writer window is returned, recheck
`IteratedFDerivProdMatch`, and consume `iterFDeriv_perm` plus the two-slot
evaluation lemmas in `H6MetricJet`.
