# Tensor Hs interpolation and spectral exhaustion

## Role

This module contains rank-generic spectral compactness bricks for
`tensorHs`.  In addition to the existing interpolation theorems, it now owns
the canonical finite spectral exhaustion for arbitrary tensor rank `(r,s)`.

## Generic exhaustion

`eigenFinset` is defined directly from
`tensorEigenIdx_one_add_lambda_lt_finite`.  The companion lemmas identify
membership, prove monotonicity, show that every eigen-index eventually occurs,
and package convergence to the top finset filter.  This is the low-level API
needed by scalar `(0,0)` Galerkin compactness; the older `(0,2)`-specific
`eigenIdxFinset` remains a compatibility API and is not imported backwards.

No convergence hypothesis, chart selector, or geometric assumption was added.

## Coordinate convergence

`tendsto_of_coeff` is now the canonical rank-generic coefficient-to-Sobolev
compactness bridge: coordinatewise convergence plus a uniform higher-order
bound gives norm convergence after a strict Sobolev downshift.  The former
private duplicate in the `(0,2)` forcing-limit file was removed, and its sole
consumer now uses this lower-layer theorem directly.  The pre-existing
low-norm interpolation theorem is retained as a short compatibility entrypoint
derived from `tendsto_of_coeff`.

## Verification

The generic exhaustion and coefficient-convergence sources are implemented
without `sorry`, and focused verification passed.  These APIs and their
dedicated machinery are 100% complete.  The later `scalar_gal_subseq` theorem
remains not started (0%); its dedicated compactness machinery is about 75%
complete.  The Perelman
noncollapsing endpoint theorem remains not started (0%) and is not claimed by
this API addition.
