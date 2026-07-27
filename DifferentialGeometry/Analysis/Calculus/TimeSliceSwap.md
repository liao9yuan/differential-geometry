# TimeSliceSwap.lean

## Purpose

`hasDerivAt_iterF` commutes a pointwise time evolution equation with any fixed
finite spatial Fréchet derivative.  Its hypotheses deliberately avoid joint
differentiability of the evolving family: only smooth spatial slices and joint
continuity of the required spatial jets of the right-hand side are used.

## Current status

The implementation uses a local interval FTC argument and differentiation under
the interval integral.  Compactness is used only in the time variable, so no
finite-dimensional assumption on the spatial model is required.  Completeness of
the target is required by the Banach-valued FTC.

Focused verification passes.  The only delicate implementation point is the
successor step: currying an integrated Fréchet derivative is handled by commuting
both the inner continuous-linear-map evaluation and the outer multilinear-map
evaluation with the interval integral.  This keeps the proof independent of
definitional unfolding of the currying equivalence.

## Closed-interval version (2026-07-26)

`hasDerivWithin_iterF` is proved and focused-green.  It commutes the same
finite spatial Frechet derivative with a time equation stated using
`HasDerivWithinAt` on `Icc a b`, including both endpoints.  No openness,
finite-dimensionality, or endpoint extension hypothesis was added.

The supporting `tube_bound_on` now derives the common spatial neighborhood
from relative continuity on `J x V`: the estimate is guarded by membership in
`J x V`, then compactness of the time segment makes the spatial neighborhood
uniform.  Consequently `iterF_integral` no longer needs `J` open.

For the HCG closed-window bootstrap this theorem is one completed analytic
brick (100%).  It does not by itself prove joint smoothness on
`Icc x V`; the next required brick is the within-set analogue of the current
joint slice-derivative kernel, followed by the finite-order bootstrap.

## FTC endpoint bridge (2026-07-27)

`hasDerivIcc_of_int` is proved and exact-green.  If a Banach-valued function
and its proposed derivative are continuous on `Icc a b`, and the ordinary
derivative equation holds on `Ioo a b`, the theorem reconstructs the function
from the interval integral and obtains `HasDerivWithinAt` at every point of the
closed interval.  In particular, it handles both endpoints without separate
one-sided derivative case splits or endpoint regularity assumptions.

This theorem is 100%.  It supplies the endpoint step used by the finite-order
closed-window Ricci-flow bootstrap; it is not itself the geometric limit-flow
endpoint.
