# PathLengthVariation

## Scope

This module is the canonical low-dependency home of the fixed-path length
variation formula for a smooth Ricci flow.  It removes the accidental
cut-locus/Jacobi import cone from consumers that need only the time derivative
of a prescribed regular path.

## Native route

The theorem follows the existing proof: on a compact time-parameter rectangle,
continuity of the evolving metric and Ricci tensor gives a uniformly dominated
derivative for the square-root speed.  Differentiation under the interval
integral and the Ricci-flow equation identify the derivative with the integral
of minus Ricci divided by speed.

The declaration is moved without changing its public name or statement.
`RicciFlow.lean` remains the compatibility import for existing consumers.

## Status

- `pathLength_timeDeriv_of_ricciFlow`: source moved to the lower module without
  a new assumption or a parallel public theorem.  The first focused pass found
  only the missing narrow home import for
  `metricRicciAt_apply_eq_ricciTensor`; after adding it, focused verification
  passed without warnings.  The old `RicciFlow.lean` module now imports this
  canonical home and no longer contains a duplicate body.
- This extraction is infrastructure for fixed-endpoint changing distance; it
  does not complete the moving-endpoint theorem, which remains 0%.
