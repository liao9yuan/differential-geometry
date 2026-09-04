# TimeH1AC

## Role

This module realizes a finite-dimensional absolutely continuous curve with an
`L2` ordinary derivative as the existing `timeH1` data type.  It is independent
of manifolds and Ricci flow.

## Native route

The continuous representative is recovered by a finite-dimensional vector
fundamental theorem of calculus.  The proof tests against coordinates of a
linear equivalence with a finite product of real lines, applies the existing
scalar absolutely-continuous fundamental theorem, and then uses the supplied
`MemLp` derivative to construct the weak derivative.  The public
`timeH1.exists_ofAC` theorem packages the representative and derivative
identities together, so no redundant proof argument is stored in a data
definition.

## Verification

`timeH1.exists_ofAC` is warning-free focused GREEN.  Its exact named refresh is
deferred until the first downstream module imports the new declaration.

## Next use

A chart-local adapter must prove that the coordinate derivative of a raw
finite-action manifold curve is in `L2`; `timeH1.exists_ofAC` then supplies
exactly the representative expected by `lAction_c1_dense`.
