# AppD1Hs

## Result

`appD1Hs` completes the smooth action `U |-> Phi(nabla U)` from spectral `H3`
to spectral `H2`.  `appD1Hs_norm` controls its operator norm by the intrinsic
`H2` coefficient jet, and `appD1Hs_core` records the exact smooth formula.

This is the spatial operator consumed by the remaining nonautonomous
first-order bootstrap arm.  Packaging its metric-dependent coefficient as a
time-measurable operator with the correct `L2_t` bound remains separate.

Focused verification passed.  This completes the generic spatial operator
machinery; it does not construct the rough metric-dependent coefficient
family.
