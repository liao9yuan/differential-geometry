# PrincipalLowRegH2

## Purpose

This module assembles the low-regularity A2 operator directly from a spectral
`H2` metric deviation.  It composes the fixed-background second covariant
derivative, the Neumann inverse-cometric correction, and the fixed
double-trace action.

## Current status

The analytic low-regularity operator is complete and focused verification
passed.  `hessianH2` and `traceH2` expose the two fixed-background factors with
smooth-core compatibility.  `lowRegPrincipal` accepts an arbitrary spectral
`H2` metric state, while `lowRegPrincipal_norm` and
`lowRegPrincipal_lip` give uniform linear-size and Lipschitz bounds on one
fixed small ball.

The geometric smooth-core agreement is now proved in
`PrincipalLowRegCore.lowRegPrincipal_core`: on a smooth realized metric
deviation, this analytic operator is exactly `principalOpH2`, hence the
Ricci--DeTurck principal-cometric arm.

This completes the A2 operator producer itself.  The same-horizon bootstrap
still needs the lower-order operator/forcing decomposition and its
time-dependent realization before the nonautonomous maximal-regularity solver
can be applied.

The uniform short-time-existence endpoint remains unproved (0%).
