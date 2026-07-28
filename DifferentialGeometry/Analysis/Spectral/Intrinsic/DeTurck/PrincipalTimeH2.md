# PrincipalTimeH2

## Purpose

This module turns the actual low-regularity Ricci--DeTurck principal
coefficient into the time-dependent `A2(t) : H4 -> H2` family consumed by the
mixed nonautonomous maximal-regularity solver.

## Current status

`principalBall_data` chooses one positive spectral `H2` radius on which the
principal coefficient is Lipschitz and has operator norm bounded linearly by
the actual metric-deviation norm.  `principalTime_data` retains this estimate
uniformly on every smaller nonnegative state radius.  Thus the radius may
still be reduced later to satisfy the contraction inequality.  `principalTime`
uses the existing almost-everywhere subtype lift; the accompanying theorems
provide strong measurability, the uniform operator-norm bound, and
almost-everywhere agreement with `lowRegPrincipal (f t)`.

Focused verification passed.  The only nonstandard proof detail is continuity
of the principal operator in the canonical continuous-linear-map topology:
the operator-norm Lipschitz estimate is converted through the bounded-set
neighborhood basis, avoiding the inherited-topology instance diamond.

This completes time-family packaging only.  The order-two bootstrap theorem
and `ricci_flow_unif_existence` remain unproved (0%).  The next independent
geometric frontier is the actual principal-subtracted lower-order `A1(t)`
factorization with an `L2` time norm.
