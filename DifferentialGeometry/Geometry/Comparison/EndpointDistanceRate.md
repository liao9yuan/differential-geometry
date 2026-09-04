# EndpointDistanceRate

## Route

The lower `RiemannianDistContinuity.param_edist_le` estimate is useful for
coordinate Lipschitz bounds, but an arbitrary chart operator norm does not
retain the sharp metric speed at the base point.  The canonical pointwise route
therefore uses the existing normal-coordinate radial-distance equality from
`GaussLemma`.

`edist_inc_tendsto` states the positive-increment limit directly.  A single
`MDifferentiableAt` hypothesis is enough: normal coordinates turn the curve
increment into an ordinary derivative, while the radial Riemannian seminorm is
continuous and homogeneous for positive scalars.

## Verification

The new module passes warning-free focused verification.  The public endpoint
`edist_inc_tendsto` is complete, and its exact named refresh passed GREEN once
the parallel P2 lanes had closed.
