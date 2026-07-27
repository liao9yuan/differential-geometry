# ForwardUniqueRmReg

## Closed-edge curvature tower

This module uses the fixed chart-trivialization frame and the rank-uniform
realization bridge to obtain one-sided joint regularity of every finite
covariant derivative of the lowered Riemann tensor from chart-Gram regularity.

It also records the reusable one-step bridge `nablaChartJoint`: joint
chart-component regularity of a moving covariant tensor is preserved by one
covariant derivative for an independently moving metric.  Applying that bridge
once and twice to `rm04Section gL (metricCov gC)` gives
`crossRm1ChartJoint` and `crossRm2ChartJoint`.  These are the closed-edge inputs
for bounding the `g₁` derivatives of the `g₁`-lowered curvature of `g₂` that
appears as `P` in `sdecRem`; the own-metric curvature tower is not
definitionally the same field.

The chart/local-frame Christoffel bridge uses locality of the covariant
derivative: the two frame sections agree on the open trivialization domain,
then the local-frame basis coordinates select the required Christoffel
coefficient.  The one-step and iterated realization congruences are oriented
from intrinsic chart components back to their frame-component realizations.

Status: focused verification and the targeted export refresh passed; the file
is warning-clean.
