# IntrinsicMetricJets

## Role

This module is the geometry-layer bridge from intrinsic Jacobi launch jets to
ordinary Frechet derivatives of the intrinsic framed pullback metric.

## Status

The initial implementation defines the endpoint Gram jet and proves its
order-zero Gram identity. A trial global operator-valued smoothness wrapper was
removed after it exposed an avoidable elaboration wall: H6 already has
open-ball smoothness for the selected chart metric and equality with the
intrinsic metric there, which is the smaller honest interface.

## Next target

Prove the exact binomial derivative recurrence for `intrMetricJet`, identify it
with the one-dimensional derivative of `intrFrameMetric` along affine model
lines, and then transfer the diagonal estimate to the full operator norm by
polarization.

## Accounting

`NormalRadiusProfile.le_exp_radius` and the final `H6NormalData` producer remain
theorem-level 0%. This file is dedicated metric-jet machinery only.
