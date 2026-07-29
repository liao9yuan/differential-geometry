# H6MetricJet

## Role

This module transfers the finite-tube intrinsic Jacobi-jet cap to endpoint
Gram jets. It is the scalar estimate layer before the two polarization steps
that recover the full pullback-metric derivative norm.

## Status

The first target is `intrMetricJet_abs_le`: a common bound for all launch
Jacobi jets through order `n` gives the explicit bound
`2 ^ n * B ^ 2` for the order-`n` Gram jet.

## Next target

Instantiate the bound with `H6JacobiPair.intrJet_upto_le`, then transfer the
diagonal affine-line estimate to the full metric derivative by polarization.

## Accounting

`NormalRadiusProfile.le_exp_radius` and the final `H6NormalData` producer
remain theorem-level 0%. This file is dedicated metric-jet machinery.
