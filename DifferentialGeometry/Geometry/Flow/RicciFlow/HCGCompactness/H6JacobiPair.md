# H6JacobiPair

## Role

This producer converts the order-zero HCG curvature bound into simultaneous
metric-norm bounds for an intrinsic Jacobi field and its covariant velocity.
It is the base estimate needed before bounding the first mixed launch
derivative.

## Status

- `intrJacobi_pair_le` is implemented without a new geometric assumption.
- The proof uses the actual intrinsic Jacobi equation, constant geodesic speed,
  `HasCurvDerivBound.riemannOp_le` through `curvAlong_le`, and the common
  position-velocity conclusion of `VolumeComparison.intrJacobi_pair`.
- Focused verification is pending the current exact-writer handback and refresh
  of the newly exported `CovariantGronwall.covGronwall_pair_at`.

## Next Target

After this base pair estimate is focused-green, prove the first mixed-launch
position-velocity estimate from `intrJacForce_le`,
`intrLaunch_var_eq`, and `intrLaunch_mix_zero`/`intrLaunch_dmix0`.

## Accounting

`NormalRadiusProfile.le_exp_radius` and `exists_h6NormalData` remain unstated or
unproved endpoints at 0%. This file advances only the dedicated all-order
Jacobi/metric-jet machinery.
