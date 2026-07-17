# Low-regularity Ricci--DeTurck remainder

## Verified result

- `rem_h0_lip` subtracts the fixed background connection Laplacian from the
  Ricci--DeTurck RHS difference and proves a uniform spectral `H2 -> H0` bound.
- The proof combines `rhs_h0_lip` with the exact two-derivative spectral bound
  for `rawTensorConnLapSmooth`; it adds no analytic assumptions.
- Focused verification passes without local warnings or sorries.

## Remaining frontier

The required mixed remainder theorem is still unstated and unproved. Its
first-derivative part must exploit exact principal cancellation. A direct use
of `rhs_h1_lip` loses one derivative because it separately estimates the fixed
background Laplacian.

The intended low-regularity split is:

1. the third derivative of the metric difference multiplied by the small
   principal-cometric deviation, controlled by the H2 radius and
   `principal_path_h2` / `principal_arm_h2`;
2. terms containing at most two derivatives of the metric difference, with
   coefficients uniformly controlled by `IsLowRegCoeff`.

The top branch is no longer a frontier: `LowRegPathSplit.phi_dev_h2`,
`top_path_dev_h2`, and `top_path_ball_h1` pass focused verification and give
the required three-dimensional small-coefficient estimate. The remaining
frontier is the exact full Ricci--DeTurck principal cancellation together with
uniform bounds for the order-zero/order-one branch. The corresponding concrete
path integrals and identity exist in the high-order development, but are
private inside a source file far above the 3000-line maintenance limit. They
cannot be made into a new public facade in that file.

The unresolved architecture choice is between two honest routes: extract the
existing exact path construction into a small module, or integrate the public
`MetricFamilyChartLinearization` identity and package its genuinely
first-order remainder in `RHSSectionCovGradL2Decomposition`. A coarse use of
`rhs_h1_lip` is not a substitute because it retains a nonsmall `H3` coefficient.
A read-only consult did not return a ruling, so this is the current consult
boundary rather than a local proof obligation.

The existing high-order three-arm estimate does not close this result because
its coefficient bounds assume `a >= 2 * dim + 10`. Only its exact algebraic
decomposition is potentially reusable at low regularity.

## Honest accounting

- `rem_h0_lip`: theorem 100%.
- Mixed `H3 -> H1` remainder theorem: not yet stated/proved, 0%; dedicated
  machinery is approximately 70%.
- Uniform low-regularity Ricci--DeTurck existence theorem: not yet
  stated/proved, 0%.
- Whole HCG compactness machinery remains approximately 57%; endpoint
  compactness theorems remain 0% until stated and proved.
