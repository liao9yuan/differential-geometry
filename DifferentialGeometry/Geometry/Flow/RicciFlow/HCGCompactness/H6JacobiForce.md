# H6JacobiForce

## Role

This module converts the order-zero and order-one HCG curvature tensor bounds
into a pointwise metric-length estimate for the actual forcing in the first
intrinsic launch derivative of the Jacobi equation. It adds no supplied forcing
bound and no generic ODE-jet assumption.

## Current Result

- `curvAlong_le` applies the order-zero bound to an arbitrary `R(X,Y)Z` term.
- `curvDerivAlong_le` rewrites the actual smooth along-curve curvature
  derivative to `nablaRiemannOp` and applies the order-one bound.
- `jacVarForce_le` controls the exact six summands of `jacVarForce`: two
  covariant-curvature-derivative products and four curvature products, with the
  coefficient two retained on the `varCurv` term.
- `intrJacForce_le` instantiates the estimate for `intrLaunch3` and
  `intrLaunchJ`. Completeness and the pointed metric install the canonical
  intrinsic Riemannian structures, while joint launch smoothness discharges all
  seven regularity obligations.

Focused verification is green with no new `sorry`, `admit`, or `axiom`. The
first failed check was only the known competing tangent-norm instance; scoping
out the `Tensor0SBundle` norm for the intrinsic declaration, as already done by
`InjectivityRadius`, resolved it. Focused verification and the exact module
refresh both pass.

## Frontier

The pointwise forcing estimate is complete. The next genuine target is the
finite-order launch-parameter jet recursion on an arbitrary fixed tube and its
sequence-uniform Gronwall bound. That recursion must consume the proved
`intrJacForce_le`; it must not replace it with a supplied forcing estimate.

## Progress

- `NormalRadiusProfile`: theorem not stated, 0%.
- `exists_h6NormalData`: theorem not stated, 0%.
- Actual first differentiated-Jacobi forcing theorem: source/focused/exact
  complete, with no `sorry`/`admit`/`axiom`.
- All-order intrinsic metric-jet machinery: about 55%.
- Native H6 producer machinery: about 69%.
- Whole HCG compactness machinery: about 62%; the unconditional textbook
  compactness endpoint remains 0%.
