# PointwiseCurvatureDerivative

## Role

This module exposes the pointwise vector-valued covariant derivative of the
Levi-Civita curvature operator. It is a curvature-layer API and carries no HCG
compactness assumptions.

## Result

`nablaRiemannOp g x D X Y Z` is the direct pointwise object
`(nabla_D R)(X,Y)Z`, defined through the existing differentiated curvature and
canonical smooth tangent extensions.

`nablaRiemannOp_eq` identifies this pointwise object with
`curvCovDerivOpAt` for arbitrary smooth extensions. The canonical projection
`nablaRiemannOp_sec` identifies the same value directly with
`nablaCurvSec`; this is the section-level form consumed by the along-curve
chain rule. Both bridges avoid the unstable public signature of
`nablaBaseSlotCurv_eq_of_leftMid`.

## H6 impact

This is the pointwise forcing term needed by the first inhomogeneous
launch-Jacobi equation. It does not by itself prove any metric-jet bound.

- `exists_h6NormalData`: theorem completion remains 0%.
- All-order intrinsic metric-jet machinery: about 51%.
- Whole native H6 producer machinery: about 67%.
- Whole HCG compactness machinery: about 62%; the unconditional textbook
  compactness endpoint remains 0%.

Focused verification is green, and the module artifact is current. The
remaining H6 work is the along-curve restriction theorem and its quantitative
use in the first inhomogeneous launch-Jacobi equation, not another pointwise
curvature definition.
