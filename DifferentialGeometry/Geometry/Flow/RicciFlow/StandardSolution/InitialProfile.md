# Initial profile

## Result

`InitialProfile.lean` now provides the concrete analytic and punctured-metric
part of the standard initial geometry.  The canonical `stdRadius` is globally
smooth, equals `2 sin(r/2)` on the tip side, is exactly two beyond `capEnd`, is
positive for positive radius, is concave on the nonnegative axis, and has
derivative in `[0, 1]`.

The file also constructs the genuine smooth metric
`stdCylMetric = dr^2 + stdRadius(r)^2 g_{S^2}` on the positive-radius polar
cylinder.  `stdEndMetric` is the product of the Euclidean ray and the radius-two
round sphere, and `stdCyl_end` proves exact pointwise equality with that product
metric past `capEnd`.

The two standard warped curvature coefficients are exposed as `stdRadCurv` and
`stdTanCurv`.  Both are proved nonnegative for positive radius.  They are each
exactly `1 / 4` in the round-cap interior; on the cylindrical interior the
radial coefficient is zero and the tangential coefficient is `1 / 4`.

## Remaining frontier

`exists_std_init` is not stated or proved.  Three distinct native routes were
checked:

- no warped-product connection or Riemann-curvature formula exists in the
  current geometry tree;
- the boundary second-fundamental-form API has no hypersurface Gauss equation
  for the Morgan--Tian surface-of-revolution route;
- `Sphere/Polar.lean` and `Sphere/PolarBij.lean` provide ambient smooth maps and
  a set-level `BijOn`, but no manifold local diffeomorphism or pullback-metric
  identity.

The smallest missing geometry producer is a structural formula for the
curvature numerator of `dr^2 + f(r)^2 h` as the sum of radial and tangential
wedge-square terms weighted by `-f''/f` and `(1-(f')^2)/f^2`.  Separately, the
positive-radius metric needs a smooth polar-collapse extension across the
origin, using the exact round germ, before compact-perturbation completeness can
apply on Euclidean three-space.  These are substantial reusable geometry
lemmas, not local coercion or elaboration repairs.

## Verification

Focused verification passed without warnings or placeholders.  No targeted or
global build was run.

## Progress

`exists_std_init` remains 0%, because it is still unstated.  P5-A2 is complete;
P5-A3 dedicated machinery is approximately 20--30%, and P5-A as a whole is
approximately 25--35%.  Dedicated machinery for all of P5 is approximately
4--7%.  The final P5 standard-solution theorem remains 0%, and the whole
Poincare-program infrastructure estimate remains approximately 15--25%.
