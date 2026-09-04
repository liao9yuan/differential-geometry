# Warped-product curvature

## Scope

This module supplies the structural curvature calculation for a metric of the
form `dr^2 + f(r)^2 h`. It works at the split tangent-space level
`Real x F`, where `h` is the fiber inner product and `fiberR` is the fiber
curvature operator.

## Verified API

- `warpInner` is the split warped inner product.
- `warpRadCurv` and `warpTanCurv` are the classical radial and tangential
  sectional-curvature coefficients.
- `warpConnDiff` is the standard difference between the warped and product
  connections.
- `warp_koszul` proves that `warpConnDiff` is the Koszul vector determined by
  the radial derivative of the warped Gram field. This is the native
  `MetricKoszul.koszulCov` certification, rather than an assumed connection
  formula.
- `warpDiffDeriv` records the product-covariant derivative of the connection
  difference on product-parallel vectors.
- `warpCurvOp` assembles product curvature, the antisymmetrized derivative
  term, and the quadratic connection-difference term.
- `warpRm_formula` proves the full curvature numerator

  `-f*f''*h(a*v-b*u,a*v-b*u) + f^2*Rm_h(u,v,v,u)
    - f^2*(f')^2*(h(u,u)*h(v,v)-h(u,v)^2)`.

- `warpRm_round` specializes the fiber to constant curvature one.
- `warpRm_coeffs` gives the consumer-facing coefficient decomposition using
  `-f''/f` and `(1-(f')^2)/f^2` times the corresponding squared-area terms.

The focused verification passed without warnings. No targeted refresh or
broad build was run.

## Remaining geometric realization

The structural formula is proved, but the theorem identifying the curvature
of the concrete `SmoothRiemannianMetric` used by `stdCylMetric` with
`warpCurvOp` is not yet stated or proved.

Three native routes were audited:

1. The connection-difference route is closest. The project has
   `riemannSec_difference`, but no theorem yet saying that the Levi-Civita
   connection of a product metric splits, or identifying the warped-minus-
   product connection under the product tangent equivalence.
2. The coordinate two-jet route has `chartRiemann_eq_jet`, but lacks the
   product-chart Gram two-jet bridge and a round-fiber normal-coordinate jet
   theorem in the required form.
3. The hypersurface route has sphere ambient-map infrastructure, but no Gauss
   equation or hypersurface-curvature realization API.

The smallest next generic lemma is the connection realization: under the
product tangent splitting, prove that the difference between the warped and
product Levi-Civita connections is `warpConnDiff`. Together with the existing
connection-difference curvature theorem and `warpDiffDeriv`, that should reduce
the concrete metric result to this module's checked algebra.

## Progress accounting

- `warpRm_coeffs`: stated and proved, 100%.
- Structural algebra/Koszul machinery in this module: 100%.
- Concrete `metricRm04StdAt` realization for `stdCylMetric`: theorem not yet
  stated, 0%; its dedicated bridge machinery is about 25-35%.
- P5-A initial-profile and curvature stage: about 35-45%.
- Final P5 standard-solution theorem: not stated, 0%; all dedicated P5
  machinery combined is about 6-10%.
- Whole Poincare-program infrastructure: about 15-25%.
