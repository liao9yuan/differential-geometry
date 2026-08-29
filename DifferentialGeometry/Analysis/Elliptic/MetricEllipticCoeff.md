# MetricEllipticCoeff

## Role

This module supplies the normalized De Giorgi coefficient attached to a
positive-radius Euclidean chart ball.  On the ball, the coefficient is a
strictly positive scalar multiple of the Riemannian weighted inverse Gram
matrix, so its bilinear form has the same sign.

## Implementation route

- Compactness of the closed ball follows from finite-dimensional Euclidean
  properness and the positive-radius closure identity.
- The lower bound for the weighted inverse Gram matrix reuses
  `exists_unif_lower_bound_on_compact`.
- The inverse lower bound is proved rather than assumed: the inverse matrix is
  identified with a positive scalar multiple of
  `densityOnEuclid⁻¹ • gramMatrixOnEuclid`, and a compact-product/unit-sphere
  minimum supplies its uniform positive quadratic lower bound.
- The normalized coefficient is the rescaled metric coefficient on the ball
  and the identity matrix off the ball.  Component measurability follows from
  continuous-on piecewise measurability.

## Verification

Focused verification passed without warnings.  No `sorry` is present.

## Project status

- `exists_metric_coeff`: proved and focused-verified (100%).
- Dedicated normalized metric-coefficient machinery in this module: complete
  (100%).
- The downstream chartwise manifold supersolution theorem is not stated or
  proved by this module (0% theorem completion here); this producer must still
  be wired to that consumer.
- The final Busemann-pair vanishing and splitting endpoints are not stated or
  proved by this module (0% theorem completion here).  This file closes only
  the local coefficient-construction gate and does not change those endpoint
  percentages.
