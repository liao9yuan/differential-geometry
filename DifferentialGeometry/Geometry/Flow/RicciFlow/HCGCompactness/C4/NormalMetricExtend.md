# NormalMetricExtend

## Role

This file turns the named normal-coordinate smoothness ball into an honest
cross-model `C∞` partial diffeomorphism, realizes the pullback metric, and
extends it to a total model-space metric by a buffered cutoff.

## Current state

- `normalBall` is the ball of radius `expMapC2Radius`.
- `normalExpPD` upgrades the restricted exponential and normal chart to a
  `PartialDiffeomorph … ∞`.
- `normalImage` is its open image.
- `normalBallDiffeo` packages that restriction using the general cross-model
  opens API.
- `normalMetric` pulls the ambient metric back to the ball, and
  `normalMetric_inner` identifies it with `normalCoordMetric`.
- `normalCut` is one on the quarter-radius ball and has topological support in
  the half-radius closed ball.
- `normalTotal` bump-extends `normalMetric` against the flat model metric.
- `normalTotal_inner` identifies the total metric with `normalCoordMetric` on
  the quarter-radius ball, leaving an open neighborhood suitable for later
  derivative and Koszul locality arguments.
- `normalTotal_eq` packages that equality at the coefficient-field level.
- `normal_cov_eq` consumes the neighborhood-local Levi--Civita/Koszul theorem
  and identifies constant-field covariant derivatives for `normalTotal` with
  the raised normal-coordinate Koszul vector.

Focused verification of the complete file passed, and the targeted module
artifact was refreshed after the final source edit. No new `sorry` or `admit`
was introduced.

## Frontier

The next geometric brick is locality of the geodesic equation/flow: while its
trajectory remains in the quarter-radius ball, the model-space geodesic for
`normalTotal` must realize the intrinsic exponential trajectory. The remaining
large design choice is still how to expose the resulting quantitative inverse
branch to the existing diagonal-exp consumers.

The moving quantitative inverse theorem itself remains unstated and therefore
0% complete. Its dedicated Step B/B1 machinery is approximately 62% complete;
Step B/B1 as a large phase is approximately 69% complete; the whole HCG
compactness infrastructure remains approximately 47% complete. These numbers
measure machinery only, not any still-unstated textbook endpoint.
