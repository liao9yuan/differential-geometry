# MetricBall

## Role

`lMetric_ball` is the ball-local replacement for the compact-slab theorem
`lMetric_scale`.  It compares the moving metric with the terminal metric at a
point of the terminal radius-`1/32` ball on a scale-invariant short backward
interval.

## Route

The proof uses the native scalar moving-metric ODE and the absolute Ricci
quadratic bound from `FlowMetricBall.IsRmControlled`.  The terminal distance
hypothesis is transported backward by the existing Calabi-distance anchor, so
the fixed point remains in the controlled moving ball and no global Ricci bound
or compactness assumption is introduced.

The terminal-distance adapter is exported as `edistTo_terminal` because the
range-control consumer also needs the same terminal minimizing-curve estimate.
The public `lMetric_ball` hypothesis is the closed condition
`d_T(center,x) ≤ radius/32`; the proof retains strict room by first reaching
`radius/16` and only then comparing with the controlled radius.

The short parameter is chosen from the model dimension before the flow,
terminal time, center, and actual ball radius.  The resulting exponent is the
scale-invariant `2 * dim^2 * eps`.

## Verification

The previous strict-hypothesis signature was focused-check green.  The exported
distance adapter and weakened closed terminal hypothesis change public
signatures, so the current source awaits a new focused check and downstream
named refresh coordinated by the root P2 lane.

## Progress

`lMetric_ball` was green before the current interface improvement and is now
pending signature re-verification.  It is one producer in the final `smooth_nlc` chain;
`smooth_nlc` itself remains unstated and unproved (0%).
