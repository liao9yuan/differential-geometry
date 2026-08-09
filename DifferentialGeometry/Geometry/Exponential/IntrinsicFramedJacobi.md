# IntrinsicFramedJacobi

## Purpose

This module is the canonical differential bridge from the total intrinsic
framed exponential to the intrinsic Jacobi-field API. It expresses the
intrinsic pullback metric as an endpoint Jacobi Gram form without introducing
another coordinate metric.

## Status

`intrFrame_deriv`, `intr_metric_jacobi`, `intrFrame_deriv_inj`, and
`intrFrame_not_conj` are implemented without `sorry`/`admit`/`axiom`.
Focused verification and the exact module refresh pass.

## Progress

- Differential-to-Jacobi bridge: 100% proved and focused-checked.
- Intrinsic pullback metric endpoint formula: 100% proved and focused-checked.
- Positive pullback-metric lower bound to differential injectivity and
  nonconjugacy: 100% proved and exact-checked.
- Sequence-uniform H6 relative-radius theorem: 0%. This module supplies a
  canonical input to that producer but does not prove the quantitative
  endpoint estimate.

## Next Target

The intrinsic Rm04 half/two estimate and its sequence-uniform nonconjugacy/local
branch consequence now live in `C4/H6NormalCoord.lean`. The next lower-layer
frontier is local identification of the chart-fixed exponential with the
intrinsic exponential at arbitrary vectors in the natural `expDomain`. Combined
with `exp_dom_of_inj_rad`, that supplies a local diffeomorphism on the geometric
injectivity ball without using the legacy `expRadiusGp` clamp.
