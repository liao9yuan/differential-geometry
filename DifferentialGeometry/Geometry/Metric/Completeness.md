# Completeness

## 2026-08-28: compact manifolds

`RiemannianMetricComplete.of_compact` is the canonical metric-layer producer
that every smooth Riemannian metric on a compact manifold is complete.  It
reuses the metric-induced extended distance and compact-space completeness;
the theorem does not require the ambient model space to be declared complete.
Its ambient metric API retains the standard sigma-compact manifold instance;
compactness supplies this instance automatically at call sites.

The first focused check found only a term-lambda token typo.  The second showed
that the result type records the ambient metric API's sigma-compact section
instance, so that instance cannot be explicitly omitted from the declaration.
Both local issues were corrected, and the final focused check passed without
warnings.

This generic helper is verified and is consumed by `NLCBallUnif` to supply
time-slice completeness without a stronger public assumption.  The downstream
`redVolume_ball_unif` and `smooth_nlc` endpoints are now also verified; this
helper remains separately counted generic infrastructure.
