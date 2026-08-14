# MetricSectional

## Scope

`NonnegSecMetric g` is the invariant nonnegative sectional-curvature numerator predicate for a smooth Riemannian metric.  It keeps the existing `metricRm04StdAt` sign convention and does not introduce a quotient-valued sectional-curvature API.

## Implemented API

`NonnegSecMetric.riemann` rewrites the predicate to the Riemann-operator pairing used by Jacobi and index-form arguments.  `Variation.jacobi_pair_le_flat` is its first comparison-geometry consumer.

## Verification and progress

Focused verification and the full-project build passed without a new warning or placeholder, and the projection has no `sorryAx` dependency.  This predicate and projection are complete, but the Busemann geodesic-concavity theorem remains unstated and therefore 0%; its dedicated comparison machinery is approximately 20%.
