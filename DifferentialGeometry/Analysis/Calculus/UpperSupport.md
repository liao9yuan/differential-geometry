# UpperSupport

## Status

`second_deriv_nonneg`, `concaveOn_of_upper`, `concaveOn_sub_sq`, and `concaveOn_tendsto` are implemented without placeholders. Focused, targeted, and full-project verification passed. Direct axiom inspection of the public endpoints reports only the standard `propext`, `Classical.choice`, and `Quot.sound` axioms.

The module isolates the one-dimensional calculus used by the Soul comparison lane. A continuous function with local twice-differentiable upper supports of nonpositive second derivative is concave. The quantitative version subtracts the sharp quadratic correction, and the limit theorem passes concavity through pointwise convergence.

`SecondVariationMinimiser.lean` now keeps its former public theorem as a compatibility wrapper around the pure calculus result.

## Project position

- One-dimensional upper-support calculus: 100%.
- Finite-distance semiconcavity from Calabi supports: 100%.
- Smooth-geodesic Busemann composition concavity: 100%.
- Public `IsGeodesicConcave` endpoint: unstated, 0%; its current predicate needs an explicit continuity correction before this machinery can feed it honestly.
- Soul theorem: unstated, 0%; dedicated machinery approximately 24%.
