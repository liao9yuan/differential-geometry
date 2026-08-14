# EndpointNonnegative

## Status

`jacobi_pair_le_flat` is implemented without placeholders; focused verification and the full-project build passed, and Lean reports no `sorryAx` dependency.

The theorem bounds the terminal Jacobi pairing by the flat comparison value along a positive-length, unit-speed minimizing geodesic under `NonnegSecMetric`:

```text
g(DJ(L), J(L)) <= g(J(L), J(L)) / L.
```

The proof uses a parallel orthonormal perpendicular frame, transfers the Jacobi equation and index form to Euclidean coefficients, compares against the linear field with the same endpoints, applies nonnegativity of the minimizing-geodesic index form to their difference, and uses `NonnegSecMetric.riemann` to discard the nonnegative curvature term.

The existing APIs reused directly are `exists_parallel_perp_frame`, `perpCoeff_ode`, `perpLift_indexForm`, `indexForm_nonneg_of_minimising_geodesic`, `IsJacobiSolOn.indexForm_eq_sub`, `indexForm_add_smul`, and `NonnegSecMetric.riemann`. No alternate curvature predicate or HCG-layer curvature bridge was introduced.

## Project position

This theorem is the first checked sectional-curvature comparison producer for the nonnegative-curvature Soul lane. Its unit-speed `[0, L]` statement first needs a routine reparameterization and minimizing-tail bridge for the existing time-one intrinsic branch. The next comparison layer is then a selected-branch Hessian bound, followed by a sectional Calabi upper support and the one-dimensional barrier-to-concavity passage.

- `jacobi_pair_le_flat`: 100%.
- Selected-branch Hessian comparison theorem: not started, 0%; dedicated endpoint machinery approximately 60%.
- Busemann geodesic-concavity theorem: unstated, 0%; dedicated comparison machinery approximately 20%.
- Compact totally convex exhaustion under nonnegative sectional curvature:
  unstated, 0%; its downstream conditional compactness argument is 100%.
- Soul theorem: unstated, 0%; dedicated machinery approximately 15%.
- Whole nonnegative-curvature lane: approximately 12--15%.
- Whole post-HCG Poincare program: approximately 15--20%.
