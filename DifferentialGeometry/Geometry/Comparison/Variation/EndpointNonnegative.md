# EndpointNonnegative

## Status

`jacobi_pair_le_flat` and its time-one specialization `intrJacobi_pair_le` are implemented without placeholders. Both passed focused, targeted, and full-project verification.

The theorem bounds the terminal Jacobi pairing by the flat comparison value along a positive-length, unit-speed minimizing geodesic under `NonnegSecMetric`:

```text
g(DJ(L), J(L)) <= g(J(L), J(L)) / L.
```

The proof uses a parallel orthonormal perpendicular frame, transfers the Jacobi equation and index form to Euclidean coefficients, compares against the linear field with the same endpoints, applies nonnegativity of the minimizing-geodesic index form to their difference, and uses `NonnegSecMetric.riemann` to discard the nonnegative curvature term.

The existing APIs reused directly are `exists_parallel_perp_frame`, `perpCoeff_ode`, `perpLift_indexForm`, `indexForm_nonneg_of_minimising_geodesic`, `IsJacobiSolOn.indexForm_eq_sub`, `indexForm_add_smul`, and `NonnegSecMetric.riemann`. The time-one specialization additionally uses `radial_min_len`, `intrJacobi_smul`, `varField_smooth`, and `covDeriv_comp_mul`. No alternate curvature predicate or HCG-layer curvature bridge was introduced.

## Project position

These theorems carry the unit-speed `[0, L]` index-form estimate through normalized radial reparameterization to the time-one intrinsic branch. The downstream branch-Hessian, exact Calabi-tail, scalar upper-support, semiconcavity, and smooth-geodesic Busemann-limit layers are now implemented.

- `jacobi_pair_le_flat`: 100%.
- `intrJacobi_pair_le`: 100% after focused, targeted, and full-project verification.
- Selected-branch Hessian comparison theorem: 100% after focused, targeted, and full-project verification.
- Smooth-geodesic Busemann composition concavity: 100%.
- Public `IsGeodesicConcave` Busemann theorem: 100%.
- Compact totally convex exhaustion under nonnegative sectional curvature:
  100%.
- Soul theorem: unstated, 0%; dedicated machinery approximately 30%.
- Whole nonnegative-curvature lane: approximately 22--25%.
- Whole post-HCG Poincare program: approximately 15--20%.
