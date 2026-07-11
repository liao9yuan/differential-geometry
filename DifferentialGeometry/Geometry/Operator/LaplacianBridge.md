# Scalar Laplacian bridge

## 2026-07-09

- `divergence_levi_eq` identifies the algebraic trace of the canonical
  Levi-Civita covariant derivative with the Voss--Weyl divergence.
- The proof expands both traces in one `g`-orthonormal basis.  The basis and
  identity inverse metric are constructed locally from the metric fibre, so
  this operator layer does not import a higher curvature module.  It reuses the
  intrinsic divergence theorem without unfolding coordinate representations
  downstream.
- `laplacian_levi_eq` and `laplacianAt_eq_delta` then identify the realized
  scalar Laplacian with the divergence-form `Delta_g` whenever the stored
  connection is canonical.
- Focused source verification passed without warnings or `sorry`.  A later
  targeted refresh did not reach this module: rebuilding the upstream
  `NablaOnTensors/Regularity/Derivation.lean` dependency hit the documented
  deterministic `nablaRSFun_eval_moving_raw` elaboration wall, and the failed
  build removed that upstream `.olean`.  The bridge source itself has no
  reported Lean error, but its module object is therefore not currently built.

This proves the source-level operator interface needed between the
interval-local heat-potential predicate and conjugate-heat mass conservation;
downstream integration must wait for the upstream object-file repair.  It does
not provide nonautonomous heat existence.  That theorem remains 0%; Perelman
no-local-collapsing remains 0%; dedicated analytic machinery is about 25% and
whole HCG machinery remains about 45%, with endpoint theorems still 0%.
