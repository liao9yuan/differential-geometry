# PrincipalCoeffDimBound

## Status (2026-08-06)

This module is the explicit, metric-independent principal-coefficient package.
It uses the dimension-only self-cometric trace bound and exposes pointwise plus
`L²` jet estimates for the DeTurck principal coefficient, the Ricci principal
difference, and the trace-Hessian difference.  Its constants are
`appCcGdiag i * dim^8` and `(10 / 4) * appCcGdiag i * dim^8`.

Focused verification passed with four Lean threads under the 6 GB cap, without
warnings.  All seven public estimates/equalities have only the project's
standard `propext`, `Classical.choice`, and `Quot.sound` axioms.  This package
therefore has 100% local theorem completion and removes one class-first
constant-choice obstruction, but it does not itself prove the uniform tame producer,
`lowreg_bounds_unif`, or `ricci_flow_unif_existence`; all three endpoints remain
theorem-level 0%.  Dedicated supporting infrastructure is approximately 98%,
and whole HCG closure remains approximately 3%.
