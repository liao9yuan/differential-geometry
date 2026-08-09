# RemainderCoeffPerOrderJetEnvelopes

## Explicit two-arm grid coefficient (2026-08-05)

The mixed-valence diagonal two-arm product-grid proof now exposes
`gnGridCoeff`, `gridRsConst`, and `grid_rs_bound`.  The existing long
`exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le` theorem is
preserved as a compatibility wrapper.

The proof no longer selects separate metric-late GN witnesses for the two
tensor arms.  Both arms use the exact `gnRsConst` supplied by `gn_rs_bound`, and
the finite grid coefficient is an explicit sum of their products.  The analytic
Hölder/Young/cell-summation proof is unchanged.  Focused verification passed
without warnings.

The `.olean`-only refresh of this module was stopped after the process reduced
free physical memory below 1 GB.  No source error was reported, and the old
artifact was not overwritten.  The next routine step, once enough memory is
available, is to refresh this one module and add the HCG class wrapper that
bounds every `gnGridCoeff` by `gnClassC`.
