# UnifDLaH1

## Role

This module is the three-dimensional class-first spectral `H1` integration of
the lower-layer DLa pointwise grid.  It composes `connFix_grid_unif`,
`dla_grid_of_conn`, and `h1_grid_unif` without introducing a metricwise
existential coefficient.

## Current status

The source theorem `dla_h1_unif` is implemented, focused-green without local
warnings, exactly exported, and axiom-audited with only `propext`,
`Classical.choice`, and `Quot.sound`.  It consumes class metric jets through
order three; the perturbation input is the usual `H2` radius plus the single
third-derivative top bound.

The theorem is genuinely class-first: its two affine coefficient functions are
chosen from `(gBase, Λ, δ₀)` before the class metric `g₀` varies.  No fourth
metric jet or curvature jet is used.

## Project accounting

- `dla_h1_unif`: complete and fully verified (100%).
- Dedicated DLa pointwise-to-`H1` machinery: complete (100%).
- Order-zero cancellation tail (`DLb + lieCorr0`): not yet assembled (0%).
- Class-first joint tame producer: still unstated (0%).
- `lowreg_bounds_unif`: still unproved (0%).
- `ricci_flow_unif_existence`: still unproved (0%).
- Whole HCG compactness project: approximately 3%.
