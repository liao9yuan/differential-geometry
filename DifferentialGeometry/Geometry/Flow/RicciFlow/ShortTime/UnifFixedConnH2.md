# `UnifFixedConnH2`

## Role

This module is the dimension-three class-first producer for the fixed-background
connection coefficient used by the low-regularity Ricci--DeTurck right-hand
side.  Its public endpoint is `connFix_h2_unif`.

## Mathematical route

- Reverse the class metric jets through orders one, two, and three.
- Apply the ungated order-zero, order-one, and order-two connection-difference
  estimates in the class metric fibre.
- Package their component bounds as the squared fibre norms of
  `iteratedCovGrad g₀ 1 2 j (connDiffSection gBase g₀)` for `j = 0,1,2`.
- Convert the pointwise bounds to `L²` and compare the total `g₀` volume with
  the fixed `gBase` volume.

The resulting coefficient depends only on `(gBase, Λ)` and is chosen before
`g₀` varies.  There is no small-perturbation hypothesis.

## Verification

Focused Lean verification passed without warnings.  The axiom audit contains
only the standard `propext`, `Classical.choice`, and `Quot.sound`.

The reusable pointwise companion `connFix_grid_unif` is also focused-green and
exactly exported after correcting its existential conclusion to expose the
chosen family as `F j`.  It is consumed by the fully axiom-audited
`dla_h1_unif` chain.

## Project accounting

- `connFix_h2_unif`: complete and focused-verified (100%).
- `connFix_grid_unif`: complete, focused-verified, and exactly exported (100%).
- Dedicated fixed-connection `H2` producer machinery: complete (100%).
- Class-first joint tame producer: still unstated (0%).
- `lowreg_bounds_unif`: still unproved (0%).
- `ricci_flow_unif_existence`: still unproved (0%).
- Whole HCG compactness project: approximately 3%.
