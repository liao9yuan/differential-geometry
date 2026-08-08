# UnifInvCoeffH3

## Role

`inv_coeff_h3_unif` is the class-first homogeneous inverse-metric coefficient
bound through three covariant derivatives.  Its smallness hypothesis remains
the spectral `H2` norm, while both conclusions are linear in the spectral `H3`
norm.

## Proof route

The verified `inv_coeff_h2_unif` supplies the pointwise and range-three lower
jet estimates.  The new top derivative uses the existing all-order
`invDiff_grid_unif` pointwise grid with `rank_two_grid_unif` at order three.
The lower grid radius comes from the capped `H2` jet; only the top factor uses
the homogeneous `H3` norm through `covsum_hs_three`.

## Verification

Focused verification passed without warnings.  The direct module refresh also
passed.  A direct axiom audit reports only `propext`, `Classical.choice`,
and `Quot.sound`.

## Project accounting

- `inv_coeff_h3_unif`: theorem-level 100%, focused-verified, and directly
  refreshed.
- The eventual class-first full top-kernel `H3` bound remains unstated and is
  therefore 0%; this file is dedicated producer infrastructure for it.
- Whole HCG closure remains approximately 3%.
