# UnifRiemH1

## Role

This module supplies the dimension-three class-first affine `H1` estimate for
the fixed-curvature order-zero correction `lc0Riem`.  It is the last of the
class-first cancellation leaves following `lc0VB` and `lc0AMix`.

## Mathematical route

The two-arm factorization `lc0Riem_eq_app` separates the coefficient into the
moving double-trace arm `lc0RiemLive` and the fixed curvature passenger
`lc0RiemPass`.

- `trace2_h2_unif` gives the live arm a class-first `H2` bound from the
  perturbation's low `H2` radius.
- `lc0RiemPass_refold` identifies the passenger, up to a sign and source/output
  permutations, with one `slotExtend` of `slotFreeOpCc g 1`.
- `sfOne_grid_unif`, slot-extension control, and permutation invariance give
  pointwise zeroth- and first-jet passenger bounds.
- `volumeReal_cross` integrates those bounds uniformly over the metric class.
- `appRS_h2_unif` combines the live `H2` packet and passenger `H1` packet.

The separated order-three perturbation coefficient is exactly zero.  The class
metric budget is uniform equivalence plus background-covariant metric jets
through order three.

## Verification

The theorem passes a warning-free focused Lean check and has a fresh exact
module export.  Both it and `lc0RiemPass_refold` audit to only `propext`,
`Classical.choice`, and `Quot.sound`.

## Project status

`riem_h1_unif` is proved and verified (100%).  The
class-first joint tame producer, `lowreg_bounds_unif`, and
`ricci_flow_unif_existence` remain unstated/unproved at 0%; whole HCG theorem
closure remains approximately 3%.
