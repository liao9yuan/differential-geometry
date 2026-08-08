# UnifEdgeDefectPair

## Role

This module controls the nonzero curvature-defect face `B * G_T` exposed by
`edge_center_peel`.  The order-four energy coefficient is absorbed with an
arbitrary positive parameter, while curvature constants that may read the
fixed smooth metric are chosen only after that metric is fixed.

## Verified declaration

- `bg_pair_abs_unif`: for every positive `eta` and every metric in the fixed
  class, there is a nonnegative metricwise constant `Gc` such that
  `2 * |<L^2 T, B * G_T>|` is bounded by
  `eta * ||T||_H4^2 + Gc * ||T||_H3^2`.

The declaration passes a warning-free focused check and its direct targeted
module refresh.  A direct axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Proof route

`topKer_cap_unif` controls the centred part of `B`, while the fixed-metric
`phiMet_cap` controls the remaining principal-metric deviation.  The exact
rough-Laplacian/Hessian commutator identifies `G_T`; its existing L2 estimate,
the rank-two finite curvature-action packet, and `covsum_hs_two` bound it by the
H2 norm of `T`.  L2 Cauchy--Schwarz and weighted Young then give the stated
lower-order form.  No derivative is placed on the energy test tensor, and no
H5 state norm is used.

The underlying all-order commutator producer and the final
`bg_pair_abs_unif` declaration were both directly audited without
`sorryAx`.

## Progress and frontier

This curvature-defect face is complete as a fixed-parameter analytic brick.
The remaining substantive post-peel estimates are the sharp
`P20/P11L/P11R` corner pair and the self-low carrier.  The aggregate
`edge_center_h4_unif`, `lowbase_full3_unif`, rest-only Rung-3 theorem, and final
Route-C endpoint remain 0%.  Dedicated Route-C infrastructure is approximately
96%; the whole HCG project remains approximately 3%.
