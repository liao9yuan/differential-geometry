# UnifTopKerPair

## Role

This module consumes the class-first centred top-kernel fibre bound in its
natural order-four principal form.  It controls the explicit `(B - C) *
nabla^2(LT)` face produced by `edge_center_peel` without an `H4` radius or a
metric-dependent smallness threshold.

## Verified declarations

- `bcD2_pair_h4_unif`: one coefficient chosen before the class metric varies
  bounds the fixed-parameter principal face by
  `C * delta / (1 - delta)^2 * ||U||_H4^2`.
- `bcD2_pair_abs_unif`: for every positive `eta`, a fibre radius is chosen
  before the metric so that twice this pairing is at most
  `eta * ||U||_H4^2`.

Both declarations pass a warning-free focused check and the module's direct
targeted refresh.  A direct axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Proof route

`topKer_cap_unif` supplies the pointwise coefficient bound.
`exists_curv_actions` chooses the finite rank-two curvature-action packet
before the metric, and `appD2_pair_h4` converts the pointwise cap directly into
the order-four energy form.  The absorption theorem uses the elementary bound
`delta / (1 - delta)^2 <= 2 delta` for `delta <= 1/4`.

## Progress and frontier

The principal face is complete as a fixed-parameter analytic brick.  The next
substantive post-peel estimates are the nonzero `B * G` curvature-defect lower
term, the sharp `P20/P11L/P11R` corner pair, and the self-low carrier.  The
aggregate `edge_center_h4_unif`, `lowbase_full3_unif`, rest-only Rung-3 theorem,
and final Route-C endpoint remain 0%.  Dedicated Route-C infrastructure is
approximately 96%; the whole HCG project remains approximately 3%.
