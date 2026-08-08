# RicciTopFibreBound

## Role

This module supplies metric-class-independent pointwise fibre bounds for the
transparent Ricci top coefficient.  It replaces the older metricwise
existential bound with a constant chosen before the metric varies.

## Verified declarations

- `dagTop_cap_unif`: the derivative-top Koszul operator has a dimension-only
  fibre bound throughout the one-third fibre ball.
- `ricciTop_cap_unif`: the diagonal realized Ricci top coefficient is bounded
  by `K * delta / (1 - delta)`, with `K` selected before every metric.
- `topKer_cap_unif`: the exact centered principal-face coefficient
  `lieRefold2 - 2s * ricciTop` is bounded by
  `K * delta / (1 - delta)^2`.

All three declarations pass a warning-free focused check and the module's exact
targeted refresh.  A direct axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Proof route

The `dagTop` estimate uses the inverse-metric fibre bound, slot insertion,
Koszul's three permutations, and fibre isometry under reindexing.  The Ricci
top estimate composes it with the public diagonal `daTrans_cap`.  The centered
top-kernel bound then combines the public `lieRefold2_cap` with the Ricci bound;
no Sobolev radius, higher state jet, or metricwise constant enters.

## Progress and frontier

These coefficient producers are complete.  Their fixed-parameter order-four
pairing and absorption consumers are verified in `UnifTopKerPair`.  The
remaining post-peel terms are the `B * G` curvature defect, the
`P20/P11L/P11R` corners, and the self-low carrier.  `edge_center_h4_unif`,
`lowbase_full3_unif`, the rest-only Rung-3 theorem, and the final Route-C
endpoint remain unstated and unproved (0%).
