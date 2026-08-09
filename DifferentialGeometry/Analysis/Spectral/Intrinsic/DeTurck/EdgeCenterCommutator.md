# EdgeCenterCommutator

## Role

This leaf is the exact, non-Green commutator layer for the centered diagonal
zero/top edge block.  It depends on the public diagonal self-refold but never
asserts an arbitrary-passenger refold.

## Current source state

`edge_center_peel` is written with a transparent statement.  It exposes the
principal Hessian head, the complete curvature defect, all three
rough-Laplacian product-rule corners, and the existing off-diagonal `Cross`
term.  Its focused check and direct export refresh are green.

The peel is principal-head-isolating, not `D4`-free: its explicit
`(B - C) · nabla^2(LT)` term carries the only allowed fourth state derivative,
and `Cross` is retained so that the downstream `b02_center_nf` cancellation is
exact.  No derivative is moved onto an energy test tensor.

## Honest progress

- `LowBaseInternal.self_refold`: focused-verified in its canonical action
  module as a diagonal projection; its exact module refresh is green.
- `edge_center_peel`: 100% complete, focused-verified, and directly refreshed.
- `bcD2_pair_h4_unif` / `bcD2_pair_abs_unif`: 100% complete,
  focused-verified, and directly refreshed; these close the class-first
  `(B - C) * nabla^2(LT)` principal face.
- `bg_pair_abs_unif`: 100% complete, focused-verified, and directly refreshed;
  it closes the nonzero `B * G` curvature defect with its fixed-metric part in
  the lower `G_g * H3^2` coefficient.
- sharp paired estimates for `P20`, `P11L/P11R`, and the self-low carrier:
  unstated and unproved, 0%.
- `edge_center_h4_unif` and `lowbase_full3_unif`: unstated and unproved, 0%.
- dedicated Route-C infrastructure: approximately 96%; the remaining
  denominator is the sharp post-peel corner/carrier estimates and
  their diagonal Gårding assembly.  Whole HCG closure remains approximately
  3%.
