# UnifEdgeSwapPair

## Role

This module proves the complete raw-top crossed pairing estimate after the
two polarized orientations have been added.  It uses the non-Green formal
partner identity, so the test tensor remains at `L2` order.

## Route

- `T, LT` is placed in `L-infinity x L2` for the swapped orientation.
- `LT, D2 T` is placed in `L6 x L3` for the other orientation.
- Exact spectral interpolation converts `H3(T)^2` to `H2(T) H4(T)`.
- The diagonal block uses `T, D2 T, V` in `L-infinity x L2 x L2`, giving
  `R H3(T) H4(T)` directly without interpolation.
- No tensor symmetry, `H5` norm, or fourth varying-metric jet is assumed.

## Verification

Focused verification and the direct export refresh passed for
`edge_swap_h4_unif`, without warnings or `sorry`.

`edge_diag_h4_unif` passed focused verification with the same class-first
hypotheses and no warnings or `sorry`.  Its direct export refresh also passed.

The crossed and diagonal public theorems are each complete (100%), and the
dedicated path-partner bridge is complete (100%).  These percentages describe
only the raw-top pairing bricks, not the remaining Route (c) assembly or the
uniform short-time existence endpoint.
