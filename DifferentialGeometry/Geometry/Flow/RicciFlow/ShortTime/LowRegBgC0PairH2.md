# LowRegBgC0PairH2

## Role

This sibling keeps the arbitrary-background order-zero `H2` pair work out of
the already oversized `LowRegBgC0Pair.lean`.  The route is three-dimensional
and targets the critical `H3 → H2` two-state currency used by the one-sided
smooth bootstrap.

## 2026-08-07 mixed arm

The public `amixBg_pair_h2` is complete.  It refolds the exact background
subtraction before estimating, uses the public linear `pbLow_h2_mul` producer
for the background connection factor, and uses exact Koszul cancellation for
the self-background factor.  Its output has the same
`B0 * D3 + B1 * N + B1 * A * N` currency as `c1_bg_pair_h2`, where `N` is the
spectral `H2` distance of the two states.

Focused verification passed after removing the unnecessary dependency on the
older `LowRegBgC0Pair` H1 module.  This theorem closes only the `AMix` arm.  The
arbitrary-background `DLa` and `DLb + Insert` arms, their full `lie0` assembly,
and the time-integrated background correction remain separate frontiers.

## Accounting

- `amixBg_pair_h2`: theorem 100% complete.
- arbitrary-background order-zero pointwise `H2` pair: one of three arms
  complete; endpoint itself remains unstated (0%).
- full arbitrary-background high `A1` producer: endpoint unstated (0%);
  dedicated underlying machinery is roughly 65%.
- `ricci_flow_unif_existence`: still 0%; conditional consumers remain separate
  from this producer work.
