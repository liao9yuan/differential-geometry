# RedDensityComplete

## Role

This module supplies target-point measurability of reduced density on a
complete, bounded-curvature smooth Ricci flow without assuming the manifold is
compact.

## Native route

- Connectedness supplies a global smooth endpoint competitor through the
  native finite Riemannian-distance path theorem.
- `exists_lMinVec_rm` turns that competitor into a complete-flow minimizing
  L-vector.
- `exists_lCost_support` gives a smooth local upper support for L-cost at the
  reached endpoint.
- The local upper support proves global target-point upper semicontinuity of
  L-cost.  The antitone reduced-density exponential then gives lower
  semicontinuity and Borel measurability.

This avoids duplicating the endpoint-splice argument and does not route through
the compact-only `lRegCostC1_le` accessor.

## Verification

Warning-free focused verification passed with the shared four-thread setting.
The direct endpoint audit reports only `propext`, `Classical.choice`, and
`Quot.sound`.
No named refresh was run because parallel tasks remain active and no downstream
module yet imports this new export.  The module contains no `sorry` or `admit`.

## Progress

- `redDensity_meas_rm`: theorem source and verified theorem 100%.
- Dedicated complete-flow measurability machinery: 100% for this endpoint.
- Geometric no-mass-loss and the P3 asymptotic-shrinker endpoint remain 0%.
- Whole P0--P9 infrastructure remains approximately 15--25%.
