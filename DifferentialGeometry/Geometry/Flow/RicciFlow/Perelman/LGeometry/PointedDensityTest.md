# PointedDensityTest

## Role

This module is the first weighted compact-test producer after
`redDensity_cpt_lim`.  It stays on one fixed model chart and proves dominated
convergence after multiplication by an arbitrary fixed nonnegative measurable
weight with an almost-everywhere compact bound.

## Route

- Reuse the same compact model-Haar region and eventual measurability shape as
  `PointedDensityCompact`.
- Add the weight to the pointwise product and to the constant integrable
  dominator.
- Discard the finite prefix on which reduced-density measurability and bounds
  are not yet available.

This is genuine weighted convergence, not an assumption wrapper.  A global
`C_c` theorem still requires a finite preferred-chart decomposition and signed
real-integral assembly (positive and negative parts) on the fixed limit space.
Mathlib already supplies `SmoothPartitionOfUnity` and the
`C_c.nnrealPart`/negative-part decomposition.  The missing project-native
bridge is narrower: a weighted analogue of `redDensity_src_lim` that transports
the model-coordinate weight through `mapChartParam`, followed by a finite
preferred-chart sum whose overlaps are controlled by that partition of unity.
The next exact theorem should therefore be the weighted source-chart adapter,
not a total-mass or no-mass-loss wrapper.

## Verification

Warning-free focused verification passed with one Lean thread.  No targeted
refresh or broader build was run during the parallel-work window.  A direct
axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Progress

- `redDensity_wgt_lim`: theorem endpoint 100% and focused GREEN; dedicated
  local weighted machinery 100%.
- Global fixed-space `redDensity_cc_lim`: not stated or proved, 0%; the remaining
  dedicated assembly machinery is approximately 35%.
