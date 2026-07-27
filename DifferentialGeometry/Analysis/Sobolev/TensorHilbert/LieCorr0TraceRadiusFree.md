# LieCorr0TraceRadiusFree

## Result

`trace_grid_rf p` gives a pointwise low-window bound for every moving trace
`lc0TraceRF g₀ g₁ p σ`.  Its constants depend on the frozen background, rank, derivative
order, and the fixed smallness threshold, but not on a high Sobolev radius.

The proof splits `pureTrace` into:

- the fixed `cometricDoubleTraceField g₀ p`, controlled by compactness;
- one inverse-metric-difference insertion, controlled by the existing diagonal-product
  grid producer.

This one rank-generic theorem supplies all three trace arms required by `lc0AMix`.

## Verification

Focused verification and the targeted module build passed.  The file contains no `sorry`.
