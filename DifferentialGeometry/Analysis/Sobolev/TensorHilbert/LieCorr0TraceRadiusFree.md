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

## 2026-08-06: class-first rank-two producer

The existing proof core is now factored through `trace_grid_of`, which accepts
an inverse-difference grid and a self-trace jet cap explicitly.  The public
`trace_grid_rf` statement is unchanged and remains the rank-generic,
metric-local compatibility interface.

The new `trace2_grid_unif` chooses its coefficient before either metric varies.
It combines the class-first slot-zero inverse-difference grid
`invDiff_zero_unif` with the dimension-only self-trace estimate
`cometricTrace_rfns`; positive covariant derivatives of the self-trace vanish
by metric compatibility.  This rank-two specialization is the pointwise input
needed for a future class-first `trace2_h2_unif`.

The dimension-only theorem cannot be imported into the lower
`CurvatureCoefficientDifferenceJetTower/TraceGrid.lean`: its current import
closure already contains that module, so doing so would create a circular
dependency.  `LieCorr0TraceRadiusFree.lean` is the lowest non-circular module
that owns the `lc0TraceRF` interface and can see both producers.

Focused verification now passes without warnings.  Both `trace2_grid_unif` and
the refactored compatibility theorem `trace_grid_rf` have axiom audits containing
only `propext`, `Classical.choice`, and `Quot.sound`.  The downstream
`trace2_h2_unif`, `lowreg_bounds_unif`, and `ricci_flow_unif_existence` remain
unstated/unproved (0%).  The whole HCG project estimate remains about 3%.

## 2026-08-06: rank-generic class-first producer

`trace_grid_unif p` is the arbitrary-passenger-rank class-first version.  It
uses the generic dimension-only self-trace bound `cometricTrace_rfns_p`, so its
coefficient is selected before either metric varies.  The existing
`trace2_grid_unif` API is preserved as the rank-two specialization.  No
dimension-three assumption is needed at the pointwise-grid layer.

The generic extension and its rank-two specialization now pass focused
verification and direct export without warnings.  The axiom census for
`trace_grid_unif` contains only `propext`, `Classical.choice`, and
`Quot.sound`.
