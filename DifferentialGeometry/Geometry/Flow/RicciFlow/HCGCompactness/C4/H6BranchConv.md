# H6BranchConv

## Status

The provider-native fixed-center diagonal is complete. It produces the limiting
phase, exact inverse branch, stage flow, inverse convergence, and the paired
branch data needed by the finite live-slot extraction.

Focused and exact verification are GREEN (`4058/4058`). Direct downstream use
in `H6StageMetrics` and `StepCStageComparisonH6` is current.

## Route

Take the smooth limit of the H6 chart metrics on one phase ball. Stage
acceleration bounds come from the existing controlled-chart estimates; smooth
spray convergence passes those bounds to the limiting metric.
