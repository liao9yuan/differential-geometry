# StepCProducersH6.lean

## 2026-07-29 H6 support and transition producer

`H6NormalData.exists_supp_data` constructs one finite refinement carrying
`HasSuppConvDataOn` for `d.chart`. Its proof uses the concrete H6 patch/core
balls, direct chart readout, live/dead/disjoint atom convergence, and one finite
diagonal for both transition directions. The transition inverse laws come from
actual H6 overlap data; no total-function inverse assumption or legacy
`205 * exp(...)` nesting bound is used.

The statement keeps per-member connectedness explicit. The distance-atom
normalization route no longer requires `Item3GpScaleTail`; the real H6 chart
and overlap estimates supply the geometric inputs at their actual consumers.
This does not prove or silently replace the independent legacy theorem
`NormalRadiusProfile.le_exp_radius`.

Focused verification and the exact module refresh are GREEN (`4144/4144`).
Direct axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`,
with no `sorryAx`. The H6 support/transition producer is 100%; Gate 5 provider
substitution is complete together with `StepCStageComparisonH6`. The
unconditional MSM135 endpoint remains unstated (0%), and whole-HCG supporting
machinery is about 70%.

The package is now consumed by `H6NormalData.exists_stage_data` together with
the provider-native metric and branch diagonals. Do not reopen the H6 radius,
transition, atom-support, or target-decode routes. The next phase is the
provider-native input/Step-B1 assembly.
