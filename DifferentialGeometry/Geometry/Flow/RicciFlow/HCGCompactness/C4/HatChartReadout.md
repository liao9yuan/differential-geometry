# HatChartReadout

## 2026-07-27 controlled chart-family interface

`HasChartCmSol` is the provider-independent finite center readout. It retains
the chosen `NormalBallChart`, the selected diagonal branch, target membership,
the exact inverse-velocity equation, and the strict local implicit solution.
Both the legacy framed provider and the intrinsic H6 provider use this one
predicate.

`NormalChartFamily` packages one coherent controlled chart at every sequence
stage and center. `legacyChartFamily` is the migration instance; the H6 route
will pass `H6NormalData.chart` to the same downstream declarations. No
existential chart selector or parallel H6 capstone hierarchy is introduced.

Focused verification is currently blocked before local elaboration because the
required `NormalBranchHessian.olean` is absent after an unrelated concurrent
artifact write collision. The source change itself has no independent
mathematical frontier. The next verification step is to refresh
`NormalBranchHessian` after the active Spectral build exits, then focused-check
and refresh this module.

