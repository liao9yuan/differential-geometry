# LowRegBgAdaptedSolve.lean

## Role

`IsAdaptedLowSolveBg` is the arbitrary-fixed-background sibling of
`IsAdaptedLowSolve`.  It stores one `IsBgSolveAt`, one exact
`IsRung3OrdBg`, the coherent `IsLowGateOrdBg` envelope, the domination of the
stored rung-three tuple, and the absorption budget evaluated at the packet's
actual threshold and state radius.

The public projections expose the background solve, its fixed-point output,
the rung-three certificate, the gate package, and the exact rung-three
absorption inequality consumed by the later mass proofs.

## Honest producer and design seam

`adaptedBg_of_given` is deliberately a given-solve, per-metric producer.  It
extracts the rung-three tuple already stored in a supplied background gate and
packages it with a supplied solve only after the caller proves the gate budget
for that solve packet.

There is no theorem producing adaptation from an arbitrary `IsBgSolveAt`.
`lowregGatePackBg` chooses `A` and `B` after `(g, g_bg)` and does not imply that
an already fixed `K.threshold` and `lowregStateRad` are small enough.  The
diagonal `lowreg_adapt_open` avoids this issue by choosing its threshold and
radius cap before running the solve.  Reversing those choices here would be a
false class-first claim.  The future class-uniform absorptive producer must
provide the budget before the varying metric is introduced.

## Verification

Focused verification passed without local warnings, and the direct module
refresh passed.  The resulting `.olean` is fresh.  The first check only exposed
a missing direct `LowRegBgSolveAt.olean`; refreshing that already verified
dependency resolved the tooling issue.  No proof or interface change was
needed beyond making the state metric and tensor valence explicit on the three
`MaxRegSolutionSpace` binders.

## Accounting

This metricwise adapted-solve brick is complete (100%).  The class-first
absorptive producer, `lowreg_loMassBg`, and headline
`ricci_flow_unif_existence` remain unstated and unproved (0%).  The broader
route-(c) background/adapted infrastructure is approximately 65% complete.
