# UnifCurvatureSup.lean

## Purpose

This is the light canonical home of the arbitrary-comparability order-zero
curvature producer. It contains `riemannDiffC`, `riemannDiff_gJet_le`,
`unifCurvatureSup_singleLink_of_diff`, `unifCurvSup_of`, and `unifCurvSup`,
without importing the metric-difference compatibility or curvature-coefficient
jet towers.

## Extraction

The complete declaration block was moved mechanically from
`UnifCurvatureJetBound.lean`. A source comparison confirmed that all 509 moved
lines are byte-for-byte identical to the previous checked declarations, and
that the compatibility file's retained tail is likewise unchanged.

The light import closure is statically free of `TsTransport`; this remains true
through `UnifCurvatureJet1Diff`, `UnifCurvatureJetOne`, and
`UnifCurvActionZero` after the consumer import change.

## Verification

Focused one-thread verification of this source passed without warnings.

The required exported artifact is not yet refreshed. The attempted exact
module refresh unexpectedly replayed nearly the full dependency graph and
started recompiling `ConnectionDifferenceArmRfnsBound`; it was stopped at the
project memory gate. The deleted upstream artifact was restored from the audit
worktree after source-hash and toolchain agreement had been confirmed.

## Progress

The moved order-zero producer remains complete (100%); this change only lowers
its dependency boundary. The order-one producer and final uniform-existence
theorem gain no new mathematical content from this refactor and retain their
previous theorem-level percentages.
