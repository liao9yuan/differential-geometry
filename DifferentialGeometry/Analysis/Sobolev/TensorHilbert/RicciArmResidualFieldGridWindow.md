# RicciArmResidualFieldGridWindow

## Current change

The moving pair-trace definitions were removed from this Sobolev estimate
file and replaced by an import of `MovingPairTrace.lean`.  The compatibility
theorem used by existing estimate consumers remains here.

This keeps the exact pair-trace algebra independent of the large residual
field grid while preserving the existing high-level consumer surface.

## Verification

The new low output-slot permutation dependency is focused-green, but
`MovingPairTrace.lean` and this downstream file have not yet passed
current-source focused verification.  The blocker is a chain of missing
shared `.olean` artifacts, currently
`TensorRSChartFiberOpNorm.olean`; no proof error in this file has been
observed.
