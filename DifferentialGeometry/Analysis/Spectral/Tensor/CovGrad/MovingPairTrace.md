# MovingPairTrace

## Mathematical conclusion

This source isolates the exact moving-cometric pair trace below the Sobolev
estimate layer.  It exposes `mvDoubleTraceField`, `mvPairTraceOp`, and the
pair-trace evaluation theorem `mvPairTrace_apply`.

The construction now uses the canonical metric-tag equivalence
`SmoothCcTensor.retagEquiv`, two explicit passenger-slot extensions, and the
generic output-slot permutation API.  It therefore no longer imports
`RicciArmResidualFieldGridWindow.lean`, and it does not carry a nonsmall
Sobolev coefficient assumption.

## Verification

The new output-slot permutation dependency is focused-green.  This file has
not yet reached current-source elaboration after the refactor because the
shared cache has a chain of missing transitive artifacts.  Two isolated
artifacts were restored, but the next focused check stopped at missing
`TensorRSChartFiberOpNorm.olean`; further cache chasing was deliberately
stopped.

No source-level `sorry` or `whnf` is present.  `mvPairTrace_apply` must still
be counted as unverified, not as a completed theorem.
