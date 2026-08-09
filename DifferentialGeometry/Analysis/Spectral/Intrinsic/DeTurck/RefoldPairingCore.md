# RefoldPairingCore

## Purpose

This module is the public exact-algebra layer below the closed-edge energy
argument.  It contains the Ricci half coefficient, one moving-metric Palatini
pair trace, and the exact DeTurck C2 action identity.  It has no Green identity,
L2 estimate, high Sobolev index, or high-jet radius in its API.

The declarations were extracted without changing their statements or proof
bodies from `EdgeRefoldPairing.lean`.  That file now imports this module, so
there is still one canonical API rather than a second copy.  Its pair-trace
input now comes from the small `MovingPairTrace.lean` source rather than the
large Sobolev residual-grid file.

## Verification

Focused verification is blocked before elaboration by missing shared build
artifacts.  The generic output-slot permutation module was extracted and
verified, and two isolated transitive artifacts were restored.  The next
missing artifact is `TensorRSChartFiberOpNorm.olean`; this was the third
consecutive cache miss, so further refresh chasing stopped.  No source-level
`sorry` or `whnf` is present.

The next verification action is a focused check after the shared cache is
restored.  A proof error has not yet been observed.
