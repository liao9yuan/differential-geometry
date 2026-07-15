# H2Pointwise

## Purpose

This module gives the sharp three-dimensional bridge from the intrinsic
spectral `H2` norm of a smooth covariant tensor to its pointwise fibre norm.
It is the low-regularity replacement for the older high-order `C2` embedding
used by the all-order Ricci--DeTurck remainder theory.

## Current state

`hs2_fiber_sq` composes the sharp covariant jet-sum embedding with
`hsJet_le`.  Its constant is fixed by the background metric and tensor rank,
before the tensor and point are chosen.  Verification is pending.

## Project accounting

The theorem itself is implemented.  It is one analytic input for the
three-dimensional `H2 x H3 -> H1` principal product estimate; it does not by
itself prove the mixed Ricci--DeTurck remainder estimate or any existence
theorem.
