# H2Pointwise

## Purpose

This module gives the sharp three-dimensional bridge from the intrinsic
spectral `H2` norm of a smooth covariant tensor to its pointwise fibre norm.
It is the low-regularity replacement for the older high-order `C2` embedding
used by the all-order Ricci--DeTurck remainder theory.

## Current state

`hs2_fiber_sq` composes the sharp covariant jet-sum embedding with
`hsJet_le`.  Its constant is fixed by the background metric and tensor rank,
before the tensor and point are chosen.  `hs2_low2` records the corresponding
square-sum bound for the order-zero-through-two `L2` jets.  `hs3_grad_low2`
applies the same mechanism to the first covariant derivative: spectral `H3`
controls its pointwise norm and its first three `L2` jets.

Focused verification passes, and the module build exporting these declarations
passes.

## Project accounting

These theorems are implemented and verified.  They are analytic inputs for the
three-dimensional `H2 x H3 -> H1` principal product estimate; it does not by
itself prove the mixed Ricci--DeTurck remainder estimate or any existence
theorem.
