# `UnifVBH1`

## Role

This module is the dimension-three class-first `H1` producer for the genuine
vector--bilinear `lc0VB` correction in the cancellation-preserving order-zero
tail.

## Current status

`vb_h1_unif` is focused-green, exactly exported, and directly axiom-audited.
The audit reports only `propext`, `Classical.choice`, and `Quot.sound`; there is
no `sorryAx`.  Its class metric budget is orders one and two; the perturbation
has an `H2` low radius and one separate order-three top bound.  Both affine
coefficient functions are chosen from `(gBase, Λ, δ₀)` before the class metric
varies.

The final local repairs were proof-shape fixes rather than new mathematics.
The zero-tensor jet uses linearity through `iteratedCovGrad_smul_real`:
`iteratedCovGrad_zero` denotes the zero-th derivative and is not a theorem that
all derivatives of the zero tensor vanish.  The fixed scalar-square identity
uses `mul_pow` before constant normalization, avoiding `ring` in a context with
many `let`-bound coefficient expressions.  A persistent LSP probe was tried
after repeated local diagnostics, but it timed out without actionable proof
state; the ordinary focused check was the authoritative verification.

The order-zero tail, the class-first joint tame producer,
`lowreg_bounds_unif`, and `ricci_flow_unif_existence` remain unproved (0%).
