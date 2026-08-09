# HsBoundOp

## Role

This module supplies finite-dimensional basis expansions that turn component
control into operator-norm control for continuous multilinear maps.

## Current status

- `opNorm_le_basis_sum` now allows an arbitrary normed real output space.
- Its proof expands each input in a finite orthonormal basis and uses only
  multilinearity, Cauchy-Schwarz, and the triangle inequality.
- The existing scalar Hilbert-Schmidt square bound remains unchanged.
- Source verification is focused-green with no local diagnostics.
- The exact module artifact is green and current.

## H6 accounting

This is reusable tensor-layer infrastructure. It does not prove the H6
normal-coordinate metric-derivative theorem by itself; the direct H6 route now
uses the stronger symmetric polarization bridge in `Polarization.lean`.
