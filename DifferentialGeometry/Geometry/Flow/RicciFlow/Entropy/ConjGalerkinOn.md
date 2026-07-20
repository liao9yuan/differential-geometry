# Exact-interval Galerkin reconstruction

## 2026-07-19 source assembly

This module removes the independent lifespan choices from the classical
Galerkin reconstruction.  Starting from a caller-supplied regular reflected
interval and the genuine finite-core Laplacian identity, it constructs the
velocity lifts, coefficient derivatives, time jets, joint interior smoothness,
and pointwise conjugate-heat equation on that same interval.

`gallim_on` packages the result as `IsHeatPotOn` on the exact closed interval.
`gallim_pos_on` then applies the existing scalar maximum principle using the
compact-slab bound for `conjCoeff`; it does not shorten the interval.  The
proofs keep dependent tensor identities inside a fixed terminal spectral space
and reduce the moving equation to scalar evaluations before rewriting.

The source contains no local `sorry`.  Focused verification is pending the
active upstream spectral object refresh, so these declarations remain
theorem-level **0%** with approximately **95%** dedicated source until the file
check passes.  Exact W comparison, finite Good-set propagation,
`NoLocalCollapsing`, and `ham3_noncollapse` remain separate theorem-level
frontiers at **0%**.
