# H3GridIntegral

## Purpose

This file is the three-dimensional integration bridge used by the
low-regularity Ricci--DeTurck coefficient estimates.  A four-term squared
metric jet (covariant orders zero through three) controls every intrinsic
antidiagonal product grid of total order at most three in `L1`.

## Current state

- `h3_grid_int` has been written from the existing pointwise `C0` and
  Gagliardo--Nirenberg estimates and the canonical grid-product integral API.
- The statement uses no derivative of the metric perturbation above order
  three.
- The focused source check passes without local warnings or sorries.  The
  repair adds the direct Gagliardo--Nirenberg import, uses its root-qualified
  theorem name, and transfers the top derivative bound through nonnegative
  real powers.

Endpoint theorem progress remains 0%; this is producer machinery only.
