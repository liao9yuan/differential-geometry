# Polarization

## Role

This module converts homogeneous diagonal bounds for symmetric continuous
multilinear maps into full operator-norm bounds.

## Verified source API

- `IsSymmetric` packages invariance under every permutation of the argument
  slots.
- `polarization_eq` proves the finite Möbius polarization identity.
- `polarConst` is an explicit nonnegative finite constant.
- `opNorm_le_diag` proves
  `‖A‖ ≤ polarConst n * C` from
  `‖A (x, ..., x)‖ ≤ C * ‖x‖^n`.
- `opNorm_le_diag_unit` derives the same conclusion from a uniform diagonal
  bound on the closed unit ball. Its proof normalizes a nonzero diagonal
  vector and uses multilinearity; it adds no finite-dimensional or geometric
  assumptions.
- `ContinuousLinearMap.opNorm_le_diag2` proves the direct curried-bilinear
  analogue with bound `2 * C`, keeping `Fin 2` curry representation details
  out of geometric consumers.

The proof keeps the combinatorics below the geometry layer: Möbius inversion
eliminates non-surjective self-maps, finite surjective self-maps are counted as
permutations, and slotwise normalization converts the unit-ball estimate into
the operator norm.

## Verification

The source focused check is green with no local diagnostics and no
`sorry`/`admit`/`axiom`. The earlier API is exact-current; the artifact refresh
for the two new diagonal corollaries is deferred until the shared exact-writer
window is returned.

## H6 status

This closes the algebraic diagonal-to-full-derivative bridge needed after the
Jacobi launch-jet estimates. The H6 endpoint theorem remains unstated and 0%;
the next producer is the unit-direction geometric diagonal estimate for the
iterated derivatives of `intrFrameMetric`.
