# H2H3Principal

## Purpose

This module isolates the low-regularity principal product estimate used by the
three-dimensional Ricci--DeTurck remainder.  Mixed tensor coefficients remain
in pointwise fibre-norm form, while the evolving covariant tensor is measured
in the intrinsic spectral scale used by the parabolic solver.

## Current state

`appCc_h3_h1` is implemented.  It assumes pointwise bounds for a mixed
coefficient and its first covariant derivative and controls the spectral `H1`
norm of its action on `nabla^2 U` by the spectral `H3` norm of `U`.
Verification is pending.

## Frontier

The next geometric producer must bound the zeroth and first jets of the
DeTurck principal-cometric coefficient, and of its difference, by the
three-dimensional metric `H2` quantities.  This theorem does not itself prove
the mixed remainder estimate or a Ricci--DeTurck existence theorem.
