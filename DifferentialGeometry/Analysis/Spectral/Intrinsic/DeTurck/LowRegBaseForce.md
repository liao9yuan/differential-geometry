# LowRegBaseForce

## Role

This module supplies the time-independent affine `H^2` forcing used by the
same-horizon order-two bootstrap.  It is the Ricci-DeTurck remainder at zero
metric deviation, represented in the fixed background spectral scale.

## Current state

- `baseForceH2` packages the genuine zero-deviation remainder in
  `tensorHs g₀ 0 2 2`.
- `baseForceH2_core` exposes its defining canonical smooth spectral embedding.
- The module deliberately imports only the genuine remainder definition and
  the spectral embedding, rather than the full nonlinear-extension stack.
- The two existing zero-perturbation lemmas were moved here from
  `DeTurckRealizedSolutionFamily.lean`; their public names and statements did
  not change.

The first focused check was blocked before elaboration by a missing deep
nonlinear-extension artifact.  The imports were then narrowed so that this
fixed affine term does not depend on that stack.  Focused verification passed
without local warnings.
