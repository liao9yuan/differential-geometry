# PrincipalLowRegPair

## Goal

Construct the adjacent-scale `H3 → H1` realization of the same
inverse-cometric principal correction used by `lowRegPrincipal : H4 → H2`,
then prove one small `H2` metric ball controls both operators and their
Sobolev-inclusion commuting square.

## Current state

- `lowRegPrincipalLo` is the canonical `H3 → H1` completion of the same
  inverse-cometric principal correction as `lowRegPrincipal : H4 → H2`.
- `principalLo_core` identifies it on smooth tensors with
  `deTurckPrincipalCometricArm`.
- `principal_pair_norm` gives one positive spectral `H2` metric radius and
  linear operator-norm bounds for both adjacent-scale operators.
- `principal_comm` proves the high/low Sobolev-inclusion commuting square on
  one positive spectral `H2` metric ball.
- The proof constructs the `H1` perturbation directly from the existing
  fixed-order `H2 × H1 → H1` action estimate, then transfers the inverse by an
  exact intertwining identity. No extra geometric decomposition or higher
  metric regularity is introduced.

Focused verification and the targeted exact module refresh pass with no
`sorry`, `admit`, `axiom`, `whnf`, or trace diagnostics.

## Project accounting

- This adjacent principal-pair module: complete (100%).
- The public uniform-existence theorem `(N) ricci_flow_unif_existence`:
  unstated/unproved (0%).
- Its dedicated low-regularity machinery, including parallel residual work:
  approximately 97%; the remaining theorem-level work is the completed
  coefficient-state maps, time realization, and final evolution assembly.
