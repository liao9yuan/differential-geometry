# PrincipalNeumannH2

## Purpose

This module performs the Banach-algebra Neumann inversion of the completed
rank-four `H2` principal perturbation.

## Current status

The Banach-algebra producer is complete and focused verification passed.
`invPerturbH2` is the inverse-minus-identity correction to `1 + perturbH2`;
`invPerturbH2_mul` records its cancellation identity, and
`invPerturbH2_norm` supplies a positive `H2` metric radius on which both the
linear perturbation and its inverse correction are uniformly controlled by the
metric `H2` norm.  `invPerturbH2_lip` proves the corresponding uniform
Lipschitz estimate between two metric deviations in the same ball by the
resolvent identity.  Focused verification passed.

The geometric smooth-core identification is now supplied by
`PrincipalLowRegCore.invPerturbH2_core`.  It identifies the inverse correction
with insertion of `gInvDiffRaisedEndoField g0 g1` in the leading covariant
slot, under the exact smooth metric tie.

`ricci_flow_unif_existence` remains an unproved endpoint (0%).  This is
dedicated A2 coefficient machinery, not the short-time-existence theorem.
