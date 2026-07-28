# PrincipalOpH2

## Result

`principalOpH2` packages the exact Ricci-DeTurck principal-cometric arm as a
completed operator from spectral `H4` symmetric two-tensors to spectral `H2`
symmetric two-tensors.  In dimension three, `principalOpH2_norm` gives an
operator norm bound linear in the spectral `H2` metric deviation on a fixed
small metric ball.  `principalOpH2_core` identifies the completed operator with
the exact smooth geometric arm.

Focused verification passed without local warnings.  No full build was run.

## Frontier

The current parameter is still a smooth realized metric.  Uniform
low-regularity existence needs the assignment from an actual spectral `H2`
metric state to this `H4 -> H2` operator.  The smallest missing theorem is a
Lipschitz operator-difference estimate on a fixed small `H2` ball, proportional
to the spectral `H2` distance between the two metric deviations.  Such an
estimate would give a density extension, continuity, and hence strong
measurability along the existing `H2` trace path.

After this top-order family is available, the lower `H3 -> H2` arm and the
`L2_t H2` forcing arm remain before the affine nonautonomous solver can be
applied.  Thus the uniform-existence endpoint itself remains unproved.
