# LowRegBgC1Pair

## Role

This module owns the fixed-background two-state correction for the order-one
DeTurck Lie coefficient.  The Ricci order-one term is background-independent.

## Current state

The exact lowered-connection and `PsiB` background factorizations are checked.
The public theorem `psiBg_pair_h2` is focused-check green: on a sufficiently
small spectral `H2` ball it gives both a static `H2` bound and an `H2` pair
bound for the fixed-background `PsiB` correction.  The pair modulus is linear
in the spectral `H2` state difference and introduces no `H3` or `H4` state
input.

The public theorem `lie1_bg_pair_h2` is also focused-check green.  It combines
the three surviving background Lie summands (the fixed connection payload and
the two `PsiB` slot variants) with the existing same-background
`lie1_pair_h2`.  The arbitrary fixed background only enlarges the `H2`
difference coefficient; the critical `H3/H2` two-arm shape is unchanged.  The
Ricci order-one term is background-independent, so this banks the complete
arbitrary-background order-one coefficient pair.

The local duplicate proof of `pbLow_h2_mul` was removed after the producer was
exported canonically from `LowRegCoeffJets`.  A direct dependency refresh had
correctly exposed the duplicate declaration that stale imports had hidden;
the consumer now reuses the exported theorem and focused verification passes.

The remaining arbitrary-background first-order wall is now the order-zero
Palatini pair, beginning with `dlaBg_pair_h1`.  Its proof must preserve the
`DLb + insert` cancellation before estimating; a separate bound of those two
arms would reintroduce the forbidden high derivative.

`ricci_flow_unif_existence` itself remains unproved (0%).  Its dedicated
low-base machinery is approximately 77%; this module closes the
arbitrary-background `C1` pair lane rather than the existence theorem itself.
