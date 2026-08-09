# LowRegBgC1Pair

## Role

This module owns the fixed-background two-state correction for the order-one
DeTurck Lie coefficient.  The Ricci order-one term is background-independent.

## Current state

The public theorem `lieBgCorr_unif` is now proved and focused-check green.  It
bounds the complete three-component fixed-background correction to
`deTurckLieArm1Coeff` on every preselected intrinsic `H2` radius.  Its bound is
chosen before the varying metric and uses uniform metric equivalence plus
background-covariant metric derivatives only through order three.  It has no
metricwise small-radius assumption, no `H3` state cap, and no fourth-jet
constant.  The proof reuses the class-first trace, sharp, fixed-connection,
pullback, mixed-application, and Lie-piece producers; the only new internal
adapter identifies the covariant fixed correction with the already controlled
connection-difference norm.

The public theorem `lowC1Corr_unif` is also proved and focused-check green.
It controls the actual coefficient-layer difference
`lowBaseData.C1(gBase) - lowBaseData.C1(g)` by integrating the complete Lie
background correction along the convex metric path.  Its bound is selected
before `g`, depends on a preselected spectral `H2` radius, and still needs only
the C3 metric class.  The path identity is private because its integral field
is an implementation detail.

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

`lieBgCorr_unif` and `lowC1Corr_unif` are proved (100%).  The downstream
`galA1FixPair3_le` theorem is still unstated/unproved (0%); its dedicated
energy-pairing machinery is only partial.  `ricci_flow_unif_existence` remains
unproved (0%).  The dedicated fixed-background direct-smoothing machinery is
approximately 86% at this coarse scale, while the whole HCG project
remains approximately 3%.
