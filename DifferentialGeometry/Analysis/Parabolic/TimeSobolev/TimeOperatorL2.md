# TimeOperatorL2

## Result

`timeOpL2` applies a `MemLp A 2` family of continuous linear maps to an
essentially bounded measurable path.  The output is in the project
`timeL2` space, and `timeOpL2_norm_le` gives

`||A(.) u(.)||_L2 <= essSup ||u|| * ||A||_L2`.

`timeOpL2_sub` records that the resulting `L2` element commutes with
subtraction even when the three representatives use different bound proofs.
`timeOpL2_congr` records invariance under almost-everywhere equality of the
input path.

This is the correct time layer for the low-regularity Ricci-DeTurck
first-order coefficient: its `H3 -> H2` operator norm is only square
integrable along the known order-one solution.

Focused verification passed without local warnings.

The remaining frontier is not this multiplication estimate.  It is the
construction of the actual Ricci-DeTurck first-order operator family from a
low-regularity metric path, together with its measurable `L2_t` norm bound.
