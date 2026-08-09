# UnifDenseTame

## Role

This module transports the class-first smooth-core tame packet through the two
metric-independent constructions already used by `LowRegDenseSolve`:

- restriction from an outer coefficient radius `Q` to a smaller state radius
  `R`;
- dense extension from `smoothCore` to the complete `lowerState` ball.

The resulting constants depend on `gBase`, `Λ`, and the fixed fibre threshold,
and are selected before the class metric varies.

## Interfaces

`coreN_outer_unif` replays `coreN_outer` using `coreN_tame_unif`.  It preserves
the top, low-difference, and high-size-times-low-difference arms verbatim.

`lowRegN_outer_unif` replays `lowRegN_outer`.  It supplies continuity of both
the dense extension and its smooth core together with the same three-arm
estimate on every lower-state ball.

Both public theorems are dimension-three statements with fixed background
`gBase`, class metric equivalence, and background-covariant metric jets through
order three.  No new analytic or realization hypotheses are introduced.

## Verification

The focused file check and direct module export pass.  The axiom audit for both
public theorems reports only `propext`, `Classical.choice`, and `Quot.sound`.
The only source repair was opening the existing `HCGCompactness` namespace;
the theorem statements and proof route were unchanged.

## Project status

Both dense-extension theorems are 100% verified and counted as closed.
`lowreg_bounds_unif` and `ricci_flow_unif_existence` remain 0%; whole HCG
theorem closure remains approximately 3%.
