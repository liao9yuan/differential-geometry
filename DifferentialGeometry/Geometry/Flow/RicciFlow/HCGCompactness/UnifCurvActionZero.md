# UnifCurvActionZero.lean

## Purpose

This module is the thin HCG adapter from the supplied class-uniform tangent
curvature caps to the finite rank-two and rank-three `IsCurvAction0` packages.
It intentionally uses only metric comparability and metric jets through order
three; it does not revive the all-rank/all-order curvature gate.

## Route

- `unifCurvSup_of` supplies the variable-metric `R` cap from the fixed
  background order-zero cap.
- `unifRmOpOne_of` supplies the variable-metric `nabla R` cap from the fixed
  background order-zero and order-one caps.
- `ptCurv_zero_of` turns those two tangent caps into the rank-two first-order
  commutator estimate.
- `unifCurvAction0_of` packages that estimate as `IsCurvAction0 g 2 K`.
- `ptCurv_zero_rank_of` at rank three gives the corresponding finite producer,
  packaged by `unifCurvAction3_of` as `IsCurvAction0 g 3 K`.

The rank-three package is required by the live `H3` comparison, not by the
order-two coefficient itself: `hsJet_le g 2 3` uses its odd-order branch on
`covGrad S`, whose covariant rank is three.  Rank two controls the curvature
commutator of `S`; rank three controls the Bochner step on `covGrad S`.

## Verification

Focused one-thread verification is green and warning-free.  The direct native
supplied-cap dependency, `UnifCurvatureJetOne`, and this adapter all have fresh
compiled artifacts; the exact adapter refresh completed successfully.

## Progress

`unifCurvAction0_of` and `unifCurvAction3_of`: both 100% focused-check verified.
The finite `H3` comparison theorem itself is not yet stated (0%); its dedicated
rank-two/rank-three action packages are now 100%.  This adapter is a small part
of the common realization-radius producer; the actual common six-number
envelope `lowreg_bounds_unif` remains unproved, and the `(N)` theorem remains
unproved (0%).
