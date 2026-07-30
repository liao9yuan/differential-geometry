# DeTurckRemainderLowBasePair

## Role

This module completes the single smooth-core first-order action
`LowBaseActionData.a1` on both adjacent spectral Sobolev scales:

- `a1Hi : H3 →L H2`;
- `a1Lo : H2 →L H1`.

The two completions come from the same dense smooth core.  `a1_pair` supplies
their norm bounds, core identities, and commuting square.  The module does not
introduce a second geometric decomposition.

## Difference interface

`a1_diff` is the coefficient-to-operator transfer needed by the pairwise and
time-dependent lanes.  A common two-jet bound on
`A.C0 - B.C0` and `A.C1 - B.C1` controls both
`A.a1Hi - B.a1Hi` and `A.a1Lo - B.a1Lo`.

`a1Lo_diff` is the sharper transfer needed by the fixed-point lane.  It
requires only a one-jet bound on `A.C0 - B.C0`, while retaining the two-jet
bound on `A.C1 - B.C1`, and controls
`A.a1Lo - B.a1Lo : H2 →L H1`.  This is the natural mixed product allocation
`H1(C0) × H2(passenger) → H1` together with
`H2(C1) × H1(∇ passenger) → H1`.  It avoids imposing the stronger C0-H2
pair estimate on the low-scale fixed-point consumer.

The proof applies the existing fixed-order product estimates to the coefficient
difference bundle and identifies the completed difference on the dense smooth
core.  It adds no high-Sobolev ball or state-smallness hypothesis.

## Remainder endpoint

`remainder_low_pair` packages the zero-based smooth remainder split with the
compatible high and low completions of its canonical first-order action.  The
full `LowBaseActionData.a2` remains the sole second-order action; it must not be
added to the principal action a second time.

## Verification

Focused verification is GREEN, including `a1Lo_diff`.  The earlier targeted
exact refresh through `a1_diff` remains current; the new public export has not
yet been exact-refreshed because no downstream module has consumed it.

## Project position

`ricci_flow_unif_existence` remains unstated and unproved (0%).  Its dedicated
low-regularity machinery is about 98--99% complete.  This module closes both
the generic adjacent-scale transfer and the sharper low-scale transfer.  The
remaining geometric frontier is the H1 pair estimate for the complete C0
coefficient; C1 already has its H2 critical pair estimate.  Their
time-dependent realization follows after that C0 endpoint.

## 2026-07-29 spectral conversion exports

`jet3_le_hs` and `jet2_le_hs` are now public conversion lemmas from the
spectral `H3`/`H2` norms to the fixed smooth jet sums used by the pair
producers. Focused verification and the targeted exact refresh are GREEN.

## 2026-07-26 session note

`a1Lo_diff` (the smooth-core A1 H2->H1 action difference) is focused GREEN.
Exact targeted refresh NOT yet run — defer until a downstream module actually
reads it.
