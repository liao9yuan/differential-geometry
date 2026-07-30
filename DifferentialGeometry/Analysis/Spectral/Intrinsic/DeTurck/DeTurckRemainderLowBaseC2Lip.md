# DeTurckRemainderLowBaseC2Lip

## Role

This sibling develops the two-endpoint `H2` continuity estimates for the
canonical second-order coefficient in `DeTurckRemainderLowBaseAction`.

## Current state

- `invGeomOp_lip` transfers the completed Neumann-resolvent Lipschitz estimate
  back to the smooth moving-inverse insertion.  It is the common inverse-metric
  factor needed when telescoping the principal, Lie-refold, Palatini-refold,
  and Ricci transferred-top pieces.
- The complete canonical `lowBaseData.C2` difference estimate is not yet
  proved.  Its remaining frontier is to expose or reproduce the three-term
  top-integrand decomposition used by the diagonal `C2` estimate and telescope
  each explicit finite product between two radial metric paths.

## Verification

Focused verification has not yet been run because the upstream Action module
is concurrently being updated.  This file currently imports only the already
verified low-regularity principal core, so it can be checked independently
before the final Action import is added.

## Project accounting

- `ricci_flow_unif_existence`: theorem not stated/proved here, 0%.
- Dedicated uniform low-regularity machinery: approximately 97%.
- Full canonical `C2` Lipschitz producer: approximately 20%; the inverse
  Nemytskii/resolvent factor is connected, while the three geometric top
  families still require two-endpoint telescoping.

## 2026-07-30 completion

The narrow `LowBaseInternal` surface now also exports
`pairTrace_pair_h2` and `pairTrace_bdd_h2`, the already-proved fixed-order
pair and one-state coefficient estimates for `lieCovPair`. They are shared by
the remaining C0 Lie-covariant refold and do not alter the public C2/A2
endpoint.

The geometric two-endpoint telescope is complete.  Public `c2_pair_lip`
controls the full canonical `C2` difference in pointwise fibre norm and its
intrinsic coefficient `H2` jet on one common spectral `H2` ball.  Public
`a2_pair_lip` transfers this to both adjacent-scale operator differences.
Both bounds depend only on the spectral `H2` norm of the state difference;
there is no `H3`/`H4` state assumption and no high-state multiplier.

Focused verification and the targeted exact refresh are GREEN.  This
C2/A2 pair lane is complete (100%).  The exact uniform-existence theorem
remains unstated/unproved (0%); its dedicated low-base machinery is about
98–99%.
