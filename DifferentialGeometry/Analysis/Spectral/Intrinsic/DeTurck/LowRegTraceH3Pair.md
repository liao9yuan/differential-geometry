# LowRegTraceH3Pair status

## Verified producer

`inv_slot_pair_h3` is a public three-dimensional producer for the moving
inverse-metric slot difference.  On one fixed fibre-small metric ball, with
both endpoints bounded in `H²` by `R` and in `H³` by `A`, it gives the tame
modulus

`B R * (D3 + D2 + A * D2)`.

The implementation uses public APIs only:

- `LowBaseInternal.fullSlot_bdd_h2` for the endpoint-low windows;
- `moserWin_fullSlot` for the endpoint-high windows;
- `invSlot_sub_factor` for the resolvent telescope;
- a new generic public `app_h3_tame` for the three-dimensional product step.

Focused verification passed.  The first pass exposed only a local
nonnegativity obligation in the Moser-window comparison; the explicit
`lowJetSq` nonnegativity argument closes it.

## Completed trace adapter

`LowBaseInternal.trace1_pair_h3` is now proved.  It transfers the inverse-slot
bound through one additional finite-dimensional slot, applies the fixed
double-trace coefficient with `app_h3_tame`, and retains both endpoint `H³`
caps and exactly the same `D3 + D2 + A * D2` currency.  The slot-successor
identity is reused from the public curvature-coefficient tower API.

The next consumer is the arbitrary-background `DLb + Insert` cancellation in
the short-time `H²` pair layer.  No further moving-trace estimate is required.

## Project accounting

- `inv_slot_pair_h3`: complete (100%).
- the one-slot moving-trace `H³` pair package: complete (100%).
- the arbitrary-background `DLb + Insert` `H²` arm: about 55%; the remaining
  work is the cancellation/application assembly in its consumer layer.
- the completed fixed-background high/low `A1` pair: not yet proved (0%).
- `ricci_flow_unif_existence`: still unproved (0%); its dedicated
  uniform-existence machinery remains approximately 80% complete.
