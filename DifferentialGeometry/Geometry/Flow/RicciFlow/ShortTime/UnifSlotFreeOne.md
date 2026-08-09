# UnifSlotFreeOne

## Class-first producer

`sfOne_grid_unif` fixes one nonnegative order-zero/order-one pointwise grid
before the class metric varies. In dimension three its two entries are the
rank-one Parseval caps `3^4 * C0^2` and `3^5 * C1^2`.

Here `C0` comes from `unifCurvSup_of`, while `C1` comes from
`unifRmOpOne_of`. Their fixed-background inputs are chosen before the class
metric, and the variable metric consumes only uniform equivalence and metric
jets through order three.

This is supporting pointwise producer machinery for the class-first `H1`
passenger-curvature packet. It does not prove the `lc0RiemPass` refold or the
integrated `H1` cap.

## Verification

The proof mirrors the verified `gradSlot_grid_unif`. It passes a warning-free
focused Lean check, has a fresh exact module export, and its axiom audit reports
only `propext`, `Classical.choice`, and `Quot.sound`.

Static interface reconciliation on 2026-08-06 updated the two low-level calls
to the exported names `sfOne_rfns_zero` and `sfOne_rfns_one`. Imports,
producer argument order, valences, and the dimension-three constants were
checked statically before the successful focused verification.

## Project status

`sfOne_grid_unif` is a verified supporting producer. The class-first joint tame producer,
`lowreg_bounds_unif`, `lowreg_dt_unif`, and `ricci_flow_unif_existence` remain
0%. The whole HCG theorem closure remains approximately 3%.
