# LieCorr0AMixRefold

## Result

`amix_refold_rf` proves that the canonical `lc0AMix` coefficient field is exactly the
symmetrized five-factor operator product:

- three moving traces of ranks `(4,2)`, `(5,3)`, and `(6,4)`;
- one slot-extended `metricConnDiffLoweredCc` arm at `g₀`;
- one slot-extended `metricConnDiffLoweredCc` arm at `gB`.

The public `lc0TraceRF` uses `pureTrace`, whose fibre theorem already realizes
`lieCorr0TraceStep`.  The two slot-extension readouts are proved structurally at ranks
`(2,3)` and `(3,3)`.

## Route Decision

The attempted import of `LieCorr0LowJet.lean` was rejected: that module is RED with about
40 pre-existing syntax and proof errors.  This small leaf extracts only the exact AMix
refold needed by the radius-free consumer and imports no unfinished facade.

## Verification

Focused verification and the targeted module build passed.  The file contains no `sorry`.

