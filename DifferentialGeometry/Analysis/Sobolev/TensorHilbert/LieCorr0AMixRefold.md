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

## Fixed-background difference

The module now also exposes the exact algebra seam needed by the sharp
arbitrary-background estimate:

- `lc0BgKappaRF` is the difference between the lowered connection factors for
  `gB` and `g0`;
- `lc0AMixBgHalfRF` is the unsymmetrized five-factor product with that
  difference in the first connection slot and the self-background factor in
  the second;
- `amix_half_bg_rf` proves the corresponding half-product subtraction identity;
- `amix_bg_refold_rf` refolds
  `lc0AMix g0 gm gB - lc0AMix g0 gm g0` into the two symmetrized
  fixed-background-difference products.

This is exact algebra only; it introduces no analytic estimate. The proof
reuses the public `slotIterSub` theorem from `SlotPermJet` rather than retaining
a duplicate local induction. The dependency direction is acyclic.

## Route Decision

The attempted import of `LieCorr0LowJet.lean` was rejected: that module is RED with about
40 pre-existing syntax and proof errors.  This small leaf extracts only the exact AMix
refold needed by the radius-free consumer and imports no unfinished facade.

## Verification

Focused verification and the targeted module build passed.  The file contains no `sorry`.
The fixed-background additions also pass focused verification with the requested
four-thread, 6144 MB configuration.

## Project position

This exact AMix algebra seam is complete (100%). The later sharp AMix `atgw`
estimate and the combined arbitrary-background Lie residual remain separate
producers and are not proved here. The headline `ricci_flow_unif_existence`
theorem therefore remains unproved (0%); this file contributes only a small
algebraic brick to its dedicated fixed-background bootstrap machinery.
