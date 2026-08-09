# Lc0InsertDiffWindow

## Result

`lc0InsDiffAtgw` proves the radius-free pointwise background-difference bound
for `lc0Insert`, with the sharp state window `i + 2`.  Its constant is chosen
before the moving metric and perturbation.

The proof uses the exact public identity `lc0InsDiff_eq`, the
moving-cometric/fixed-passenger formula `wOmegaDiff_eq`, the existing
connection-difference window, two `atgwFold` steps, and the slot-insertion norm
comparison.  The new leaf does not import `LieCorr0LowJet`; the actual-subject
identity belongs to the already compiled coefficient L2 layer.

## Verification

The promoted `lc0InsDiff_eq` producer and the new ordinary window leaf both
passed focused verification.  The producer's targeted dependency refresh also
passed.  The new leaf contains no `sorry`, axiom, or local heartbeat override.

## Remaining frontier

The marked companion was deliberately deferred.  The ordinary theorem is the
leaf needed by the capped background self-low jet; a marked version remains a
separate input for the quadratic background self-low jet.

Progress accounting at this checkpoint:

- `lc0InsDiffAtgw`: 100%.
- ordinary/marked insertion-window pair: about 50% (ordinary complete, marked
  not started).
- fixed-background mass-chain port: about 10%.
- route-(c) background endpoint machinery: about 42%.
- headline `ricci_flow_unif_existence`: 0% until the theorem itself is proved;
  its dedicated uniform-existence infrastructure remains about 80%.
- whole HCG compactness project: about 3%.
