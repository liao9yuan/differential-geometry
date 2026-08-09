# IteratedAppCcLeibniz

## Canonical top corner

`appCcPsi_diag` identifies the top argument corner in the iterated `appCcRS`
Leibniz expansion with `slotExtendIter`.  The proof is the direct recursion on
the derivative order and removes a formerly private high-layer dependency from
future mixed-rank rough-Laplacian calculations.

## Verification and scope

The focused check passed with four Lean threads and the 6144 MB cap, without a
local warning.  It is a routine structural API brick; the complete `q/K`
curvature cancellation needed by Route (c) remains unstated and is therefore
still 0% complete.
