# IteratedFDerivProdMatch

## Role

This module proves matching of all joint iterated derivatives at the seam of a
parameterized half-line extension from equality of the complete one-sided time
jet.

## Status

The duplicate fixed-direction commutation proof has been removed. The module
now imports the canonical theorem from `DirectionalJet`.

After refreshing `DirectionalJet`, the focused check exposed one regularity
coercion at the transverse derivative step. The target is an inequality in
`WithTop ℕ∞`, where the right-hand `∞` is the embedded top of `ℕ∞`, not the
outer `WithTop` top. The proof now uses
`WithTop.coe_le_coe.mpr le_top`.

The source is focused-green with no local diagnostics.

## Next target

No H6 consumer imports this ancillary bridge, so no exact refresh is required
for the current H6 chain. Refresh it only when a downstream consumer needs the
export.
