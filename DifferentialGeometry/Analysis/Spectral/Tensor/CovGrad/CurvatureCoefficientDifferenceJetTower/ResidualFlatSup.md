# ResidualFlatSup

## 2026-08-03: memory refactor of the hog theorem

Holds two proof blocks extracted from
`boundedFactorGrid_cappedTopLayer_integral_flat` (`ResidualFlat.lean`):
`rfnsIterCont` (continuity of `x ↦ rfns(∇ˡP)(x)`) and `jetSupLow` (the `m ≤ 2`
pointwise fibre bound from a jet ball, with the supercritical constant `Cemb`
and its fixed-window spec taken as parameters, so this file never touches the
supercritical lemma).  No new mathematics; both statements are the former
`have`-blocks verbatim.

Imports: the monolith's original 22 (same list as `ResidualCells`), so the
preamble is the standard chunk preamble.  Needs **no**
`backward.isDefEq.respectTransparency false`.

Verification: focused check and targeted build both GREEN.
