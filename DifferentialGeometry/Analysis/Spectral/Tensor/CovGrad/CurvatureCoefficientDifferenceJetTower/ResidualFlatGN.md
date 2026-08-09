# ResidualFlatGN

## 2026-08-03: memory refactor of the hog theorem

Holds `jetGNInterp`, the `hGNv` proof block extracted from
`boundedFactorGrid_cappedTopLayer_integral_flat` (`ResidualFlat.lean`).  The
Gagliardo–Nirenberg constant is a parameter `Cgn : ℕ → ℝ` plus the single
identification `hCgn_ch` naming it as the chosen witness, so the `Exists.choose`
bookkeeping happens once in the consumer and is never duplicated here.  No new
mathematics; the statement is the former `have`-block verbatim.

Imports: the monolith's original 22 (same list as `ResidualCells`).  Needs **no**
`backward.isDefEq.respectTransparency false`.

Verification: focused check and targeted build both GREEN.
