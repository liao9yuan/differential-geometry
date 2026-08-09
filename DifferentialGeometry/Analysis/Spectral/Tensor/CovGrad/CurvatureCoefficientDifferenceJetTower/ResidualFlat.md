# ResidualFlat

## 2026-08-03: created by the `CurvatureCoefficientDifferenceJetTower` monolith split

Chunk 11.  Deliberately holds a SINGLE theorem:
`boundedFactorGrid_cappedTopLayer_integral_flat` was the memory hog of the whole
module.  Do not merge this chunk with its neighbours.

- 214 lines; 1 public declaration at `Integral.Connection` level, 0 internal ones.
- Imports: `ResidualCells`, `ResidualFlatSup`, `ResidualFlatGN`,
  `Analysis/Sobolev/BoundedFactorGridIntegral`.
- Public API contributed by this chunk:
  - `boundedFactorGrid_cappedTopLayer_integral_flat`

The public statement is byte-identical to the monolith's (checked by diff, not by
eye).  Chunk map, memory figures and the split recipe:
`../CurvatureCoefficientDifferenceJetTower.md`.

## 2026-08-03 (later): memory refactor — EXECUTED, and what the plan got wrong

**Verification: GREEN.**  Focused check 3.09 GB / 19 s; targeted build 2.86 GB /
17 s.  Previously: five watchdog kills at 7.58 / 8.04 / 8.66 / 8.43 GB with the
declaration never completing.

### The plan's diagnosis was wrong; measurement found the real driver

The fallback plan blamed (a) the section-level
`backward.isDefEq.respectTransparency false`, (b) the whole-grid `rfl` inside
`hgrid_eq`, and (c) the `.choose`-carrying `Cgn`.  All three were addressed —
`hΛsup_low` moved to `ResidualFlatSup.jetSupLow`, `hGNv` to
`ResidualFlatGN.jetGNInterp` (constants passed as parameters, no re-`choose`),
the whole grid/integrability layer to the tensor-free
`Combinatorics.bdFactorCell_int / bdFactorGrid_cont / bdFactorGrid_int /
bdFactorGrid_int_eq`, and the `respectTransparency` escape dropped entirely —
and the peak moved only **8.43 → 8.25 GB**.  Still killed.

A `sorry`-truncation bisection of the remaining body (six 20-second runs, table
in the chunk-map note) put every prefix at 3.08–3.09 GB up to and including the
`cappedTopLayerCell_integral_le` application and calc steps 1–3, and then
**7.95 GB (killed)** on adding the last calc step, `by ring`.

`ring` was proving `A * (B * C) = A * B * C`.  Replacing it with
`(mul_assoc _ _ _).symm` removed ~5 GB.  Cause: `ring` identifies atoms up to
reducible defeq, and `set`-introduced locals are let-bound, so `gcount i` and
`MB i ^ (9 * (i + 2))` zeta-unfold through `MB → vol, Lam, Cgn` into a `dite`
around `Exists.choose` of the Gagliardo–Nirenberg existential, with a symbolic
exponent blocking any collapse.

### What was kept

The three extractions stay: they are verified, they sit at their canonical
layers (the grid lemmas are genuinely generic and reusable, with no tensor
types), and they hold the residual peak at the ~2.8 GB import floor.  But the
honest accounting is that **the `ring` replacement is what made this file
buildable**, not the extraction.

### Route notes worth keeping

- `refine le_trans (le_of_eq (bdFactorGrid_int_eq b hcont …)) ?_` replaces the
  old `rw [hgrid_eq]`.  Unification against a `set`-bound `b` is fine here
  (zeta + beta); `rw`'s syntactic `kabstract` matching is what needed the
  transparency escape.
- `jetSupLow` takes `hLam : Lam = Cemb * √(a+2) * R` as a hypothesis rather than
  the expression, so the consumer's `set Lam … with hLam` feeds it directly.
- No new `maxHeartbeats`: the file-level 3200000 / 1600000 are carried verbatim
  into each piece.
