# ResidualBase

## 2026-08-03: created by the `CurvatureCoefficientDifferenceJetTower` monolith split

Chunk 14.  The δ₀ fibre-small bridge and the radius-free top-separated base-coefficient bound.

- 409 lines; 2 public declarations at `Integral.Connection` level, 0 internal ones in the `CurvatureCoefficientDifferenceJetTower` scope.
- Imports: `TsRungs`, `ResidualFree`; everything else arrives transitively.
- Public API contributed by this chunk:
  - `rfns_symmS_zero_le_fibreSmall`
  - `ricciArmOrder0BaseCoeff_perOrder_l2_topSeparated_generic`

Every declaration is verbatim from the monolith — statement AND proof.  Nothing here is new mathematics.  The only edits are mechanical: the `private ` modifier was dropped and the affected declarations were wrapped in the internal `CurvatureCoefficientDifferenceJetTower` scope so that the public `Connection` namespace is byte-for-byte the old API.

Verification: **NOT YET GREEN** — no `.olean` on disk at the time this note was written.  See `../CurvatureCoefficientDifferenceJetTower.md` for the blocker.
Chunk map, memory figures and the split recipe: `../CurvatureCoefficientDifferenceJetTower.md`.
