# ResidualWindow

## 2026-08-03: created by the `CurvatureCoefficientDifferenceJetTower` monolith split

Chunk 12.  The two all-orders ball-uniform grid-window integrators (flat and tame-window).

- 225 lines; 2 public declarations at `Integral.Connection` level, 0 internal ones in the `CurvatureCoefficientDifferenceJetTower` scope.
- Imports: `ResidualFlat`, `Residual`; everything else arrives transitively.
- Public API contributed by this chunk:
  - `boundedFactorGridWindow_integral_ballUniform_flat_allOrders`
  - `boundedFactorGridWindow_integral_ballUniform_tameWindow_allOrders`

Every declaration is verbatim from the monolith — statement AND proof.  Nothing here is new mathematics.  The only edits are mechanical: the `private ` modifier was dropped and the affected declarations were wrapped in the internal `CurvatureCoefficientDifferenceJetTower` scope so that the public `Connection` namespace is byte-for-byte the old API.

Verification: **NOT YET GREEN** — no `.olean` on disk at the time this note was written.  See `../CurvatureCoefficientDifferenceJetTower.md` for the blocker.
Chunk map, memory figures and the split recipe: `../CurvatureCoefficientDifferenceJetTower.md`.
