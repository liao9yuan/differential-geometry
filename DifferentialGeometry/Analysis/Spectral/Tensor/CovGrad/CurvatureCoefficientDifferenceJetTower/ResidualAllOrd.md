# ResidualAllOrd

## 2026-08-03: created by the `CurvatureCoefficientDifferenceJetTower` monolith split

Chunk 15 (top).  The all-orders base-coefficient bound and the Koszul export subsection.  Closes `TopSeparatedResidualIntegrator`.

- 439 lines; 3 public declarations at `Integral.Connection` level, 0 internal ones in the `CurvatureCoefficientDifferenceJetTower` scope.
- Imports: `ResidualBase`; everything else arrives transitively.
- Public API contributed by this chunk:
  - `ricciArmOrder0BaseCoeff_perOrder_l2_topSeparated_generic_allOrders`
  - `rfns_iteratedCovGrad_raisedKoszul_pointwise_le`
  - `koszul_l2_succ`

Every declaration is verbatim from the monolith — statement AND proof.  Nothing here is new mathematics.  The only edits are mechanical: the `private ` modifier was dropped and the affected declarations were wrapped in the internal `CurvatureCoefficientDifferenceJetTower` scope so that the public `Connection` namespace is byte-for-byte the old API.

Verification: **NOT YET GREEN** — no `.olean` on disk at the time this note was written.  See `../CurvatureCoefficientDifferenceJetTower.md` for the blocker.
Chunk map, memory figures and the split recipe: `../CurvatureCoefficientDifferenceJetTower.md`.
