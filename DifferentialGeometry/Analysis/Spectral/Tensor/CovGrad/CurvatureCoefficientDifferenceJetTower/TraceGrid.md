# TraceGrid

## 2026-08-03: created by the `CurvatureCoefficientDifferenceJetTower` monolith split

Chunk 5.  The pair-trace difference grid and the metric-factor-telescope trace conversion.

- 1158 lines; 2 public declarations at `Integral.Connection` level, 2 internal ones in the `CurvatureCoefficientDifferenceJetTower` scope.
- Imports: `PairTrace`; everything else arrives transitively.
- Public API contributed by this chunk:
  - `rfns_iteratedCovGrad_riemannCoeff_metricFactorTelescope_traceConversion_le`
  - `rfns_iteratedCovGrad_riemannMixedCoeff_backgroundDifference_diagonalProductGrid_le`

Every declaration is verbatim from the monolith — statement AND proof.  Nothing here is new mathematics.  The only edits are mechanical: the `private ` modifier was dropped and the affected declarations were wrapped in the internal `CurvatureCoefficientDifferenceJetTower` scope so that the public `Connection` namespace is byte-for-byte the old API.

Verification: targeted module build GREEN (single Lean process, `-LeanThreads 1`), zero errors, zero `sorry`.
Chunk map, memory figures and the split recipe: `../CurvatureCoefficientDifferenceJetTower.md`.
