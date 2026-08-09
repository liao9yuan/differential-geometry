# TsRungs

## 2026-08-03: created by the `CurvatureCoefficientDifferenceJetTower` monolith split

Chunk 8.  Top-separated rungs for slot insert, the G1 lowering split, and the curvature / Riemann arm-0 coefficients.

- 2306 lines; 4 public declarations at `Integral.Connection` level, 10 internal ones in the `CurvatureCoefficientDifferenceJetTower` scope.
- Imports: `TsTransport`; everything else arrives transitively.
- Public API contributed by this chunk:
  - `rfns_iteratedCovGrad_slotInsertEndoCc_zero_ricEndoBackgroundDifferenceField_topSeparated_le`
  - `rfns_iteratedCovGrad_riemannG1LoweringDifference_topSeparated_le`
  - `rfns_iteratedCovGrad_ricciArmOrder0CurvCoeff_backgroundDifference_topSeparated_le`
  - `rfns_iteratedCovGrad_ricciArmOrder0RiemannCoeff_backgroundDifference_topSeparated_le`

Every declaration is verbatim from the monolith — statement AND proof.  Nothing here is new mathematics.  The only edits are mechanical: the `private ` modifier was dropped and the affected declarations were wrapped in the internal `CurvatureCoefficientDifferenceJetTower` scope so that the public `Connection` namespace is byte-for-byte the old API.

Verification: targeted module build GREEN (single Lean process, `-LeanThreads 1`), zero errors, zero `sorry`.
Chunk map, memory figures and the split recipe: `../CurvatureCoefficientDifferenceJetTower.md`.
