# TsTransport

## 2026-08-03: created by the `CurvatureCoefficientDifferenceJetTower` monolith split

Chunk 7.  The `ts*` top-separated transport mirrors (cast/domDomCongr/metric-lowering/head-transport) and the lowered-difference rung built on them.

- 1658 lines; 1 public declarations at `Integral.Connection` level, 42 internal ones in the `CurvatureCoefficientDifferenceJetTower` scope.
- Imports: `Envelope`; everything else arrives transitively.
- Public API contributed by this chunk:
  - `rfns_iteratedCovGrad_riemannLoweredBackgroundDifference_topSeparated_le`

Every declaration is verbatim from the monolith — statement AND proof.  Nothing here is new mathematics.  The only edits are mechanical: the `private ` modifier was dropped and the affected declarations were wrapped in the internal `CurvatureCoefficientDifferenceJetTower` scope so that the public `Connection` namespace is byte-for-byte the old API.

Verification: targeted module build GREEN (single Lean process, `-LeanThreads 1`), zero errors, zero `sorry`.
Chunk map, memory figures and the split recipe: `../CurvatureCoefficientDifferenceJetTower.md`.
