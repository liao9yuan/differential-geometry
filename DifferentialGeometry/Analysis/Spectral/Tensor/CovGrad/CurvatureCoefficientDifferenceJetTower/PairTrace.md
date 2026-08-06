# PairTrace

## 2026-08-03: created by the `CurvatureCoefficientDifferenceJetTower` monolith split

Chunk 4.  `appCcRS` slot algebra, the pure double-trace field, `pairTraceOp`, and the public moving-trace split `pureTrace_split`.

- 2015 lines; 5 public declarations at `Integral.Connection` level, 39 internal ones in the `CurvatureCoefficientDifferenceJetTower` scope.
- Imports: `Palatini`; everything else arrives transitively.
- Public API contributed by this chunk:
  - `rfns_iteratedCovGrad_riemannMixedCoeff_backgroundDifference_le_loweredDifference`
  - `rfns_iteratedCovGrad_riemannG1LoweringDifference_diagonalProductGrid_le`
  - `pureTrace`
  - `pureTrace_toSection`
  - `pureTrace_split`

Every declaration is verbatim from the monolith — statement AND proof.  Nothing here is new mathematics.  The only edits are mechanical: the `private ` modifier was dropped and the affected declarations were wrapped in the internal `CurvatureCoefficientDifferenceJetTower` scope so that the public `Connection` namespace is byte-for-byte the old API.

Verification: targeted module build GREEN (single Lean process, `-LeanThreads 1`), zero errors, zero `sorry`.
Chunk map, memory figures and the split recipe: `../CurvatureCoefficientDifferenceJetTower.md`.
