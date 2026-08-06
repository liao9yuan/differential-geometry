# Lowered

## 2026-08-03: created by the `CurvatureCoefficientDifferenceJetTower` monolith split

Chunk 2.  The lowered Riemann background difference (`riemannLoweredCovec` and its section/Cc packaging) and the top-separated / t-grid bounds for the connection difference.

- 1266 lines; 11 public declarations at `Integral.Connection` level, 27 internal ones in the `CurvatureCoefficientDifferenceJetTower` scope.
- Imports: `Grid`; everything else arrives transitively.
- Public API contributed by this chunk:
  - `riemannLoweredCovec`
  - `riemannLoweredCovec_apply`
  - `riemannLoweredCovec_section_contMDiff`
  - `riemannLoweredField`
  - `riemannLoweredCc`
  - `riemannLoweredCc_unitModel`
  - `riemannLoweredCc_unitModel_apply`
  - `riemannLoweredBackgroundDifference`
  - `riemannLoweredBackgroundDifference_unitModel_apply`
  - `rfns_iteratedCovGrad_connDiffSection_topSeparated_le`
  - `exists_rfns_iteratedCovGrad_connDiffSection_tgrid`

Every declaration is verbatim from the monolith — statement AND proof.  Nothing here is new mathematics.  The only edits are mechanical: the `private ` modifier was dropped and the affected declarations were wrapped in the internal `CurvatureCoefficientDifferenceJetTower` scope so that the public `Connection` namespace is byte-for-byte the old API.

Verification: targeted module build GREEN (single Lean process, `-LeanThreads 1`), zero errors, zero `sorry`.
Chunk map, memory figures and the split recipe: `../CurvatureCoefficientDifferenceJetTower.md`.
