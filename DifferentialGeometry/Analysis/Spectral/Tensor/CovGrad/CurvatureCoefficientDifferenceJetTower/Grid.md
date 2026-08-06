# Grid

## 2026-08-03: created by the `CurvatureCoefficientDifferenceJetTower` monolith split

Chunk 1 (root).  Carries the original 22 imports for the whole chain.  Ricci endomorphism fields on the frozen background, the order-0 curvature-coefficient background-difference decomposition, and the `tWindow` / `antidiagonalTupleGrid` counting layer.

- 1183 lines; 10 public declarations at `Integral.Connection` level, 20 internal ones in the `CurvatureCoefficientDifferenceJetTower` scope.
- Imports: the monolith's own 22 imports (this chunk is a root of the chunk DAG).
- Public API contributed by this chunk:
  - `ricEndoRaisedField`
  - `ricEndoBackgroundDifferenceField`
  - `ricEndoBackgroundDifferenceField_apply`
  - `ricciArmOrder0CurvCoeff_backgroundDifference_decomp`
  - `ricMixedSharpEndoFib`
  - `ricMixedSharpEndoFib_apply`
  - `ricMixedSharpEndoFib_contMDiff`
  - `ricMixedSharpEndoField`
  - `ricMixedSharpEndoField_apply`
  - `slotInsertEndoCc_zero_ricEndoBackgroundDifference_telescope`

Every declaration is verbatim from the monolith — statement AND proof.  Nothing here is new mathematics.  The only edits are mechanical: the `private ` modifier was dropped and the affected declarations were wrapped in the internal `CurvatureCoefficientDifferenceJetTower` scope so that the public `Connection` namespace is byte-for-byte the old API.

Verification: targeted module build GREEN (single Lean process, `-LeanThreads 1`), zero errors, zero `sorry`.
Chunk map, memory figures and the split recipe: `../CurvatureCoefficientDifferenceJetTower.md`.
