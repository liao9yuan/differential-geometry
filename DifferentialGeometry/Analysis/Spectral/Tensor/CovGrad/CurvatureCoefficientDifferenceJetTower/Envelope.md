# Envelope

## 2026-08-03: created by the `CurvatureCoefficientDifferenceJetTower` monolith split

Chunk 6.  Per-order L2 ball-uniform bounds for the order-0 coefficients and their tame envelopes.

- 1414 lines; 12 public declarations at `Integral.Connection` level, 1 internal ones in the `CurvatureCoefficientDifferenceJetTower` scope.
- Imports: `TraceGrid`; everything else arrives transitively.
- Public API contributed by this chunk:
  - `rfns_iteratedCovGrad_riemannCoeff_metricFactorTelescope_diagonalProductGrid_le`
  - `rfns_iteratedCovGrad_ricciArmOrder0RiemannCoeff_backgroundDifference_diagonalProductGrid_le`
  - `slotInsertEndoCc_ricEndoBackgroundDifferenceField_perOrder_l2_ballUniform`
  - `ricciArmOrder0RiemannCoeff_backgroundDifference_perOrder_l2_ballUniform`
  - `ricciArmOrder0CurvCoeff_backgroundDifference_perOrder_l2_ballUniform`
  - `antidiagonalTupleGrid_integral_ballUniform_tameWindow`
  - `raisedKoszul_perOrder_l2_le_iteratedCovGrad_succ`
  - `slotInsertEndoCc_ricEndoBackgroundDifferenceField_perOrder_l2_tameEnvelope`
  - `ricciArmOrder0RiemannCoeff_backgroundDifference_perOrder_l2_tameEnvelope`
  - `ricciArmOrder0CurvCoeff_backgroundDifference_perOrder_l2_tameEnvelope`
  - `ricciArmOrder0BaseCoeff_backgroundDifference_perOrder_l2_tameEnvelope`
  - `ricciArmOrder0BaseCoeff_perOrder_l2_tameEnvelope_generic`

Every declaration is verbatim from the monolith — statement AND proof.  Nothing here is new mathematics.  The only edits are mechanical: the `private ` modifier was dropped and the affected declarations were wrapped in the internal `CurvatureCoefficientDifferenceJetTower` scope so that the public `Connection` namespace is byte-for-byte the old API.

Verification: targeted module build GREEN (single Lean process, `-LeanThreads 1`), zero errors, zero `sorry`.
Chunk map, memory figures and the split recipe: `../CurvatureCoefficientDifferenceJetTower.md`.
