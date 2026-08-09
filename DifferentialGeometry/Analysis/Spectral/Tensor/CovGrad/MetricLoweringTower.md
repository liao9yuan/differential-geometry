# MetricLoweringTower

## Status (2026-08-06)

This file is the project-native mixed-index lowering adapter for the
three-dimensional class-uniform Morrey route.

- `lowerRSField` and `lowerCc` concretely lower every upper index with the same
  metric that defines the Levi-Civita connection.
- `lowerCc_apply`, `lowerCc_unit`, and `lowerCc_rfns` expose the section value
  and exact pointwise norm isometry.
- `lowerCc_jet_rfns` proves the pointwise fibre-norm identity for the complete
  three-dimensional Morrey window `j = 0,1,2`.
- `lowerCc_jet_norm` integrates that identity to the exact global `L²` jet
  isometry.

The lowering tower is complete.  Its one-step proof uses metric compatibility
and the constant slot rotation `[D,U,L] ↔ [U,D,L]`; the second-order case then
uses the existing iterated slot-permutation naturality theorem.  The public
statement remains intentionally limited to orders at most two.

Focused verification passed without warnings or `sorry`.  The exported jet
theorems were also axiom-audited: they use only the standard Lean axioms
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.

Progress: this lowering adapter and its theorems are 100% complete.  It is one
finished infrastructure component for the class-first tame producer;
`ricci_flow_unif_existence` itself remains unproved (0%), and the whole HCG
compactness project remains approximately 3% complete.
