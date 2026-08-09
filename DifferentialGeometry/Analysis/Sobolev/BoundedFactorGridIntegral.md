# BoundedFactorGridIntegral

## 2026-08-03: generic integration layer for `Combinatorics.boundedFactorGrid`

New sibling of `BoundedFactorProductGrid.lean` (the canonical home of
`boundedFactorGrid`), added rather than extending that file so that no existing
module's import closure changes.  Four generic lemmas over an arbitrary factor
family `b : X → ℕ → ℝ` on a compact space with a finite measure —
`bdFactorCell_int`, `bdFactorGrid_cont`, `bdFactorGrid_int`,
`bdFactorGrid_int_eq` — i.e. cell integrability, grid continuity, grid
integrability, and grid integral = double sum of cell integrals.

They carry no tensor or manifold structure, so they cost nothing to elaborate
(1.41 GB peak = the bare import floor); the geometric consumer
(`…CurvatureCoefficientDifferenceJetTower/ResidualFlat.lean`) instantiates `b`
with a pointwise fibre norm.  Extracted from the former inline
`hcell_int`/`hgrid_cont`/`hgrid_int`/`hgrid_eq` blocks of
`boundedFactorGrid_cappedTopLayer_integral_flat`; no new mathematics.

`finOnCpt` (private) builds `IsFiniteMeasureOnCompacts` from `IsFiniteMeasure`,
because Mathlib has no instance in that direction; taking `IsFiniteMeasure`
means the consumer only has to supply what it already has.

Verification: focused check and targeted build both GREEN, no warnings.
