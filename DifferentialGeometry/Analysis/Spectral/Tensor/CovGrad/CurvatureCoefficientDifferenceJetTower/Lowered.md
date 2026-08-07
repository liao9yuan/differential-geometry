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

## 2026-08-06 class-first sharp-flat grid

`sharpFlat_grid_unif` now chooses one nonnegative coefficient sequence after
the fibre-smallness ceiling and before either metric varies.  It combines the
class-first inverse-difference grid `invDiff_zero_unif` with the explicit
dimension-only self seed `rfns_idEndo_le`; all positive derivatives of the
self term vanish by the existing parallelism theorem.  The former long theorem
`exists_rfns_iteratedCovGrad_sharpFlatEndoCc_tgrid` is retained as a thin
metric-local compatibility wrapper.

Focused verification and direct export passed.  Both the class-first theorem
and its compatibility wrapper depend only on the standard project axioms
`propext`, `Classical.choice`, and `Quot.sound`.

`sharpFlat_grid_unif` is complete (100%).  The next producer is the analogous
class-first connection-difference grid; `lowreg_bounds_unif` and
`ricci_flow_unif_existence` remain theorem-level 0%.

`connDiff_grid_unif` now completes that next producer: it keeps the explicit
Leibniz/antidiagonal constants of the former metric-local proof but consumes
the class-first sharp-flat sequence before introducing `g₀` or `g₁`.  The old
`exists_rfns_iteratedCovGrad_connDiffSection_tgrid` declaration is now a thin
compatibility wrapper.  Focused verification and axiom auditing passed; both
declarations use only `propext`, `Classical.choice`, and `Quot.sound`.

The class-first connection-difference grid is complete (100%).  The next
short-time adapter is its `H²` tame package via `h2_tame_unif`.
