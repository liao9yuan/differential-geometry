# ResidualCells

## 2026-08-03: created by the `CurvatureCoefficientDifferenceJetTower` monolith split

Chunk 10.  The two product-cell integral lemmas.  They depend on NOTHING else in this module, so this chunk imports only the monolith’s own 22 imports; that is what keeps the hog in chunk 11 inside the memory budget.  Do not re-point its imports at the main chain.

- 823 lines; 0 public declarations at `Integral.Connection` level, 2 internal ones in the `CurvatureCoefficientDifferenceJetTower` scope.
- Imports: the monolith's own 22 imports (this chunk is a root of the chunk DAG).
- Contributes no public declarations (internal layer only).

Every declaration is verbatim from the monolith — statement AND proof.  Nothing here is new mathematics.  The only edits are mechanical: the `private ` modifier was dropped and the affected declarations were wrapped in the internal `CurvatureCoefficientDifferenceJetTower` scope so that the public `Connection` namespace is byte-for-byte the old API.

Verification: targeted module build GREEN (single Lean process, `-LeanThreads 1`), zero errors, zero `sorry`.
Chunk map, memory figures and the split recipe: `../CurvatureCoefficientDifferenceJetTower.md`.
