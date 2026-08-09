# Residual

## 2026-08-03: created by the `CurvatureCoefficientDifferenceJetTower` monolith split

Chunk 9.  Opens `section TopSeparatedResidualIntegrator` with the ball-uniform tame-window integrator.  Hangs off `Envelope`, not off `TsRungs` — see the chunk map for why.

- 191 lines; 1 public declarations at `Integral.Connection` level, 0 internal ones in the `CurvatureCoefficientDifferenceJetTower` scope.
- Imports: `Envelope`; everything else arrives transitively.
- Public API contributed by this chunk:
  - `boundedFactorGridWindow_integral_ballUniform_tameWindow`

Every declaration is verbatim from the monolith — statement AND proof.  Nothing here is new mathematics.  The only edits are mechanical: the `private ` modifier was dropped and the affected declarations were wrapped in the internal `CurvatureCoefficientDifferenceJetTower` scope so that the public `Connection` namespace is byte-for-byte the old API.

Verification: targeted module build GREEN (single Lean process, `-LeanThreads 1`), zero errors, zero `sorry`.
Chunk map, memory figures and the split recipe: `../CurvatureCoefficientDifferenceJetTower.md`.
