# CrossingCost

## Scope

This file implements the smooth fixed-manifold content of book 12,
`lem:red-crossing-cost`.  It deliberately contains no Ricci-flow-spacetime,
surgery-event, or worldline interface.

## Native route

- `lLength S T gamma a b` is the book's backward-time action: its density is
  `sqrt tau * (R + |gamma'|^2)` at forward time `T - tau`.
- `Variation.arcLength gRef gamma a b` is the canonical fixed-reference-metric
  length.  The hypothesis `d <= arcLength` is the curve-level form of crossing
  two sets whose `gRef`-distance is at least `d`.
- On the interval, scalar curvature is bounded below by `Q` and the moving
  metric is bounded below by `c * gRef` along the curve velocity.  The proof
  applies
  `Q + c |gamma'|^2 >= 2 sqrt(c Q) |gamma'|`, multiplies by the lower time
  weight `sqrt a`, and integrates.

The theorem requests only the metric-family smoothness and scalar continuity
used to integrate `lDensity`; it does not require the Ricci-flow equation or
the other fields of `IsSolutionOn`.

The stronger endpoint/set-distance presentation can discharge the crossing
hypothesis through the existing Riemannian arc-length distance bridge.  It is
not duplicated here because that bridge currently lives in the higher
comparison layer; this L-geometry theorem only needs the canonical arc length.

## Status

- `lLength_cross`: source written, with no `sorry`, `admit`, axiom, or new
  frontier predicate.
- Focused source verification and the named module refresh are warning-free
  GREEN.  The unified P2 public axiom audit is also GREEN.
- Target theorem: source-complete and focused-check verified (100% at the source
  theorem level).  Dedicated local machinery: 100%.  Exported-artifact and
  public-axiom verification are complete.
- This is one local P2c crossing estimate; it is well below 1% of the whole
  Poincare formalization program and does not implement surgery spacetime.

## Local lessons

- Import `Geometry.Geodesic.MaximalInterval` directly before using
  `Geodesic.speedSqrt_integrableOn_Icc_of_C1`, and keep the qualified identifier
  intact rather than ending a source line at its namespace dot.
- Close a zero-velocity branch at its actual residual goal `0 <= 0`; do not
  rely on a preceding simplification to discharge it implicitly.
- For local `let` constants in algebraic rewrites, `simp only [K, hroot]`
  unfolds the local definition reliably where `rw [K, hroot]` does not.
- Locally omit unused section instances so the focused theorem check remains
  warning-free without strengthening or changing the public statement.
