# Pointwise pointed reduced-density convergence

## Route

- `redDensity_pt_lim` specializes the checked `lSegValue_pt_lim` theorem to
  square-root time `[0, sqrt tau]` and unrestricted spacetime domains.
- The restricted segment values are identified with ordinary `lCost` through
  the raw-segment density theorem and `lCost_eq_reg`; convergence in
  `WithTop Real` is reflected to `Real` with `WithTop.tendsto_untopD`.
- Unfolding `redLength` gives convergence after division by the fixed positive
  normalization.  Continuity of negation, subtraction, and `Real.exp` then
  yields pointwise convergence of `redDensity`.
- The statement keeps exactly the compact/chart confinement and scalar lower
  bounds used by the pointed value producer.  It introduces no desired
  convergence assumption, kappa-solution data, surgery data, or RFWS object.

## Elaboration notes

- The first pass exposed the standard tangent-fiber instance diamond while
  constructing a temporary Riemannian endpoint connector, plus missing local
  pseudo-metric installations in the density expression.  Disabling only the
  legacy tangent norm instances in that private construction and installing
  `lSegmentMetric` with the original chart topology resolved those local
  issues.
- The final source uses the canonical finite-action segment bridge from
  `SegmentDensity` rather than retaining a duplicate endpoint-connector route.

## Verification

- The canonical-bridge source passed a warning-free focused check.
- A direct audit of the final canonical `redDensity_pt_lim` source reported only
  `propext`, `Classical.choice`, and `Quot.sound`.
- The exact named module refresh passed once this declaration had a real
  compact-density downstream consumer.  A final warning-free focused check
  passed after documenting the necessary heartbeat allowance.
- A final local style pass removed the empty line immediately after the theorem
  command; the mathematical statement and proof are unchanged.

## Progress

- `redDensity_pt_lim`: theorem endpoint 100%; dedicated pointwise-density
  machinery 100%.
- The later compact-test integral convergence theorem remains unstated (0%);
  its dedicated P2b machinery is advanced by this pointwise endpoint but still
  requires the already checked chart-volume-density and measurability inputs.
- P2d eventwise/surgery reduced geometry and the P3 asymptotic-shrinker
  endpoint remain 0% and are outside this module.
