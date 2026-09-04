# SegmentDensity

## Route

- Reparameterize a raw finite-action segment by `tau = s^2`, preserving
  absolute continuity and density integrability on a positive compact interval.
- Extract continuity directly from the epsilon--delta definition of absolute
  continuity, using a one-interval witness and the original metric-ball
  neighborhood basis. This avoids comparing whole Riemannian metric or
  tangent-bundle instances.
- Cover the compact image by finitely many chart intervals and realize each
  chart representative in `timeH1`; `lSegChartH1_fin` packages the resulting
  finite chart-H1 decomposition.
- Feed that decomposition to `lAction_c1_dense`, then use
  `lRegCostC1_le_bdd`, `le_lSegValue`, and the raw/regular action identity to
  prove `lSegValue_eq_reg`.
- `lSegValue_eq_of_seg` removes the redundant global-`C1` witness from
  downstream uses: one supplied finite-action endpoint segment is itself
  regularized by the checked density theorem, and its first global `C1`
  approximant witnesses nonemptiness.

## Failed routes

- Directly invoking the generic `continuousOn` or `uniformContinuousOn`
  projections caused `whnf` heartbeat timeouts while normalizing the local
  fixed-time metric.
- Installing a fresh Riemannian metric instance exposed a tangent-norm instance
  diamond. The final scalar metric-ball proof avoids that comparison entirely.

## Verification

- `SegmentDensity.lean` is warning-free focused GREEN.
- Direct axiom checks for `lSegChartH1_fin` and `lSegValue_eq_reg` report only
  `propext`, `Classical.choice`, and `Quot.sound`.
- `lSegValue_eq_of_seg` is warning-free focused GREEN and its direct axiom
  check reports the same three standard logical axioms.
- The exact `SegmentDensity` named refresh is GREEN. It was run under the
  script's exclusive global lock after the other repository tasks were
  confirmed inactive, because `PointedDensity` is now a real downstream
  consumer of the new exports.

## Progress

- `lSegChartH1_fin`: theorem endpoint 100%; dedicated raw-curve chart-H1
  machinery 100%.
- `lSegValue_eq_reg`: theorem endpoint 100%; dedicated density/infimum
  machinery 100%.
- `lSegValue_eq_of_seg`: theorem endpoint 100%; it adds no assumptions beyond
  the supplied raw endpoint segment and the hypotheses already used by the
  equality proof.
- The broader P2b package theorem remains unstated at 0%; its dedicated
  reduced-geometry machinery is approximately 88--91%.
- P2c remains an unstated 0% package with approximately 69--75% reusable smooth
  machinery. P2d, the P3 asymptotic shrinker, and `poincare_of_inputs` remain
  0%.
