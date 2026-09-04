# VolumeConvergence

## Role

`ConvOut.volDens_compOn` is the compact-chart Riemannian volume-density
producer for the P2b pointed reduced-geometry package.  It converts the already
checked uniform convergence of fixed-chart Gram operators into uniform
convergence of `chartDensity` along compact-confined coordinate paths.

## Route

- Reuses `ConvOut.chartGram_convOn` and `chartGramOp_bound`.
- Uses a private scalar functional obtained from the coordinate Gram matrix of
  a fixed-chart Gram operator.  This normalization is essential because
  `chartModelBasis` need not be orthonormal for the ambient inner product.
- Restricts the scalar functional to one compact operator-norm ball, where
  continuity gives uniform continuity; no extra metric-positivity hypothesis is
  added.
- The result is an ordinary smooth pointed-flow producer and does not introduce
  surgery or RFWS data.

## Verification

Focused verification is warning-free GREEN.  The first pass exposed only two
local `let`-set unfolding shapes and an implicit final density rewrite; both
were resolved by stating the ball-membership goals and the intermediate
density convergence explicitly.  No mathematical or API blocker appeared.
The exact named module refresh is GREEN now that the compact reduced-density
consumer is being implemented.

The same file now also provides the source pullback-density bridge.  The
parametrization `mapChartParam` has the mathematically forced order: preferred
chart inverse first, followed by the pointed comparison map.  On the
bump-one/source region, `paramDens_src_eq` identifies its parameter density for
the term metric with `chartDensity` of `gSeqExt`.  The proof reuses
`sourceFlow_metric_eq`, the pullback-metric inner-product formula,
`gSeqExt_inner_of_mem`, and
`paramDensity_eq_abs_det_mul_chartDensity`; it introduces no new metric or
compactness assumption.  The new declarations are warning-free focused GREEN.
Their direct axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound`.

## Next consumer

The active consumer is compact-test convergence of transported reduced-density
measures.  Pointwise reduced-density convergence and the source
Riemannian-volume pullback-density bridge are now checked; the next assembly can
rewrite the source-manifold integral in the common coordinate chart.
