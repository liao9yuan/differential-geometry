# MetricPreconvWindowGInf.lean

## 2026-06-13

Implemented the first green C-II-final `gInf` brick in the new file.

What landed:
- `metricPreconvNorm`: exposes the pointwise `metricDerivNorm` convergence that
  sits inside `metricPreconvInf`, by reusing `metricPreconv_gInf`,
  `exists_uniform_patch`, `exists_diag_subseq`, and the finite-cover assembly.
- `netNormDiag`: diagonalizes those fixed-time pointwise norm producers over a
  countable time net, producing one master subsequence and one smooth limit
  metric for each net time.
- `windowOfNet`: records the final consumer shape once an all-time
  `Real -> SmoothRiemannianMetric` family is available and agrees with the
  net-time limits.

Verification: focused check and targeted module build passed. Axiom checks for
`metricPreconvNorm`, `netNormDiag`, and `windowOfNet` were clean: only
`propext`, `Classical.choice`, and `Quot.sound`.

Remaining blocker: the all-time `gInf : Real -> SmoothRiemannianMetric I M`
construction is still not implemented. The missing step is the Cauchy/extension
argument from net-time limits plus `hgLip`, followed by smoothness of each
time-slice. This file now leaves that as the single visible frontier instead of
repackaging it as an assumption inside the net-time diagonal.
