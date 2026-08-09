# SegmentPole.lean

## 2026-07-27 sharp pole normalization

`curveDensity_pole` is proved without a positivity assumption on the launch
vector.  A rectangular coefficient matrix expresses the transverse launch
frame in `chartModelBasis`.  Continuity of `normalGramMatrix` at zero and
`normalChartAt_metric_pullback_at_origin` identify the limiting Gram matrix
with the identity; `intrJacobi_raw`, radial Jacobi scaling, and determinant
scaling then give the normalized density limit.  The same proof covers
`finrank = 1`: the transverse matrix is empty, its determinant is one, and the
normalizing power is zero.

`poleLimit` and `transDens_le_hyp` now consume the sharp constant one.  Focused
verification passed without warnings.  The exact targeted artifact refresh
also passed, and `SegmentPole.olean` is current with the live source.

`transDens_le_one` extends the transverse comparison to the endpoint `t = 1`.
It uses scalar continuity of `curveDensity` and the model density together with
the already proved strict-left estimate; it does not assume endpoint
nonconjugacy.  Focused verification passed.

Honest accounting: `curveDensity_pole`, `poleLimit`, and
`transDens_le_hyp`, and `transDens_le_one` are theorem-level 100%.  The
sharp-pole subproject is 100%.
The absolute and relative segment-ball endpoints in `SegmentPolar.lean` remain
theorem-level 0%; their dedicated L6/L7 machinery is about 90%, and the full
time-zero `MetricCompactBase` theorem remains 0% because volume is only one of
its producer fields.
