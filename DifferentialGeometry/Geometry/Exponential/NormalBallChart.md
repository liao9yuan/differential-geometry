# NormalBallChart

## 2026-07-27 H6 metric-jet base

`NormalBallChart.MetricEquivOn.deriv_zero` is the provider-independent
order-zero bridge for the H6 metric-jet induction. The existing half/two
quadratic estimate first gives the mixed bilinear estimate through
`MetricEquivOn.abs_apply_le`; taking the bilinear operator norm then yields
`MetricDerivBound ... 0 2`.

`NormalBallChart.MetricDerivBound.of_eqOn` is the complementary
provider-independent transfer lemma. Equality of two metric maps on an open
coordinate domain gives equality of every `iteratedFDeriv` at its points, so
an intrinsic metric-jet estimate transfers to the metric carried by a
`NormalBallChart` without changing its constant.

This is routine reusable geometry, not a producer theorem and not an
all-orders result. It closes only the base case that every future
`exists_intr_metricJets` induction may reuse, together with the final
provider-transfer step. The source is focused-green; its artifact refresh is
deferred while an unrelated exact build owns the shared write chain.

Progress accounting: `exists_h6NormalData` remains unstated (theorem-level
0%). Dedicated all-order metric-jet machinery remains about 35%; this local
base and transfer API is less than 3% of that machinery. Overall dedicated H6
producer machinery remains about 55%, and unconditional MSM135 Theorem 3.9
remains 0%.
