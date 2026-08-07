# UnifH1L6RS

## Status (2026-08-06)

`h1Lp6RS_unif` is the dimension-three, class-first mixed-tensor `H¹ → L⁶`
producer.  It lowers upper indices with the varying metric, recasts the resulting
covariant section to the fixed background, and uses the strict order-one
cross-metric jet window.  Its honest metric inputs are uniform equivalence and
only `MetricCovDerivOrderBoundOn univ 1 g gBase Λ`; there is no reverse first
jet and no order-two jet.

Focused verification passed without warnings or `sorry`.  The axiom audit for
`h1Lp6RS_unif` reports exactly `propext`, `Classical.choice`, and `Quot.sound`,
with no `sorryAx`.  The theorem and its dedicated producer package are 100%
complete.  The larger class-first joint tame producer is still unstated (0%);
`lowreg_bounds_unif` and `ricci_flow_unif_existence` also remain theorem-level
0%.
