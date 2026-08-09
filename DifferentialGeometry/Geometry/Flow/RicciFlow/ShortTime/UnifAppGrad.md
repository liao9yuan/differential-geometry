# UnifAppGrad

## Status (2026-08-06)

`appCc_grad_unif` is the dimension-three class-first wrapper around the
order-two mixed product grid.  Its coefficient is fixed from the background,
class parameter, and valences before the class metric and tensor fields vary.

The lower analysis theorem `appCc_grad_of_grid` consumes a supplied collapsed
grid bound.  The existing metricwise `appCc_grad_l2` now derives that collapsed
bound from its old raw two-arm certificate and reuses the same helper, so its
public interface is unchanged.

Focused verification passed without warnings or `sorry`.  The axiom audit for
`appCc_grad_of_grid`, the refactored `appCc_grad_l2`, and `appCc_grad_unif`
reports only `propext`, `Classical.choice`, and `Quot.sound`; none depends on
`sorryAx`.  This wrapper closes only the differentiated
application cell; the remaining Sobolev comparison constants in the full
`H³ → H¹` and `H² → H¹` application theorems must still be made class-first.
The joint tame producer, `lowreg_bounds_unif`, and
`ricci_flow_unif_existence` remain theorem-level 0%.
