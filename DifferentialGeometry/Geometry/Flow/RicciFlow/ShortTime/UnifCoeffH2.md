# UnifCoeffH2

## 2026-08-06 class-first sharp-flat bound

`sharp_h2_unif` transports the already uniform sharp-flat pointwise grid
through `h2_low_unif`.  The pointwise grid occupies the final low-jet window,
so the proof inserts it into the nonnegative cumulative window explicitly.
The resulting `H2` coefficient is fixed before the class and path metrics
vary and consumes only class metric jets of orders one and two.

Focused verification passed without warnings.  Its axiom audit contains only
the standard `propext`, `Classical.choice`, and `Quot.sound`.  This closes one
factor needed by the class-first order-one Lie producer; that producer itself,
`lowreg_bounds_unif`, and `ricci_flow_unif_existence` remain theorem-level 0%.

## 2026-08-06 class-first lowered connection bound

`connLow_tame_unif` combines the class-first connection-difference grid with
the dimension-three class-first `H2` summation theorem.  It selects both affine
coefficient functions before the class metric varies and consumes only the
uniform-equivalence, first-jet, and second-jet class hypotheses.  The third
derivative in the statement belongs to the realized perturbation, not to the
varying class metric.

Focused verification passed without warnings.  Its axiom audit contains only
the standard `propext`, `Classical.choice`, and `Quot.sound`.  The theorem is
infrastructure for the order-one RHS producer; `lowreg_bounds_unif` and
`ricci_flow_unif_existence` remain theorem-level 0%.

## 2026-08-06 class-first moving trace bound

`trace2_h2_unif` combines `trace2_grid_unif` with the reusable low-window
summation theorem `h2_low_unif`.  Its coefficient is fixed before both the
class metric and the path metric vary, and it consumes only class metric jets
of orders one and two.  Focused verification passed without warnings; its
axiom audit contains only `propext`, `Classical.choice`, and `Quot.sound`.

`trace_h2_unif p` now supplies the same class-first package at arbitrary
passenger rank.  It applies `h2_low_unif` to `trace_grid_unif p`; the only
dimension-specific input remains the three-dimensional Sobolev summation.
The existing `trace2_h2_unif` statement remains available as a specialization.

The rank-generic theorem and the preserved rank-two wrapper now pass focused
verification and direct export without warnings.  The axiom census for
`trace_h2_unif` contains only `propext`, `Classical.choice`, and `Quot.sound`.
