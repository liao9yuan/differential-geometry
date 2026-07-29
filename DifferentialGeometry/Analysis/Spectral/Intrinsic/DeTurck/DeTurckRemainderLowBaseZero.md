# DeTurckRemainderLowBaseZero

## Role

This module records the first action-level consequence of the public
fixed-order zero-arm refold without duplicating its Riemann or Lie algebra.

## Verified state

`zeroA2Act` is the refolded second-order action and `zeroLowAct` is the
remaining algebraic lower action. `zeroPath_split` compares the original
three-arm path identity with `rhs_sub_zero_refold` and cancels the common top
arm through `refoldTopInt_eq`. Focused verification passes, and the file has
no `sorry`, `admit`, axiom declaration, or `whnf`.

`zeroLowAct` is deliberately not advertised as the final `A1`: its
zero-order coefficient still exposes a fourth-state-derivative head under
the available radius-free estimate.

## Route audit

- The RicciFlower-native route lacks public evaluation/decomposition lemmas
  for the complete order-zero fibre action.
- The finite-order refold route reaches private `lc0w_*` decompositions in
  the oversized tame file. The public pointwise residual estimate retains an
  explicit `nabla^(i+2) T` head, so it cannot yield the required `H3 -> H2`
  action bound by itself.
- The chart-linearization route cannot consume `realizedFam`:
  `IsMetricPerturbationFamily` requires globally smooth component functions
  on the whole model space, whereas realized chart Gram fields are only
  smooth on the chart target. No cutoff-family producer is public.

Thus `LowBaseActionSplit` remains unstated and unproved (0%); final `A1`
high/low/compatibility remain 0%. Dedicated uniform-existence machinery
remains conservatively 88--90%.

