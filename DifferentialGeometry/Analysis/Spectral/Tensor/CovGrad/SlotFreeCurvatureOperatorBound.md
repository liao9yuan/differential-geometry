# SlotFreeCurvatureOperatorBound

## Purpose

This file is the invariant-norm bridge for the canonical rank-one operator
`slotFreeOpCc g 1`. It turns supplied tangent-operator caps for `Rm` and
`nabla Rm` into pointwise mixed-tensor fibre caps at coefficient jet orders
zero and one.

## Route

The implementation specializes the existing orthonormal-frame Parseval route
used by `GradSlotCurvatureBound`. Rank one has exactly one covariant passenger
slot, so the component formula contains one curvature insertion and no
two-slot triangle estimate. The resulting general-dimensional powers are
`d^4` at order zero and `d^5` at order one.

The source uses `slotFreeCurvOpFib_apply_eval` and `slotFree_cov_eval` directly;
it introduces no new curvature hypothesis or consumer-side package.

## Verification

The two public bounds pass a warning-free focused Lean check and the module has
a fresh exact export. Their axiom audits report only `propext`,
`Classical.choice`, and `Quot.sound`. The only local repair needed was to make
three `toModel` normal forms explicit before rewriting.

## Project status

These two verified bounds are supporting producer machinery only.
The class-first joint tame producer remains unstated (0%);
`lowreg_bounds_unif`, `lowreg_dt_unif`, and `ricci_flow_unif_existence` remain
0%. The whole HCG theorem closure remains approximately 3%.
