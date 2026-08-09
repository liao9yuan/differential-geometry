# CurvatureDerivativeAlong

## Role

This module is the chain-rule bridge between the intrinsic along-curve object
`curvDerivAlong` and the pointwise curvature derivative
`nablaRiemannOp`. It carries no HCG-specific bound or forcing assumption.

## Current result

The arbitrary-field bridge is complete.

- `curvDeriv_restrict` identifies `curvDerivAlong` on restrictions of three
  smooth global fields with `nablaRiemannOp`.
- `curvDeriv_congr_at` proves that, for smooth fields along a smooth curve,
  `curvDerivAlong` at one time depends only on the three field values at that
  time.
- `curvDeriv_eq_nabla` combines those results to identify the arbitrary
  along-curve object with the pointwise covariant derivative of the Riemann
  operator.

The point-value proof uses one smooth ambient chart-frame near the foot.
Each along-curve field is expanded in that frame with globally smooth scalar
coefficient germs. The finite-sum and smooth-scalar linearity lemmas for
`curvDerivAlong` then reduce equality to equality of chart coordinates at the
evaluation time. No forcing or extension-compatibility assumption is added.

Focused verification and the exact module refresh are green. The exact refresh
completed 3803/3803, and the file has no `sorry`, `admit`, or `axiom`.

## H6 impact

This closes the full arbitrary-field `nabla R` forcing bridge. The next
mathematical step is to combine `curvDeriv_eq_nabla` with
`HasCurvDerivBound.nablaRiemannOp_le`, then bound the five lower curvature-slot
terms in the actual `jacVarForce` from the C0 curvature bound and the intrinsic
launch/Jacobi field estimates.

- `NormalRadiusProfile`: theorem completion remains 0%.
- `exists_h6NormalData`: theorem completion remains 0%.
- All-order intrinsic metric-jet machinery: about 53%.
- Whole native H6 producer machinery: about 68%.
- Whole HCG compactness machinery: about 62%; the unconditional textbook
  compactness endpoint remains 0%.
