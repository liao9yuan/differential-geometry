# UnifAlgCoeffH3

## Role

`fullRaised_h3_unif` is the class-first affine `H3` bound for the full raised
rank-two algebraic coefficient.  Its `H2` smallness radius and coefficient are
chosen from the dimension-three metric class before the class metric varies.

## Proof route

The public `fullRaisedEndoField_diff_split` separates the inverse-metric
difference from the frozen identity.  `inv_coeff_h3_unif` controls the former.
The latter is parallel, so only its order-zero term survives; its uniform
`L2` cost is the dimension constant `27` times the class volume bound.  The two
parts are combined with a squared affine bound in the perturbation's spectral
`H3` norm.  No connection-difference estimate and no fourth metric jet enter.

## Verification

Verification has not yet been run.

## Project accounting

- `fullRaised_h3_unif`: theorem-level 0% until focused verification and direct
  axiom audit pass; dedicated implementation is written.
- The class-first full top-kernel algebraic coefficient producer is the target
  closed by this file; downstream kernel/product assembly remains separate.
- Dedicated uniform-existence machinery remains approximately 82%; whole HCG
  closure remains approximately 3%.
