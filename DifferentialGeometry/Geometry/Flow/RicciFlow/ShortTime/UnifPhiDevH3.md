# `UnifPhiDevH3`

## Role

`phi_dev_h3_unif` is the class-first homogeneous `H³` sibling of
`phi_dev_h2_unif`. It preserves the existing common `H²` realization radius and
pointwise deviation bound, and controls the full range-four covariant jet sum by
the sum of the two endpoint spectral `H³` norms.

## Proof route

- Reuse `phi_dev_h2_unif` for the unchanged pointwise estimate.
- Use `inv_coeff_h3_unif` for the homogeneous range-four inverse-coefficient
  jet estimate; its smallness hypothesis is still discharged by the convex
  path's `H²` bound.
- Bound the convex path's spectral `H³` norm directly by the sum of the endpoint
  norms using linearity and the triangle inequality.
- Apply the order-generic `trace_l2_le` and `ricci_l2_le` bounds through order
  three, then reuse the existing reindexing and norm-square algebra.

No uniform spectral `H⁴` to raw fourth-derivative conversion is used or needed.

## Status

Source is written. Focused verification, direct module refresh, and direct axiom
audit are pending.

## Progress boundary

- `phi_dev_h3_unif`: source implementation complete; theorem verification is
  pending.
- Dedicated homogeneous top-coefficient H3 machinery: nearly complete, pending
  this theorem's checks.
- Whole uniform-existence campaign: this is one local coefficient producer; its
  overall percentage remains governed by the campaign plan rather than this
  file.
