# UnifGridRS

## Status (2026-08-06)

This module is the smallest class-first mixed two-arm grid producer needed by
the dimension-three uniform-existence route.

- `gridRSClassC` replaces every per-metric `gridRsConst` coefficient by a
  finite expression in the fixed background-class `gnClassC` coefficients.
- `grid_rs_const_le` exposes the reusable comparison between those two
  coefficients for arbitrary finite grid order.
- `grid_rs_unif` fixes the order-two window and combines that coefficient cap
  with the two mixed `morreyRS_unif` pointwise bounds.  It chooses one constant
  before the class metric and tensor fields vary, and returns both integrability
  and the product bound in terms of the two `H2` jet radii.
- No consumer wrapper or new analytic assumption is introduced.

Focused verification passed without warnings or `sorry`, after one local
repair replacing a misoriented additive-monotonicity tactic.  A temporary
axiom census for `grid_rs_unif` reported only `propext`, `Classical.choice`, and
`Quot.sound`, with no `sorryAx`.  The module artifact was exported directly
after its two previously stale dependencies were refreshed.

The later public comparison `grid_rs_const_le` also passes focused
verification and direct refresh; its direct axiom audit reports the same three
standard axioms.

Progress accounting: `grid_rs_unif` and its dedicated source are 100%
complete.  This closes the class-first order-two mixed product-grid leaf, but
not the class-uniform application coefficients that consume it.  The
class-first joint tame producer, `lowreg_bounds_unif`, and
`ricci_flow_unif_existence` remain theorem-level 0%; dedicated
uniform-existence machinery is approximately 95%, and the whole HCG
compactness project remains approximately 3% complete.
