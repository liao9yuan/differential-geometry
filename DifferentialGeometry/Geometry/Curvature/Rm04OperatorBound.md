# Rm04OperatorBound

## 2026-07-27 intrinsic curvature-operator estimate

Added the reusable pointwise estimate `riemannOp_sq_le`.  It bounds
`|R(J,V)V|_g^2` by the intrinsic fiber norm of `metricRm04At`, the squared
lengths of `J` and `V`, and one explicit dimension factor.  The statement has
no exponential-map, radial-coordinate, compactness, or Ricci-flow hypotheses.

This is dedicated H6 machinery, not the H6 radius-profile theorem itself.  The
next consumer is the intrinsic Jacobi ODE estimate in `IntrinsicGronwall`.
Focused verification passed without diagnostics.  The first exact refresh also
passed; a final no-warning refresh remains after removing an unused private
`Fintype` binder.
